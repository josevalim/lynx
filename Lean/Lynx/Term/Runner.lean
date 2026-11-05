module

public import Lynx.Term.Dispatch
public import Lynx.Concurrent

/-! Finite local-process execution. Sends insert directly into the destination
mailbox; message transit, remote processes, links, and monitors are not
modeled. Positive receive timeouts are scheduler events, with no elapsed-time
model. Zero timeouts are immediate; infinity never expires. Scheduling occurs
after spawn/send/receive completion, and another
runnable process takes over when the current one blocks or terminates.
Only continuations created by this run can execute: saved Environment entries
are state snapshots, not independent external actors. Deadlock is relative to
that closed execution.
-/

namespace Lynx.Term.Runner

open Lynx Lynx.Concurrent

/-- Preserve the process tree so advancing either branch has a structural
termination argument. Completion callbacks distinguish the root from children. -/
private inductive Pool (α : Type) where
  | empty
  | process {β : Type} : PID → Result β → (Except Exception β → Option (Except Exception α)) → Pool α
  | parallel : Pool α → Pool α → Pool α

/-- Each step replaces a computation by its continuations, possibly in either
parallel branch. This relation ignores scheduler and mailbox contents. -/
private inductive Progress : Pool α → Pool α → Prop where
  | ok : Progress .empty (.process processId (.ok value) finish)
  | error : Progress .empty (.process processId (.error exception) finish)
  | get : Progress (.process processId (next env) finish) (.process processId (.get next) finish)
  | set : Progress (.process processId next finish) (.process processId (.set env next) finish)
  | send : Progress (.process processId next finish) (.process processId (.send dest message next) finish)
  | receive : Progress (.process processId (next reply) finish)
      (.process processId (.receive timeout select next) finish)
  | schedule : Progress (.parallel (.process processId (next childPid) finish)
      (.process childPid child (fun _ => none))) (.process processId (Result.schedule child next) finish)
  | left : Progress a' a → Progress (.parallel a' b) (.parallel a b)
  | right : Progress b' b → Progress (.parallel a b') (.parallel a b)

private theorem accEmpty : Acc (@Progress α) .empty := by
  constructor
  intro p h
  cases h

private theorem accParallel (a b : Pool α) (ha : Acc Progress a) (hb : Acc Progress b) :
    Acc Progress (.parallel a b) := by
  induction ha generalizing b with
  | intro a ha iha =>
    induction hb with
    | intro b hb ihb =>
      constructor
      intro p h
      cases h with
      | left h => exact iha _ h _ (Acc.intro b hb)
      | right h => exact ihb _ h

private theorem accProcess {β : Type} (computation : Result β) :
    ∀ (processId : PID) (finish : Except Exception β → Option (Except Exception α)),
      Acc Progress (.process processId computation finish) := by
  induction computation with
  | ok value =>
    intro processId finish
    constructor
    intro p h
    cases h
    exact accEmpty
  | error exception =>
    intro processId finish
    constructor
    intro p h
    cases h
    exact accEmpty
  | get next ih =>
    intro processId finish
    constructor
    intro p h
    cases h with
    | get => apply ih
  | set env next ih =>
    intro processId finish
    constructor
    intro p h
    cases h
    apply ih
  | send dest message next ih =>
    intro processId finish
    constructor
    intro p h
    cases h
    apply ih
  | receive timeout select next ih =>
    intro processId finish
    constructor
    intro p h
    cases h <;> apply ih
  | schedule child next childIH nextIH =>
    intro processId finish
    constructor
    intro p h
    cases h with
    | schedule => exact accParallel _ _ (nextIH _ _ _) (childIH _ _)

private theorem wf : WellFounded (@Progress α) := by
  constructor
  intro p
  induction p with
  | empty => exact accEmpty
  | process processId c finish => exact accProcess c processId finish
  | parallel a b ha hb => exact accParallel a b ha hb

private abbrev Finished (α : Type) := Option (Except Exception α × ProcessState)

private def restore (root : PID) (finished : Finished α) (env : Environment) : Environment :=
  { env with currentPid := root
             currentProcess := match finished with
               | some (_, process) => process
               | none => (findProcess root env.processes).getD {}
             processes := removeProcess root env.processes }

private def findReady (env : Environment) (accept : PID → Bool) : Pool α → Option PID
  | .empty => none
  | .parallel left right => (findReady env accept left).orElse fun _ => findReady env accept right
  | .process processId computation _ =>
      if !accept processId then none else
        match computation with
        | .receive timeout select _ =>
            if (selectMessage (select (activate env processId)) ((findProcess processId env.processes).getD {}).mailbox).isSome
            then some processId else
              match timeout with
              | .infinity => none
              | .finite => none
              | .immediate => some processId
        | _ => some processId

/-- Only positive receives without a queued match can be explicitly expired. -/
private def findTimeout (env : Environment) (accept : PID → Bool) : Pool α → Option PID
  | .empty => none
  | .parallel left right => (findTimeout env accept left).orElse fun _ => findTimeout env accept right
  | .process processId computation _ =>
      if !accept processId then none else
        match computation with
        | .receive timeout select _ =>
            match timeout with
            | .finite =>
                if (selectMessage (select (activate env processId)) ((findProcess processId env.processes).getD {}).mailbox).isNone
                then some processId else none
            | _ => none
        | _ => none

/-- Consume one choice at each process-effect boundary. -/
private def schedule : List ScheduleChoice → ScheduleChoice × List ScheduleChoice
  | [] => (.current, [])
  | choice :: rest => (choice, rest)

/-- The current process if it can run, otherwise the first runnable process. -/
private def runnable (env : Environment) (pool : Pool α) : Option (PID × Bool) :=
  ((findReady env (· == env.currentPid) pool).orElse fun _ =>
    findReady env (fun _ => true) pool).map (·, false)

/-- The process a choice selects, falling back to a runnable one. -/
private def requested (env : Environment) (pool : Pool α) : ScheduleChoice → Option (PID × Bool)
  | .current => findReady env (· == env.currentPid) pool |>.map (·, false)
  | .swap processId => ((findReady env (· == processId) pool).map (·, false)).orElse fun _ =>
      runnable env pool
  | .timeout processId => ((findTimeout env (· == processId) pool).map (·, true)).orElse fun _ =>
      runnable env pool

/-- A blocked preferred process consumes another scheduling choice. Recursion
is bounded by the supplied choices; each execution step still decreases the
process tree. Without a choice, ordinary runnable processes precede expiry. -/
private def choose (pool : Pool α) (env : Environment) (preferred : ScheduleChoice)
    (choices : List ScheduleChoice) : List ScheduleChoice × Option (PID × Bool) :=
  match requested env pool preferred with
  | some chosen => (choices, some chosen)
  | none =>
      match choices with
      | choice :: rest => choose pool env choice rest
      | [] =>
          ([], (runnable env pool).orElse fun _ =>
            (findTimeout env (fun _ => true) pool).map (·, true))

private structure Advance (before : Pool α) where
  next : Pool α
  decreases : Progress next before
  environment : Environment
  finished : Finished α := none
  boundary : Bool := false
  exhausted : Bool := false

/-- Execute one structural step of the selected process. A blocked receive
returns no step; unmatched messages and the continuation remain intact. -/
private def step (pool : Pool α) (env : Environment) (chosen : PID) (expire : Bool) : Option (Advance pool) :=
  match pool with
  | .empty => none
  | .parallel left right =>
      match step left env chosen expire with
      | some transition => some {
          transition with next := .parallel transition.next right
                          decreases := .left transition.decreases }
      | none => (step right env chosen expire).map fun transition => {
          transition with next := .parallel left transition.next
                          decreases := .right transition.decreases }
  | .process processId computation finish =>
      if processId != chosen then none else
      let active := activate env processId
      match computation with
      -- A process that does not return ends the whole run.
      | .error .exhausted => some {
          next := .empty, decreases := .error, environment := active, exhausted := true }
      | .ok value => some {
          next := .empty, decreases := .ok, environment := active
          finished := (finish (.ok value)).map (·, active.currentProcess) }
      | .error exception => some {
          next := .empty, decreases := .error, environment := active
          finished := (finish (.error exception)).map (·, active.currentProcess) }
      | .get next => some {
          next := .process processId (next active) finish
          decreases := .get, environment := save active }
      | .set updated next => some {
          next := .process processId next finish
          decreases := .set, environment := save updated }
      | Result.schedule child next =>
          let childPid := active.pidCounter + 1
          let active := { active with
            pidCounter := childPid
            processes := (childPid, {}) :: active.processes }
          some {
            next := .parallel (.process processId (next childPid) finish)
              (.process childPid child (fun _ => none))
            decreases := .schedule, environment := save active
            boundary := true }
      | .send destination message next => some {
          next := .process processId next finish
          decreases := .send, environment := save (deliver active destination message)
          boundary := true }
      | .receive timeout select next =>
          match selectMessage (select active) active.currentProcess.mailbox with
          | some (_, value, remaining) => some {
              next := .process processId (next (some value)) finish
              decreases := .receive
              environment := save { active with currentProcess.mailbox := remaining }
              boundary := true }
          | none =>
              let reply : Option (Option _) := match timeout with
                | .infinity => none
                | .finite => if expire then some none else none
                | .immediate => some none
              reply.map fun reply => {
                next := .process processId (next reply) finish
                decreases := .receive
                environment := save active
                boundary := true }

private def isEmpty : Pool α → Bool
  | .empty => true
  | .parallel left right => isEmpty left && isEmpty right
  | .process .. => false

private instance : WellFoundedRelation (Pool α) := ⟨Progress, wf⟩

private def execute (root : PID) (env : Environment) (pool : Pool α)
    (finished : Finished α) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    Outcome α × Environment :=
  let (choices, chosen) := choose pool env preferred choices
  match chosen.bind (fun (processId, expire) => step pool env processId expire) with
  | none =>
      let final := restore root finished env
      match isEmpty pool, finished with
      | true, some (.ok value, _) => (.ok value, final)
      | true, some (.error exception, _) => (.error exception, final)
      | _, _ => (.deadlock, final)
  | some transition =>
      if transition.exhausted then
        (.error .exhausted, restore root finished (save transition.environment)) else
      let finished := transition.finished.orElse fun _ => finished
      let (preferred, choices) := if transition.boundary then schedule choices
        else (ScheduleChoice.current, choices)
      execute root transition.environment transition.next finished preferred choices
termination_by pool
decreasing_by exact transition.decreases

/-- Local computations execute structurally; concurrent execution decreases
through the process tree, without an execution budget. -/
def run (computation : Result α) (env : Environment) (choices : List ScheduleChoice) :
    Outcome α × Environment :=
  match computation with
  | .ok value => (.ok value, env)
  | .error exception => (.error exception, env)
  | .get next => run (next env) env choices
  | .set next continuation => run continuation next choices
  | Result.schedule _ _ | .send _ _ _ | .receive _ _ _ =>
      execute env.currentPid (save env) (.process env.currentPid computation some) none .current
        choices

/-! ### Soundness

Each execution is a `Concurrent.Run`. The process tree flattens into the
configuration's task list, and the scheduler only selects steps the
transition system allows. -/

private theorem orElse_eq_some {first : Option β} {second : Unit → Option β} {value : β} :
    first.orElse second = some value ↔
      first = some value ∨ first = none ∧ second () = some value := by
  cases first <;> simp [Option.orElse]

private theorem orElse_eq_none {first : Option β} {second : Unit → Option β} :
    first.orElse second = none ↔ first = none ∧ second () = none := by
  cases first <;> simp [Option.orElse]

private theorem isSome_orElse {first : Option β} {second : Unit → Option β} :
    (first.orElse second).isSome = (first.isSome || (second ()).isSome) := by
  cases first <;> simp [Option.orElse]

private def leaves : Pool α → List (PID × Concurrent.Task α)
  | .empty => []
  | .process processId computation finish => [(processId, ⟨computation, finish⟩)]
  | .parallel left right => leaves left ++ leaves right

private theorem isEmpty_iff (pool : Pool α) : isEmpty pool = true ↔ leaves pool = [] := by
  induction pool <;> simp_all [isEmpty, leaves]

private theorem findReady_accept {env : Environment} {accept : PID → Bool} {pool : Pool α}
    {chosen : PID} (found : findReady env accept pool = some chosen) : accept chosen = true := by
  induction pool with
  | empty => simp [findReady] at found
  | parallel left right ihl ihr =>
    simp only [findReady, orElse_eq_some] at found
    rcases found with found | ⟨_, found⟩
    · exact ihl found
    · exact ihr found
  | process processId computation finish =>
    simp only [findReady] at found
    split at found
    · simp at found
    · rename_i accepted
      have : chosen = processId := by
        split at found
        · split at found
          · simp at found; exact found.symm
          · split at found <;> simp_all
        · simp at found; exact found.symm
      simp_all

private theorem findTimeout_accept {env : Environment} {accept : PID → Bool} {pool : Pool α}
    {chosen : PID} (found : findTimeout env accept pool = some chosen) : accept chosen = true := by
  induction pool with
  | empty => simp [findTimeout] at found
  | parallel left right ihl ihr =>
    simp only [findTimeout, orElse_eq_some] at found
    rcases found with found | ⟨_, found⟩
    · exact ihl found
    · exact ihr found
  | process processId computation finish =>
    simp only [findTimeout] at found
    split at found
    · simp at found
    · rename_i accepted
      have : chosen = processId := by
        split at found
        · split at found
          · split at found <;> simp_all
          · simp at found
        · simp at found
      simp_all

/-- A process with a step that is not an expiry is found by `findReady`. -/
private theorem findReady_isSome {env : Environment} {accept : PID → Bool} {pool : Pool α}
    {processId : PID} {task : Concurrent.Task α} {transition : Concurrent.Transition α}
    (mem : (processId, task) ∈ leaves pool) (possible : transition ∈ task.transitions env processId)
    (unexpired : transition.expired = false) (accepted : accept processId = true) :
    (findReady env accept pool).isSome := by
  induction pool with
  | empty => simp [leaves] at mem
  | parallel left right ihl ihr =>
    simp only [leaves, List.mem_append] at mem
    simp only [findReady, isSome_orElse]
    rcases mem with mem | mem
    · simp [ihl mem]
    · simp [ihr mem]
  | process candidate computation finish =>
    simp only [leaves, List.mem_singleton, Prod.mk.injEq] at mem
    obtain ⟨rfl, rfl⟩ := mem
    simp only [findReady, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases computation with
    | receive timeout select next =>
      simp only [Task.transitions] at possible
      split at possible
      · rename_i selected
        simp [activate] at selected
        simp [activate, selected]
      · rename_i selected
        simp only [activate] at selected
        simp only [activate, selected, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        cases timeout <;> simp_all
    | _ => simp

/-- A process with an expiry step is found by `findTimeout`. -/
private theorem findTimeout_isSome {env : Environment} {accept : PID → Bool} {pool : Pool α}
    {processId : PID} {task : Concurrent.Task α} {transition : Concurrent.Transition α}
    (mem : (processId, task) ∈ leaves pool) (possible : transition ∈ task.transitions env processId)
    (expired : transition.expired = true) (accepted : accept processId = true) :
    (findTimeout env accept pool).isSome := by
  induction pool with
  | empty => simp [leaves] at mem
  | parallel left right ihl ihr =>
    simp only [leaves, List.mem_append] at mem
    simp only [findTimeout, isSome_orElse]
    rcases mem with mem | mem
    · simp [ihl mem]
    · simp [ihr mem]
  | process candidate computation finish =>
    simp only [leaves, List.mem_singleton, Prod.mk.injEq] at mem
    obtain ⟨rfl, rfl⟩ := mem
    simp only [findTimeout, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases computation with
    | receive timeout select next =>
      simp only [Task.transitions] at possible
      split at possible
      · simp_all
      · rename_i selected
        simp only [activate] at selected
        cases timeout <;> simp_all [activate]
    | ok | get | set | schedule | send => simp_all [Task.transitions]
    | error exception => cases exception <;> simp_all [Task.transitions]

private theorem step_isSome_of_findReady {env : Environment} {accept : PID → Bool}
    {pool : Pool α} {chosen : PID} (found : findReady env accept pool = some chosen) :
    (step pool env chosen false).isSome := by
  induction pool with
  | empty => simp [findReady] at found
  | parallel left right ihl ihr =>
    simp only [findReady, orElse_eq_some] at found
    simp only [step]
    rcases found with found | ⟨_, found⟩
    · have := ihl found
      split <;> simp_all
    · split
      · simp
      · simp [ihr found]
  | process processId computation finish =>
    simp only [findReady] at found
    split at found
    · simp at found
    · simp only [step]
      cases computation with
      | receive timeout select next =>
        simp only at found
        split at found
        · simp only [Option.some.injEq] at found
          subst found
          rename_i selected
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨_, selected⟩ := Option.isSome_iff_exists.mp selected
          simp only [activate] at selected ⊢
          simp [selected]
        · rename_i selected
          cases timeout <;> simp at found
          subst found
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
            activate] at selected ⊢
          simp [selected]
      | error exception =>
        simp only [Option.some.injEq] at found
        subst found
        cases exception <;> simp
      | _ =>
        simp only [Option.some.injEq] at found
        subst found
        simp

private theorem step_isSome_of_findTimeout {env : Environment} {accept : PID → Bool}
    {pool : Pool α} {chosen : PID} (found : findTimeout env accept pool = some chosen) :
    (step pool env chosen true).isSome := by
  induction pool with
  | empty => simp [findTimeout] at found
  | parallel left right ihl ihr =>
    simp only [findTimeout, orElse_eq_some] at found
    simp only [step]
    rcases found with found | ⟨_, found⟩
    · have := ihl found
      split <;> simp_all
    · split
      · simp
      · simp [ihr found]
  | process processId computation finish =>
    simp only [findTimeout] at found
    split at found
    · simp at found
    · simp only [step]
      cases computation with
      | receive timeout select next =>
        cases timeout <;> simp at found
        obtain ⟨selected, rfl⟩ := found
        simp only [activate] at selected ⊢
        simp [selected]
      | _ => simp at found

private theorem runnable_found {env : Environment} {pool : Pool α} {chosen : PID} {expire : Bool}
    (found : runnable env pool = some (chosen, expire)) : (step pool env chosen expire).isSome := by
  simp only [runnable, Option.map_eq_some_iff, Prod.mk.injEq, orElse_eq_some] at found
  obtain ⟨_, found, rfl, rfl⟩ := found
  rcases found with found | ⟨_, found⟩ <;> exact step_isSome_of_findReady found

private theorem requested_found {env : Environment} {pool : Pool α} {preferred : ScheduleChoice}
    {chosen : PID} {expire : Bool} (found : requested env pool preferred = some (chosen, expire)) :
    (step pool env chosen expire).isSome := by
  cases preferred with
  | current =>
    simp only [requested, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨_, found, rfl, rfl⟩ := found
    exact step_isSome_of_findReady found
  | swap processId =>
    simp only [requested, orElse_eq_some, Option.map_eq_some_iff, Prod.mk.injEq] at found
    rcases found with ⟨_, found, rfl, rfl⟩ | ⟨_, found⟩
    · exact step_isSome_of_findReady found
    · exact runnable_found found
  | timeout processId =>
    simp only [requested, orElse_eq_some, Option.map_eq_some_iff, Prod.mk.injEq] at found
    rcases found with ⟨_, found, rfl, rfl⟩ | ⟨_, found⟩
    · exact step_isSome_of_findTimeout found
    · exact runnable_found found

/-- The scheduler only selects processes that can step. -/
private theorem choose_isSome {pool : Pool α} {env : Environment} {preferred : ScheduleChoice}
    {choices remaining : List ScheduleChoice} {chosen : PID} {expire : Bool}
    (chose : choose pool env preferred choices = (remaining, some (chosen, expire))) :
    (step pool env chosen expire).isSome := by
  induction choices generalizing preferred with
  | nil =>
    unfold choose at chose
    cases found : requested env pool preferred with
    | some request =>
      simp only [found, Prod.mk.injEq, Option.some.injEq] at chose
      rw [chose.2] at found
      exact requested_found found
    | none =>
      simp only [found, Prod.mk.injEq, orElse_eq_some, Option.map_eq_some_iff] at chose
      rcases chose.2 with found | ⟨_, _, found, equal⟩
      · exact runnable_found found
      · obtain ⟨rfl, rfl⟩ := equal
        exact step_isSome_of_findTimeout found
  | cons choice rest ih =>
    unfold choose at chose
    cases found : requested env pool preferred with
    | some request =>
      simp only [found, Prod.mk.injEq, Option.some.injEq] at chose
      rw [chose.2] at found
      exact requested_found found
    | none =>
      simp only [found] at chose
      exact ih chose

/-- When nothing is chosen, no process has any step. -/
private theorem choose_none {pool : Pool α} {env : Environment} {preferred : ScheduleChoice}
    {choices remaining : List ScheduleChoice}
    (chose : choose pool env preferred choices = (remaining, none)) :
    ∀ processId task, (processId, task) ∈ leaves pool → task.transitions env processId = [] := by
  induction choices generalizing preferred with
  | nil =>
    unfold choose at chose
    cases found : requested env pool preferred with
    | some request => simp [found] at chose
    | none =>
      simp only [found, Prod.mk.injEq, orElse_eq_none, Option.map_eq_none_iff, runnable] at chose
      obtain ⟨_, ⟨_, ready⟩, timeout⟩ := chose
      intro processId task mem
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro transition possible
      cases expired : transition.expired
      · have := findReady_isSome (accept := fun _ => true) mem possible expired rfl
        simp_all
      · have := findTimeout_isSome (accept := fun _ => true) mem possible expired rfl
        simp_all
  | cons choice rest ih =>
    unfold choose at chose
    cases found : requested env pool preferred with
    | some request => simp [found] at chose
    | none =>
      simp only [found] at chose
      exact ih chose

/-- A ready current process keeps running after an environment access or exit. -/
private theorem choose_current {pool : Pool α} {env : Environment}
    {choices remaining : List ScheduleChoice} {chosen : PID} {expire : Bool}
    (chose : choose pool env .current choices = (remaining, some (chosen, expire)))
    (ready : Concurrent.Ready env (leaves pool) env.currentPid) :
    chosen = env.currentPid ∧ expire = false := by
  obtain ⟨task, mem, transition, possible, unexpired⟩ := ready
  obtain ⟨current, found⟩ := Option.isSome_iff_exists.mp
    (findReady_isSome (accept := (· == env.currentPid)) mem possible unexpired (by simp))
  have accepted := findReady_accept found
  unfold choose at chose
  simp only [requested, found, Option.map_some, Prod.mk.injEq, Option.some.injEq] at chose
  simp_all

/-- A process step of the runner is a step of the transition system. -/
private theorem step_sound {pool : Pool α} {env : Environment} {chosen : PID} {expire : Bool}
    {advance : Advance pool} (stepped : step pool env chosen expire = some advance) :
    ∃ before after task, leaves pool = before ++ (chosen, task) :: after ∧
      ∃ transition ∈ task.transitions env chosen,
        (expire = false → transition.expired = false) ∧
        leaves advance.next = before ++ transition.tasks ++ after ∧
        advance.environment = transition.environment ∧ advance.finished = transition.finished ∧
        advance.boundary = transition.boundary ∧ advance.exhausted = transition.exhausted := by
  induction pool with
  | empty => simp [step] at stepped
  | parallel left right ihl ihr =>
    simp only [step] at stepped
    split at stepped
    · rename_i advance' found
      simp only [Option.some.injEq] at stepped
      subst stepped
      obtain ⟨before, after, task, split, transition, possible, unexpired, tasks, rest⟩ := ihl found
      exact ⟨before, after ++ leaves right, task, by simp [leaves, split], transition, possible,
        unexpired, by simp [leaves, tasks], rest⟩
    · simp only [Option.map_eq_some_iff] at stepped
      obtain ⟨advance', found, rfl⟩ := stepped
      obtain ⟨before, after, task, split, transition, possible, unexpired, tasks, rest⟩ := ihr found
      exact ⟨leaves left ++ before, after, task, by simp [leaves, split], transition, possible,
        unexpired, by simp [leaves, tasks], rest⟩
  | process processId computation finish =>
    simp only [step] at stepped
    split at stepped
    · simp at stepped
    · rename_i same
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at same
      subst same
      refine ⟨[], [], ⟨computation, finish⟩, rfl, ?_⟩
      cases computation with
      | receive timeout select next =>
        simp only at stepped
        split at stepped
        · rename_i selected
          simp only [Option.some.injEq] at stepped
          subst stepped
          simp [Task.transitions, selected, leaves]
        · rename_i selected
          cases timeout <;> cases expire <;> simp only [Option.map_eq_some_iff] at stepped <;>
            simp at stepped <;> subst stepped <;> simp [Task.transitions, selected, leaves]
      | error exception =>
        cases exception <;> simp only [Option.some.injEq] at stepped <;> subst stepped <;>
          simp [Task.transitions, leaves]
      | _ =>
        simp only [Option.some.injEq] at stepped
        subst stepped
        simp [Task.transitions, Task.child, leaves]

private theorem execute_reaches (root : PID) (pool : Pool α) :
    ∀ env finished preferred choices sticky, (sticky = true → preferred = .current) →
      ∃ events last, Concurrent.Run (.running env (leaves pool) finished sticky) events last ∧
        Concurrent.Terminal last (execute root env pool finished preferred choices).1 := by
  induction pool using (wf (α := α)).induction with
  | _ pool ih =>
  intro env finished preferred choices sticky current
  rw [execute]
  generalize chose : choose pool env preferred choices = chosen
  obtain ⟨remaining, chosen⟩ := chosen
  simp only
  split
  · have blocked : ∀ processId task, (processId, task) ∈ leaves pool →
        task.transitions env processId = [] := by
      cases chosen with
      | none => exact choose_none chose
      | some chosen =>
        have := choose_isSome chose
        simp_all
    refine ⟨[], _, .refl, ?_⟩
    have deadlock (pending : isEmpty pool = false ∨ finished = none) :
        Concurrent.Terminal (.running env (leaves pool) finished sticky) .deadlock :=
      .deadlock blocked fun nil => by
        rcases pending with pending | pending
        · simp [← isEmpty_iff, pending] at nil
        · exact pending
    cases empty : isEmpty pool with
    | false => rcases finished with _ | ⟨_ | _, _⟩ <;> exact deadlock (.inl empty)
    | true =>
      have nil := (isEmpty_iff pool).mp empty
      rcases finished with _ | ⟨_ | _, _⟩
      · exact deadlock (.inr rfl)
      · rw [nil]; exact .raised
      · rw [nil]; exact .returned
  · rename_i advance stepped
    cases chosen with
    | none => simp at stepped
    | some chosen =>
    obtain ⟨processId, expire⟩ := chosen
    simp only [Option.bind_some] at stepped
    obtain ⟨before, after, task, split, transition, possible, unexpired, tasks, environment,
      finishedEq, boundary, exhausted⟩ := step_sound stepped
    have allowed : Concurrent.Allowed env (leaves pool) sticky processId transition := by
      intro sticky ready
      rw [current sticky] at chose
      obtain ⟨rfl, rfl⟩ := choose_current chose ready
      exact ⟨rfl, unexpired rfl⟩
    split
    · rename_i halted
      exact ⟨[transition.event], _,
        .step (.exhaust split possible allowed (exhausted ▸ halted)) .refl, .halted⟩
    · rename_i returns
      obtain ⟨events, last, run, terminal⟩ := ih advance.next advance.decreases
        advance.environment (advance.finished.orElse fun _ => finished)
        (if advance.boundary then schedule remaining else (ScheduleChoice.current, remaining)).1
        (if advance.boundary then schedule remaining else (ScheduleChoice.current, remaining)).2
        (!advance.boundary) (by intro sticky; simp_all)
      refine ⟨transition.event :: events, last, ?_, terminal⟩
      have step := Concurrent.Step.run (finished := finished) split possible allowed
        (by simp_all)
      rw [← tasks, ← environment, ← finishedEq, ← boundary] at step
      exact .step step run

private theorem enter_reaches (computation : Result α) (env : Environment)
    (choices : List ScheduleChoice) (request : isRequest computation = true) :
    ∃ events last, Concurrent.Run (.start env computation) events last ∧
      Concurrent.Terminal last (execute env.currentPid (save env)
        (.process env.currentPid computation some) none .current choices).1 := by
  obtain ⟨events, last, steps, terminal⟩ := execute_reaches env.currentPid
    (.process env.currentPid computation some) (save env) none .current choices true (fun _ => rfl)
  exact ⟨_, last, .step (.enter request) steps, terminal⟩

private theorem run_reaches (computation : Result α) (env : Environment)
    (choices : List ScheduleChoice) :
    ∃ events last, Concurrent.Run (.start env computation) events last ∧
      Concurrent.Terminal last (run computation env choices).1 := by
  induction computation generalizing env with
  | ok => exact ⟨[], _, .refl, by rw [run]; exact .ok⟩
  | error => exact ⟨[], _, .refl, by rw [run]; exact .error⟩
  | get next ih =>
    obtain ⟨events, last, steps, terminal⟩ := ih env env
    exact ⟨_, last, .step .get steps, by rw [run]; exact terminal⟩
  | set updated next ih =>
    obtain ⟨events, last, steps, terminal⟩ := ih updated
    exact ⟨_, last, .step .set steps, by rw [run]; exact terminal⟩
  | schedule | send | receive => rw [run]; exact enter_reaches _ env choices rfl

end Lynx.Term.Runner

public section

namespace Lynx

/-- Execute a computation in an existing environment, consuming the supplied
scheduler choices. Use `Lynx.sequential` to start from a fresh runtime. The
implementation is hidden; the application lemmas below describe its behavior,
and `Lynx.Result.run_reaches` relates it to `Lynx.Concurrent.Step`. Function
values are called through the `Dispatcher` the computation received, so running
needs no program table. -/
def Result.run (computation : Result α) (env : Environment)
    (choices : List ScheduleChoice := []) : Outcome α × Environment :=
  Term.Runner.run computation env choices

instance : CoeFun (Result α) fun _ => Environment → Outcome α × Environment :=
  ⟨fun computation env => computation.run env⟩

namespace Result

@[simp] theorem ok_apply (value : α) (env : Environment) (choices : List ScheduleChoice) :
    (Result.ok value : Result α).run env choices = (.ok value, env) := by
  change Term.Runner.run (.ok value) env choices = _
  rw [Term.Runner.run]

@[simp] theorem error_apply (exception : Exception) (env : Environment)
    (choices : List ScheduleChoice) :
    (Result.error exception : Result α).run env choices = (.error exception, env) := by
  change Term.Runner.run (.error exception) env choices = _
  rw [Term.Runner.run]

@[simp] theorem get_continuation_apply (continuation : Environment → Result α)
    (env : Environment) (choices : List ScheduleChoice) :
    (Result.get continuation).run env choices = (continuation env).run env choices := by
  change Term.Runner.run (.get continuation) env choices = _
  rw [Term.Runner.run]
  rfl

@[simp] theorem set_continuation_apply (next : Environment) (continuation : Result α)
    (env : Environment) (choices : List ScheduleChoice) :
    (Result.set next continuation).run env choices = continuation.run next choices := by
  change Term.Runner.run (.set next continuation) env choices = _
  rw [Term.Runner.run]
  rfl

/-- Every execution, under any scheduler choices, is a run of the transition
system ending in a terminal configuration with the same outcome. -/
theorem run_reaches (computation : Result α) (env : Environment) (choices : List ScheduleChoice) :
    ∃ events last, Concurrent.Run (.start env computation) events last ∧
      Concurrent.Terminal last (computation.run env choices).1 :=
  Term.Runner.run_reaches computation env choices

@[simp] theorem IsPure.ok_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (choices : List ScheduleChoice) (value : α) :
    computation.run env choices = (.ok value, final) ↔ computation = .ok value ∧ env = final := by
  cases computation <;> simp_all

@[simp] theorem IsPure.error_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (choices : List ScheduleChoice) (exception : Exception) :
    computation.run env choices = (.error exception, final) ↔
      computation = .error exception ∧ env = final := by
  cases computation <;> simp_all

end Result

end Lynx
