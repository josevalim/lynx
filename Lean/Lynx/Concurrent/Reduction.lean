module

public import Lynx.Concurrent
public import Lynx.Concurrent.Termination
public import Lynx.Concurrent.Footprint
import all Lynx.Concurrent.Footprint

/-! Reductions of `Lynx.Concurrent.check`: the steps of a configuration named by
keys, and the facts every reachable configuration satisfies. -/

public section

namespace Lynx.Concurrent

open Lynx


/-! Which records each operation changes. -/

private theorem State.processes_update {state : State} {processId other : PID}
    {process : Option ProcessState} :
    (state.update processId process).processes other =
      if other = processId then process else state.processes other := rfl

/-- Changing records keeps which processes are live, and the children they spawned. -/
private def State.Keeps (before after : State) : Prop :=
  ∀ processId, (after.processes processId).isSome = (before.processes processId).isSome ∧
    (after.process processId).children = (before.process processId).children

private theorem State.Keeps.refl (state : State) : state.Keeps state := fun _ => ⟨rfl, rfl⟩

private theorem State.Keeps.trans {first second third : State} (one : first.Keeps second)
    (two : second.Keeps third) : first.Keeps third := fun processId =>
  ⟨(two processId).1.trans (one processId).1, (two processId).2.trans (one processId).2⟩

private theorem State.keeps_modify {state : State} {processId : PID} {change : ProcessState → ProcessState}
    (children : ∀ process, (change process).children = process.children) :
    state.Keeps (state.modify processId change) := by
  intro other
  unfold State.modify
  split
  · rename_i process found
    by_cases same : other = processId
    · subst same; simp [State.process, State.update, found, children]
    · simp [State.process, State.update, same]
  · exact ⟨rfl, rfl⟩

private theorem State.keeps_append {state : State} {processId : PID} {message : Term} :
    state.Keeps (state.append processId message) :=
  State.keeps_modify fun _ => rfl

private theorem State.keeps_emit {state : State} {source target : PID} {signal : Signal} :
    state.Keeps (state.emit source target signal) := fun _ => ⟨rfl, rfl⟩

private theorem State.keeps_store {state : State} {processId : PID} {env : Environment} :
    state.Keeps (state.store processId env) :=
  State.keeps_modify fun _ => rfl

private theorem State.keeps_allocate {state : State} {processId : PID} :
    state.Keeps (state.allocate processId).2 :=
  State.keeps_modify fun _ => rfl

private theorem State.keeps_exitSignal {state : State} {target source : PID} {reason : Term}
    {linked : Bool} : state.Keeps (state.exitSignal target source reason linked).1 := by
  unfold State.exitSignal
  cases linked <;> simp only [Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true] <;>
    repeat' (first | (dsimp only; done) | split | exact State.Keeps.refl _ | exact State.keeps_append |
      (apply State.keeps_modify; intro; rfl) |
      (apply State.Keeps.trans (State.keeps_modify ?_) State.keeps_append; intro; rfl) | dsimp only)

private theorem State.keeps_receive {state : State} {envelope : Envelope} :
    state.Keeps (state.receive envelope).1 := by
  unfold State.receive
  split
  all_goals first
    | exact State.keeps_exitSignal
    | (repeat' (first | split | exact State.Keeps.refl _ | exact State.keeps_append |
        (apply State.keeps_modify; intro; rfl) |
        (apply State.Keeps.trans (State.keeps_modify ?_) State.keeps_append; intro; rfl) | dsimp only))

private theorem State.keeps_bounce {state : State} {envelope : Envelope} :
    state.Keeps (state.bounce envelope) := by
  unfold State.bounce
  split <;> first | exact State.keeps_emit | exact State.Keeps.refl _

private theorem State.keeps_fire {state : State} {timer : Timer} : state.Keeps (state.fire timer) :=
  fun _ => ⟨rfl, rfl⟩

private theorem State.keeps_timers {state : State} {timers : List Timer} :
    state.Keeps { state with timers } := fun _ => ⟨rfl, rfl⟩

private theorem State.Keeps.emit {state changed : State} {source target : PID} {signal : Signal}
    (kept : state.Keeps changed) : state.Keeps (changed.emit source target signal) :=
  kept.trans State.keeps_emit

private theorem State.Keeps.append {state changed : State} {processId : PID} {message : Term}
    (kept : state.Keeps changed) : state.Keeps (changed.append processId message) :=
  kept.trans State.keeps_append

private theorem State.Keeps.modify {state changed : State} {processId : PID}
    {change : ProcessState → ProcessState} (kept : state.Keeps changed)
    (children : ∀ process, (change process).children = process.children) :
    state.Keeps (changed.modify processId change) :=
  kept.trans (State.keeps_modify children)

private theorem State.Keeps.timers {state changed : State} {timers : List Timer}
    (kept : state.Keeps changed) : state.Keeps { changed with timers } :=
  kept.trans State.keeps_timers

private theorem State.Keeps.allocate {state changed : State} {processId : PID}
    (kept : state.Keeps changed) : state.Keeps (changed.allocate processId).2 :=
  kept.trans State.keeps_allocate

private theorem State.Keeps.exitSignal {state changed : State} {target source : PID} {reason : Term}
    {linked : Bool} (kept : state.Keeps changed) :
    state.Keeps (changed.exitSignal target source reason linked).1 :=
  kept.trans State.keeps_exitSignal



private theorem State.keeps_request {state : State} {processId : PID} {query : Request} {reply : Term}
    {after : State} {exits : Option Term} (answered : state.request processId query = some (reply, after, exits)) :
    state.Keeps after := by
  cases query <;> simp only [State.request] at answered
  all_goals
    repeat' (first
      | (simp only [Option.some.injEq, Prod.mk.injEq] at answered; obtain ⟨-, rfl, -⟩ := answered)
      | split at answered
      | simp at answered)
  all_goals first
    | exact State.keeps_allocate
    | exact State.keeps_exitSignal
    | exact State.keeps_emit
    | (refine State.keeps_modify ?_; intro; rfl)
    | (refine State.Keeps.modify ?_ ?_; exact State.keeps_timers; intro; rfl)
    | ((repeat' split) <;> first
        | (refine State.Keeps.emit ?_; refine State.Keeps.modify ?_ ?_; exact State.keeps_allocate; intro; rfl)
        | (refine State.Keeps.emit ?_; refine State.keeps_modify ?_; intro; rfl)
        | (refine State.keeps_modify ?_; intro; rfl)
        | exact State.keeps_append
        | (refine State.Keeps.timers ?_; exact State.keeps_allocate)
        | exact State.keeps_allocate
        | exact State.Keeps.refl _)
    | exact State.Keeps.refl _

/-- Folding steps that keep the records keeps them. -/
private theorem foldl_processes {items : List γ} {step : State → γ → State}
    (keep : ∀ state item, (step state item).processes = state.processes) (start : State) :
    (items.foldl step start).processes = start.processes := by
  induction items generalizing start with
  | nil => rfl
  | cons head rest ih => simp only [List.foldl_cons]; rw [ih, keep]

/-- The processes after a process ends: it is not live, and every other record stays. -/
private theorem State.processes_terminate {state : State} {processId : PID} {reason : Term} :
    (state.terminate processId reason).processes = (state.update processId none).processes := by
  unfold State.terminate
  dsimp only
  rw [foldl_processes (fun _ item => by cases item; rfl),
    foldl_processes (step := fun state linked => state.emit processId linked (.exit reason true))
      (fun _ _ => rfl)]

/-- What spawning does to the records: the child's PID is the parent's next, the
child is live, the parent counts one more child, and every other record stays. -/
private theorem State.spawnWith_facts {state : State} {processId : PID} {options : SpawnOptions} :
    (state.spawnWith processId options).1 = processId ++ [(state.process processId).children + 1] ∧
    ((state.spawnWith processId options).2.processes (state.spawnWith processId options).1).isSome ∧
    ((state.spawnWith processId options).2.processes processId).isSome ∧
    ((state.spawnWith processId options).2.process processId).children =
      (state.process processId).children + 1 ∧
    ∀ other, other ≠ processId → other ≠ (state.spawnWith processId options).1 →
      ((state.spawnWith processId options).2.processes other).isSome = (state.processes other).isSome ∧
      ((state.spawnWith processId options).2.process other).children = (state.process other).children := by
  have kept : (state.spawn processId).2.Keeps (state.spawnWith processId options).2 := by
    simp only [State.spawnWith]
    split <;> split <;> first
      | exact State.Keeps.refl _
      | (refine State.Keeps.modify ?_ ?_; refine State.Keeps.modify ?_ ?_; refine State.Keeps.allocate ?_
         refine State.Keeps.modify ?_ ?_; refine State.keeps_modify ?_
         all_goals intro; rfl)
      | (refine State.Keeps.modify ?_ ?_; refine State.Keeps.modify ?_ ?_; refine State.Keeps.allocate ?_
         exact State.Keeps.refl _
         all_goals intro; rfl)
      | (refine State.Keeps.modify ?_ ?_; refine State.keeps_modify ?_
         all_goals intro; rfl)
  have first : (state.spawnWith processId options).1 = (state.spawn processId).1 := by
    simp only [State.spawnWith]
  have distinct : processId ++ [(state.process processId).children + 1] ≠ processId := by
    intro equal; have := congrArg List.length equal; simp at this
  rw [first]
  refine ⟨rfl, ?_, ?_, ?_, fun other notParent notChild => ?_⟩
  · rw [(kept _).1]; simp [State.spawn, State.processes_update]
  · rw [(kept _).1]; simp [State.spawn, State.processes_update]
  · rw [(kept _).2]
    simp only [State.process] at distinct ⊢
    simp [State.spawn, State.process, State.processes_update, distinct.symm]
  · rw [(kept _).1, (kept _).2]
    simp only [State.spawn, State.process] at notChild
    simp [State.spawn, State.process, State.processes_update, notParent, notChild]

private theorem State.keeps_inTransit {state : State} {inTransit : List Envelope} :
    state.Keeps { state with inTransit } := fun _ => ⟨rfl, rfl⟩

/-- A process that never reports the run's result. -/
private def Task.Quiet (task : Task α) : Prop := ∀ result, task.finish result = none

/-- What a step of a process does to the processes: it ends the process,
whose record goes while the others are kept; or it continues, keeping every
record; or it spawns a child. -/
private theorem transition_shape {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.transitions state processId) :
    (transition.tasks = [] ∧ (∀ child, transition.event ≠ .spawn processId child) ∧
      ∃ middle, state.Keeps middle ∧
      transition.state.processes = (middle.update processId none).processes) ∨
    (∃ task', transition.tasks = [(processId, task')] ∧ state.Keeps transition.state ∧
      (task.Quiet → task'.Quiet) ∧ ∀ child, transition.event ≠ .spawn processId child) ∨
    (∃ task' childTask options, transition.tasks =
        [(processId, task'), ((state.spawnWith processId options).1, childTask)] ∧
      transition.state = (state.spawnWith processId options).2 ∧
      transition.event = .spawn processId (state.spawnWith processId options).1 ∧
      (task.Quiet → task'.Quiet) ∧ childTask.Quiet) := by
  simp only [Task.transitions, List.mem_append] at possible
  rcases possible with possible | possible
  · obtain ⟨computation, finish⟩ := task
    cases computation with
    | ok =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      exact .inl ⟨rfl, fun _ spawn => by simp [Task.ended] at spawn, state, State.Keeps.refl _, State.processes_terminate⟩
    | error exception =>
      cases exception <;> simp only [Task.own, List.mem_singleton] at possible <;> subst possible
      all_goals first
        | exact .inl ⟨rfl, fun _ spawn => by simp [Task.ended] at spawn, state, State.Keeps.refl _, State.processes_terminate⟩
        | exact .inl ⟨rfl, fun _ spawn => by simp at spawn, state, State.Keeps.refl _, rfl⟩
    | get next =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      exact .inr (.inl ⟨_, rfl, State.Keeps.refl _, fun quiet => quiet, fun _ spawn => by simp at spawn⟩)
    | set env next =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      exact .inr (.inl ⟨_, rfl, State.keeps_store, fun quiet => quiet, fun _ spawn => by simp at spawn⟩)
    | schedule options child next =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      exact .inr (.inr ⟨_, _, options, rfl, rfl, rfl, fun quiet => quiet, fun _ => rfl⟩)
    | send destination message next =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      refine .inr (.inl ⟨_, rfl, ?_, fun quiet => quiet, fun _ spawn => by simp at spawn⟩)
      dsimp only
      split
      · exact State.keeps_append
      · exact State.keeps_emit
    | receive timeout select next =>
      simp only [Task.own] at possible
      split at possible
      · simp only [List.mem_singleton] at possible; subst possible
        exact .inr (.inl ⟨_, rfl, State.keeps_modify fun _ => rfl, fun quiet => quiet,
          fun _ spawn => by simp at spawn⟩)
      · split at possible <;> simp only [List.mem_singleton, List.not_mem_nil] at possible <;>
          subst possible <;> exact .inr (.inl ⟨_, rfl, State.Keeps.refl _, fun quiet => quiet, fun _ spawn => by simp at spawn⟩)
    | request query next =>
      simp only [Task.own] at possible
      split at possible
      · simp at possible
      · rename_i answered
        simp only [List.mem_singleton] at possible; subst possible
        exact .inr (.inl ⟨_, rfl, State.keeps_request answered, fun quiet => quiet, fun _ spawn => by simp at spawn⟩)
      · rename_i answered
        simp only [List.mem_singleton] at possible; subst possible
        exact .inl ⟨rfl, fun _ spawn => by simp [Task.ended] at spawn, _, State.keeps_request answered, State.processes_terminate⟩
  · simp only [Task.deliveries, Task.delivery, List.mem_filterMap] at possible
    obtain ⟨⟨envelope, rest⟩, -, found⟩ := possible
    split at found
    · simp at found
    · have kept := State.keeps_inTransit.trans (State.keeps_receive (state := { state with inTransit := rest })
        (envelope := envelope))
      split at found <;> simp only [Option.some.injEq] at found <;> subst found
      · rename_i exits
        refine .inr (.inl ⟨_, rfl, ?_, fun quiet => quiet, fun _ spawn => by simp at spawn⟩)
        dsimp only
        exact kept
      · exact .inl ⟨rfl, fun _ spawn => by simp [Task.ended] at spawn, _, kept, State.processes_terminate⟩

/-! ### Well-formed configurations -/

/-- Facts every reachable configuration satisfies: processes have distinct PIDs,
each process has spawned every child PID that another process extends, every
process is live, at most one reports the run's result, and every live record
belongs to a process. -/
private def Wellformed : Config α → Prop
  | .start .. => True
  | .running state tasks _ _ =>
      tasks.Pairwise (fun first second => first.1 ≠ second.1) ∧
      (∀ parent ∈ tasks, ∀ descendant ∈ tasks, ∀ index rest,
        descendant.1 = parent.1 ++ index :: rest → index ≤ (state.process parent.1).children) ∧
      (∀ entry ∈ tasks, (state.processes entry.1).isSome) ∧
      tasks.Pairwise (fun first second => first.2.Quiet ∨ second.2.Quiet) ∧
      ∀ processId, (state.processes processId).isSome → processId ∈ tasks.map Prod.fst

private theorem ne_append_cons (processId : PID) (index : Nat) (rest : List Nat) :
    processId ≠ processId ++ index :: rest := by
  intro equal
  have := congrArg List.length equal
  simp at this

/-- A spawned PID either extends its parent or ends below it. -/
private theorem append_eq_spawned {parent processId : PID} {index last : Nat} {rest : List Nat}
    (equal : parent ++ index :: rest = processId ++ [last]) :
    (parent = processId ∧ index = last ∧ rest = []) ∨
      ∃ rest', processId = parent ++ index :: rest' := by
  rcases List.eq_nil_or_concat rest with rfl | ⟨rest', final, rfl⟩
  · left
    have := List.append_inj' equal rfl
    simp_all
  · right
    refine ⟨rest', ?_⟩
    have := List.append_inj' (show (parent ++ index :: rest') ++ [final] = processId ++ [last] by
      simpa using equal) rfl
    exact this.1.symm

private theorem pairwise_replace {relation : γ → γ → Prop} {before after replacement : List γ}
    {original : γ} (pairwise : (before ++ original :: after).Pairwise relation)
    (inner : replacement.Pairwise relation)
    (left : ∀ item ∈ before, relation item original → ∀ added ∈ replacement, relation item added)
    (right : ∀ item ∈ after, relation original item → ∀ added ∈ replacement, relation added item) :
    (before ++ replacement ++ after).Pairwise relation := by
  rw [List.pairwise_append] at pairwise
  obtain ⟨pairBefore, pairRest, cross⟩ := pairwise
  rw [List.pairwise_cons] at pairRest
  obtain ⟨originalAfter, pairAfter⟩ := pairRest
  rw [List.append_assoc, List.pairwise_append, List.pairwise_append]
  refine ⟨pairBefore, ⟨inner, pairAfter, ?_⟩, ?_⟩
  · intro added addedMem item itemMem
    exact right item itemMem (originalAfter item itemMem) added addedMem
  · intro item itemMem other otherMem
    rw [List.mem_append] at otherMem
    rcases otherMem with otherMem | otherMem
    · exact left item itemMem (cross item itemMem original (by simp)) other otherMem
    · exact cross item itemMem other (by simp [otherMem])

/-- What a step of a process leaves of the processes, in the terms the
invariant needs. -/
private theorem transition_facts {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.transitions state processId)
    (live : (state.processes processId).isSome) :
    -- Other processes, besides a spawned child, are kept.
    (∀ other, other ≠ processId → (∀ child, transition.event = .spawn processId child → other ≠ child) →
      (transition.state.processes other).isSome = (state.processes other).isSome ∧
      (transition.state.process other).children = (state.process other).children) ∧
    -- What it leaves is itself, live, and possibly a new child below it.
    transition.tasks.Pairwise (fun first second => first.1 ≠ second.1) ∧
    (∀ entry ∈ transition.tasks, entry.1 = processId ∨ ∃ child,
      transition.event = .spawn processId child ∧ entry.1 = child) ∧
    (transition.tasks ≠ [] → (transition.state.processes processId).isSome ∧
      (state.process processId).children ≤ (transition.state.process processId).children) ∧
    (∀ child, transition.event = .spawn processId child →
      child = processId ++ [(state.process processId).children + 1] ∧
      (transition.state.processes child).isSome ∧
      (transition.state.process processId).children = (state.process processId).children + 1) ∧
    (∀ added ∈ transition.tasks, task.Quiet → added.2.Quiet) ∧
    transition.tasks.Pairwise (fun first second => first.2.Quiet ∨ second.2.Quiet) ∧
    -- A live process or spawned child is among what it leaves.
    ((transition.state.processes processId).isSome → processId ∈ transition.tasks.map Prod.fst) ∧
    (∀ child, transition.event = .spawn processId child → child ∈ transition.tasks.map Prod.fst) := by
  rcases transition_shape possible with ⟨empty, notSpawn, middle, kept, processes⟩ |
    ⟨task', single, kept, quiet, notSpawn⟩ | ⟨task', childTask, options, pair, state', event, quiet, childQuiet⟩
  · refine ⟨fun other notSelf _ => ?_, by simp [empty], by simp [empty], by simp [empty],
      fun child spawn => absurd spawn (notSpawn child), by simp [empty], by simp [empty], ?_,
      fun child spawn => absurd spawn (notSpawn child)⟩
    · have := kept other
      simp only [State.process, processes, State.processes_update, notSelf, ite_false] at this ⊢
      exact this
    · intro live'
      simp [processes, State.processes_update] at live'
  · refine ⟨fun other _ _ => kept other, by simp [single], by simp [single], fun _ => ?_,
      fun child spawn => absurd spawn (notSpawn child), ?_, by simp [single], fun _ => by simp [single],
      fun child spawn => absurd spawn (notSpawn child)⟩
    · exact ⟨(kept processId).1 ▸ live, Nat.le_of_eq (kept processId).2.symm⟩
    · simp only [single, List.mem_singleton]
      rintro _ rfl
      exact quiet
  · obtain ⟨childPid, childLive, parentLive, children, others⟩ :=
      State.spawnWith_facts (state := state) (processId := processId) (options := options)
    have distinct : processId ≠ (state.spawnWith processId options).1 := by
      rw [childPid]; exact ne_append_cons _ _ _
    refine ⟨fun other notSelf notChild => ?_, by simp [pair, distinct], ?_, fun _ => ?_, ?_, ?_, ?_,
      fun _ => by simp [pair], fun child spawn => by rw [event] at spawn; cases spawn; simp [pair]⟩
    · rw [state']; exact others other notSelf (notChild _ event)
    · intro entry mem
      simp only [pair, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact .inl rfl
      · exact .inr ⟨_, event, rfl⟩
    · rw [state']; exact ⟨parentLive, by omega⟩
    · intro child spawn
      rw [event] at spawn
      cases spawn
      rw [state']
      exact ⟨childPid, childLive, children⟩
    · simp only [pair, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) taskQuiet
      · exact quiet taskQuiet
      · exact childQuiet
    · simp [pair, childQuiet]

/-- A process step preserves well-formedness. -/
private theorem wellformed_apply {state : State} {before after : List (PID × Task α)}
    {processId : PID} {task : Task α} {transition : Transition α}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (wellformed : Wellformed (.running state (before ++ (processId, task) :: after) finished exhausted))
    (possible : transition ∈ task.transitions state processId) :
    Wellformed (transition.apply before after finished exhausted) := by
  obtain ⟨distinct, fresh, live, quiet, owned⟩ := wellformed
  have self : (processId, task) ∈ before ++ (processId, task) :: after := by simp
  obtain ⟨frame, inner, entries, grows, spawned, quietAdded, quietInner, stays, childStays⟩ :=
    transition_facts possible (live _ self)
  have old : ∀ entry, entry ∈ before ∨ entry ∈ after →
      entry ∈ before ++ (processId, task) :: after := by
    intro entry mem
    rcases mem with mem | mem <;> simp [mem]
  -- Other processes have other PIDs.
  have others : ∀ entry, entry ∈ before ∨ entry ∈ after → entry.1 ≠ processId := by
    have pairs := distinct
    rw [List.pairwise_append, List.pairwise_cons] at pairs
    intro entry mem
    rcases mem with mem | mem
    · exact pairs.2.2 entry mem (processId, task) (by simp)
    · exact fun equal => pairs.2.1.1 entry mem equal.symm
  -- A spawned child is new.
  have child_new : ∀ child, transition.event = .spawn processId child →
      ∀ entry ∈ before ++ (processId, task) :: after, entry.1 ≠ child := by
    intro child spawn entry mem equal
    have := fresh (processId, task) self entry mem _ [] (by
      rw [equal, (spawned child spawn).1])
    dsimp only at this
    omega
  have kept : ∀ entry, entry ∈ before ∨ entry ∈ after →
      (transition.state.processes entry.1).isSome = (state.processes entry.1).isSome ∧
      (transition.state.process entry.1).children = (state.process entry.1).children :=
    fun entry mem => frame entry.1 (others entry mem) fun child spawn =>
      child_new child spawn entry (old entry mem)
  simp only [Transition.apply, Wellformed]
  refine ⟨pairwise_replace distinct inner ?_ ?_, ?_, ?live, ?quiet, ?owned⟩
  case owned =>
    intro candidate alive
    simp only [List.map_append, List.mem_append]
    by_cases self' : candidate = processId
    · subst self'; exact .inl (.inr (stays alive))
    · by_cases spawned' : ∃ child, transition.event = .spawn processId child ∧ candidate = child
      · obtain ⟨child, spawn, same⟩ := spawned'
        rw [same]
        exact .inl (.inr (childStays child spawn))
      · have kept := frame candidate self' fun child' spawn same => spawned' ⟨child', spawn, same⟩
        have := owned candidate (kept.1 ▸ alive)
        simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at this
        rcases this with this | this | this
        · exact .inl (.inl this)
        · exact absurd this self'
        · exact .inr this
  case live =>
    intro entry mem
    simp only [List.mem_append] at mem
    rcases mem with (mem | mem) | mem
    · rw [(kept entry (.inl mem)).1]; exact live entry (old entry (.inl mem))
    · rcases entries entry mem with equal | ⟨child, spawn, equal⟩
      · rw [equal]; exact (grows (List.ne_nil_of_mem mem)).1
      · rw [equal]; exact (spawned child spawn).2.1
    · rw [(kept entry (.inr mem)).1]; exact live entry (old entry (.inr mem))
  case quiet =>
    refine pairwise_replace quiet quietInner ?_ ?_
    · intro item mem either added addedMem
      rcases either with itemQuiet | taskQuiet
      · exact .inl itemQuiet
      · exact .inr (quietAdded added addedMem taskQuiet)
    · intro item mem either added addedMem
      rcases either with taskQuiet | itemQuiet
      · exact .inl (quietAdded added addedMem taskQuiet)
      · exact .inr itemQuiet
  · intro item mem _ added addedMem
    rcases entries added addedMem with equal | ⟨child, spawn, equal⟩
    · rw [equal]; exact others item (.inl mem)
    · rw [equal]; exact child_new child spawn item (by simp [mem])
  · intro item mem _ added addedMem
    rcases entries added addedMem with equal | ⟨child, spawn, equal⟩
    · rw [equal]; exact fun same => others item (.inr mem) same.symm
    · rw [equal]; exact fun same => child_new child spawn item (by simp [mem]) same.symm
  intro parent parentMem descendant descendantMem index rest extended
  simp only [List.mem_append] at parentMem descendantMem
  have classify : ∀ entry, entry ∈ before ∨ entry ∈ transition.tasks ∨ entry ∈ after →
      (entry ∈ before ∨ entry ∈ after) ∨ (entry.1 = processId ∧ transition.tasks ≠ []) ∨
        ∃ child, transition.event = .spawn processId child ∧ entry.1 = child := by
    intro entry mem
    rcases mem with mem | mem | mem
    · exact .inl (.inl mem)
    · rcases entries entry mem with equal | spawn
      · exact .inr (.inl ⟨equal, List.ne_nil_of_mem mem⟩)
      · exact .inr (.inr spawn)
    · exact .inl (.inr mem)
  have parentClass := classify parent (by rcases parentMem with (h | h) | h <;> simp [h])
  have descendantClass := classify descendant
    (by rcases descendantMem with (h | h) | h <;> simp [h])
  rcases parentClass with parentOld | ⟨parentSelf, nonempty⟩ | ⟨child, spawn, parentChild⟩
  · rw [(kept parent parentOld).2]
    rcases descendantClass with descendantOld | ⟨descendantSelf, -⟩ |
        ⟨child, spawn, descendantChild⟩
    · exact fresh parent (old parent parentOld) descendant (old descendant descendantOld) index rest
        extended
    · exact fresh parent (old parent parentOld) (processId, task) self index rest
        (by rw [← descendantSelf]; exact extended)
    · rw [descendantChild, (spawned child spawn).1] at extended
      rcases append_eq_spawned extended.symm with ⟨same, -, -⟩ | ⟨rest', below⟩
      · exact absurd same (others parent parentOld)
      · exact fresh parent (old parent parentOld) (processId, task) self index rest' below
  · rw [parentSelf] at extended ⊢
    rcases descendantClass with descendantOld | ⟨descendantSelf, -⟩ |
        ⟨child, spawn, descendantChild⟩
    · have bound := fresh (processId, task) self descendant (old descendant descendantOld) index
        rest extended
      dsimp only at bound
      have := (grows nonempty).2
      omega
    · rw [descendantSelf] at extended
      exact absurd extended (ne_append_cons _ _ _)
    · rw [descendantChild, (spawned child spawn).1] at extended
      have := List.append_cancel_left extended
      simp only [List.cons.injEq] at this
      rw [(spawned child spawn).2.2]
      omega
  · exfalso
    rw [parentChild, (spawned child spawn).1, List.append_assoc] at extended
    rcases descendantClass with descendantOld | ⟨descendantSelf, -⟩ |
        ⟨child', spawn', descendantChild⟩
    · have := fresh (processId, task) self descendant (old descendant descendantOld) _ _ extended
      dsimp only at this
      omega
    · rw [descendantSelf] at extended
      exact ne_append_cons _ _ _ extended
    · rw [spawn] at spawn'
      cases spawn'
      rw [descendantChild, (spawned child spawn).1] at extended
      have := congrArg List.length extended
      simp at this

/-- Steps that keep every record keep well-formedness. -/
private theorem wellformed_keeps {state state' : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (kept : state.Keeps state') :
    Wellformed (.running state' tasks finished exhausted) := by
  obtain ⟨distinct, fresh, live, quiet, owned⟩ := wellformed
  refine ⟨distinct, fun parent mem descendant mem' index rest extended => ?_,
    fun entry mem => (kept entry.1).1 ▸ live entry mem, quiet,
    fun processId alive => owned processId ((kept processId).1 ▸ alive)⟩
  rw [(kept parent.1).2]
  exact fresh parent mem descendant mem' index rest extended

/-- Every step preserves well-formedness. -/
private theorem Step.wellformed {first next : Config α} {event : Event}
    (step : Step first event next) (wellformed : Wellformed first) : Wellformed next := by
  cases first with
  | start env computation elapsed =>
    simp only [Step, Config.successors] at step
    cases computation <;> simp only [isRequest] at step
    all_goals first
      | (simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial)
      | (simp at step; done)
      | (simp only [↓reduceIte, List.mem_singleton, Prod.mk.injEq] at step
         obtain ⟨-, rfl⟩ := step
         refine ⟨by simp, ?_, by simp [State.initial], by simp, ?_⟩
         · simp only [List.mem_singleton]
           rintro _ rfl _ rfl index rest extended
           exact absurd extended (ne_append_cons _ _ _)
         · intro candidate alive
           simp only [State.initial] at alive
           split at alive <;> simp_all)
  | running state tasks finished exhausted =>
    simp only [Step, Config.successors, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_filterMap, Prod.exists] at step
    rcases step with (⟨before, processId, task, after, split, transition, possible, same⟩ |
      ⟨envelope, rest, -, bounced⟩) | ⟨timer, -, same⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      rw [eq_of_mem_splits split] at wellformed
      exact wellformed_apply wellformed possible
    · split at bounced
      · simp at bounced
      · simp only [Option.some.injEq, Prod.mk.injEq] at bounced
        obtain ⟨-, rfl⟩ := bounced
        exact wellformed_keeps wellformed (State.keeps_inTransit.trans State.keeps_bounce)
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      exact wellformed_keeps wellformed State.keeps_fire

/-! ### Keyed steps -/

/-- Names a step across configurations: the step of a process by its place
among the process's own steps, a signal by its pair of processes, or a timer
by its reference. -/
inductive Key where
  | own (processId : PID) (index : Nat)
  | deliver (source target : PID)
  | bounce (source target : PID)
  | fire (reference : List Nat)

/-- Compare keys in evaluation. -/
@[expose] def Key.beq : Key → Key → Bool
  | .own processId index, .own processId' index' => processId == processId' && index == index'
  | .deliver source target, .deliver source' target' => source == source' && target == target'
  | .bounce source target, .bounce source' target' => source == source' && target == target'
  | .fire reference, .fire reference' => reference == reference'
  | _, _ => false

instance : BEq Key := ⟨Key.beq⟩

instance : LawfulBEq Key where
  eq_of_beq {first second} equal := by
    change Key.beq first second = true at equal
    cases first <;> cases second <;> simp_all [Key.beq]
  rfl {key} := by
    change Key.beq key key = true
    cases key <;> simp [Key.beq]

instance : DecidableEq Key := fun first second => decidable_of_iff (first == second) beq_iff_eq

/-- The steps of a process, each with its key. -/
@[expose] def Task.keyed (state : State) (processId : PID) (task : Task α) : List (Key × Transition α) :=
  (task.own state processId).zipIdx.map (fun (transition, index) => (.own processId index, transition)) ++
  (deliverable state.inTransit).filterMap fun (envelope, rest) =>
    if envelope.target != processId then none
    else some (.deliver envelope.source processId, task.delivery state processId envelope rest)

private theorem Task.keyed_snd (state : State) (processId : PID) (task : Task α) :
    (task.keyed state processId).map Prod.snd = task.transitions state processId := by
  simp only [Task.keyed, Task.transitions, Task.deliveries, List.map_append, List.map_map]
  congr 1
  · simp [Function.comp_def]
  · rw [List.map_filterMap]
    congr 1
    funext item
    split <;> rfl

/-- Every step of a configuration, with its key. -/
@[expose] def Config.steps : Config α → List (Key × Event × Config α)
  | .start .. => []
  | .running state tasks finished exhausted =>
      (splits tasks).flatMap (fun (before, (processId, task), after) =>
        (task.keyed state processId).map fun (key, transition) =>
          (key, transition.event, transition.apply before after finished exhausted)) ++
      (deliverable state.inTransit).filterMap (fun (envelope, rest) =>
        if (tasks.lookup envelope.target).isSome then none
        else some (.bounce envelope.source envelope.target, .bounce envelope,
          .running ({ state with inTransit := rest }.bounce envelope) tasks finished exhausted)) ++
      state.firing.map fun timer =>
        (.fire timer.reference, .fire timer.reference, .running (state.fire timer) tasks finished exhausted)

/-- Without their keys, the steps of a running configuration are its successors. -/
private theorem Config.steps_running {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} :
    (Config.running state tasks finished exhausted).steps.map (fun step => (step.2.1, step.2.2)) =
      (Config.running state tasks finished exhausted).successors := by
  simp only [Config.steps, Config.successors, List.map_append, List.map_flatMap, List.map_map,
    List.map_filterMap]
  congr 1
  · congr 1
    · congr 1
      funext split
      obtain ⟨before, ⟨processId, task⟩, after⟩ := split
      rw [← Task.keyed_snd, List.map_map]
      rfl
    · congr 1
      funext item
      split <;> rfl

/-- A process with a unique PID splits the tasks in one way. -/
private theorem split_unique_eq {entries before after before' after' : List (PID × γ)} {processId : PID}
    {item item' : γ} (distinct : entries.Pairwise (fun first second => first.1 ≠ second.1))
    (split : entries = before ++ (processId, item) :: after)
    (split' : entries = before' ++ (processId, item') :: after') :
    before = before' ∧ item = item' ∧ after = after' := by
  induction before generalizing entries before' with
  | nil =>
    cases before' with
    | nil =>
      rw [split] at split'
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at split'
      exact ⟨rfl, split'.1, split'.2⟩
    | cons first rest =>
      subst split
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at split'
      obtain ⟨rfl, rfl⟩ := split'
      have := (List.pairwise_cons.mp distinct).1 (processId, item') (by simp)
      exact absurd rfl this
  | cons first rest ih =>
    subst split
    cases before' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at split'
      obtain ⟨rfl, rfl⟩ := split'
      have := (List.pairwise_cons.mp distinct).1 (processId, item) (by simp)
      exact absurd rfl this
    | cons first' rest' =>
      simp only [List.cons_append, List.cons.injEq] at split'
      obtain ⟨rfl, split'⟩ := split'
      obtain ⟨rfl, rfl, rfl⟩ := ih (List.pairwise_cons.mp distinct).2 rfl split'
      exact ⟨rfl, rfl, rfl⟩

private theorem split_unique {entries before after before' after' : List (PID × γ)} {processId : PID}
    {item item' : γ} (distinct : entries.Pairwise (fun first second => first.1 ≠ second.1))
    (split : (before, (processId, item), after) ∈ splits entries)
    (split' : (before', (processId, item'), after') ∈ splits entries) :
    before = before' ∧ item = item' ∧ after = after' :=
  split_unique_eq distinct (eq_of_mem_splits split) (eq_of_mem_splits split')

/-- Signals that can arrive next are of different pairs, none already seen. -/
private theorem deliverableFrom_pairs {before : List Envelope} {seen : List (PID × PID)}
    {inTransit : List Envelope} :
    (∀ item ∈ deliverableFrom before seen inTransit, (item.1.source, item.1.target) ∉ seen) ∧
    (deliverableFrom before seen inTransit).Pairwise (fun first second =>
      (first.1.source, first.1.target) ≠ (second.1.source, second.1.target)) := by
  induction inTransit generalizing before seen with
  | nil => simp [deliverableFrom]
  | cons head rest ih =>
    simp only [deliverableFrom]
    split
    · exact ih
    · rename_i fresh
      obtain ⟨notSeen, pairwise⟩ := ih (before := before ++ [head])
        (seen := (head.source, head.target) :: seen)
      refine ⟨fun item mem => ?_, List.pairwise_cons.mpr ⟨fun item mem equal => ?_, pairwise⟩⟩
      · simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · simpa using fresh
        · exact fun found => notSeen item mem (List.mem_cons_of_mem _ found)
      · exact notSeen item mem (by rw [← equal]; exact List.mem_cons_self)

/-- At most one signal of each pair can arrive next. -/
private theorem deliverable_unique {inTransit : List Envelope} {envelope envelope' : Envelope}
    {rest rest' : List Envelope} (mem : (envelope, rest) ∈ deliverable inTransit)
    (mem' : (envelope', rest') ∈ deliverable inTransit) (source : envelope.source = envelope'.source)
    (target : envelope.target = envelope'.target) : envelope = envelope' ∧ rest = rest' := by
  have pairwise := (deliverableFrom_pairs (before := []) (seen := []) (inTransit := inTransit)).2
  unfold deliverable at mem mem'
  generalize deliverableFrom [] [] inTransit = items at mem mem' pairwise
  induction items with
  | nil => simp at mem
  | cons head tail ih =>
    rw [List.pairwise_cons] at pairwise
    simp only [List.mem_cons] at mem mem'
    rcases mem with rfl | mem <;> rcases mem' with equal | mem'
    · simp only [Prod.mk.injEq] at equal; exact ⟨equal.1.symm, equal.2.symm⟩
    · exact absurd (by rw [source, target]) (pairwise.1 _ mem')
    · exact absurd (by rw [← equal, source, target]) (pairwise.1 _ mem)
    · exact ih mem mem' pairwise.2

/-- Timers that can fire have different references. -/
private theorem firstOfEach_unique {seen : List (List Nat)} {timers : List Timer} {timer timer' : Timer}
    (mem : timer ∈ firstOfEach seen timers) (mem' : timer' ∈ firstOfEach seen timers)
    (same : timer.reference = timer'.reference) : timer = timer' := by
  have fresh : ∀ {timers : List Timer} {seen : List (List Nat)} {timer : Timer},
      timer ∈ firstOfEach seen timers → timer.reference ∉ seen := by
    intro timers
    induction timers with
    | nil => intro seen timer mem; simp [firstOfEach] at mem
    | cons head rest ih =>
      intro seen timer mem
      simp only [firstOfEach] at mem
      split at mem
      · exact ih mem
      · rename_i notSeen
        simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · simpa using notSeen
        · exact fun found => ih mem (List.mem_cons_of_mem _ found)
  induction timers generalizing seen with
  | nil => simp [firstOfEach] at mem
  | cons head rest ih =>
    simp only [firstOfEach] at mem mem'
    split at mem
    · rename_i seenHead
      simp only [seenHead, ↓reduceIte] at mem'
      exact ih mem mem'
    · rename_i seenHead
      simp only [seenHead, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at mem mem'
      rcases mem with rfl | mem <;> rcases mem' with rfl | mem'
      · rfl
      · exact absurd (same ▸ List.mem_cons_self) (fresh mem')
      · exact absurd (same.symm ▸ List.mem_cons_self) (fresh mem)
      · exact ih mem mem'

private theorem mem_keyed {state : State} {processId : PID} {task : Task α} {key : Key}
    {transition : Transition α} :
    (key, transition) ∈ task.keyed state processId ↔
      (∃ index, key = .own processId index ∧ (task.own state processId)[index]? = some transition) ∨
      (∃ envelope rest, (envelope, rest) ∈ deliverable state.inTransit ∧
        envelope.target = processId ∧ key = .deliver envelope.source processId ∧
        transition = task.delivery state processId envelope rest) := by
  simp only [Task.keyed, List.mem_append, List.mem_map, List.mem_filterMap, Prod.mk.injEq,
    Prod.exists]
  apply or_congr
  · constructor
    · rintro ⟨transition', index, mem, rfl, rfl⟩
      exact ⟨index, rfl, List.mem_zipIdx_iff_getElem?.mp mem⟩
    · rintro ⟨index, rfl, found⟩
      exact ⟨transition, index, List.mem_zipIdx_iff_getElem?.mpr found, rfl, rfl⟩
  · constructor
    · rintro ⟨envelope, rest, mem, found⟩
      split at found
      · simp at found
      · rename_i target
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        exact ⟨envelope, rest, mem, by simpa using target, rfl, rfl⟩
    · rintro ⟨envelope, rest, mem, target, rfl, rfl⟩
      exact ⟨envelope, rest, mem, by simp [target]⟩

private theorem mem_steps {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key}
    {event : Event} {next : Config α} :
    (key, event, next) ∈ (Config.running state tasks finished exhausted).steps ↔
      (∃ before processId task after transition, (before, (processId, task), after) ∈ splits tasks ∧
        (key, transition) ∈ task.keyed state processId ∧ event = transition.event ∧
        next = transition.apply before after finished exhausted) ∨
      (∃ envelope rest, (envelope, rest) ∈ deliverable state.inTransit ∧
        (tasks.lookup envelope.target).isSome = false ∧
        key = .bounce envelope.source envelope.target ∧ event = .bounce envelope ∧
        next = .running ({ state with inTransit := rest }.bounce envelope) tasks finished exhausted) ∨
      (∃ timer ∈ state.firing, key = .fire timer.reference ∧ event = .fire timer.reference ∧
        next = .running (state.fire timer) tasks finished exhausted) := by
  simp only [Config.steps, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap,
    Prod.exists, Prod.mk.injEq]
  rw [or_assoc]
  apply or_congr
  · constructor
    · rintro ⟨before, processId, task, after, split, key', transition, mem, rfl, rfl, rfl⟩
      exact ⟨before, processId, task, after, transition, split, mem, rfl, rfl⟩
    · rintro ⟨before, processId, task, after, transition, split, mem, rfl, rfl⟩
      exact ⟨before, processId, task, after, split, key, transition, mem, rfl, rfl, rfl⟩
  apply or_congr
  · constructor
    · rintro ⟨envelope, rest, mem, found⟩
      split at found
      · simp at found
      · rename_i dead
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact ⟨envelope, rest, mem, Bool.eq_false_iff.mpr dead, rfl, rfl, rfl⟩
    · rintro ⟨envelope, rest, mem, dead, rfl, rfl, rfl⟩
      exact ⟨envelope, rest, mem, by simp [dead]⟩
  · constructor
    · rintro ⟨timer, mem, rfl, rfl, rfl⟩
      exact ⟨timer, mem, rfl, rfl, rfl⟩
    · rintro ⟨timer, mem, rfl, rfl, rfl⟩
      exact ⟨timer, mem, rfl, rfl, rfl⟩

/-- In a well-formed configuration, a key names at most one step. -/
private theorem steps_unique {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key}
    {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (Config.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key, event', next') ∈ (Config.running state tasks finished exhausted).steps) :
    event = event' ∧ next = next' := by
  rw [mem_steps] at mem mem'
  rcases mem with ⟨before, processId, task, after, transition, split, keyed, rfl, rfl⟩ |
    ⟨envelope, rest, delivered, dead, rfl, rfl, rfl⟩ | ⟨timer, firing, rfl, rfl, rfl⟩ <;>
  rcases mem' with ⟨before', processId', task', after', transition', split', keyed', rfl, rfl⟩ |
    ⟨envelope', rest', delivered', dead', same, rfl, rfl⟩ | ⟨timer', firing', same, rfl, rfl⟩
  · rw [mem_keyed] at keyed keyed'
    rcases keyed with ⟨index, rfl, found⟩ | ⟨envelope, rest, delivered, target, rfl, rfl⟩ <;>
    rcases keyed' with ⟨index', same, found'⟩ | ⟨envelope', rest', delivered', target', same, rfl⟩
    · simp only [Key.own.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨rfl, rfl, rfl⟩ := split_unique wellformed.1 split split'
      rw [found, Option.some.injEq] at found'
      subst found'
      exact ⟨rfl, rfl⟩
    · cases same
    · cases same
    · simp only [Key.deliver.injEq] at same
      obtain ⟨source, rfl⟩ := same
      obtain ⟨rfl, rfl, rfl⟩ := split_unique wellformed.1 split split'
      obtain ⟨rfl, rfl⟩ := deliverable_unique delivered delivered' source (target.trans target'.symm)
      exact ⟨rfl, rfl⟩
  · rw [mem_keyed] at keyed; rcases keyed with ⟨_, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ <;> cases same
  · rw [mem_keyed] at keyed; rcases keyed with ⟨_, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ <;> cases same
  · rw [mem_keyed] at keyed'; rcases keyed' with ⟨_, same, _⟩ | ⟨_, _, _, _, same, _⟩ <;> cases same
  · simp only [Key.bounce.injEq] at same
    obtain ⟨source, target⟩ := same
    obtain ⟨rfl, rfl⟩ := deliverable_unique delivered delivered' source target
    exact ⟨rfl, rfl⟩
  · cases same
  · rw [mem_keyed] at keyed'; rcases keyed' with ⟨_, same, _⟩ | ⟨_, _, _, _, same, _⟩ <;> cases same
  · cases same
  · simp only [Key.fire.injEq] at same
    obtain rfl := firstOfEach_unique firing firing' same
    exact ⟨rfl, rfl⟩

/-! ### Commuting steps -/

/-- What the step with a key observes and does, if the configuration has one. -/
@[expose] def Config.footprint : Config α → Key → Option Footprint
  | .start .., _ => none
  | .running state tasks _ _, .own processId index =>
      match tasks.lookup processId with
      | some task =>
          if index < (task.own state processId).length then some (task.footprint state processId)
          else none
      | none => none
  | .running state tasks _ _, .deliver source target =>
      match tasks.lookup target, state.inTransit.find? (Envelope.between source target) with
      | some _, some envelope => some (Footprint.delivery state envelope)
      | _, _ => none
  | .running state tasks _ _, .bounce source target =>
      match tasks.lookup target, state.inTransit.find? (Envelope.between source target) with
      | none, some envelope => some (Footprint.bounce envelope)
      | _, _ => none
  | .running state _ _ _, .fire reference =>
      match state.timers.find? (·.reference == reference) with
      | some timer => some (Footprint.fire timer)
      | none => none

/-- Whether the steps with two keys commute at a configuration: both can be
taken, neither changes what the other observes, and their effects reach the
same state in either order. -/
@[expose] def Config.independent : Config α → Key → Key → Bool
  | .start .., _, _ => false
  | config@(.running state ..), first, second =>
      first != second && match config.footprint first, config.footprint second with
        | some footprint, some footprint' => footprint.independent footprint' state
        | _, _ => false

/-- A step every run can take first, if there is one: a process reading or
replacing its environment, or receiving a message already queued. Its effects
stay in its own record, so it commutes with every step the process survives,
and a signal ending the process absorbs it. -/
@[expose] def Config.forced : Config α → Option Key
  | .start .. => none
  | .running state tasks _ _ =>
      (tasks.find? fun (processId, task) => task.local state processId).map fun (processId, _) =>
        .own processId 0

/-- Replace the process with a PID by others. -/
private def replace (processId : PID) (replacement : List (PID × Task α))
    (tasks : List (PID × Task α)) : List (PID × Task α) :=
  tasks.flatMap fun entry => if entry.1 = processId then replacement else [entry]

private theorem replace_others {processId : PID} {replacement tasks : List (PID × Task α)}
    (others : ∀ entry ∈ tasks, entry.1 ≠ processId) : replace processId replacement tasks = tasks := by
  induction tasks with
  | nil => rfl
  | cons head rest ih =>
    simp only [replace, List.flatMap_cons] at ih ⊢
    rw [ite_eq_right (others head (by simp)), ih fun entry mem => others entry (by simp [mem])]
    rfl

private theorem replace_split {processId : PID} {task : Task α}
    {before after replacement : List (PID × Task α)}
    (distinct : (before ++ (processId, task) :: after).Pairwise fun first second => first.1 ≠ second.1) :
    replace processId replacement (before ++ (processId, task) :: after) =
      before ++ replacement ++ after := by
  rw [List.pairwise_append, List.pairwise_cons] at distinct
  obtain ⟨-, ⟨notAfter, -⟩, notBefore⟩ := distinct
  have front := replace_others (replacement := replacement) fun entry mem =>
    notBefore entry mem (processId, task) (by simp)
  have back := replace_others (replacement := replacement) fun entry mem same =>
    notAfter entry mem same.symm
  simp only [replace, List.flatMap_append, List.flatMap_cons, ite_true] at front back ⊢
  rw [front, back]
  simp

private theorem mem_of_lookup {entries : List (PID × γ)} {processId : PID} {item : γ}
    (found : entries.lookup processId = some item) : (processId, item) ∈ entries := by
  induction entries with
  | nil => simp [List.lookup] at found
  | cons head rest ih =>
    obtain ⟨processId', item'⟩ := head
    simp only [List.lookup] at found
    split at found
    · rename_i same
      simp only [beq_iff_eq] at same
      subst same
      simp only [Option.some.injEq] at found
      subst found
      simp
    · exact List.mem_cons_of_mem _ (ih found)

private theorem lookup_of_mem {entries : List (PID × γ)} {processId : PID} {item : γ}
    (distinct : entries.Pairwise fun first second => first.1 ≠ second.1)
    (mem : (processId, item) ∈ entries) : entries.lookup processId = some item := by
  induction entries with
  | nil => simp at mem
  | cons head rest ih =>
    obtain ⟨processId', item'⟩ := head
    simp only [List.pairwise_cons] at distinct
    simp only [List.mem_cons, Prod.mk.injEq] at mem
    rcases mem with ⟨rfl, rfl⟩ | mem
    · simp [List.lookup]
    · have ne : processId ≠ processId' := fun equal => distinct.1 (processId, item) mem equal.symm
      have : (processId == processId') = false := by simpa using ne
      simp [List.lookup, this, ih distinct.2 mem]

private theorem lookup_none {entries : List (PID × γ)} {processId : PID}
    (missing : processId ∉ entries.map Prod.fst) : entries.lookup processId = none := by
  cases found : entries.lookup processId with
  | none => rfl
  | some item => exact absurd (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup found)) missing

private theorem replace_flatMap {processId : PID} {replacement : List (PID × Task α)}
    {items : List γ} {change : γ → List (PID × Task α)} :
    replace processId replacement (items.flatMap change) =
      items.flatMap fun item => replace processId replacement (change item) := by
  induction items with
  | nil => rfl
  | cons head rest ih => simp only [List.flatMap_cons, replace, List.flatMap_append] at ih ⊢; rw [ih]

private theorem lookup_replace {processId other : PID} {replacement tasks : List (PID × Task α)}
    (ne : other ≠ processId) (fresh : other ∉ replacement.map Prod.fst) :
    (replace processId replacement tasks).lookup other = tasks.lookup other := by
  induction tasks with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨processId', task⟩ := head
    have unfolded : replace processId replacement ((processId', task) :: rest) =
        (if processId' = processId then replacement else [(processId', task)]) ++
          replace processId replacement rest := by
      simp [replace]
    rw [unfolded, List.lookup_append, ih]
    split
    · rename_i same
      subst same
      have : (other == processId') = false := by simpa using ne
      rw [lookup_none fresh]
      simp [List.lookup, this]
    · simp only [List.lookup]
      split <;> rfl

private theorem replace_comm {processId other : PID}
    {replacement replacement' tasks : List (PID × Task α)} (ne : processId ≠ other)
    (fresh : other ∉ replacement.map Prod.fst) (fresh' : processId ∉ replacement'.map Prod.fst) :
    replace processId replacement (replace other replacement' tasks) =
      replace other replacement' (replace processId replacement tasks) := by
  have outside : ∀ {processId : PID} {replacement : List (PID × Task α)},
      processId ∉ replacement.map Prod.fst → ∀ more : List (PID × Task α),
        replace processId more replacement = replacement := fun fresh more =>
    replace_others fun entry mem same => fresh (by rw [← same]; exact List.mem_map_of_mem mem)
  have inner : ∀ (processId : PID) (replacement : List (PID × Task α)),
      replace processId replacement tasks =
        tasks.flatMap fun entry => if entry.1 = processId then replacement else [entry] :=
    fun _ _ => rfl
  rw [inner other, inner processId, replace_flatMap, replace_flatMap]
  congr 1
  funext entry
  by_cases first : entry.1 = processId
  · have second : entry.1 ≠ other := first ▸ ne
    rw [ite_eq_right second, ite_eq_left first, outside fresh]
    simp [replace, first]
  · by_cases second : entry.1 = other
    · rw [ite_eq_left second, ite_eq_right first, outside fresh']
      simp [replace, second]
    · rw [ite_eq_right second, ite_eq_right first]
      simp [replace, first, second]

/-- A step reporting the run's result ends a process that reports it. -/
private theorem finished_facts {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.transitions state processId)
    (reported : transition.finished.isSome) : transition.tasks = [] ∧ ¬task.Quiet := by
  have ended : ∀ {γ : Type} {finish : Except Exception γ → Option (Except Exception α)} {event : Event}
      {state : State} {reason : Term} {result : Except Exception γ},
      (Task.ended finish event state processId reason result).finished.isSome →
        (Task.ended finish event state processId reason result).tasks = [] ∧
          ∃ result, finish result ≠ none := by
    intro γ finish event state reason result found
    refine ⟨rfl, result, ?_⟩
    simp only [Task.ended] at found
    simpa [Option.isSome_iff_ne_none] using found
  have quiet : ∀ {γ : Type} {computation : Result γ}
      {finish : Except Exception γ → Option (Except Exception α)},
      (∃ result, finish result ≠ none) → ¬(⟨computation, finish⟩ : Task α).Quiet :=
    fun ⟨result, found⟩ quiet => found (quiet result)
  simp only [Task.transitions, List.mem_append] at possible
  rcases possible with possible | possible
  · obtain ⟨computation, finish⟩ := task
    cases computation with
    | ok =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      exact ⟨(ended reported).1, quiet (ended reported).2⟩
    | error exception =>
      cases exception <;> simp only [Task.own, List.mem_singleton] at possible <;> subst possible
      all_goals first
        | exact ⟨(ended reported).1, quiet (ended reported).2⟩
        | simp at reported
    | request query next =>
      simp only [Task.own] at possible
      split at possible
      · simp at possible
      · simp only [List.mem_singleton] at possible; subst possible; simp at reported
      · simp only [List.mem_singleton] at possible; subst possible
        exact ⟨(ended reported).1, quiet (ended reported).2⟩
    | receive timeout select next =>
      simp only [Task.own] at possible
      split at possible
      · simp only [List.mem_singleton] at possible; subst possible; simp at reported
      · split at possible <;> simp only [List.mem_singleton, List.not_mem_nil] at possible <;>
          subst possible <;> simp at reported
    | _ => simp only [Task.own, List.mem_singleton] at possible; subst possible; simp at reported
  · simp only [Task.deliveries, Task.delivery, List.mem_filterMap] at possible
    obtain ⟨⟨envelope, rest⟩, -, found⟩ := possible
    split at found
    · simp at found
    · split at found <;> simp only [Option.some.injEq] at found <;> subst found
      · simp at reported
      · exact ⟨(ended reported).1, quiet (ended reported).2⟩

/-- What a step does to a configuration: its event, its effect on the state,
the process it replaces among the tasks, if any, and what it reports. -/
private structure Move (α : Type) : Type 1 where
  event : Event
  effect : Effect
  owner : Option PID := none
  replacement : List (PID × Task α) := []
  finished : Option (Except Exception α) := none
  exhausted : Bool := false

private def Move.tasks (move : Move α) (tasks : List (PID × Task α)) : List (PID × Task α) :=
  match move.owner with
  | some processId => replace processId move.replacement tasks
  | none => tasks

private def Move.config (move : Move α) (state : State) (tasks : List (PID × Task α))
    (finished : Option (Except Exception α)) (exhausted : Bool) : Config α :=
  .running (move.effect.apply state) (move.tasks tasks) (move.finished.orElse fun _ => finished)
    (exhausted || move.exhausted)

/-- The process a key's step observes: the one stepping, the one taking a
signal, or the one a signal bounces from. -/
private def Key.watched : Key → Option PID
  | .own processId _ | .deliver _ processId | .bounce _ processId => some processId
  | .fire _ => none

/-- The process whose task a key's step can replace. -/
private def Key.process : Key → Option PID
  | .own processId _ | .deliver _ processId => some processId
  | _ => none

/-- What tasks need for a key's step to be taken in the same way. -/
private def Supports (key : Key) (move : Move α) (tasks tasks' : List (PID × Task α)) : Prop :=
  match key with
  | .own processId _ => tasks'.lookup processId = tasks.lookup processId
  | .deliver _ target =>
      if move.owner.isSome then tasks'.lookup target = tasks.lookup target
      else (tasks'.lookup target).isSome
  | .bounce _ target => tasks'.lookup target = none
  | .fire _ => True

/-- A keyed step as a move, which the key takes in the same way from other
configurations agreeing on what it observes. -/
private structure Moves (key : Key) (footprint : Footprint) (state : State)
    (tasks : List (PID × Task α)) (finished : Option (Except Exception α))
    (exhausted : Bool) (event : Event) (next : Config α) (move : Move α) : Prop where
  effect : move.effect = footprint.effect
  event : event = move.event
  next : next = move.config state tasks finished exhausted
  transfer : ∀ state' tasks' finished' exhausted',
    Wellformed (.running state' tasks' finished' exhausted') →
    footprint.observes.Agree state state' → Supports key move tasks tasks' →
    (key, move.event, move.config state' tasks' finished' exhausted') ∈
      (Config.running state' tasks' finished' exhausted').steps
  owner : ∀ processId, move.owner = some processId → key.process = some processId
  replaced : ∀ entry ∈ move.replacement, some entry.1 = key.process ∨
    (entry.1 ∉ tasks.map Prod.fst ∧ (footprint.effect.record entry.1 none).isSome)
  ends : ∀ processId, move.owner = some processId → processId ∉ move.replacement.map Prod.fst →
    footprint.effect.record processId (state.processes processId) = none
  observed : ∀ processId, key.watched = some processId →
    ∃ view, (processId, view) ∈ footprint.observes.records
  reports : move.finished.isSome → ∃ processId task, move.owner = some processId ∧
    processId ∉ move.replacement.map Prod.fst ∧ tasks.lookup processId = some task ∧ ¬task.Quiet
  /-- Only a process's own step leaves processes in its place. -/
  replacing : move.replacement ≠ [] → ∃ processId index, key = .own processId index

private theorem split_of_lookup {tasks : List (PID × Task α)} {processId : PID} {task : Task α}
    (found : tasks.lookup processId = some task) :
    ∃ before after, tasks = before ++ (processId, task) :: after :=
  List.append_of_mem (mem_of_lookup found)

/-- A spawned child is not among the processes. -/
private theorem child_fresh {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    {processId child : PID} {task : Task α} {transition : Transition α}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (mem : (processId, task) ∈ tasks) (possible : transition ∈ task.transitions state processId)
    (spawn : transition.event = .spawn processId child) : child ∉ tasks.map Prod.fst := by
  intro found
  simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right] at found
  obtain ⟨task', found⟩ := found
  have live := wellformed.2.2.1 _ mem
  have spawned := (transition_facts possible live).2.2.2.2.1 child spawn
  have := wellformed.2.1 (processId, task) mem (child, task') found _ [] (by rw [spawned.1])
  simp only at this
  omega

private theorem own_moves {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    {before after : List (PID × Task α)} {processId : PID} {task : Task α} {index : Nat}
    {transition : Transition α}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (split : (before, (processId, task), after) ∈ splits tasks)
    (found : (task.own state processId)[index]? = some transition) :
    Moves (.own processId index) (task.footprint state processId) state tasks finished exhausted
      transition.event (transition.apply before after finished exhausted)
      { event := transition.event, effect := (task.footprint state processId).effect
        owner := some processId, replacement := transition.tasks, finished := transition.finished
        exhausted := transition.exhausted } := by
  have equal := eq_of_mem_splits split
  have mem : (processId, task) ∈ tasks := by rw [equal]; simp
  have live := wellformed.2.2.1 _ mem
  have possibleOwn := List.mem_of_getElem? found
  have possible : transition ∈ task.transitions state processId := by
    simp [Task.transitions, possibleOwn]
  obtain ⟨frame, inner, entries, grows, spawned, -, -, stays, -⟩ := transition_facts possible live
  refine ⟨rfl, rfl, ?_, ?_, fun _ found => by cases found; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Transition.apply, Move.config, Move.tasks]
    rw [own_state live possibleOwn, equal, replace_split (equal ▸ wellformed.1)]
  · intro state' tasks' finished' exhausted' wellformed' agree supports
    simp only [Supports, lookup_of_mem wellformed.1 mem] at supports
    obtain ⟨before', after', equal'⟩ := split_of_lookup supports
    obtain ⟨transition', found', matched⟩ :=
      (own_matches live agree).get found
    refine mem_steps.mpr (.inl ⟨before', processId, task, after', transition', ?_, ?_, ?_, ?_⟩)
    · rw [equal']; exact mem_splits
    · exact mem_keyed.mpr (.inl ⟨index, rfl, found'⟩)
    · exact matched.1.symm
    · obtain ⟨-, tasks, finished, exhausted, state⟩ := matched
      simp only [Transition.apply, Move.config, Move.tasks, state, tasks, finished, exhausted]
      rw [equal', replace_split (equal' ▸ wellformed'.1)]
  · intro entry added
    rcases entries entry added with same | ⟨child, spawn, same⟩
    · exact .inl (by rw [same]; rfl)
    · refine .inr ⟨same ▸ child_fresh wellformed mem possible spawn, ?_⟩
      have dead : state.processes child = none := by
        cases alive : state.processes child with
        | none => rfl
        | some _ =>
          exact absurd (wellformed.2.2.2.2 child (by simp [alive]))
            (child_fresh wellformed mem possible spawn)
      have := (spawned child spawn).2.1
      rw [own_state live possibleOwn, Effect.processes_apply, dead] at this
      rw [same]; exact this
  · intro processId' owner notAdded
    cases owner
    rw [← Effect.processes_apply, ← own_state live possibleOwn]
    cases alive : transition.state.processes processId with
    | none => rfl
    | some _ => exact absurd (stays (by simp [alive])) notAdded
  · intro processId' watched
    cases watched
    exact Task.footprint_observes
  · intro reported
    obtain ⟨empty, notQuiet⟩ := finished_facts possible reported
    exact ⟨processId, task, rfl, by simp [empty], lookup_of_mem wellformed.1 mem, notQuiet⟩
  · exact fun _ => ⟨processId, index, rfl⟩

private theorem Footprint.delivery_observes {state : State} {envelope : Envelope} :
    (envelope.target, ProcessState.live) ∈ (Footprint.delivery state envelope).observes.records := by
  obtain ⟨source, target, signal⟩ := envelope
  unfold Footprint.delivery
  cases signal <;> simp only [Observes.and] <;> (try split) <;> simp

/-- A signal arriving leaves the receiver, or ends it. -/
private theorem delivery_shape {state : State} {processId : PID} {task : Task α} {envelope : Envelope}
    {rest : List Envelope} :
    (task.delivery state processId envelope rest).event = .deliver envelope ∧
    (task.delivery state processId envelope rest).exhausted = false ∧
    (((task.delivery state processId envelope rest).tasks = [(processId, task)] ∧
        (task.delivery state processId envelope rest).finished = none ∧
        ({ state with inTransit := rest }.receive envelope).2 = none) ∨
      ((task.delivery state processId envelope rest).tasks = [] ∧
        (task.delivery state processId envelope rest).state.processes processId = none ∧
        ({ state with inTransit := rest }.receive envelope).2.isSome)) := by
  simp only [Task.delivery]
  split
  · rename_i exits
    exact ⟨rfl, rfl, .inl ⟨rfl, rfl, exits⟩⟩
  · rename_i reason exits
    refine ⟨rfl, rfl, .inr ⟨rfl, ?_, by simp [exits]⟩⟩
    simp [Task.ended, State.processes_terminate, State.update]

private theorem deliver_moves {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    {before after : List (PID × Task α)} {processId : PID} {task : Task α}
    {envelope : Envelope} {rest : List Envelope}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (split : (before, (processId, task), after) ∈ splits tasks)
    (delivered : (envelope, rest) ∈ deliverable state.inTransit) (target : envelope.target = processId) :
    Moves (.deliver envelope.source processId) (Footprint.delivery state envelope) state tasks
      finished exhausted (task.delivery state processId envelope rest).event
      ((task.delivery state processId envelope rest).apply before after finished exhausted)
      { event := (task.delivery state processId envelope rest).event
        effect := (Footprint.delivery state envelope).effect
        owner := if (task.delivery state processId envelope rest).tasks.isEmpty then some processId
          else none
        finished := (task.delivery state processId envelope rest).finished
        exhausted := (task.delivery state processId envelope rest).exhausted } := by
  have equal := eq_of_mem_splits split
  have mem : (processId, task) ∈ tasks := by rw [equal]; simp
  have stateEq := (delivery_matches (task := task) delivered target
    (Observes.Agree.refl _ state)).2.2
  obtain ⟨event, noExhaust, shape⟩ := delivery_shape (state := state) (processId := processId)
    (task := task) (envelope := envelope) (rest := rest)
  refine ⟨rfl, rfl, ?_, ?_, (fun _ owner => by split at owner <;> simp_all [Key.process]), ?_, ?_, ?_, ?_,
    fun nonempty => absurd rfl nonempty⟩
  · simp only [Transition.apply, Move.config, Move.tasks, stateEq, noExhaust]
    rcases shape with ⟨tasksEq, finishedEq, -⟩ | ⟨tasksEq, -, -⟩
    · simp [tasksEq, finishedEq, equal]
    · simp only [tasksEq, List.isEmpty_nil, ↓reduceIte, List.append_nil]
      rw [equal, replace_split (equal ▸ wellformed.1)]
      simp
  · intro state' tasks' finished' exhausted' wellformed' agree supports
    have exitsSame : ∀ task' : Task α,
        (task'.delivery state processId envelope rest).tasks.isEmpty =
          (task.delivery state processId envelope rest).tasks.isEmpty := by
      intro task'
      obtain ⟨-, -, shape'⟩ := delivery_shape (state := state) (processId := processId)
        (task := task') (envelope := envelope) (rest := rest)
      rcases shape with ⟨tasksEq, -, exits⟩ | ⟨tasksEq, -, exits⟩ <;>
        rcases shape' with ⟨tasksEq', -, exits'⟩ | ⟨tasksEq', -, exits'⟩ <;>
        simp_all
    obtain ⟨task', found'⟩ : ∃ task', tasks'.lookup processId = some task' := by
      simp only [Supports] at supports
      split at supports
      · exact ⟨task, supports.trans (lookup_of_mem wellformed.1 mem)⟩
      · exact Option.isSome_iff_exists.mp supports
    obtain ⟨before', after', equal'⟩ := split_of_lookup found'
    obtain ⟨delivered', matched, -⟩ := delivery_matches (task := task') delivered target agree
    refine mem_steps.mpr (.inl ⟨before', processId, task', after',
      task'.delivery state' processId envelope (arrive envelope.source envelope.target state'.inTransit),
      ?_, ?_, ?_, ?_⟩)
    · rw [equal']; exact mem_splits
    · exact mem_keyed.mpr (.inr ⟨envelope, _, delivered', target, rfl, rfl⟩)
    · rw [matched.1]
      obtain ⟨event'', -, -⟩ := delivery_shape (state := state) (processId := processId)
        (task := task') (envelope := envelope) (rest := rest)
      rw [event'', event]
    · obtain ⟨-, tasksMatch, finishedMatch, exhaustedMatch, stateMatch⟩ := matched
      obtain ⟨-, noExhaust', shape'⟩ := delivery_shape (state := state) (processId := processId)
        (task := task') (envelope := envelope) (rest := rest)
      simp only [Transition.apply, Move.config, Move.tasks, stateMatch, tasksMatch, finishedMatch,
        exhaustedMatch, noExhaust', noExhaust]
      rcases shape' with ⟨tasksEq', finishedEq', -⟩ | ⟨tasksEq', -, -⟩
      · have : (task.delivery state processId envelope rest).tasks.isEmpty = false := by
          rw [← exitsSame task', tasksEq']; rfl
        rcases shape with ⟨-, finishedEq, -⟩ | ⟨tasksEq, -, -⟩
        · simp [tasksEq', finishedEq', finishedEq, this, equal']
        · simp [tasksEq] at this
      · have : (task.delivery state processId envelope rest).tasks.isEmpty = true := by
          rw [← exitsSame task', tasksEq']; rfl
        simp only [this, ↓reduceIte] at supports
        simp only [Supports, ↓reduceIte, Option.isSome_some, found',
          lookup_of_mem wellformed.1 mem, Option.some.injEq] at supports
        subst supports
        simp only [tasksEq', ↓reduceIte, List.append_nil, List.isEmpty_nil]
        rw [equal', replace_split (equal' ▸ wellformed'.1)]
        simp
  · intro entry added; simp at added
  · intro processId' owner notAdded
    split at owner
    · rename_i empty
      cases owner
      rw [← Effect.processes_apply, ← stateEq]
      rcases shape with ⟨tasksEq, -, -⟩ | ⟨-, dead, -⟩
      · simp [tasksEq] at empty
      · exact dead
    · cases owner
  · intro processId' watched
    cases watched
    exact ⟨_, target ▸ Footprint.delivery_observes⟩
  · intro reported
    rcases shape with ⟨-, finishedEq, -⟩ | ⟨tasksEq, -, -⟩
    · simp [finishedEq] at reported
    · have possible : task.delivery state processId envelope rest ∈ task.transitions state processId := by
        simp only [Task.transitions, Task.deliveries, List.mem_append, List.mem_filterMap]
        refine .inr ⟨(envelope, rest), delivered, ?_⟩
        simp [target]
      obtain ⟨-, notQuiet⟩ := finished_facts possible reported
      exact ⟨processId, task, by simp [tasksEq], by simp, lookup_of_mem wellformed.1 mem, notQuiet⟩

private theorem bounce_moves {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    {envelope : Envelope} {rest : List Envelope}
    (delivered : (envelope, rest) ∈ deliverable state.inTransit) :
    Moves (.bounce envelope.source envelope.target) (Footprint.bounce envelope) state tasks
      finished exhausted (.bounce envelope)
      (.running ({ state with inTransit := rest }.bounce envelope) tasks finished exhausted)
      { event := .bounce envelope, effect := (Footprint.bounce envelope).effect } := by
  obtain ⟨-, -, -, stateEq⟩ := bounce_matches (other := state) delivered (Observes.Agree.refl _ state)
  refine ⟨rfl, rfl, ?_, ?_, (fun _ found => by cases found), (fun _ added => by simp at added),
    (fun _ found => by cases found), ?_, (fun reported => by simp at reported),
    fun nonempty => absurd rfl nonempty⟩
  · simp [Move.config, Move.tasks, stateEq]
  · intro state' tasks' finished' exhausted' _ agree supports
    obtain ⟨-, delivered', stateEq', -⟩ := bounce_matches delivered agree
    have dead : (tasks'.lookup envelope.target).isSome = false := by
      simp only [Supports] at supports; simp [supports]
    refine mem_steps.mpr (.inr (.inl ⟨envelope, _, delivered', dead, rfl, rfl, ?_⟩))
    simp [Move.config, Move.tasks, stateEq']
  · intro processId watched
    cases watched
    exact ⟨ProcessState.live, by simp [Footprint.bounce]⟩

private theorem fire_moves {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {timer : Timer}
    (firing : timer ∈ state.firing) :
    Moves (.fire timer.reference) (Footprint.fire timer) state tasks finished exhausted
      (.fire timer.reference) (.running (state.fire timer) tasks finished exhausted)
      { event := .fire timer.reference, effect := (Footprint.fire timer).effect } := by
  refine ⟨rfl, rfl, ?_, ?_, (fun _ found => by cases found), (fun _ added => by simp at added),
    (fun _ found => by cases found), (fun _ watched => by cases watched),
    (fun reported => by simp at reported), fun nonempty => absurd rfl nonempty⟩
  · simp [Move.config, Move.tasks, (fire_matches firing (Observes.Agree.refl _ state)).2]
  · intro state' tasks' finished' exhausted' _ agree _
    obtain ⟨firing', stateEq⟩ := fire_matches firing agree
    refine mem_steps.mpr (.inr (.inr ⟨timer, firing', rfl, rfl, ?_⟩))
    simp [Move.config, Move.tasks, stateEq]

private theorem oldest_iff {source target : PID} {inTransit : List Envelope} {envelope : Envelope} :
    oldest source target inTransit = [envelope] ↔
      inTransit.find? (Envelope.between source target) = some envelope := by
  simp only [oldest]
  cases inTransit.find? (Envelope.between source target) <;> simp

private theorem between_of_find {source target : PID} {inTransit : List Envelope} {envelope : Envelope}
    (found : inTransit.find? (Envelope.between source target) = some envelope) :
    envelope.source = source ∧ envelope.target = target := by
  have := List.find?_some found
  simpa [Envelope.between] using this

/-- The step with a key, as a move. -/
private theorem moves {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key}
    {event : Event} {next : Config α} {footprint : Footprint}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint) :
    ∃ move, Moves key footprint state tasks finished exhausted event next move := by
  rw [mem_steps] at mem
  rcases mem with ⟨before, processId, task, after, transition, split, keyed, rfl, rfl⟩ |
    ⟨envelope, rest, delivered, dead, rfl, rfl, rfl⟩ | ⟨timer, firing, rfl, rfl, rfl⟩
  · have lookup : tasks.lookup processId = some task :=
      lookup_of_mem wellformed.1 (by rw [eq_of_mem_splits split]; simp)
    rw [mem_keyed] at keyed
    rcases keyed with ⟨index, rfl, own⟩ | ⟨envelope, rest, delivered, target, rfl, rfl⟩
    · have bound : index < (task.own state processId).length := by
        have := List.getElem?_eq_some_iff.mp own; exact this.1
      simp only [Config.footprint, lookup, bound, ↓reduceIte, Option.some.injEq] at found
      subst found
      exact ⟨_, own_moves wellformed split own⟩
    · have oldestFound := oldest_iff.mp (mem_deliverable_iff.mp delivered).1
      rw [target] at oldestFound
      simp only [Config.footprint, lookup, oldestFound, Option.some.injEq] at found
      subst found
      exact ⟨_, deliver_moves wellformed split delivered target⟩
  · have oldestFound := oldest_iff.mp (mem_deliverable_iff.mp delivered).1
    have missing : tasks.lookup envelope.target = none := by simpa using dead
    simp only [Config.footprint, missing, oldestFound, Option.some.injEq] at found
    subst found
    exact ⟨_, bounce_moves delivered⟩
  · have timerFound : state.timers.find? (·.reference == timer.reference) = some timer := by
      have := mem_firing_iff.mp firing
      simp only [firstTimer] at this
      cases equal : state.timers.find? (·.reference == timer.reference) <;> simp_all
    simp only [Config.footprint, timerFound, Option.some.injEq] at found
    subst found
    exact ⟨_, fire_moves firing⟩

/-- A key with a footprint names a step. -/
private theorem enabled {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key}
    {footprint : Footprint}
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint) :
    ∃ event next, (key, event, next) ∈ (Config.running state tasks finished exhausted).steps := by
  cases key with
  | own processId index =>
    simp only [Config.footprint] at found
    split at found
    · rename_i task lookup
      split at found
      · rename_i bound
        obtain ⟨before, after, equal⟩ := split_of_lookup lookup
        exact ⟨_, _, mem_steps.mpr (.inl ⟨before, processId, task, after, _, by rw [equal]; exact mem_splits,
          mem_keyed.mpr (.inl ⟨index, rfl, List.getElem?_eq_getElem bound⟩), rfl, rfl⟩)⟩
      · simp at found
    · simp at found
  | deliver source target =>
    simp only [Config.footprint] at found
    split at found
    · rename_i task envelope lookup oldestFound
      obtain ⟨before, after, equal⟩ := split_of_lookup lookup
      obtain ⟨rfl, rfl⟩ := between_of_find oldestFound
      have delivered : (envelope, arrive envelope.source envelope.target state.inTransit) ∈
          deliverable state.inTransit := mem_deliverable_iff.mpr ⟨oldest_iff.mpr oldestFound, rfl⟩
      exact ⟨_, _, mem_steps.mpr (.inl ⟨before, envelope.target, task, after, _,
        by rw [equal]; exact mem_splits, mem_keyed.mpr (.inr ⟨envelope, _, delivered, rfl, rfl, rfl⟩),
        rfl, rfl⟩)⟩
    · simp at found
  | bounce source target =>
    simp only [Config.footprint] at found
    split at found
    · rename_i envelope lookup oldestFound
      obtain ⟨rfl, rfl⟩ := between_of_find oldestFound
      have delivered : (envelope, arrive envelope.source envelope.target state.inTransit) ∈
          deliverable state.inTransit := mem_deliverable_iff.mpr ⟨oldest_iff.mpr oldestFound, rfl⟩
      exact ⟨_, _, mem_steps.mpr (.inr (.inl ⟨envelope, _, delivered, by simp [lookup], rfl, rfl, rfl⟩))⟩
    · simp at found
  | fire reference =>
    simp only [Config.footprint] at found
    split at found
    · rename_i timer timerFound
      have same : timer.reference = reference := by simpa using List.find?_some timerFound
      subst same
      have firing : timer ∈ state.firing := mem_firing_iff.mpr (by simp [firstTimer, timerFound])
      exact ⟨_, _, mem_steps.mpr (.inr (.inr ⟨timer, firing, rfl, rfl, rfl⟩))⟩
    · simp at found

/-- An effect keeping what a step observes keeps whether observed processes are live. -/
private theorem Effect.live_of_agree {effect : Effect} {observes : Observes} {state : State}
    {processId : PID} {view : ProcessState → ProcessState}
    (agree : observes.Agree state (effect.apply state)) (mem : (processId, view) ∈ observes.records) :
    (effect.record processId (state.processes processId)).isSome = (state.processes processId).isSome := by
  have := congrArg Option.isSome (agree.1 _ mem)
  simpa using this

private theorem task_of_footprint {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key}
    {footprint : Footprint} {processId : PID}
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint)
    (process : key.process = some processId) : (tasks.lookup processId).isSome := by
  cases key with
  | own processId' index =>
    cases process
    simp only [Config.footprint] at found
    split at found <;> simp_all
  | deliver source target =>
    cases process
    simp only [Config.footprint] at found
    split at found <;> simp_all
  | _ => cases process

private theorem missing_of_footprint {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {source target : PID}
    {footprint : Footprint}
    (found : (Config.running state tasks finished exhausted).footprint (.bounce source target) =
      some footprint) : tasks.lookup target = none := by
  simp only [Config.footprint] at found
  split at found
  · assumption
  · simp at found

private theorem index_of_footprint {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID}
    {index : Nat} {footprint : Footprint}
    (found : (Config.running state tasks finished exhausted).footprint (.own processId index) =
      some footprint) : index = 0 := by
  simp only [Config.footprint] at found
  split at found
  · split at found
    · rename_i bound
      have := Task.own_length (state := state) (processId := processId) (task := by assumption)
      omega
    · simp at found
  · simp at found

private theorem live_of_lookup {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : (tasks.lookup processId).isSome) : (state.processes processId).isSome := by
  obtain ⟨task, found⟩ := Option.isSome_iff_exists.mp found
  exact wellformed.2.2.1 _ (mem_of_lookup found)

private theorem mem_of_isSome {tasks : List (PID × Task α)} {processId : PID}
    (found : (tasks.lookup processId).isSome) : processId ∈ tasks.map Prod.fst := by
  obtain ⟨task, found⟩ := Option.isSome_iff_exists.mp found
  exact List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup found)

private theorem dead_of_missing {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (missing : tasks.lookup processId = none) : state.processes processId = none := by
  cases alive : state.processes processId with
  | none => rfl
  | some _ =>
    have := wellformed.2.2.2.2 processId (by simp [alive])
    simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right] at this
    obtain ⟨task, mem⟩ := this
    have := lookup_of_mem wellformed.1 mem
    simp_all

private theorem lookup_replace_self {processId : PID} {replacement tasks : List (PID × Task α)}
    (distinct : tasks.Pairwise fun first second => first.1 ≠ second.1)
    (present : processId ∈ tasks.map Prod.fst) :
    (replace processId replacement tasks).lookup processId = replacement.lookup processId := by
  simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right] at present
  obtain ⟨task, mem⟩ := present
  obtain ⟨before, after, rfl⟩ := List.append_of_mem mem
  rw [replace_split distinct]
  rw [List.pairwise_append, List.pairwise_cons] at distinct
  have missing : before.lookup processId = none := lookup_none fun found => by
    simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right] at found
    obtain ⟨task', mem'⟩ := found
    exact distinct.2.2 _ mem' (processId, task) (by simp) rfl
  have missing' : after.lookup processId = none := lookup_none fun found => by
    simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right] at found
    obtain ⟨task', mem'⟩ := found
    exact distinct.2.1.1 _ mem' rfl
  rw [List.lookup_append, List.lookup_append, missing, missing']
  cases replacement.lookup processId <;> rfl

/-- Two processes of a well-formed configuration do not both report the result. -/
private theorem quiet_of_distinct {tasks : List (PID × Task α)} {processId other : PID}
    {task task' : Task α} (distinct : tasks.Pairwise fun first second => first.1 ≠ second.1)
    (quiet : tasks.Pairwise fun first second => first.2.Quiet ∨ second.2.Quiet)
    (found : tasks.lookup processId = some task) (found' : tasks.lookup other = some task')
    (ne : processId ≠ other) : task.Quiet ∨ task'.Quiet := by
  have mem := mem_of_lookup found
  have mem' := mem_of_lookup found'
  induction tasks with
  | nil => simp at mem
  | cons head rest ih =>
    rw [List.pairwise_cons] at distinct quiet
    simp only [List.mem_cons] at mem mem'
    rcases mem with rfl | mem <;> rcases mem' with equal | mem'
    · simp only [Prod.mk.injEq] at equal; exact absurd equal.1.symm ne
    · exact quiet.1 _ mem'
    · subst equal; exact (quiet.1 _ mem).symm
    · have lookup := lookup_of_mem distinct.2 mem
      have lookup' := lookup_of_mem distinct.2 mem'
      exact ih distinct.2 quiet.2 lookup lookup' (mem_of_lookup lookup) (mem_of_lookup lookup')

private theorem watched_of_process {key : Key} {processId : PID}
    (process : key.process = some processId) : key.watched = some processId := by
  cases key <;> simp_all [Key.process, Key.watched]

private theorem isSome_lookup {entries : List (PID × γ)} {processId : PID}
    (mem : processId ∈ entries.map Prod.fst) : (entries.lookup processId).isSome := by
  induction entries with
  | nil => simp at mem
  | cons head rest ih =>
    obtain ⟨processId', item⟩ := head
    simp only [List.map_cons, List.mem_cons] at mem
    simp only [List.lookup]
    split
    · rfl
    · rename_i different
      rcases mem with rfl | mem
      · simp at different
      · exact ih mem

/-- Two independent steps of a well-formed configuration, as moves. -/
private structure Pair (state : State) (tasks : List (PID × Task α))
    (finished : Option (Except Exception α)) (exhausted : Bool) (key key' : Key)
    (footprint footprint' : Footprint) (move move' : Move α) : Prop where
  wellformed : Wellformed (.running state tasks finished exhausted)
  found : (Config.running state tasks finished exhausted).footprint key = some footprint
  found' : (Config.running state tasks finished exhausted).footprint key' = some footprint'
  moved : ∃ event next, Moves key footprint state tasks finished exhausted event next move
  moved' : ∃ event next, Moves key' footprint' state tasks finished exhausted event next move'
  distinct : key ≠ key'
  agree : footprint'.observes.Agree state (footprint.effect.apply state)
  agree' : footprint.observes.Agree state (footprint'.effect.apply state)

private theorem Pair.symm {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {footprint footprint' : Footprint} {move move' : Move α}
    (pair : Pair state tasks finished exhausted key key' footprint footprint' move move') :
    Pair state tasks finished exhausted key' key footprint' footprint move' move :=
  ⟨pair.wellformed, pair.found', pair.found, pair.moved', pair.moved, Ne.symm pair.distinct, pair.agree',
    pair.agree⟩

/-- A move ending a process changes what any step observing it observes. -/
private theorem Pair.not_ends {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {footprint footprint' : Footprint} {move move' : Move α}
    (pair : Pair state tasks finished exhausted key key' footprint footprint' move move')
    {processId : PID} (owner : move.owner = some processId)
    (watched : key'.watched = some processId) : processId ∈ move.replacement.map Prod.fst := by
  obtain ⟨_, _, moved⟩ := pair.moved
  obtain ⟨_, _, moved'⟩ := pair.moved'
  have present := task_of_footprint pair.found (moved.owner processId owner)
  have live := live_of_lookup pair.wellformed present
  by_cases added : processId ∈ move.replacement.map Prod.fst
  · exact added
  exfalso
  have notAdded := added
  obtain ⟨view, mem⟩ := moved'.observed processId watched
  have := Effect.live_of_agree pair.agree mem
  rw [moved.ends processId owner notAdded, live] at this
  simp at this

/-- After a move, the other step's process has the task it needs. -/
private theorem Pair.supports {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {footprint footprint' : Footprint} {move move' : Move α}
    (pair : Pair state tasks finished exhausted key key' footprint footprint' move move') :
    Supports key' move' tasks (move.tasks tasks) := by
  obtain ⟨_, _, moved⟩ := pair.moved
  obtain ⟨_, _, moved'⟩ := pair.moved'
  have wellformed := pair.wellformed
  cases owner : move.owner with
  | none =>
    have same : move.tasks tasks = tasks := by simp [Move.tasks, owner]
    rw [same]
    cases key' with
    | own => rfl
    | deliver source target =>
      simp only [Supports]
      split
      · trivial
      · exact task_of_footprint pair.found' rfl
    | bounce => exact missing_of_footprint pair.found'
    | fire => trivial
  | some processId =>
    have process := moved.owner processId owner
    have present := task_of_footprint pair.found process
    have fresh : ∀ other ∈ move.replacement.map Prod.fst, other ≠ processId →
        other ∉ tasks.map Prod.fst ∧ (footprint.effect.record other none).isSome := by
      intro other mem ne
      simp only [List.mem_map] at mem
      obtain ⟨entry, mem, rfl⟩ := mem
      rcases moved.replaced entry mem with same | fresh
      · rw [process] at same; cases same; exact absurd rfl ne
      · exact fresh
    have unchanged : ∀ other, other ≠ processId → other ∈ tasks.map Prod.fst →
        (move.tasks tasks).lookup other = tasks.lookup other := by
      intro other ne mem
      simp only [Move.tasks, owner]
      exact lookup_replace ne fun added => (fresh other added ne).1 mem
    have kept : processId ∈ move.replacement.map Prod.fst →
        ((move.tasks tasks).lookup processId).isSome := by
      intro added
      simp only [Move.tasks, owner]
      rw [lookup_replace_self wellformed.1 (mem_of_isSome present)]
      exact isSome_lookup added
    cases key' with
    | own other index =>
      simp only [Supports]
      have present' := task_of_footprint pair.found' (rfl : Key.process (.own other index) = some other)
      by_cases same : other = processId
      · subst same
        exfalso
        have added := pair.not_ends owner rfl
        obtain ⟨processId', index', equal⟩ := moved.replacing (List.ne_nil_of_mem
          (List.mem_map.mp added).choose_spec.1)
        subst equal
        cases process
        have := index_of_footprint pair.found
        have := index_of_footprint pair.found'
        exact pair.distinct (by subst_vars; rfl)
      · exact unchanged other same (mem_of_isSome present')
    | deliver source target =>
      simp only [Supports]
      have present' := task_of_footprint pair.found' (rfl : Key.process (.deliver source target) = some target)
      by_cases same : target = processId
      · subst same
        have added := pair.not_ends owner rfl
        split
        · exfalso
          rename_i ending
          obtain ⟨target', owner'⟩ := Option.isSome_iff_exists.mp ending
          have process' := moved'.owner target' owner'
          simp only [Key.process, Option.some.injEq] at process'
          subst process'
          have empty : move'.replacement = [] := by
            cases replaced : move'.replacement with
            | nil => rfl
            | cons head rest =>
              obtain ⟨_, _, equal⟩ := moved'.replacing (by simp [replaced])
              cases equal
          have := pair.symm.not_ends owner' (watched_of_process process)
          simp [empty] at this
        · exact kept added
      · have := unchanged target same (mem_of_isSome present')
        split
        · exact this
        · rw [this]; exact present'
    | bounce source target =>
      simp only [Supports]
      have missing := missing_of_footprint pair.found'
      have dead := dead_of_missing wellformed missing
      have ne : target ≠ processId := fun same => by subst same; simp [missing] at present
      have notAdded : target ∉ move.replacement.map Prod.fst := fun mem => by
        obtain ⟨-, created⟩ := fresh target mem ne
        obtain ⟨view, observed⟩ := moved'.observed target rfl
        have := Effect.live_of_agree pair.agree observed
        rw [dead] at this
        simp_all
      simp only [Move.tasks, owner]
      rw [lookup_replace ne notAdded, missing]
    | fire => trivial

/-- Independent moves change the tasks in either order to the same tasks. -/
private theorem Pair.tasks_comm {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {footprint footprint' : Footprint} {move move' : Move α}
    (pair : Pair state tasks finished exhausted key key' footprint footprint' move move') :
    move.tasks (move'.tasks tasks) = move'.tasks (move.tasks tasks) := by
  obtain ⟨_, _, moved⟩ := pair.moved
  obtain ⟨_, _, moved'⟩ := pair.moved'
  cases owner : move.owner with
  | none => simp [Move.tasks, owner]
  | some processId =>
    cases owner' : move'.owner with
    | none => simp [Move.tasks, owner, owner']
    | some other =>
      simp only [Move.tasks, owner, owner']
      have process := moved.owner processId owner
      have process' := moved'.owner other owner'
      have present := task_of_footprint pair.found process
      have present' := task_of_footprint pair.found' process'
      by_cases same : processId = other
      · exfalso
        subst same
        have added := pair.not_ends owner (watched_of_process process')
        have added' := pair.symm.not_ends owner' (watched_of_process process)
        obtain ⟨_, index, equal⟩ := moved.replacing (List.ne_nil_of_mem
          (List.mem_map.mp added).choose_spec.1)
        obtain ⟨_, index', equal'⟩ := moved'.replacing (List.ne_nil_of_mem
          (List.mem_map.mp added').choose_spec.1)
        subst equal equal'
        simp only [Key.process, Option.some.injEq] at process process'
        subst process process'
        have := index_of_footprint pair.found
        have := index_of_footprint pair.found'
        exact pair.distinct (by subst_vars; rfl)
      · apply replace_comm same
        · intro added
          rcases List.mem_map.mp added with ⟨entry, mem, equal⟩
          rcases moved.replaced entry mem with same' | fresh
          · rw [process, equal] at same'; cases same'; exact same rfl
          · exact fresh.1 (equal ▸ mem_of_isSome present')
        · intro added
          rcases List.mem_map.mp added with ⟨entry, mem, equal⟩
          rcases moved'.replaced entry mem with same' | fresh
          · rw [process', equal] at same'; cases same'; exact same rfl
          · exact fresh.1 (equal ▸ mem_of_isSome present)

/-- At most one of two independent moves reports the result. -/
private theorem Pair.quiet {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {footprint footprint' : Footprint} {move move' : Move α}
    (pair : Pair state tasks finished exhausted key key' footprint footprint' move move') :
    move.finished = none ∨ move'.finished = none := by
  obtain ⟨_, _, moved⟩ := pair.moved
  obtain ⟨_, _, moved'⟩ := pair.moved'
  cases reported : move.finished with
  | none => exact .inl rfl
  | some _ =>
    cases reported' : move'.finished with
    | none => exact .inr rfl
    | some _ =>
      exfalso
      obtain ⟨processId, task, owner, notAdded, found, notQuiet⟩ := moved.reports (by simp [reported])
      obtain ⟨other, task', owner', -, found', notQuiet'⟩ := moved'.reports (by simp [reported'])
      by_cases same : processId = other
      · subst same
        exact notAdded (pair.not_ends owner (watched_of_process (moved'.owner _ owner')))
      · rcases quiet_of_distinct pair.wellformed.1 pair.wellformed.2.2.2.1 found found' same with
          quiet | quiet
        · exact notQuiet quiet
        · exact notQuiet' quiet

private theorem Step.of_mem_steps {config next : Config α} {key : Key} {event : Event}
    (mem : (key, event, next) ∈ config.steps) : Step config event next := by
  cases config with
  | start => simp [Config.steps] at mem
  | running state tasks finished exhausted =>
    simp only [Step, ← Config.steps_running]
    exact List.mem_map.mpr ⟨_, mem, rfl⟩

private theorem orElse_comm {first second rest : Option γ} (none : first = none ∨ second = none) :
    (first.orElse fun _ => second.orElse fun _ => rest) =
      second.orElse fun _ => first.orElse fun _ => rest := by
  rcases none with rfl | rfl
  · cases second <;> rfl
  · cases first <;> rfl

/-- Two steps of a pair whose effects commute reach the same configuration in
either order. -/
private theorem Pair.square {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {footprint footprint' : Footprint} {move move' : Move α} {event event' : Event}
    {next next' : Config α}
    (pair : Pair state tasks finished exhausted key key' footprint footprint' move move')
    (moved : Moves key footprint state tasks finished exhausted event next move)
    (moved' : Moves key' footprint' state tasks finished exhausted event' next' move')
    (commutes : footprint.effect.apply (footprint'.effect.apply state) =
      footprint'.effect.apply (footprint.effect.apply state))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key', event', next') ∈ (Config.running state tasks finished exhausted).steps) :
    ∃ last, (key', event', last) ∈ next.steps ∧ (key, event, last) ∈ next'.steps := by
  have wellformed := Step.wellformed (Step.of_mem_steps mem) pair.wellformed
  have wellformed' := Step.wellformed (Step.of_mem_steps mem') pair.wellformed
  rw [moved.next] at wellformed ⊢
  rw [moved'.next] at wellformed' ⊢
  have forth := moved'.transfer _ _ _ _ wellformed (by rw [moved.effect]; exact pair.agree)
    pair.supports
  have back := moved.transfer _ _ _ _ wellformed' (by rw [moved'.effect]; exact pair.agree')
    pair.symm.supports
  refine ⟨_, by rw [moved'.event]; exact forth, ?_⟩
  rw [moved.event]
  have same : move.config (move'.effect.apply state) (move'.tasks tasks)
      (move'.finished.orElse fun _ => finished) (exhausted || move'.exhausted) =
      move'.config (move.effect.apply state) (move.tasks tasks)
        (move.finished.orElse fun _ => finished) (exhausted || move.exhausted) := by
    simp only [Move.config]
    rw [moved.effect, moved'.effect, commutes, pair.tasks_comm, orElse_comm pair.quiet]
    congr 1
    cases exhausted <;> cases move.exhausted <;> cases move'.exhausted <;> rfl
  rw [← same]
  exact back

/-- Independent steps commute: when one step follows another, it can also be
taken first, followed by the other. -/
private theorem diamond {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (independent : (Config.running state tasks finished exhausted).independent key' key = true)
    (mem' : (key', event', next') ∈ next.steps) :
    ∃ next'', (key', event', next'') ∈ (Config.running state tasks finished exhausted).steps ∧
      Step next'' event next' := by
  simp only [Config.independent, Bool.and_eq_true, bne_iff_ne, ne_eq] at independent
  obtain ⟨distinct, independent⟩ := independent
  split at independent
  · rename_i footprint' footprint found' found
    simp only [Footprint.independent, Bool.and_eq_true] at independent
    obtain ⟨⟨keeps', keeps⟩, commutes⟩ := independent
    obtain ⟨move, moved⟩ := moves wellformed mem found
    obtain ⟨event₀, next₀, mem₀⟩ := enabled found'
    obtain ⟨move', moved'⟩ := moves wellformed mem₀ found'
    have pair : Pair state tasks finished exhausted key key' footprint footprint' move move' :=
      ⟨wellformed, found, found', ⟨_, _, moved⟩, ⟨_, _, moved'⟩, Ne.symm distinct,
        Effect.agree_of_keeps keeps, Effect.agree_of_keeps keeps'⟩
    obtain ⟨last, forth, back⟩ := pair.square moved moved' (Effect.apply_comm commutes).symm mem mem₀
    have wellformedNext := Step.wellformed (Step.of_mem_steps mem) wellformed
    rw [moved.next] at wellformedNext mem' forth
    obtain ⟨rfl, rfl⟩ := steps_unique wellformedNext mem' forth
    exact ⟨next₀, mem₀, Step.of_mem_steps back⟩
  · simp at independent

/-- Every step of a running configuration has a key. -/
private theorem Step.keyed {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {event : Event}
    {next : Config α} (step : Step (.running state tasks finished exhausted) event next) :
    ∃ key, (key, event, next) ∈ (Config.running state tasks finished exhausted).steps := by
  simp only [Step, ← Config.steps_running, List.mem_map] at step
  obtain ⟨⟨key, event', next'⟩, mem, equal⟩ := step
  simp only [Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  exact ⟨key, mem⟩

/-! ### Steps every run can take first -/

/-- A keyed step observes processes other than its own only through whether they are live. -/
private theorem footprint_observes_others {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key} {footprint : Footprint}
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint) :
    ∀ entry ∈ footprint.observes.records, some entry.1 = key.watched ∨ entry.2 = ProcessState.live := by
  intro entry mem
  cases key with
  | own processId index =>
    simp only [Config.footprint] at found
    split at found
    · split at found
      · simp only [Option.some.injEq] at found
        subst found
        rcases Task.footprint_observes_others entry mem with same | live
        · exact .inl (by simp [Key.watched, same])
        · exact .inr live
      · simp at found
    · simp at found
  | deliver source target =>
    simp only [Config.footprint] at found
    split at found
    · rename_i envelope _ oldestFound
      simp only [Option.some.injEq] at found
      subst found
      obtain ⟨-, rfl⟩ := between_of_find oldestFound
      exact .inl (by simp [Key.watched, Footprint.delivery_observes_target entry mem])
    · simp at found
  | bounce source target =>
    simp only [Config.footprint] at found
    split at found
    · simp only [Option.some.injEq] at found
      subst found
      simp only [Footprint.bounce, List.mem_singleton] at mem
      exact .inr (by rw [mem])
    · simp at found
  | fire reference =>
    simp only [Config.footprint] at found
    split at found
    · simp only [Option.some.injEq] at found
      subst found
      simp [Footprint.fire] at mem
    · simp at found

/-- A keyed step changes the records of its own process and of a child it spawns only. -/
private theorem footprint_changes_others {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key} {footprint : Footprint}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint) :
    ∀ entry ∈ footprint.effect.records, some entry.1 = key.watched ∨ entry.1 ∉ tasks.map Prod.fst := by
  intro entry mem
  cases key with
  | own processId index =>
    simp only [Config.footprint] at found
    split at found
    · rename_i task lookup
      split at found
      · simp only [Option.some.injEq] at found
        subst found
        rcases Task.footprint_changes entry mem with same | child
        · exact .inl (by simp [Key.watched, same])
        · refine .inr fun present => ?_
          simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right] at present
          obtain ⟨task', present⟩ := present
          have := wellformed.2.1 (processId, task) (mem_of_lookup lookup) (entry.1, task') present _ []
            (by rw [child])
          simp only at this
          omega
      · simp at found
    · simp at found
  | deliver source target =>
    simp only [Config.footprint] at found
    split at found
    · rename_i envelope _ oldestFound
      simp only [Option.some.injEq] at found
      subst found
      obtain ⟨-, rfl⟩ := between_of_find oldestFound
      exact .inl (by simp [Key.watched, Footprint.delivery_changes entry mem])
    · simp at found
  | bounce source target =>
    simp only [Config.footprint] at found
    split at found
    · simp only [Option.some.injEq] at found
      subst found
      simp [Footprint.bounce] at mem
    · simp at found
  | fire reference =>
    simp only [Config.footprint] at found
    split at found
    · simp only [Option.some.injEq] at found
      subst found
      simp [Footprint.fire] at mem
    · simp at found

/-- A view that ignores what local steps change. -/
private def Public (view : ProcessState → ProcessState) : Prop :=
  ∀ process pdict refCounter mailbox, view { process with pdict, refCounter, mailbox } = view process

/-- A signal the receiver survives observes what local steps keep, and changes
the receiver's record as it does when it arrives. -/
private theorem delivery_survived {state : State} {envelope : Envelope} {rest : List Envelope}
    (survives : ({ state with inTransit := rest }.receive envelope).2 = none) :
    (∀ entry ∈ (Footprint.delivery state envelope).observes.records, Public entry.2) ∧
    (Footprint.delivery state envelope).effect =
      ({ inTransit := some (arrive envelope.source envelope.target) } : Effect).andThen
        (.change envelope.target (·.receive envelope.source envelope.signal)) := by
  obtain ⟨source, target, signal⟩ := envelope
  cases signal with
  | exit reason linked =>
    simp only [State.receive, State.exitSignal_snd] at survives
    have survives' : (state.exitSignal target source reason linked).2 = none := by
      rw [State.exitSignal_snd]; exact survives
    simp only [Footprint.delivery, survives']
    refine ⟨fun entry mem => ?_, by first | trivial | rfl⟩
    simp only [Observes.and, List.cons_append, List.nil_append, Observes.record, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> intro process pdict refCounter mailbox <;> rfl
  | _ =>
    refine ⟨fun entry mem => ?_, rfl⟩
    simp only [Footprint.delivery, List.mem_singleton] at mem
    subst mem
    intro process pdict refCounter mailbox
    rfl

/-- Changing one record commutes with an effect that changes it as a function of it alone. -/
private theorem Effect.apply_modify {effect : Effect} {state : State} {processId : PID}
    {change : ProcessState → ProcessState}
    (commutes : effect.record processId ((state.processes processId).map change) =
      (effect.record processId (state.processes processId)).map change) :
    effect.apply (state.modify processId change) = (effect.apply state).modify processId change := by
  refine State.ext' (funext fun candidate => ?_) ?_ ?_ ?_
  · simp only [Effect.processes_apply, State.processes_modify]
    split
    · subst_vars; exact commutes
    · rfl
  · simp [Effect.apply]
  · simp [Effect.apply]
  · simp [Effect.apply]


/-- A step has a footprint. -/
private theorem footprint_of_mem {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key} {event : Event}
    {next : Config α} (wellformed : Wellformed (.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps) :
    ∃ footprint, (Config.running state tasks finished exhausted).footprint key = some footprint := by
  rw [mem_steps] at mem
  rcases mem with ⟨before, processId, task, after, transition, split, keyed, -, -⟩ |
    ⟨envelope, rest, delivered, dead, rfl, -, -⟩ | ⟨timer, firing, rfl, -, -⟩
  · have lookup : tasks.lookup processId = some task :=
      lookup_of_mem wellformed.1 (by rw [eq_of_mem_splits split]; simp)
    rw [mem_keyed] at keyed
    rcases keyed with ⟨index, rfl, own⟩ | ⟨envelope, rest, delivered, target, rfl, -⟩
    · have bound : index < (task.own state processId).length := (List.getElem?_eq_some_iff.mp own).1
      exact ⟨task.footprint state processId, by simp [Config.footprint, lookup, bound]⟩
    · have oldestFound := oldest_iff.mp (mem_deliverable_iff.mp delivered).1
      rw [target] at oldestFound
      exact ⟨Footprint.delivery state envelope, by simp [Config.footprint, lookup, oldestFound]⟩
  · have oldestFound := oldest_iff.mp (mem_deliverable_iff.mp delivered).1
    have missing : tasks.lookup envelope.target = none := by simpa using dead
    exact ⟨Footprint.bounce envelope, by simp [Config.footprint, missing, oldestFound]⟩
  · have timerFound : state.timers.find? (·.reference == timer.reference) = some timer := by
      have := mem_firing_iff.mp firing
      simp only [firstTimer] at this
      cases equal : state.timers.find? (·.reference == timer.reference) <;> simp_all
    exact ⟨Footprint.fire timer, by simp [Config.footprint, timerFound]⟩

private theorem Effect.record_id {effect : Effect} {processId : PID}
    (outside : ∀ entry ∈ effect.records, entry.1 ≠ processId) : effect.record processId = id := by
  simp only [Effect.record]
  cases found : effect.records.find? (·.1 == processId) with
  | none => rfl
  | some entry =>
    have := List.find?_some found
    exact absurd (by simpa using this) (outside entry (List.mem_of_find?_eq_some found))

/-- How a step other than a process's own touches the process: not at all,
besides whether it is live, or it is a signal the process takes. -/
private theorem footprint_at {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key} {footprint : Footprint}
    {processId : PID} (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint)
    (present : (tasks.lookup processId).isSome) (other : ∀ index, key ≠ .own processId index) :
    (footprint.effect.record processId = id ∧
      ∀ entry ∈ footprint.observes.records, entry.1 = processId → entry.2 = ProcessState.live) ∨
    ∃ source envelope, key = .deliver source processId ∧ envelope.source = source ∧
      envelope.target = processId ∧
      (envelope, arrive source processId state.inTransit) ∈ deliverable state.inTransit ∧
      footprint = Footprint.delivery state envelope := by
  have notWatched : key.watched = some processId →
      ∃ source envelope, key = .deliver source processId ∧ envelope.source = source ∧
        envelope.target = processId ∧
        (envelope, arrive source processId state.inTransit) ∈ deliverable state.inTransit ∧
        footprint = Footprint.delivery state envelope := by
    intro watched
    cases key with
    | own processId' index =>
      simp only [Key.watched, Option.some.injEq] at watched
      subst watched
      exact absurd rfl (other index)
    | deliver source target =>
      simp only [Key.watched, Option.some.injEq] at watched
      subst watched
      simp only [Config.footprint] at found
      split at found
      · rename_i envelope _ oldestFound
        simp only [Option.some.injEq] at found
        obtain ⟨equalSource, equalTarget⟩ := between_of_find oldestFound
        refine ⟨source, envelope, rfl, equalSource, equalTarget, ?_, found.symm⟩
        rw [mem_deliverable_iff, ← equalSource, ← equalTarget]
        exact ⟨oldest_iff.mpr (equalSource ▸ equalTarget ▸ oldestFound), rfl⟩
      · simp at found
    | bounce source target =>
      simp only [Key.watched, Option.some.injEq] at watched
      subst watched
      simp [missing_of_footprint found] at present
    | fire => cases watched
  by_cases watched : key.watched = some processId
  · exact .inr (notWatched watched)
  · refine .inl ⟨Effect.record_id fun entry mem same => ?_, fun entry mem same => ?_⟩
    · rcases footprint_changes_others wellformed found entry mem with same' | fresh
      · exact watched (by rw [← same', same])
      · exact fresh (same ▸ mem_of_isSome present)
    · rcases footprint_observes_others found entry mem with same' | live
      · exact absurd (by rw [← same', same]) watched
      · exact live

/-- A local step and another step the process survives reach the same configuration in
either order. -/
private theorem local_square {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID} {task : Task α}
    {key : Key} {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : tasks.lookup processId = some task) (isLocal : task.local state processId = true)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key, event', next') ∈ (Config.running state tasks finished exhausted).steps)
    (other : ∀ index, key ≠ .own processId index)
    (survives : ∀ source envelope, key = .deliver source processId →
      (envelope, arrive source processId state.inTransit) ∈ deliverable state.inTransit →
      envelope.source = source → envelope.target = processId →
      ({ state with inTransit := arrive source processId state.inTransit }.receive envelope).2 = none) :
    ∃ last, (key, event', last) ∈ next.steps ∧ (.own processId 0, event, last) ∈ next'.steps := by
  have present : (tasks.lookup processId).isSome := by simp [found]
  have live := live_of_lookup wellformed present
  obtain ⟨footprint, foundOwn⟩ := footprint_of_mem wellformed mem
  have ownFootprint : footprint = task.footprint state processId := by
    simp only [Config.footprint, found] at foundOwn
    split at foundOwn
    · simp only [Option.some.injEq] at foundOwn; exact foundOwn.symm
    · simp at foundOwn
  subst ownFootprint
  obtain ⟨footprint', found'⟩ := footprint_of_mem wellformed mem'
  obtain ⟨move, moved⟩ := moves wellformed mem foundOwn
  obtain ⟨move', moved'⟩ := moves wellformed mem' found'
  obtain ⟨view, change, ready, observes, apply, records, isReady, shape, -⟩ := Task.local_shape isLocal
  obtain ⟨process, record⟩ := Option.isSome_iff_exists.mp live
  have processEq : state.process processId = process := by simp [State.process, record]
  rw [processEq] at isReady
  -- How the other step touches the process.
  have touches := footprint_at wellformed found' present other
  have agree : footprint'.observes.Agree state ((task.footprint state processId).effect.apply state) := by
    rw [apply]
    refine ⟨fun entry mem => ?_, fun _ _ => by simp, fun _ _ => by simp, by simp⟩
    rw [State.processes_modify]
    split
    · rename_i same
      rw [same, record]
      simp only [Option.map_some, Option.some.injEq]
      obtain ⟨pdict, refCounter, mailbox, changed⟩ := shape.fields process
      rw [changed]
      rcases touches with ⟨-, views⟩ | ⟨source, envelope, rfl, equalSource, equalTarget, delivered, rfl⟩
      · rw [views entry mem same]; rfl
      · obtain ⟨views, -⟩ := delivery_survived (survives source envelope rfl delivered equalSource
          equalTarget)
        exact views entry mem process pdict refCounter mailbox
    · rfl
  have agree' : (task.footprint state processId).observes.Agree state (footprint'.effect.apply state) := by
    rw [observes]
    refine ⟨fun entry mem => ?_, fun _ mem => by simp [Observes.record] at mem,
      fun _ mem => by simp [Observes.record] at mem, by simp⟩
    simp only [Observes.record, List.mem_singleton] at mem
    subst mem
    simp only [Effect.processes_apply, record]
    rcases touches with ⟨unchanged, -⟩ | ⟨source, envelope, rfl, equalSource, equalTarget, delivered, rfl⟩
    · rw [unchanged]; rfl
    · obtain ⟨-, effect⟩ := delivery_survived (survives source envelope rfl delivered equalSource
        equalTarget)
      rw [effect, Effect.record_andThen]
      simp only [Effect.record, Effect.change, List.find?_nil, List.find?_cons, equalTarget,
        beq_self_eq_true, Function.comp_apply, id, Option.map_some]
      exact congrArg some (shape.receive process _ _ isReady).2.1
  have commutes : (task.footprint state processId).effect.apply (footprint'.effect.apply state) =
      footprint'.effect.apply ((task.footprint state processId).effect.apply state) := by
    rw [apply, apply]
    refine (Effect.apply_modify ?_).symm
    rw [record]
    rcases touches with ⟨unchanged, -⟩ | ⟨source, envelope, rfl, equalSource, equalTarget, delivered, rfl⟩
    · rw [unchanged]; rfl
    · obtain ⟨-, effect⟩ := delivery_survived (survives source envelope rfl delivered equalSource
        equalTarget)
      rw [effect, Effect.record_andThen]
      simp only [Effect.record, Effect.change, List.find?_nil, List.find?_cons, equalTarget,
        beq_self_eq_true, Function.comp_apply, id, Option.map_some, Option.some.injEq]
      exact (shape.receive process _ _ isReady).2.2.symm
  have pair : Pair state tasks finished exhausted (.own processId 0) key
      (task.footprint state processId) footprint' move move' :=
    ⟨wellformed, foundOwn, found', ⟨_, _, moved⟩, ⟨_, _, moved'⟩, fun same => other 0 same.symm,
      agree, agree'⟩
  exact pair.square moved moved' commutes mem mem'

/-- The step of a process with a local step, as a transition. -/
private theorem local_step {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID} {task : Task α}
    {event : Event} {next : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : tasks.lookup processId = some task)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps) :
    ∃ before after transition, tasks = before ++ (processId, task) :: after ∧
      transition ∈ task.own state processId ∧ event = transition.event ∧
      next = transition.apply before after finished exhausted := by
  rw [mem_steps] at mem
  rcases mem with ⟨before, processId', task', after, transition, split, keyed, rfl, rfl⟩ |
    ⟨_, _, _, _, same, _, _⟩ | ⟨_, _, same, _, _⟩
  · rw [mem_keyed] at keyed
    rcases keyed with ⟨index, same, own⟩ | ⟨_, _, _, _, same, _⟩
    · simp only [Key.own.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have equal := eq_of_mem_splits split
      have := lookup_of_mem wellformed.1 (by rw [equal]; simp : (processId, task') ∈ tasks)
      rw [found, Option.some.injEq] at this
      subst this
      exact ⟨before, after, transition, equal, List.mem_of_getElem? own, rfl, rfl⟩
    · cases same
  · cases same
  · cases same

/-- A signal ending a process absorbs its local step. -/
private theorem local_absorbs {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId source : PID}
    {task : Task α} {event event' : Event} {next next' : Config α} {envelope : Envelope}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : tasks.lookup processId = some task) (isLocal : task.local state processId = true)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (.deliver source processId, event', next') ∈
      (Config.running state tasks finished exhausted).steps)
    (delivered : (envelope, arrive source processId state.inTransit) ∈ deliverable state.inTransit)
    (equalSource : envelope.source = source) (equalTarget : envelope.target = processId)
    (ends : ({ state with inTransit := arrive source processId state.inTransit }.receive envelope).2.isSome) :
    (.deliver source processId, event', next') ∈ next.steps := by
  have live := live_of_lookup (processId := processId) wellformed (by simp [found])
  obtain ⟨before, after, transition, equal, own, rfl, rfl⟩ := local_step wellformed found mem
  obtain ⟨transition₀, computation, owned, tasksEq, finishedEq, exhaustedEq⟩ := Task.local_own isLocal
  rw [owned, List.mem_singleton] at own
  subst own
  obtain ⟨view, change, ready, -, apply, -, -, shape, -⟩ := Task.local_shape isLocal
  have stateEq : transition.state = state.modify processId change := by
    rw [own_state live (by rw [owned]; exact List.mem_singleton_self _), apply]
  -- The delivery from the original configuration.
  rw [mem_steps] at mem'
  rcases mem' with ⟨before', processId', task', after', transition', split', keyed', rfl, rfl⟩ |
    ⟨_, _, _, _, same, _, _⟩ | ⟨_, _, same, _, _⟩
  rotate_left
  · cases same
  · cases same
  rw [mem_keyed] at keyed'
  rcases keyed' with ⟨_, same, _⟩ | ⟨envelope', rest', delivered', target', same, rfl⟩
  · cases same
  simp only [Key.deliver.injEq] at same
  obtain ⟨source', rfl⟩ := same
  obtain ⟨rfl, rfl⟩ := deliverable_unique delivered delivered' (equalSource.trans source')
    (equalTarget.trans target'.symm)
  obtain ⟨rfl, rfl, rfl⟩ := split_unique wellformed.1 (by rw [equal]; exact mem_splits) split'
  -- The same delivery after the local step ends the process in the same way.
  obtain ⟨envelopeSource, envelopeTarget, signal⟩ := envelope
  simp only at equalSource equalTarget
  subst equalSource equalTarget
  have absorbed := local_absorbed (state := { state with
      inTransit := arrive envelopeSource envelopeTarget state.inTransit })
    shape.fields shape.links ends
  have modified : ({ state.modify envelopeTarget change with
      inTransit := arrive envelopeSource envelopeTarget (state.modify envelopeTarget change).inTransit } : State) =
      ({ state with inTransit := arrive envelopeSource envelopeTarget state.inTransit } : State).modify
        envelopeTarget change := by
    unfold State.modify; split <;> rename_i found' <;> simp [found', State.update]
  simp only [Transition.apply, stateEq, tasksEq, finishedEq, exhaustedEq, Bool.or_false]
  refine mem_steps.mpr (.inl ⟨before, envelopeTarget, ⟨computation, task.finish⟩, after, _,
    by simpa using mem_splits, mem_keyed.mpr (.inr ⟨⟨envelopeSource, envelopeTarget, signal⟩,
      arrive envelopeSource envelopeTarget (state.modify envelopeTarget change).inTransit,
      by simpa using delivered, rfl, rfl, rfl⟩), ?_, ?_⟩)
  · rw [delivery_shape.1, delivery_shape.1]
  obtain ⟨exits, terminated⟩ := absorbed
  obtain ⟨reason, exiting⟩ := Option.isSome_iff_exists.mp ends
  simp only [Task.delivery, modified, exits, exiting, Option.getD_some] at terminated ⊢
  simp only [Task.ended, Transition.apply, terminated]
  rfl


/-- After another step the process survives, its local step stays local. -/
private theorem local_persists {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID} {task : Task α}
    {key : Key} {event : Event} {next : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : tasks.lookup processId = some task) (isLocal : task.local state processId = true)
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (other : ∀ index, key ≠ .own processId index)
    (survives : ∀ source envelope, key = .deliver source processId →
      (envelope, arrive source processId state.inTransit) ∈ deliverable state.inTransit →
      envelope.source = source → envelope.target = processId →
      ({ state with inTransit := arrive source processId state.inTransit }.receive envelope).2 = none) :
    ∃ state' tasks' finished' exhausted', next = .running state' tasks' finished' exhausted' ∧
      tasks'.lookup processId = some task ∧ task.local state' processId = true := by
  have present : (tasks.lookup processId).isSome := by simp [found]
  have live := live_of_lookup wellformed present
  obtain ⟨footprint, found'⟩ := footprint_of_mem wellformed mem
  obtain ⟨move, moved⟩ := moves wellformed mem found'
  obtain ⟨view, change, ready, -, -, -, isReady, shape, stays⟩ := Task.local_shape isLocal
  obtain ⟨process, record⟩ := Option.isSome_iff_exists.mp live
  have processEq : state.process processId = process := by simp [State.process, record]
  rw [processEq] at isReady
  have touches := footprint_at wellformed found' present other
  -- The process's record after the step, and what its local step needs of it.
  have after : ∃ process', footprint.effect.record processId (state.processes processId) = some process' ∧
      process'.pdict = process.pdict ∧ process'.refCounter = process.refCounter ∧ ready process' := by
    simp only [record]
    rcases touches with ⟨unchanged, -⟩ | ⟨source, envelope, rfl, equalSource, equalTarget, delivered, rfl⟩
    · exact ⟨process, by rw [unchanged]; rfl, rfl, rfl, isReady⟩
    · obtain ⟨-, effect⟩ := delivery_survived (survives source envelope rfl delivered equalSource
        equalTarget)
      rw [effect, Effect.record_andThen]
      simp only [Effect.record, Effect.change, List.find?_nil, List.find?_cons, equalTarget,
        beq_self_eq_true, Function.comp_apply, id, Option.map_some]
      obtain ⟨split, pdict, refCounter⟩ := ProcessState.receive_split (process := process)
        (source := envelope.source) (signal := envelope.signal)
      refine ⟨_, rfl, ?_, ?_, (shape.receive process _ _ isReady).1⟩ <;> rw [split]
      · exact pdict
      · exact refCounter
  obtain ⟨process', record', pdict, refCounter, ready'⟩ := after
  have record'' := record'
  rw [record] at record''
  refine ⟨footprint.effect.apply state, move.tasks tasks, move.finished.orElse fun _ => finished,
    exhausted || move.exhausted, by rw [moved.next]; simp only [Move.config, moved.effect], ?_, ?_⟩
  · cases owner : move.owner with
    | none => simp [Move.tasks, owner, found]
    | some owner' =>
      have process := moved.owner owner' owner
      by_cases same : owner' = processId
      · exfalso
        subst same
        have empty : move.replacement = [] := by
          cases replaced : move.replacement with
          | nil => rfl
          | cons head rest =>
            obtain ⟨_, index, equal⟩ := moved.replacing (by simp [replaced])
            subst equal
            simp only [Key.process, Option.some.injEq] at process
            exact absurd process.symm (fun same => other index (by rw [same]))
        have ended := moved.ends owner' owner (by simp [empty])
        rw [record'] at ended
        cases ended
      · simp only [Move.tasks, owner]
        rw [lookup_replace (Ne.symm same) fun added => ?_]
        · exact found
        · rcases List.mem_map.mp added with ⟨entry, mem, equal⟩
          rcases moved.replaced entry mem with same' | fresh
          · rw [process, equal] at same'; cases same'; exact same rfl
          · exact fresh.1 (equal ▸ mem_of_isSome present)
  · refine stays _ ?_ ?_
    · simp [State.view, State.process, Effect.processes_apply, record'', record, pdict, refCounter]
    · simpa [State.process, Effect.processes_apply, record'', record] using ready'

/-- Every run of a configuration with a local step can take it first: it
commutes with every step its process survives, and a signal ending the
process absorbs it. -/
private theorem local_first {outcome : Outcome α} :
    ∀ {first last : Config α} {events : List Event}, Run first events last →
    ∀ {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
      {exhausted : Bool} {processId : PID} {task : Task α} {event : Event} {next : Config α},
      first = .running state tasks finished exhausted → Wellformed first →
      tasks.lookup processId = some task → task.local state processId = true →
      (.own processId 0, event, next) ∈ first.steps → Terminal last outcome →
      ∃ events', Run next events' last := by
  intro first last events run
  induction run with
  | refl =>
    intro state tasks finished exhausted processId task event next _ _ _ _ mem terminal
    have := Step.of_mem_steps mem
    simp [Step, terminal.successors_eq_nil] at this
  | step step rest ih =>
    rename_i first event' middle events last
    intro state tasks finished exhausted processId task event next equal wellformed found isLocal
      mem terminal
    subst equal
    obtain ⟨key, mem'⟩ := Step.keyed step
    by_cases own : ∃ index, key = .own processId index
    · obtain ⟨index, rfl⟩ := own
      obtain ⟨footprint, found'⟩ := footprint_of_mem wellformed mem'
      obtain rfl := index_of_footprint found'
      obtain ⟨rfl, rfl⟩ := steps_unique wellformed mem' mem
      exact ⟨events, rest⟩
    have other : ∀ index, key ≠ .own processId index := fun index same => own ⟨index, same⟩
    by_cases kills : ∃ source envelope, key = .deliver source processId ∧
        (envelope, arrive source processId state.inTransit) ∈ deliverable state.inTransit ∧
        envelope.source = source ∧ envelope.target = processId ∧
        ({ state with inTransit := arrive source processId state.inTransit }.receive envelope).2.isSome
    · obtain ⟨source, envelope, rfl, delivered, equalSource, equalTarget, ends⟩ := kills
      exact ⟨_, .step (Step.of_mem_steps (local_absorbs wellformed found isLocal mem mem' delivered
        equalSource equalTarget ends)) rest⟩
    have survives : ∀ source envelope, key = .deliver source processId →
        (envelope, arrive source processId state.inTransit) ∈ deliverable state.inTransit →
        envelope.source = source → envelope.target = processId →
        ({ state with inTransit := arrive source processId state.inTransit }.receive envelope).2 = none := by
      intro source envelope same delivered equalSource equalTarget
      cases exits : ({ state with inTransit := arrive source processId state.inTransit }.receive
        envelope).2 with
      | none => rfl
      | some _ => exact absurd ⟨source, envelope, same, delivered, equalSource, equalTarget, by simp [exits]⟩ kills
    obtain ⟨last', forth, back⟩ := local_square wellformed found isLocal mem mem' other survives
    obtain ⟨state', tasks', finished', exhausted', rfl, found', isLocal'⟩ :=
      local_persists wellformed found isLocal mem' other survives
    obtain ⟨events', run'⟩ := ih rfl (Step.wellformed step wellformed) found' isLocal' back terminal
    exact ⟨_, .step (Step.of_mem_steps forth) run'⟩

/-! ### Exploration

For a closed program, every run can be enumerated: `Config.steps` lists each
step, and `check` follows them. Of runs that differ only in the order of steps
that commute (`Config.independent`), it follows one: a step is followed with
the steps that commute with it and were followed before it asleep, as runs
taking those first are covered elsewhere. Proving `check` by evaluation
establishes a property for every schedule (see `Lynx.concurrent_of_check`). -/

/-- Follow every step not asleep. Each step is followed with the steps asleep
and the steps followed before it that commute with it asleep. -/
@[expose] def explore (visit : List Key → Config α → Bool) (independent : Key → Key → Bool)
    (sleep : List Key) : List Key → List (Key × Event × Config α) → Bool
  | _, [] => true
  | done, (key, _, next) :: rest =>
      if sleep.contains key then explore visit independent sleep done rest
      else visit ((sleep ++ done).filter (independent · key)) next &&
        explore visit independent sleep (done ++ [key]) rest

/-- Whether every run from the configuration ends in an accepted outcome,
following at most `depth` steps along each run, where runs taking a step
asleep first are covered elsewhere. A step every run can take first
(`Config.forced`) is followed alone. -/
@[expose] def checkFrom (accept : Outcome α → Bool) : Nat → List Key → Config α → Bool
  | 0, _, _ => false
  | depth + 1, sleep, config =>
      match config.steps with
      | [] =>
          match config.successors with
          | [] => accept config.outcome
          | successors => successors.all fun (_, next) => checkFrom accept depth [] next
      | steps =>
          match config.forced.bind fun key => steps.find? (·.1 == key) with
          | some (key, _, next) => checkFrom accept depth (sleep.filter (config.independent · key)) next
          | none => explore (checkFrom accept depth) config.independent sleep [] steps

/-- Whether every run from the configuration ends in an accepted outcome,
following at most `depth` steps along each run. -/
@[expose] def check (accept : Outcome α → Bool) (depth : Nat) (config : Config α) : Bool :=
  checkFrom accept depth [] config

/-- How a run that `check` rejects fails. -/
inductive Failure (α : Type) where
  /-- The run ends in an outcome that is not accepted. -/
  | rejected : Outcome α → Failure α
  /-- The run takes more steps than the depth allows. -/
  | unfinished : Failure α

/-- The first run that `explore` finds. -/
@[expose] def exploreFind (visit : List Key → Config α → Option (List Event × β))
    (independent : Key → Key → Bool) (sleep : List Key) :
    List Key → List (Key × Event × Config α) → Option (List Event × β)
  | _, [] => none
  | done, (key, event, next) :: rest =>
      if sleep.contains key then exploreFind visit independent sleep done rest
      else match visit ((sleep ++ done).filter (independent · key)) next with
        | some (events, failure) => some (event :: events, failure)
        | none => exploreFind visit independent sleep (done ++ [key]) rest

/-- The first run that `checkFrom` rejects. -/
@[expose] def counterexampleFrom (accept : Outcome α → Bool) :
    Nat → List Key → Config α → Option (List Event × Failure α)
  | 0, _, _ => some ([], .unfinished)
  | depth + 1, sleep, config =>
      match config.steps with
      | [] =>
          match config.successors with
          | [] => if accept config.outcome then none else some ([], .rejected config.outcome)
          | successors => successors.findSome? fun (event, next) =>
              (counterexampleFrom accept depth [] next).map fun (events, failure) =>
                (event :: events, failure)
      | steps =>
          match config.forced.bind fun key => steps.find? (·.1 == key) with
          | some (key, event, next) =>
              (counterexampleFrom accept depth (sleep.filter (config.independent · key)) next).map
                fun (events, failure) => (event :: events, failure)
          | none => exploreFind (counterexampleFrom accept depth) config.independent sleep [] steps

/-- The first run that `check` rejects, as the events of its steps and how it
fails. Evaluating it is a fast way to find why a check fails. -/
@[expose] def counterexample (accept : Outcome α → Bool) (depth : Nat) (config : Config α) :
    Option (List Event × Failure α) :=
  counterexampleFrom accept depth [] config

/-- A configuration reaches another. -/
private def Reaches (first last : Config α) : Prop := ∃ events, Run first events last

private theorem Reaches.step {first next last : Config α} {event : Event}
    (step : Step first event next) (reaches : Reaches next last) : Reaches first last :=
  let ⟨events, run⟩ := reaches; ⟨event :: events, .step step run⟩

/-- `explore` follows a step from which the run continues, with a sleep set
that excludes the run: steps asleep before it cannot start the run, and of
the steps it follows first, none starts it. -/
private theorem explore_sound {visit : List Key → Config α → Bool}
    {independent : Key → Key → Bool} {sleep : List Key} {steps : List (Key × Event × Config α)}
    {last : Config α} {goal : Prop}
    (visited : ∀ key event next, (key, event, next) ∈ steps → ∀ sleep', visit sleep' next = true →
      Reaches next last →
      (∀ key' ∈ sleep', ∀ event' next', (key', event', next') ∈ next.steps → ¬Reaches next' last) →
      goal)
    (diamond : ∀ key event next, (key, event, next) ∈ steps → ∀ key', independent key' key = true →
      ∀ event' next', (key', event', next') ∈ next.steps →
        ∃ next'', (key', event', next'') ∈ steps ∧ Step next'' event next')
    (unique : ∀ key event event' next next', (key, event, next) ∈ steps →
      (key, event', next') ∈ steps → next = next')
    (asleep : ∀ key ∈ sleep, ∀ event next, (key, event, next) ∈ steps → ¬Reaches next last)
    (first : ∃ key event next, (key, event, next) ∈ steps ∧ Reaches next last)
    (explored : explore visit independent sleep [] steps = true) : goal := by
  suffices ∀ (earlier rest : List (Key × Event × Config α)) (done : List Key), steps = earlier ++ rest →
      (∀ key ∈ done, ∃ event next, (key, event, next) ∈ earlier) →
      (∀ key event next, (key, event, next) ∈ earlier → key ∉ sleep → ¬Reaches next last) →
      explore visit independent sleep done rest = true → goal from
    this [] steps [] rfl (by simp) (by simp) explored
  intro earlier rest
  induction rest generalizing earlier with
  | nil =>
    intro done equal _ unreached _
    obtain ⟨key, event, next, mem, reaches⟩ := first
    simp only [List.append_nil] at equal
    subst equal
    by_cases slept : key ∈ sleep
    · exact absurd reaches (asleep key slept event next mem)
    · exact absurd reaches (unreached key event next mem slept)
  | cons step rest ih =>
    obtain ⟨key, event, next⟩ := step
    intro done equal found unreached explored
    have mem : (key, event, next) ∈ steps := by rw [equal]; simp
    have extend : steps = (earlier ++ [(key, event, next)]) ++ rest := by rw [equal]; simp
    simp only [explore] at explored
    split at explored
    · rename_i slept
      refine ih _ done extend (fun key mem => ?_) (fun key' event' next' mem' out => ?_) explored
      · obtain ⟨event, next, mem⟩ := found key mem; exact ⟨event, next, by simp [mem]⟩
      · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at mem'
        rcases mem' with mem' | ⟨rfl, rfl, rfl⟩
        · exact unreached _ _ _ mem' out
        · exact absurd (List.elem_iff.mp slept) out
    · rename_i awake
      simp only [Bool.and_eq_true] at explored
      by_cases reaches : Reaches next last
      · refine visited key event next mem _ explored.1 reaches fun key' slept event' next' mem' => ?_
        simp only [List.mem_filter, List.mem_append] at slept
        obtain ⟨slept | finished, independent'⟩ := slept
        · intro reaches'
          obtain ⟨next'', mem'', step⟩ := diamond key event next mem key' independent' event' next' mem'
          exact asleep key' slept event' next'' mem'' (Reaches.step step reaches')
        · intro reaches'
          obtain ⟨next'', mem'', step⟩ := diamond key event next mem key' independent' event' next' mem'
          obtain ⟨event₀, next₀, mem₀⟩ := found key' finished
          have same := unique key' event₀ event' next₀ next'' (by rw [equal]; simp [mem₀]) mem''
          subst same
          have awake' : key' ∉ sleep := fun slept => by
            obtain ⟨event₁, next₁, mem₁⟩ := found key' finished
            exact asleep key' slept event₁ next₁ (by rw [equal]; simp [mem₁])
              (unique key' event₁ event₀ next₁ next₀ (by rw [equal]; simp [mem₁])
                (by rw [equal]; simp [mem₀]) ▸ Reaches.step step reaches')
          exact unreached key' event₀ next₀ mem₀ awake' (Reaches.step step reaches')
      · refine ih _ _ extend (fun key' mem' => ?_) (fun key' event' next' mem' out => ?_)
          explored.2
        · simp only [List.mem_append, List.mem_singleton] at mem'
          rcases mem' with mem' | rfl
          · obtain ⟨event, next, mem⟩ := found key' mem'; exact ⟨event, next, by simp [mem]⟩
          · exact ⟨event, next, by simp⟩
        · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at mem'
          rcases mem' with mem' | ⟨rfl, rfl, rfl⟩
          · exact unreached _ _ _ mem' out
          · exact reaches

private theorem steps_nil_of_successors {config : Config α} (none : config.successors = []) :
    config.steps = [] := by
  cases config with
  | start => rfl
  | running => rw [← List.map_eq_nil_iff, Config.steps_running, none]

/-- The step `check` follows alone is a local step of a process. -/
private theorem forced_facts {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key} {event : Event}
    {next : Config α} (wellformed : Wellformed (.running state tasks finished exhausted))
    (found : ((Config.running state tasks finished exhausted).forced.bind fun key =>
      (Config.running state tasks finished exhausted).steps.find? (·.1 == key)) = some (key, event, next)) :
    ∃ processId task, tasks.lookup processId = some task ∧ task.local state processId = true ∧
      key = .own processId 0 ∧ (key, event, next) ∈ (Config.running state tasks finished exhausted).steps := by
  simp only [Option.bind_eq_some_iff] at found
  obtain ⟨forced, isForced, step⟩ := found
  have same : key = forced := by simpa using List.find?_some step
  subst same
  simp only [Config.forced, Option.map_eq_some_iff] at isForced
  obtain ⟨⟨processId, task⟩, local', rfl⟩ := isForced
  have isLocal : task.local state processId = true := by simpa using List.find?_some local'
  exact ⟨processId, task, lookup_of_mem wellformed.1 (List.mem_of_find?_eq_some local'), isLocal, rfl,
    List.mem_of_find?_eq_some step⟩

private theorem check_wellformed {accept : Outcome α → Bool} :
    ∀ {depth : Nat} {sleep : List Key} {first last : Config α} {events : List Event}
      {outcome : Outcome α},
      Wellformed first → checkFrom accept depth sleep first = true → Run first events last →
      Terminal last outcome →
      (∀ key ∈ sleep, ∀ event next, (key, event, next) ∈ first.steps → ¬Reaches next last) →
      accept outcome = true := by
  intro depth
  induction depth with
  | zero => intro _ _ _ _ _ _ checked; simp [checkFrom] at checked
  | succ depth ih =>
    intro sleep first last events outcome wellformed checked run terminal asleep
    unfold checkFrom at checked
    cases found : first.steps with
    | nil =>
      -- No keyed steps: follow every step.
      simp only [found] at checked
      cases run with
      | refl =>
        simp only [terminal.successors_eq_nil, terminal.outcome_eq] at checked
        exact checked
      | step step rest =>
        split at checked
        · rename_i none
          simp [Step, none] at step
        · simp only [List.all_eq_true] at checked
          exact ih (Step.wellformed step wellformed) (checked _ step) rest terminal (by simp)
    | cons entry entries =>
      simp only [found] at checked
      rw [← found] at checked
      cases run with
      | refl =>
        have := steps_nil_of_successors terminal.successors_eq_nil
        simp [found] at this
      | step step rest =>
        cases first with
        | start => simp [Config.steps] at found
        | running state tasks finished exhausted =>
          split at checked
          · -- A step every run can take first.
            rename_i key event' next forced
            obtain ⟨processId, task, lookup, isLocal, rfl, mem⟩ := forced_facts wellformed forced
            obtain ⟨events', run'⟩ := local_first (.step step rest) rfl wellformed lookup isLocal mem
              terminal
            refine ih (Step.wellformed (Step.of_mem_steps mem) wellformed) checked run' terminal ?_
            intro key' slept event'' next'' mem' reaches
            simp only [List.mem_filter] at slept
            obtain ⟨next₀, mem₀, step₀⟩ := diamond wellformed mem slept.2 mem'
            exact asleep key' slept.1 event'' next₀ mem₀ (Reaches.step step₀ reaches)
          · obtain ⟨key, mem⟩ := Step.keyed step
            exact explore_sound (goal := accept outcome = true)
              (fun key event next mem sleep' visited reaches asleep' =>
                let ⟨_, run'⟩ := reaches
                ih (Step.wellformed (Step.of_mem_steps mem) wellformed) visited run' terminal asleep')
              (fun key event next mem key' independent event' next' mem' =>
                diamond wellformed mem independent mem')
              (fun key event event' next next' mem mem' => (steps_unique wellformed mem mem').2)
              asleep ⟨key, _, _, mem, _, rest⟩ checked

/-- Every run of a computation that `check` accepts ends in an accepted outcome. -/
theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {env : Environment}
    {computation : Result α} {elapsed : PID → Nat → Nat} {last : Config α} {events : List Event}
    {outcome : Outcome α} (checked : check accept depth (.start env computation elapsed) = true)
    (run : Run (.start env computation elapsed) events last) (terminal : Terminal last outcome) :
    accept outcome = true :=
  check_wellformed (show Wellformed (Config.start env computation elapsed) from trivial) checked run
    terminal (by simp)

end Lynx.Concurrent
