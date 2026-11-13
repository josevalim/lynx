module

public import Lynx.Concurrent
public import Lynx.Concurrent.Termination

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
process is live, and at most one reports the run's result. -/
private def Wellformed : Config α → Prop
  | .start .. => True
  | .running state tasks _ _ =>
      tasks.Pairwise (fun first second => first.1 ≠ second.1) ∧
      (∀ parent ∈ tasks, ∀ descendant ∈ tasks, ∀ index rest,
        descendant.1 = parent.1 ++ index :: rest → index ≤ (state.process parent.1).children) ∧
      (∀ entry ∈ tasks, (state.processes entry.1).isSome) ∧
      tasks.Pairwise (fun first second => first.2.Quiet ∨ second.2.Quiet)

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
    transition.tasks.Pairwise (fun first second => first.2.Quiet ∨ second.2.Quiet) := by
  rcases transition_shape possible with ⟨empty, notSpawn, middle, kept, processes⟩ |
    ⟨task', single, kept, quiet, notSpawn⟩ | ⟨task', childTask, options, pair, state', event, quiet, childQuiet⟩
  · refine ⟨fun other notSelf _ => ?_, by simp [empty], by simp [empty], by simp [empty],
      fun child spawn => absurd spawn (notSpawn child), by simp [empty], by simp [empty]⟩
    have := kept other
    simp only [State.process, processes, State.processes_update, notSelf, ite_false] at this ⊢
    exact this
  · refine ⟨fun other _ _ => kept other, by simp [single], by simp [single], fun _ => ?_,
      fun child spawn => absurd spawn (notSpawn child), ?_, by simp [single]⟩
    · exact ⟨(kept processId).1 ▸ live, Nat.le_of_eq (kept processId).2.symm⟩
    · simp only [single, List.mem_singleton]
      rintro _ rfl
      exact quiet
  · obtain ⟨childPid, childLive, parentLive, children, others⟩ :=
      State.spawnWith_facts (state := state) (processId := processId) (options := options)
    have distinct : processId ≠ (state.spawnWith processId options).1 := by
      rw [childPid]; exact ne_append_cons _ _ _
    refine ⟨fun other notSelf notChild => ?_, by simp [pair, distinct], ?_, fun _ => ?_, ?_, ?_, ?_⟩
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
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state (before ++ (processId, task) :: after) finished exhausted))
    (possible : transition ∈ task.transitions state processId) :
    Wellformed (transition.apply before after finished exhausted) := by
  obtain ⟨distinct, fresh, live, quiet⟩ := wellformed
  have self : (processId, task) ∈ before ++ (processId, task) :: after := by simp
  obtain ⟨frame, inner, entries, grows, spawned, quietAdded, quietInner⟩ :=
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
  refine ⟨pairwise_replace distinct inner ?_ ?_, ?_, ?live, ?quiet⟩
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
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (kept : state.Keeps state') :
    Wellformed (.running state' tasks finished exhausted) := by
  obtain ⟨distinct, fresh, live, quiet⟩ := wellformed
  refine ⟨distinct, fun parent mem descendant mem' index rest extended => ?_,
    fun entry mem => (kept entry.1).1 ▸ live entry mem, quiet⟩
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
         refine ⟨by simp, ?_, by simp [State.initial], by simp⟩
         simp only [List.mem_singleton]
         rintro _ rfl _ rfl index rest extended
         exact absurd extended (ne_append_cons _ _ _))
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
deriving DecidableEq

/-- The steps of a process, each with its key. -/
def Task.keyed (state : State) (processId : PID) (task : Task α) : List (Key × Transition α) :=
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
def Config.steps : Config α → List (Key × Event × Config α)
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
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} :
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
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {key : Key}
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
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {key : Key}
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

end Lynx.Concurrent
