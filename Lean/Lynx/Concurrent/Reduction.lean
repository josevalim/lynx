module

public import Lynx.Concurrent

/-! `check` follows a process about to read its environment before any other
step. Reading changes nothing other processes observe, and their steps cannot
change what it reads, so every run can take the read first and reach the same
terminal configuration. Elsewhere it follows steps with sleep sets: steps whose
footprints do not conflict commute, so a run that takes a sleeping step first
reaches what a run explored before does. This module proves that `check` is
sound. -/

public section

namespace Lynx.Concurrent

open Lynx

/-! ### Effects on other processes -/

/-- What steps of other processes keep in a record: what the process reads, the
children it spawned, a pending exit signal, and the messages it has yet to
receive, which they can only follow with more. -/
private def Unchanged (before after : ProcessState) : Prop :=
  after.pdict = before.pdict ∧ after.refCounter = before.refCounter ∧
    after.children = before.children ∧ (before.signal.isSome → after.signal.isSome) ∧
    before.mailbox <+: after.mailbox

private theorem Unchanged.refl (process : ProcessState) : Unchanged process process :=
  ⟨rfl, rfl, rfl, id, List.prefix_refl _⟩

private theorem Unchanged.trans {first second third : ProcessState}
    (left : Unchanged first second) (right : Unchanged second third) : Unchanged first third :=
  ⟨right.1.trans left.1, right.2.1.trans left.2.1, right.2.2.1.trans left.2.2.1,
    fun pending => right.2.2.2.1 (left.2.2.2.1 pending), left.2.2.2.2.trans right.2.2.2.2⟩

/-- A state change keeps a process's record, and whether the process is live. -/
private def Keeps (processId : PID) (before after : State) : Prop :=
  Option.Rel Unchanged (before.processes processId) (after.processes processId)

private theorem Keeps.refl (processId : PID) (state : State) : Keeps processId state state := by
  unfold Keeps
  cases state.processes processId
  · exact .none
  · exact .some (Unchanged.refl _)

private theorem Keeps.trans {processId : PID} {first second third : State}
    (left : Keeps processId first second) (right : Keeps processId second third) :
    Keeps processId first third := by
  unfold Keeps at *
  generalize first.processes processId = a at left
  generalize second.processes processId = b at left right
  generalize third.processes processId = c at right
  cases left with
  | none => exact right
  | some unchanged =>
    cases right with
    | some unchanged' => exact .some (unchanged.trans unchanged')

/-- What the record of a kept process keeps. -/
private theorem Keeps.process {processId : PID} {before after : State}
    (kept : Keeps processId before after) :
    Unchanged (before.process processId) (after.process processId) := by
  unfold Keeps at kept
  unfold State.process
  generalize before.processes processId = a at kept
  generalize after.processes processId = b at kept
  cases kept with
  | none => exact Unchanged.refl _
  | some unchanged => exact unchanged

private theorem State.process_update {state : State} {processId other : PID}
    {process : Option ProcessState} :
    (state.update other process).process processId =
      if processId = other then process.getD {} else state.process processId := by
  simp only [State.process, State.update]
  split <;> rfl

private theorem keeps_update_ne {state : State} {processId other : PID}
    {process : Option ProcessState} (ne : processId ≠ other) :
    Keeps processId state (state.update other process) := by
  simp only [Keeps, State.update, ne, ite_false]
  exact Keeps.refl processId state

private theorem keeps_modify {state : State} {processId other : PID}
    {change : ProcessState → ProcessState}
    (kept : processId ≠ other ∨ ∀ process, Unchanged process (change process)) :
    Keeps processId state (state.modify other change) := by
  unfold State.modify
  split
  · rename_i process found
    by_cases equal : processId = other
    · subst equal
      simp only [Keeps, State.update, ite_true, found]
      rcases kept with ne | kept
      · exact absurd rfl ne
      · exact .some (kept process)
    · exact keeps_update_ne equal
  · exact Keeps.refl _ _

private theorem keeps_deliver {state : State} {processId other : PID} {message : Term} :
    Keeps processId state (state.deliver other message) := by
  unfold State.deliver
  split
  · rename_i process found
    by_cases equal : processId = other
    · subst equal
      simp only [Keeps, State.update, ite_true, found]
      exact .some ⟨rfl, rfl, rfl, id, List.prefix_append _ _⟩
    · exact keeps_update_ne equal
  · exact Keeps.refl _ _

private theorem keeps_kill {state : State} {processId other : PID} {reason : Term} :
    Keeps processId state (state.kill other reason) :=
  keeps_modify (.inr fun process => ⟨rfl, rfl, rfl, fun pending => by
    cases signal : process.signal <;> simp_all, List.prefix_refl _⟩)

private theorem keeps_signal {state : State} {processId target sender : PID} {reason : Term}
    {untrappable : Bool} : Keeps processId state (state.signal target sender reason untrappable) := by
  unfold State.signal
  split
  · exact keeps_kill
  · split
    · exact keeps_deliver
    · split
      · exact Keeps.refl _ _
      · exact keeps_kill

private theorem keeps_foldl {processId : PID} {items : List γ} {step : State → γ → State}
    (each : ∀ state item, Keeps processId state (step state item)) (state : State) :
    Keeps processId state (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact Keeps.refl _ _
  | cons item rest ih => exact (each state item).trans (ih _)

/-! Each lemma below extends a kept record through one more operation, so
compound operations unfold into a chain of them. -/

private theorem Keeps.update {state before : State} {processId other : PID}
    {process : Option ProcessState} (ne : processId ≠ other) (kept : Keeps processId state before) :
    Keeps processId state (before.update other process) :=
  kept.trans (keeps_update_ne ne)

private theorem Keeps.modify {state before : State} {processId other : PID}
    {change : ProcessState → ProcessState}
    (unchanged : processId ≠ other ∨ ∀ process, Unchanged process (change process))
    (kept : Keeps processId state before) : Keeps processId state (before.modify other change) :=
  kept.trans (keeps_modify unchanged)

private theorem Keeps.deliver {state before : State} {processId other : PID} {message : Term}
    (kept : Keeps processId state before) : Keeps processId state (before.deliver other message) :=
  kept.trans keeps_deliver

private theorem Keeps.signal {state before : State} {processId target sender : PID}
    {reason : Term} {untrappable : Bool} (kept : Keeps processId state before) :
    Keeps processId state (before.signal target sender reason untrappable) :=
  kept.trans keeps_signal

private theorem Keeps.kill {state before : State} {processId other : PID} {reason : Term}
    (kept : Keeps processId state before) : Keeps processId state (before.kill other reason) :=
  kept.trans keeps_kill

private theorem Keeps.foldl {state before : State} {processId : PID} {items : List γ}
    {step : State → γ → State} (kept : Keeps processId state before)
    (each : ∀ current item, Keeps processId state current → Keeps processId state (step current item)) :
    Keeps processId state (items.foldl step before) := by
  induction items generalizing before with
  | nil => exact kept
  | cons item rest ih => exact ih (each _ _ kept)

/-- Records of other processes keep their fields, other than the ones listed. -/
private theorem unchanged_fields (process : ProcessState)
    (links : List PID) (monitors monitoring : List (List Nat × PID)) (aliases : List (List Nat)) :
    Unchanged process { process with links, monitors, monitoring, aliases } :=
  ⟨rfl, rfl, rfl, id, List.prefix_refl _⟩

/-- Unfold a compound operation on a kept record. -/
syntax "keeps_chain" : tactic
macro_rules
  | `(tactic| keeps_chain) => `(tactic| repeat (first
      | exact Keeps.refl _ _
      | assumption
      | (apply Keeps.deliver)
      | (apply Keeps.kill)
      | (apply Keeps.signal)
      | (apply Keeps.update (by assumption))
      | (apply Keeps.modify (.inl (by assumption)))
      | (apply Keeps.modify (.inr fun process => unchanged_fields process _ _ _ _))
      | refine Keeps.foldl ?_ (fun current item kept => ?_)
      | split))

private theorem keeps_terminate {state : State} {processId other : PID} {reason : Term}
    (ne : processId ≠ other) : Keeps processId state (state.terminate other reason) := by
  simp only [State.terminate]
  keeps_chain

private theorem keeps_monitor {state before : State} {processId other target : PID}
    {alias : Bool} (ne : processId ≠ other) (kept : Keeps processId state before) :
    Keeps processId state (before.monitor other target alias).2 := by
  simp only [State.monitor]
  keeps_chain

private theorem keeps_request {state : State} {processId other : PID} {query : Request}
    (ne : processId ≠ other) : Keeps processId state (state.request other query).2 := by
  cases query with
  | monitor target alias => exact keeps_monitor ne (Keeps.refl _ _)
  | _ => simp only [State.request]; keeps_chain

private theorem keeps_spawnWith {state : State} {processId other : PID} {options : SpawnOptions}
    (ne : processId ≠ other) (fresh : processId ≠ (state.spawnWith other options).1) :
    Keeps processId state (state.spawnWith other options).2 := by
  have child : processId ≠ other ++ [(state.process other).children + 1] := by
    simpa [State.spawnWith, State.spawn] using fresh
  simp only [State.spawnWith, State.spawn]
  repeat' (first | (apply keeps_monitor ne) | (apply Keeps.modify (.inl child)) | split)
  all_goals keeps_chain

/-! ### Children of the stepping process -/

/-- A state change keeps the number of children a process spawned, and keeps it
live. -/
private def KeepsChildren (processId : PID) (before after : State) : Prop :=
  (after.process processId).children = (before.process processId).children ∧
    ((before.processes processId).isSome → (after.processes processId).isSome)

private theorem KeepsChildren.refl (processId : PID) (state : State) :
    KeepsChildren processId state state := ⟨rfl, id⟩

private theorem KeepsChildren.trans {processId : PID} {first second third : State}
    (left : KeepsChildren processId first second) (right : KeepsChildren processId second third) :
    KeepsChildren processId first third :=
  ⟨right.1.trans left.1, fun live => right.2 (left.2 live)⟩

private theorem KeepsChildren.update {state before : State} {processId other : PID}
    {process : Option ProcessState}
    (same : processId ≠ other ∨
      ((process.getD {}).children = (before.process other).children ∧ process.isSome))
    (kept : KeepsChildren processId state before) :
    KeepsChildren processId state (before.update other process) := by
  unfold KeepsChildren at *
  rw [State.process_update]
  simp only [State.update]
  split
  · rename_i equal
    subst equal
    rcases same with ne | ⟨same, live⟩
    · exact absurd rfl ne
    · exact ⟨by rw [same, kept.1], fun _ => live⟩
  · exact kept

private theorem KeepsChildren.modify {state before : State} {processId other : PID}
    {change : ProcessState → ProcessState}
    (same : ∀ process, (change process).children = process.children)
    (kept : KeepsChildren processId state before) :
    KeepsChildren processId state (before.modify other change) := by
  unfold State.modify
  split
  · rename_i process found
    refine KeepsChildren.update ?_ kept
    by_cases equal : processId = other
    · right
      simp [State.process, found, same]
    · exact .inl equal
  · exact kept

private theorem KeepsChildren.deliver {state before : State} {processId other : PID}
    {message : Term} (kept : KeepsChildren processId state before) :
    KeepsChildren processId state (before.deliver other message) := by
  unfold State.deliver
  split
  · rename_i process found
    refine KeepsChildren.update ?_ kept
    by_cases equal : processId = other
    · right
      simp [State.process, found]
    · exact .inl equal
  · exact kept

private theorem KeepsChildren.kill {state before : State} {processId other : PID}
    {reason : Term} (kept : KeepsChildren processId state before) :
    KeepsChildren processId state (before.kill other reason) :=
  KeepsChildren.modify (fun _ => rfl) kept

private theorem KeepsChildren.signal {state before : State} {processId target sender : PID}
    {reason : Term} {untrappable : Bool} (kept : KeepsChildren processId state before) :
    KeepsChildren processId state (before.signal target sender reason untrappable) := by
  unfold State.signal
  split
  · exact kept.kill
  · split
    · exact kept.deliver
    · split
      · exact kept
      · exact kept.kill

private theorem KeepsChildren.foldl {state before : State} {processId : PID} {items : List γ}
    {step : State → γ → State} (kept : KeepsChildren processId state before)
    (each : ∀ current item, KeepsChildren processId state current →
      KeepsChildren processId state (step current item)) :
    KeepsChildren processId state (items.foldl step before) := by
  induction items generalizing before with
  | nil => exact kept
  | cons item rest ih => exact ih (each _ _ kept)

/-- Unfold a compound operation that keeps the children of every process. -/
syntax "children_chain" : tactic
macro_rules
  | `(tactic| children_chain) => `(tactic| repeat (first
      | exact KeepsChildren.refl _ _
      | assumption
      | dsimp only
      | (apply KeepsChildren.deliver)
      | (apply KeepsChildren.kill)
      | (apply KeepsChildren.signal)
      | refine KeepsChildren.modify (by intro _; rfl) ?_
      | refine KeepsChildren.foldl ?_ (fun current item kept => ?_)
      | split))

private theorem KeepsChildren.monitor {state before : State} {processId other target : PID}
    {alias : Bool} (kept : KeepsChildren processId state before) :
    KeepsChildren processId state (before.monitor other target alias).2 := by
  simp only [State.monitor]
  children_chain

private theorem keepsChildren_request {state : State} {processId other : PID} {query : Request} :
    KeepsChildren processId state (state.request other query).2 := by
  cases query with
  | monitor target alias => exact KeepsChildren.monitor (KeepsChildren.refl _ _)
  | _ => simp only [State.request]; children_chain

/-- Timers only deliver messages, so they keep every record otherwise,
including pending signals. -/
private theorem timerSteps_keeps {state after : State} {event : Event}
    (possible : (event, after) ∈ state.timerSteps) (processId : PID) :
    Keeps processId state after ∧ KeepsChildren processId state after ∧
      (after.process processId).signal = (state.process processId).signal := by
  simp only [State.timerSteps, List.mem_map] at possible
  obtain ⟨timer, -, step⟩ := possible
  split at step <;> simp only [Prod.mk.injEq] at step <;> obtain ⟨-, rfl⟩ := step
  · refine ⟨keeps_deliver, KeepsChildren.deliver (KeepsChildren.refl _ _), ?_⟩
    show ((state.deliver _ _).process processId).signal = _
    unfold State.deliver
    split
    · rw [State.process_update]
      split
      · subst processId; simp_all [State.process]
      · rfl
    · rfl
  · exact ⟨Keeps.refl _ _, KeepsChildren.refl _ _, rfl⟩

/-! ### Transitions -/

/-- The children of a spawning process, and the PID of its new child. -/
private theorem spawnWith_children {state : State} {processId : PID} {options : SpawnOptions} :
    (state.spawnWith processId options).1 = processId ++ [(state.process processId).children + 1] ∧
      ((state.spawnWith processId options).2.process processId).children =
        (state.process processId).children + 1 ∧
      ((state.spawnWith processId options).2.processes processId).isSome ∧
      ((state.spawnWith processId options).2.processes (state.spawnWith processId options).1).isSome := by
  have fresh : processId ≠ processId ++ [(state.process processId).children + 1] := by
    intro equal
    have := congrArg List.length equal
    simp at this
  have spawned : ((state.spawn processId).2.process processId).children =
      (state.process processId).children + 1 := by
    simp only [State.spawn, State.process_update]
    simp [fresh]
  have kept : ∀ other, KeepsChildren other (state.spawn processId).2
      (state.spawnWith processId options).2 := by
    intro other
    simp only [State.spawnWith]
    repeat' (first | (apply KeepsChildren.monitor) |
      (refine KeepsChildren.modify (by intro _; rfl) ?_) | split)
    all_goals children_chain
  refine ⟨rfl, (kept processId).1.trans spawned, (kept processId).2 ?_, (kept _).2 ?_⟩
  · simp [State.spawn, State.update, fresh]
  · simp [State.spawn, State.update, State.spawnWith]

/-- A process whose result does not reach the run's outcome. -/
private def Task.Quiet (task : Task α) : Prop := ∀ result, task.finish result = none

/-- How a step of a process changes the shared state and the processes. -/
private theorem transition_frame {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.transitions state processId) :
    (∀ other, other ≠ processId →
      (∀ child, transition.event = .spawn processId child → other ≠ child) →
      Keeps other state transition.state) ∧
    (transition.tasks = [] ∨
      (∃ next, transition.tasks = [(processId, next)] ∧
        KeepsChildren processId state transition.state ∧ (task.Quiet → next.Quiet)) ∨
      ∃ next child spawned, transition.tasks = [(processId, next), (child, spawned)] ∧
        transition.event = .spawn processId child ∧
        child = processId ++ [(state.process processId).children + 1] ∧
        (transition.state.process processId).children = (state.process processId).children + 1 ∧
        (transition.state.processes processId).isSome ∧
        (transition.state.processes child).isSome ∧
        (task.Quiet → next.Quiet) ∧ spawned.Quiet) ∧
    (task.Quiet → transition.finished = none) := by
  obtain ⟨computation, finish⟩ := task
  have quietMap : ∀ (result : Except Exception _) (view : Environment),
      Task.Quiet (⟨computation, finish⟩ : Task α) →
        (finish result).map (·, view) = none := by
    intro result view quiet
    have : finish result = none := quiet result
    simp [this]
  rcases signal : (state.process processId).signal with _ | reason
  · cases computation with
    | ok value =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun other ne _ => keeps_terminate ne, .inl rfl, quietMap _ _⟩
    | error exception =>
      cases exception <;> simp only [Task.transitions, signal, List.mem_singleton] at possible <;>
        subst possible <;>
        first
        | exact ⟨fun other ne _ => keeps_terminate ne, .inl rfl, quietMap _ _⟩
        | exact ⟨fun other ne _ => keeps_update_ne ne, .inl rfl, fun _ => rfl⟩
    | get next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun _ _ _ => Keeps.refl _ _, .inr (.inl ⟨_, rfl, KeepsChildren.refl _ _, id⟩),
        fun _ => rfl⟩
    | set updated next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      refine ⟨fun other ne _ => keeps_update_ne ne, .inr (.inl ⟨_, rfl, ?_, id⟩), fun _ => rfl⟩
      exact KeepsChildren.update (.inr ⟨rfl, rfl⟩) (KeepsChildren.refl _ _)
    | schedule options child next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      obtain ⟨childPid, children, parentLive, childLive⟩ :=
        spawnWith_children (state := state) (processId := processId) (options := options)
      refine ⟨fun other ne fresh => keeps_spawnWith ne (fresh _ rfl), .inr (.inr ?_), fun _ => rfl⟩
      exact ⟨_, _, _, rfl, rfl, childPid, children, parentLive, childLive, id, fun _ => rfl⟩
    | send destination message next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun _ _ _ => keeps_deliver,
        .inr (.inl ⟨_, rfl, (KeepsChildren.refl _ _).deliver, id⟩), fun _ => rfl⟩
    | receive timeout select next =>
      simp only [Task.transitions, signal] at possible
      split at possible
      · simp only [List.mem_singleton] at possible
        subst possible
        refine ⟨fun other ne _ => keeps_update_ne ne, .inr (.inl ⟨_, rfl, ?_, id⟩), fun _ => rfl⟩
        exact KeepsChildren.update (.inr ⟨rfl, rfl⟩) (KeepsChildren.refl _ _)
      · split at possible <;> simp only [List.mem_singleton, List.not_mem_nil] at possible <;>
          subst possible <;>
          exact ⟨fun _ _ _ => Keeps.refl _ _,
            .inr (.inl ⟨_, rfl, KeepsChildren.refl _ _, id⟩), fun _ => rfl⟩
    | request query next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun other ne _ => keeps_request ne,
        .inr (.inl ⟨_, rfl, keepsChildren_request, id⟩), fun _ => rfl⟩
  · simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    exact ⟨fun other ne _ => keeps_terminate ne, .inl rfl, quietMap _ _⟩

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

/-- A kept process stays live. -/
private theorem Keeps.live {processId : PID} {before after : State}
    (kept : Keeps processId before after) (live : (before.processes processId).isSome) :
    (after.processes processId).isSome := by
  unfold Keeps at kept
  generalize before.processes processId = a at kept live
  generalize after.processes processId = b at kept
  cases kept with
  | none => exact live
  | some => rfl

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

/-- The processes a transition leaves: the stepping process, and possibly a
spawned child with the next PID below it. -/
private theorem transition_tasks {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.transitions state processId) :
    transition.tasks.Pairwise (fun first second => first.1 ≠ second.1) ∧
    (∀ entry ∈ transition.tasks, entry.1 = processId ∨ ∃ child,
      transition.event = .spawn processId child ∧ entry.1 = child) ∧
    ((state.process processId).children ≤ (transition.state.process processId).children ∨
      transition.tasks = []) ∧
    ∀ child, transition.event = .spawn processId child →
      child = processId ++ [(state.process processId).children + 1] ∧
      (transition.state.process processId).children = (state.process processId).children + 1 := by
  obtain ⟨-, shape, -⟩ := transition_frame possible
  rcases shape with empty | ⟨next, single, kept, -⟩ |
    ⟨next, child, spawned, pair, event, childPid, children, -⟩
  · refine ⟨by simp [empty], by simp [empty], .inr empty, fun child spawn => ?_⟩
    -- Exits are not spawns.
    obtain ⟨computation, finish⟩ := task
    simp only [Task.transitions] at possible
    split at possible
    · simp only [List.mem_singleton] at possible; subst possible; cases spawn
    · split at possible <;> (try split at possible) <;> (try split at possible) <;>
        simp_all
      -- A request may get several replies, none of them a spawn.
      all_goals obtain ⟨_, _, rfl⟩ := possible; cases spawn
  · refine ⟨by simp [single], by simp [single], .inl (Nat.le_of_eq kept.1.symm), fun child spawn => ?_⟩
    obtain ⟨computation, finish⟩ := task
    simp only [Task.transitions] at possible
    split at possible
    · simp only [List.mem_singleton] at possible; subst possible; cases spawn
    · split at possible <;> (try split at possible) <;> (try split at possible) <;>
        simp_all
      -- A request may get several replies, none of them a spawn.
      all_goals obtain ⟨_, _, rfl⟩ := possible; cases spawn
  · refine ⟨?_, ?_, .inl (by omega), fun other spawn => ?_⟩
    · rw [pair, childPid]
      simp
    · intro entry mem
      simp only [pair, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact .inl rfl
      · exact .inr ⟨child, event, rfl⟩
    · rw [event] at spawn
      cases spawn
      exact ⟨childPid, children⟩

/-- A process step preserves well-formedness. -/
private theorem wellformed_apply {state : State} {before after : List (PID × Task α)}
    {processId : PID} {task : Task α} {transition : Transition α}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state (before ++ (processId, task) :: after) finished exhausted))
    (possible : transition ∈ task.transitions state processId) :
    Wellformed (transition.apply before after finished exhausted) := by
  obtain ⟨distinct, fresh, live, quiet⟩ := wellformed
  obtain ⟨frame, shape, -⟩ := transition_frame possible
  obtain ⟨inner, entries, grows, spawned⟩ := transition_tasks possible
  have self : (processId, task) ∈ before ++ (processId, task) :: after := by simp
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
  -- Other processes keep their children.
  have kept : ∀ entry, entry ∈ before ∨ entry ∈ after →
      (transition.state.process entry.1).children = (state.process entry.1).children := by
    intro entry mem
    exact (frame entry.1 (others entry mem) fun child spawn =>
      child_new child spawn entry (old entry mem)).process.2.2.1
  simp only [Transition.apply, Wellformed]
  refine ⟨pairwise_replace distinct inner ?_ ?_, ?_, ?live, ?quiet⟩
  case live =>
    -- Every process stays live.
    intro entry mem
    simp only [List.mem_append] at mem
    have selfLive := live (processId, task) self
    rcases mem with (mem | mem) | mem
    · exact (frame entry.1 (others entry (.inl mem)) fun child spawn =>
        child_new child spawn entry (old entry (.inl mem))).live (live entry (old entry (.inl mem)))
    · rcases shape with empty | ⟨next, single, kept, -⟩ |
        ⟨next, child, spawned', pair, -, -, -, parentLive, childLive, -⟩
      · simp [empty] at mem
      · rw [single, List.mem_singleton] at mem
        subst mem
        exact kept.2 selfLive
      · rw [pair] at mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact parentLive
        · exact childLive
    · exact (frame entry.1 (others entry (.inr mem)) fun child spawn =>
        child_new child spawn entry (old entry (.inr mem))).live (live entry (old entry (.inr mem)))
  case quiet =>
    -- At most one process reports the result.
    have addedQuiet : ∀ added ∈ transition.tasks, task.Quiet → added.2.Quiet := by
      intro added mem quietTask
      rcases shape with empty | ⟨next, single, -, nextQuiet⟩ |
        ⟨next, child, spawned', pair, -, -, -, -, -, nextQuiet, spawnedQuiet⟩
      · simp [empty] at mem
      · rw [single, List.mem_singleton] at mem
        subst mem
        exact nextQuiet quietTask
      · rw [pair] at mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact nextQuiet quietTask
        · exact spawnedQuiet
    refine pairwise_replace quiet ?_ ?_ ?_
    · rcases shape with empty | ⟨next, single, -, -⟩ |
        ⟨next, child, spawned', pair, -, -, -, -, -, -, spawnedQuiet⟩
      · simp [empty]
      · simp [single]
      · simp [pair, spawnedQuiet]
    · intro item mem either added addedMem
      rcases either with itemQuiet | taskQuiet
      · exact .inl itemQuiet
      · exact .inr (addedQuiet added addedMem taskQuiet)
    · intro item mem either added addedMem
      rcases either with taskQuiet | itemQuiet
      · exact .inl (addedQuiet added addedMem taskQuiet)
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
  -- Classify an entry of the new configuration.
  have classify : ∀ entry, entry ∈ before ∨ entry ∈ transition.tasks ∨ entry ∈ after →
      (entry ∈ before ∨ entry ∈ after) ∨ (entry.1 = processId ∧ transition.tasks ≠ []) ∨
        ∃ child, transition.event = .spawn processId child ∧ entry.1 = child := by
    intro entry mem
    rcases mem with mem | mem | mem
    · exact .inl (.inl mem)
    · rcases entries entry mem with self | spawn
      · exact .inr (.inl ⟨self, List.ne_nil_of_mem mem⟩)
      · exact .inr (.inr spawn)
    · exact .inl (.inr mem)
  have parentClass := classify parent (by rcases parentMem with (h | h) | h <;> simp [h])
  have descendantClass := classify descendant
    (by rcases descendantMem with (h | h) | h <;> simp [h])
  rcases parentClass with parentOld | ⟨parentSelf, nonempty⟩ | ⟨child, spawn, parentChild⟩
  · -- An existing parent keeps its children.
    rw [kept parent parentOld]
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
  · -- The stepping process has at least its former children.
    rw [parentSelf] at extended ⊢
    rcases descendantClass with descendantOld | ⟨descendantSelf, -⟩ |
        ⟨child, spawn, descendantChild⟩
    · have bound := fresh (processId, task) self descendant (old descendant descendantOld) index
        rest extended
      dsimp only at bound
      rcases grows with grows | empty
      · omega
      · exact absurd empty nonempty
    · rw [descendantSelf] at extended
      exact absurd extended (ne_append_cons _ _ _)
    · rw [descendantChild, (spawned child spawn).1] at extended
      have := List.append_cancel_left extended
      simp only [List.cons.injEq] at this
      rw [(spawned child spawn).2, ← this.1]
      exact Nat.le_refl _
  · -- A new child has no descendants yet.
    exfalso
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

/-- Every step preserves well-formedness. -/
private theorem Step.wellformed {first next : Config α} {event : Event}
    (step : Step first event next) (wellformed : Wellformed first) : Wellformed next := by
  cases step with
  | get | set => trivial
  | enter =>
    refine ⟨by simp, ?_, by simp [State.initial], by simp⟩
    simp only [List.mem_singleton]
    rintro _ rfl _ rfl index rest extended
    exact absurd extended (ne_append_cons _ _ _)
  | run split possible =>
    subst split
    exact wellformed_apply wellformed possible
  | timer possible =>
    obtain ⟨distinct, fresh, live, quiet⟩ := wellformed
    refine ⟨distinct, fun parent member descendant member' index rest extended => ?_,
      fun entry member => (timerSteps_keeps possible entry.1).2.1.2 (live entry member), quiet⟩
    rw [(timerSteps_keeps possible parent.1).2.1.1]
    exact fresh parent member descendant member' index rest extended

/-! ### Erasing what a process keeps

Other processes neither read nor change the dictionary and reference counter a
process keeps in its environment, so their steps commute with erasing them. -/

/-- A record without what its process keeps in its environment. -/
private def ProcessState.erase (process : ProcessState) : ProcessState :=
  { process with pdict := [], refCounter := 0 }

/-- A state without what one process keeps in its environment. -/
private def State.erase (state : State) (processId : PID) : State :=
  { state with processes := fun candidate =>
      if candidate = processId then (state.processes candidate).map ProcessState.erase
      else state.processes candidate }

private theorem State.ext' {first second : State} (timers : first.timers = second.timers)
    (elapsed : first.elapsed = second.elapsed)
    (equal : ∀ candidate, first.processes candidate = second.processes candidate) :
    first = second := by
  cases first; cases second; simp_all; funext candidate; exact equal candidate

@[simp] private theorem erase_timers {state : State} {processId : PID} :
    (state.erase processId).timers = state.timers := rfl

@[simp] private theorem erase_elapsed {state : State} {processId : PID} :
    (state.erase processId).elapsed = state.elapsed := rfl

private theorem erase_processes {state : State} {processId candidate : PID} :
    (state.erase processId).processes candidate =
      if candidate = processId then (state.processes candidate).map ProcessState.erase
      else state.processes candidate := rfl

private theorem erase_process_ne {state : State} {processId other : PID} (ne : other ≠ processId) :
    (state.erase processId).process other = state.process other := by
  simp [State.process, erase_processes, ne]

private theorem erase_view_ne {state : State} {processId other : PID} (ne : other ≠ processId) :
    (state.erase processId).view other = state.view other := by
  simp [State.view, erase_process_ne ne]

/-- Erasing keeps every field other than the environment. -/
private theorem erase_process_fields {state : State} {processId other : PID} :
    ((state.erase processId).process other).mailbox = (state.process other).mailbox ∧
    ((state.erase processId).process other).links = (state.process other).links ∧
    ((state.erase processId).process other).monitors = (state.process other).monitors ∧
    ((state.erase processId).process other).monitoring = (state.process other).monitoring ∧
    ((state.erase processId).process other).aliases = (state.process other).aliases ∧
    ((state.erase processId).process other).trapExit = (state.process other).trapExit ∧
    ((state.erase processId).process other).signal = (state.process other).signal ∧
    ((state.erase processId).process other).children = (state.process other).children := by
  by_cases equal : other = processId
  · subst equal
    simp only [State.process, erase_processes, ite_true]
    cases state.processes other <;> simp [ProcessState.erase]
  · simp [erase_process_ne equal]

private theorem erase_isSome {state : State} {processId other : PID} :
    ((state.erase processId).processes other).isSome = (state.processes other).isSome := by
  simp only [erase_processes]; split <;> simp

/-- A change of a record commutes with erasing its environment. -/
private def Oblivious (change : ProcessState → ProcessState) : Prop :=
  ∀ process, (change process).erase = change process.erase

private theorem erase_update_ne {state : State} {processId other : PID}
    {process : Option ProcessState} (ne : other ≠ processId) :
    (state.update other process).erase processId = (state.erase processId).update other process := by
  refine State.ext' rfl (by simp) fun candidate => ?_
  simp only [erase_processes, State.update]
  by_cases first : candidate = other <;> by_cases second : candidate = processId <;> simp_all

private theorem erase_update_self {state : State} {processId : PID} :
    (state.update processId none).erase processId = (state.erase processId).update processId none := by
  refine State.ext' rfl (by simp) fun candidate => ?_
  simp only [erase_processes, State.update]
  by_cases first : candidate = processId <;> simp_all

private theorem erase_modify {state : State} {processId other : PID}
    {change : ProcessState → ProcessState} (oblivious : Oblivious change) :
    (state.modify other change).erase processId = (state.erase processId).modify other change := by
  refine State.ext' (by simp) (by simp) fun candidate => ?_
  unfold State.modify
  rw [erase_processes]
  by_cases same : other = processId
  · subst same
    cases found : state.processes other with
    | none => simp [erase_processes, found]
    | some process =>
      simp only [erase_processes, found, ite_true, Option.map_some, State.update]
      by_cases equal : candidate = other <;> simp_all [oblivious process]
  · cases found : state.processes other with
    | none => simp [erase_processes, found, same]
    | some process =>
      simp only [erase_processes, found, same, ite_false, State.update]
      by_cases equal : candidate = other <;> by_cases equal' : candidate = processId <;> simp_all

private theorem erase_deliver {state : State} {processId other : PID} {message : Term} :
    (state.deliver other message).erase processId = (state.erase processId).deliver other message := by
  have : state.deliver other message = state.modify other fun process =>
      { process with mailbox := process.mailbox ++ [message] } := by
    unfold State.deliver State.modify; split <;> rfl
  have : (state.erase processId).deliver other message = (state.erase processId).modify other
      fun process => { process with mailbox := process.mailbox ++ [message] } := by
    unfold State.deliver State.modify; split <;> rfl
  rw [‹state.deliver other message = _›, this]
  exact erase_modify (by intro _; rfl)

private theorem erase_kill {state : State} {processId other : PID} {reason : Term} :
    (state.kill other reason).erase processId = (state.erase processId).kill other reason :=
  erase_modify (by intro _; rfl)

private theorem erase_signal {state : State} {processId target sender : PID} {reason : Term}
    {untrappable : Bool} :
    (state.signal target sender reason untrappable).erase processId =
      (state.erase processId).signal target sender reason untrappable := by
  have trapExit := (erase_process_fields (state := state) (processId := processId)
    (other := target)).2.2.2.2.2.1
  unfold State.signal
  rw [trapExit]
  split
  · exact erase_kill
  · split
    · exact erase_deliver
    · split
      · rfl
      · exact erase_kill

private theorem erase_foldl {items : List γ} {step : State → γ → State} {processId : PID}
    (each : ∀ state item, (step state item).erase processId = step (state.erase processId) item)
    (state : State) :
    (items.foldl step state).erase processId = items.foldl step (state.erase processId) := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih => simp only [List.foldl_cons, ih, each]

private theorem erase_modify_ne {state : State} {processId other : PID}
    {change : ProcessState → ProcessState} (ne : other ≠ processId) :
    (state.modify other change).erase processId = (state.erase processId).modify other change := by
  refine State.ext' (by simp) (by simp) fun candidate => ?_
  unfold State.modify
  cases found : state.processes other with
  | none => simp [erase_processes, found, ne]
  | some process =>
    simp only [erase_processes, found, ne, ite_false, State.update]
    by_cases equal : candidate = other <;> by_cases equal' : candidate = processId <;> simp_all

private theorem erase_with_timers {state : State} {processId : PID} {timers : List Timer} :
    ({ state with timers } : State).erase processId = { state.erase processId with timers } := rfl

private theorem erase_terminate {state : State} {processId other : PID} {reason : Term}
    (ne : other ≠ processId) :
    (state.terminate other reason).erase processId =
      (state.erase processId).terminate other reason := by
  simp only [State.terminate, erase_process_ne ne]
  rw [erase_foldl fun current item => by rw [erase_modify (by intro _; rfl), erase_deliver]]
  rw [erase_foldl fun current item => by rw [erase_signal, erase_modify (by intro _; rfl)]]
  rw [erase_with_timers, erase_update_ne ne]
  rfl

private theorem erase_monitor {state : State} {processId other target : PID} {alias : Bool}
    (ne : other ≠ processId) :
    (state.erase processId).monitor other target alias =
      ((state.monitor other target alias).1, (state.monitor other target alias).2.erase processId) := by
  simp only [State.monitor, erase_process_ne ne]
  rw [← erase_modify_ne (change := fun process =>
    { process with refCounter := process.refCounter + 1 }) ne]
  generalize (state.modify other fun process =>
    { process with refCounter := process.refCounter + 1 }) = counted
  rw [erase_processes]
  by_cases same : target = processId
  · subst same
    cases found : counted.processes target with
    | none => simp [erase_deliver]
    | some watched =>
      simp only [ite_true, Option.map_some]
      rw [erase_modify_ne ne, erase_modify (by intro _; rfl)]
  · cases found : counted.processes target with
    | none => simp [same, erase_deliver]
    | some watched =>
      simp only [same, ite_false]
      rw [erase_modify_ne ne, erase_modify (by intro _; rfl)]

/-- Erasing keeps whether a process is alive. -/
private theorem erase_processes_none {state : State} {processId target : PID} :
    (state.erase processId).processes target = none ↔ state.processes target = none := by
  rw [erase_processes]; split <;> simp

private theorem erase_processes_some {state : State} {processId target : PID}
    {process : ProcessState} (found : state.processes target = some process) :
    ∃ erased, (state.erase processId).processes target = some erased := by
  rw [erase_processes]; split <;> simp [found]

private theorem erase_request {state : State} {processId other : PID} {query : Request}
    (ne : other ≠ processId) :
    (state.erase processId).request other query =
      ((state.request other query).1, (state.request other query).2.erase processId) := by
  cases query with
  | monitor target alias =>
    simp only [State.request, erase_monitor ne]
  | demonitor reference flush =>
    simp only [State.request, erase_process_ne ne]
    rw [erase_modify_ne ne, erase_foldl fun current item => by
      obtain ⟨found, target⟩ := item
      dsimp only
      split
      · exact erase_modify (by intro _; rfl)
      · rfl]
  | link target =>
    simp only [State.request]
    split
    · rfl
    · cases found : state.processes target with
      | none =>
        simp only [erase_processes_none.mpr found, erase_process_ne ne]
        split
        · simp [erase_deliver]
        · rfl
      | some process =>
        obtain ⟨erased, found'⟩ := erase_processes_some (processId := processId) found
        simp only [found']
        rw [erase_modify (by intro _; rfl), erase_modify_ne ne]
  | unlink target =>
    simp only [State.request]
    rw [erase_modify (by intro _; rfl), erase_modify_ne ne]
  | exit target reason =>
    simp only [State.request, erase_process_ne ne]
    split
    · simp [erase_kill]
    · simp [erase_signal]
  | trapExit enabled =>
    simp only [State.request, erase_process_ne ne, erase_modify_ne ne]
  | alive target =>
    simp only [State.request]
    cases found : state.processes target with
    | none => simp [erase_processes_none.mpr found]
    | some process =>
      obtain ⟨erased, found'⟩ := erase_processes_some (processId := processId) found
      simp [found']
  | sendAlias alias message =>
    simp only [State.request, (erase_process_fields (state := state) (processId := processId)
      (other := alias.dropLast)).2.2.2.2.1]
    split
    · simp [erase_deliver]
    · rfl
  | startTimer destination message duration =>
    simp only [State.request, erase_process_ne ne, ← erase_modify_ne (change := fun process =>
      { process with refCounter := process.refCounter + 1 }) ne]
    generalize (state.modify other fun process =>
      { process with refCounter := process.refCounter + 1 }) = counted
    rw [erase_isSome]
    split <;> rfl
  | cancelTimer reference =>
    simp only [State.request, erase_timers, erase_elapsed, erase_process_ne ne]
    split
    · simp only [Prod.mk.injEq, true_and]
      exact (erase_modify_ne (state := { state with
        timers := state.timers.filter (·.reference != reference) }) ne).symm
    · rfl

private theorem erase_spawnWith {state : State} {processId other : PID} {options : SpawnOptions}
    (ne : other ≠ processId)
    (fresh : other ++ [(state.process other).children + 1] ≠ processId) :
    (state.erase processId).spawnWith other options =
      ((state.spawnWith other options).1, (state.spawnWith other options).2.erase processId) := by
  obtain ⟨link, monitor⟩ := options
  simp only [State.spawnWith, State.spawn, erase_process_ne ne]
  rw [← erase_update_ne ne, ← erase_update_ne fresh]
  cases link <;> cases monitor <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · rw [erase_monitor ne]
  · rw [← erase_modify_ne ne, ← erase_modify (by intro _; rfl)]
  · rw [← erase_modify_ne ne, ← erase_modify (by intro _; rfl), erase_monitor ne]

private theorem erase_timerSteps {state : State} {processId : PID} :
    (state.erase processId).timerSteps =
      state.timerSteps.map fun (event, next) => (event, next.erase processId) := by
  simp only [State.timerSteps, erase_timers, List.map_map]
  apply List.map_congr_left
  intro timer _
  simp only [Function.comp_apply]
  split
  · rw [← erase_deliver]; rfl
  · rfl

/-- Steps of other processes commute with erasing what a process keeps. -/
private theorem transitions_erase {state : State} {processId other : PID} {task : Task α}
    (ne : other ≠ processId)
    (fresh : other ++ [(state.process other).children + 1] ≠ processId) :
    task.transitions (state.erase processId) other =
      (task.transitions state other).map fun transition =>
        { transition with state := transition.state.erase processId } := by
  obtain ⟨computation, finish⟩ := task
  simp only [Task.transitions, erase_view_ne ne, erase_process_ne ne]
  split
  · simp [erase_terminate ne]
  · cases computation with
    | ok => simp [erase_terminate ne]
    | error exception => cases exception <;> simp [erase_terminate ne, erase_update_ne ne]
    | get => simp
    | set updated next =>
      simp [State.store, erase_update_ne ne, erase_process_ne ne]
    | schedule options child next =>
      simp only [erase_spawnWith ne fresh, List.map_cons, List.map_nil]
    | send destination message next => simp [erase_deliver]
    | receive timeout select next =>
      dsimp only
      split
      · simp [erase_update_ne ne]
      · cases timeout <;> simp
    | request query next =>
      simp only [erase_request ne]
      rfl

/-- Storing the environment of a live process only changes what erasing removes. -/
private theorem erase_store {state : State} {processId : PID} {env : Environment}
    (live : (state.processes processId).isSome) :
    (state.store processId env).erase processId = state.erase processId := by
  refine State.ext' rfl (by simp) fun candidate => ?_
  simp only [erase_processes, State.store, State.update, State.process]
  by_cases same : candidate = processId
  · subst same
    obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp live
    simp [found, ProcessState.erase]
  · simp [same]

/-- States that agree but for what a process keeps are equal once it stores the same. -/
private theorem eq_store_of_erase {first second : State} {processId : PID} {env : Environment}
    (equal : second.erase processId = first.erase processId)
    (live : (first.processes processId).isSome)
    (pdict : (second.process processId).pdict = env.pdict)
    (refCounter : (second.process processId).refCounter = env.refCounter) :
    second = first.store processId env := by
  have timers : second.timers = first.timers := by
    simpa using congrArg State.timers equal
  have elapsed : second.elapsed = first.elapsed := by
    simpa using congrArg State.elapsed equal
  refine State.ext' timers elapsed fun candidate => ?_
  have atCandidate := congrArg (fun state : State => state.processes candidate) equal
  simp only [erase_processes] at atCandidate
  simp only [State.store, State.update]
  by_cases same : candidate = processId
  · subst same
    simp only [ite_true] at atCandidate ⊢
    obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp live
    cases found' : second.processes candidate with
    | none => simp [found, found'] at atCandidate
    | some process' =>
      simp only [found, found', Option.map_some, Option.some.injEq] at atCandidate
      simp only [State.process, found, found', Option.getD_some] at pdict refCounter ⊢
      cases process; cases process'
      simp only [ProcessState.erase, ProcessState.mk.injEq] at atCandidate
      simp_all
  · simpa [same] using atCandidate

/-- Exiting forgets what the process kept. -/
private theorem terminate_erase {state : State} {processId : PID} {reason : Term} :
    (state.erase processId).terminate processId reason = state.terminate processId reason := by
  have fields := erase_process_fields (state := state) (processId := processId) (other := processId)
  have removed : (state.erase processId).update processId none = state.update processId none := by
    refine State.ext' rfl (by simp) fun candidate => ?_
    simp only [erase_processes, State.update]
    split <;> simp_all
  simp only [State.terminate, fields.2.1, fields.2.2.1, removed, erase_timers]

/-- A step of another process from a state that agrees but for what a process
keeps has a step that agrees, with the same event and processes. -/
private theorem transition_of_erase {first second : State} {processId other : PID} {task : Task α}
    {transition : Transition α} (ne : other ≠ processId)
    (fresh : other ++ [(first.process other).children + 1] ≠ processId)
    (equal : second.erase processId = first.erase processId)
    (possible : transition ∈ task.transitions first other) :
    ∃ moved ∈ task.transitions second other, moved.event = transition.event ∧
      moved.tasks = transition.tasks ∧ moved.finished = transition.finished ∧
      moved.exhausted = transition.exhausted ∧
      moved.state.erase processId = transition.state.erase processId := by
  have children : (second.process other).children = (first.process other).children := by
    rw [← erase_process_ne (state := second) ne, ← erase_process_ne (state := first) ne, equal]
  have lists := (transitions_erase (task := task) ne fresh).symm.trans
    ((congrArg (task.transitions · other) equal).symm.trans
      (transitions_erase (task := task) ne (by rw [children]; exact fresh)))
  have mem : { transition with state := transition.state.erase processId } ∈
      (task.transitions second other).map fun transition =>
        { transition with state := transition.state.erase processId } := by
    rw [← lists]; exact List.mem_map_of_mem possible
  obtain ⟨moved, possible', same⟩ := List.mem_map.mp mem
  cases moved; cases transition
  simp only [Transition.mk.injEq] at same
  obtain ⟨rfl, stateEq, rfl, rfl, -, rfl⟩ := same
  exact ⟨_, possible', rfl, rfl, rfl, rfl, stateEq⟩

/-- A timer step from a state that agrees but for what a process keeps has a
step that agrees, with the same event. -/
private theorem timer_of_erase {first second next : State} {processId : PID} {event : Event}
    (equal : second.erase processId = first.erase processId)
    (possible : (event, next) ∈ first.timerSteps) :
    ∃ next', (event, next') ∈ second.timerSteps ∧ next'.erase processId = next.erase processId := by
  have lists := (erase_timerSteps (state := first) (processId := processId)).symm.trans
    ((congrArg State.timerSteps equal).symm.trans erase_timerSteps)
  have mem : (event, next.erase processId) ∈ second.timerSteps.map fun (event, next) =>
      (event, next.erase processId) := by
    rw [← lists]; exact List.mem_map_of_mem (f := fun (event, next) => (event, next.erase processId))
      possible
  obtain ⟨⟨event', next'⟩, possible', same⟩ := List.mem_map.mp mem
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, same⟩ := same
  exact ⟨next', possible', same⟩

/-! ### Reading the environment first -/

/-- The read of a process about to read its environment, from any state where
it reads the same and has no pending signal. -/
private theorem read_transitions {state other : State} {processId : PID} {β : Type}
    {read : Environment → Result β} {finish : Except Exception β → Option (Except Exception α)}
    (pdict : (other.process processId).pdict = (state.process processId).pdict)
    (refCounter : (other.process processId).refCounter = (state.process processId).refCounter)
    (signal : (other.process processId).signal = none) :
    (⟨.get read, finish⟩ : Task α).transitions other processId =
      [{ event := .internal processId, state := other
         tasks := [(processId, ⟨read (state.view processId), finish⟩)] }] := by
  have view : other.view processId = state.view processId := by
    simp only [State.view, pdict, refCounter]
  simp [Task.transitions, signal, view]

/-- A process with a pending signal exits, whatever it was about to do. -/
private theorem signaled_transitions {state : State} {processId : PID} {reason : Term}
    {β : Type} {first second : Result β} {finish : Except Exception β → Option (Except Exception α)}
    (signal : (state.process processId).signal = some reason) :
    (⟨first, finish⟩ : Task α).transitions state processId =
      (⟨second, finish⟩ : Task α).transitions state processId := by
  simp [Task.transitions, signal]

/-- A configuration where some process can step is not terminal. -/
private theorem not_terminal {first next : Config α} {event : Event} {outcome : Outcome α}
    (step : Step first event next) (terminal : Terminal first outcome) : False := by
  have := step.mem_successors
  rw [terminal.successors_eq_nil] at this
  simp at this

/-- Two splits of a list around elements, the first one earlier. -/
private theorem split_order {before after before' after' : List γ} {item item' : γ}
    (equal : before ++ item :: after = before' ++ item' :: after') :
    (before = before' ∧ item = item' ∧ after = after') ∨
    (∃ middle, before' = before ++ item :: middle ∧ after = middle ++ item' :: after') ∨
    (∃ middle, before = before' ++ item' :: middle ∧ after' = middle ++ item :: after) := by
  rcases List.append_eq_append_iff.mp equal with ⟨extra, rfl, rest⟩ | ⟨extra, rfl, rest⟩
  · cases extra with
    | nil => simp_all
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact .inr (.inl ⟨tail, rfl, rfl⟩)
  · cases extra with
    | nil => simp_all
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact .inr (.inr ⟨tail, rfl, rfl⟩)

private theorem pairwise_between {relation : γ → γ → Prop} {before middle after : List γ}
    {first second : γ}
    (pairwise : (before ++ first :: middle ++ second :: after).Pairwise relation) :
    relation first second := by
  rw [List.append_assoc, List.pairwise_append, List.cons_append, List.pairwise_cons] at pairwise
  exact pairwise.2.1.1 second (by simp)

/-- A step of another process keeps what a process reads, its pending signal,
and its place among the processes. -/
private theorem other_step {state : State} {before after before' after' : List (PID × Task α)}
    {processId other : PID} {task task' : Task α} {transition : Transition α}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state (before ++ (processId, task) :: after) finished exhausted))
    (split : before ++ (processId, task) :: after = before' ++ (other, task') :: after')
    (ne : before ≠ before')
    (possible : transition ∈ task'.transitions state other) :
    Keeps processId state transition.state ∧
      ((∃ middle, before' = before ++ (processId, task) :: middle ∧
          after = middle ++ (other, task') :: after') ∨
        (∃ middle, before = before' ++ (other, task') :: middle ∧
          after' = middle ++ (processId, task) :: after)) := by
  obtain ⟨distinct, fresh, -, -⟩ := wellformed
  have order := split_order split
  rcases order with ⟨same, -, -⟩ | later | earlier
  · exact absurd same ne
  all_goals refine ⟨?_, by first | exact .inl later | exact .inr earlier⟩
  all_goals
    obtain ⟨frame, -, -⟩ := transition_frame possible
    obtain ⟨-, -, -, spawned⟩ := transition_tasks possible
    have otherMem : (other, task') ∈ before ++ (processId, task) :: after := by
      rw [split]; simp
  · obtain ⟨middle, rfl, rfl⟩ := later
    have ne : processId ≠ other :=
      pairwise_between (relation := fun first second : PID × Task α => first.1 ≠ second.1)
        (first := (processId, task)) (second := (other, task')) (by simpa using distinct)
    refine frame processId ne fun child spawn equal => ?_
    have := fresh (other, task') otherMem (processId, task) (by simp) _ [] (by
      rw [equal, (spawned child spawn).1])
    dsimp only at this
    omega
  · obtain ⟨middle, rfl, rfl⟩ := earlier
    have ne : other ≠ processId :=
      pairwise_between (relation := fun first second : PID × Task α => first.1 ≠ second.1)
        (first := (other, task')) (second := (processId, task)) (by simpa using distinct)
    refine frame processId (Ne.symm ne) fun child spawn equal => ?_
    have := fresh (other, task') otherMem (processId, task) (by simp) _ [] (by
      rw [equal, (spawned child spawn).1])
    dsimp only at this
    omega

/-- Configurations that differ only in what a process with a pending exit
signal was about to do. It exits the same way from both. -/
private def Twins (processId : PID) : Config α → Config α → Prop
  | .running state tasks finished exhausted, .running state' tasks' finished' exhausted' =>
      state' = state ∧ finished' = finished ∧ exhausted' = exhausted ∧
      (state.process processId).signal.isSome ∧
      ∃ before after, ∃ β, ∃ finish : Except Exception β → Option (Except Exception α),
        ∃ first second : Result β,
          tasks = before ++ (processId, ⟨first, finish⟩) :: after ∧
          tasks' = before ++ (processId, ⟨second, finish⟩) :: after
  | _, _ => False

/-- Twins reach the same terminal configurations. -/
private theorem twins_run {processId : PID} {first last : Config α} {events : List Event}
    {outcome : Outcome α} (run : Run first events last) (terminal : Terminal last outcome) :
    ∀ {other}, Wellformed first → Twins processId first other →
      ∃ events', Run other events' last := by
  induction run with
  | @refl config =>
    intro other _ twins
    exfalso
    rcases other with _ | ⟨state', tasks', finished', exhausted'⟩ <;>
      rcases config with _ | ⟨state, tasks, finished, exhausted⟩ <;>
      simp only [Twins] at twins
    obtain ⟨-, -, -, pending, before, after, β, finish, computation, -, split, -⟩ := twins
    obtain ⟨reason, signal⟩ := Option.isSome_iff_exists.mp pending
    refine not_terminal (Step.run (transition :=
      { event := .exit processId reason, state := state.terminate processId reason, tasks := []
        finished := (finish (.error (.exit reason))).map (·, state.view processId) })
      split ?_) terminal
    simp [Task.transitions, signal]
  | step step rest ih =>
    intro other wellformed twins
    rcases other with _ | ⟨state', tasks', finished', exhausted'⟩
    · cases step <;> simp [Twins] at twins
    cases step with
    | get | set | enter => simp [Twins] at twins
    | @timer _ next state tasks finished exhausted possible =>
      -- A timer steps the same way from both.
      obtain ⟨rfl, rfl, rfl, pending, before, after, β, finish, computation, computation',
        split, rfl⟩ := twins
      obtain ⟨events', run'⟩ := ih terminal (Step.wellformed (.timer possible) wellformed)
        (other := .running next (before ++ (processId, ⟨computation', finish⟩) :: after) finished'
          exhausted')
        ⟨rfl, rfl, rfl, (timerSteps_keeps possible processId).1.process.2.2.2.1 pending, before,
          after, β, finish, computation, computation', split, rfl⟩
      exact ⟨_, .step (.timer possible) run'⟩
    | @run tasks before' stepping task' after' transition state finished exhausted split'
        possible =>
      obtain ⟨rfl, rfl, rfl, pending, before, after, β, finish, computation, computation',
        split, rfl⟩ := twins
      subst split
      by_cases same : before = before'
      · -- The process with the pending signal exits, the same way from its twin.
        subst same
        have equal := List.append_cancel_left split'
        simp only [List.cons.injEq, Prod.mk.injEq] at equal
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
        obtain ⟨reason, signal⟩ := Option.isSome_iff_exists.mp pending
        rw [signaled_transitions (second := computation') signal] at possible
        exact ⟨_, .step (Step.run rfl possible) rest⟩
      · -- Another process steps the same way from both.
        obtain ⟨kept, order⟩ := other_step wellformed split' same possible
        have pending' : (transition.state.process processId).signal.isSome :=
          kept.process.2.2.2.1 pending
        have wellformed' := Step.wellformed (.run split' possible) wellformed
        rcases order with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
        · obtain ⟨events', run'⟩ := ih terminal wellformed'
            (other := transition.apply (before ++ (processId, ⟨computation', finish⟩) :: middle)
              after' finished' exhausted')
            ⟨rfl, rfl, rfl, pending', before, middle ++ transition.tasks ++ after', β, finish,
              computation, computation', by simp, by simp⟩
          exact ⟨_, .step (Step.run (by simp) possible) run'⟩
        · obtain ⟨events', run'⟩ := ih terminal wellformed'
            (other := transition.apply before' (middle ++ (processId, ⟨computation', finish⟩) :: after)
              finished' exhausted')
            ⟨rfl, rfl, rfl, pending', before' ++ transition.tasks ++ middle, after, β, finish,
              computation, computation', by simp, by simp⟩
          exact ⟨_, .step (Step.run (by simp) possible) run'⟩

/-- Every run where a process is about to read its environment can read first,
reaching the same terminal configuration. -/
private theorem read_first {first last : Config α} {events : List Event} {outcome : Outcome α}
    (run : Run first events last) (terminal : Terminal last outcome) :
    ∀ {state tasks finished exhausted before after processId β}
      {read : Environment → Result β} {finish : Except Exception β → Option (Except Exception α)},
      first = .running state tasks finished exhausted → Wellformed first →
      tasks = before ++ (processId, ⟨.get read, finish⟩) :: after →
      (state.process processId).signal = none →
      ∃ events', Run (Config.running state
        (before ++ [(processId, ⟨read (state.view processId), finish⟩)] ++ after) finished exhausted)
        events' last := by
  induction run with
  | @refl config =>
    intro state tasks finished exhausted before after processId β read finish equal _ split signal
    subst equal
    let readStep : Transition α :=
      { event := .internal processId, state := state
        tasks := [(processId, ⟨read (state.view processId), finish⟩)] }
    refine (not_terminal (Step.run (transition := readStep) split ?_) terminal).elim
    rw [read_transitions rfl rfl signal]
    exact List.mem_singleton_self _
  | step step rest ih =>
    intro state tasks finished exhausted before after processId β read finish equal wellformed split
      signal
    subst equal
    cases step with
    | @timer _ next state tasks finished exhausted possible =>
      -- A timer keeps what the process reads, and the read follows it.
      obtain ⟨kept, -, same⟩ := timerSteps_keeps possible processId
      obtain ⟨events', run'⟩ := ih terminal (state := next) (tasks := tasks) (finished := finished)
        (exhausted := exhausted) (before := before) (after := after) (read := read)
        (finish := finish) rfl (Step.wellformed (.timer possible) wellformed) split
        (by rw [same, signal])
      have view : next.view processId = state.view processId := by
        simp only [State.view, kept.process.1, kept.process.2.1]
      exact ⟨_, .step (.timer possible) (by simpa [view] using run')⟩
    | @run tasks before' stepping task' after' transition state finished exhausted split'
        possible =>
      subst split
      by_cases same : before = before'
      · -- The reading process steps: it reads.
        subst same
        have equal := List.append_cancel_left split'
        simp only [List.cons.injEq, Prod.mk.injEq] at equal
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
        rw [read_transitions rfl rfl signal, List.mem_singleton] at possible
        subst possible
        exact ⟨_, by simpa [Transition.apply] using rest⟩
      · -- Another process steps, and the read follows it.
        obtain ⟨kept, order⟩ := other_step wellformed split' same possible
        have wellformed' := Step.wellformed (.run split' possible) wellformed
        cases signal' : (transition.state.process processId).signal with
        | none =>
          rcases order with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
          · obtain ⟨events', run'⟩ := ih terminal (state := transition.state)
              (tasks := before ++ (processId, ⟨.get read, finish⟩) ::
                (middle ++ transition.tasks ++ after'))
              (finished := transition.finished.orElse fun _ => finished)
              (exhausted := exhausted || transition.exhausted)
              (before := before) (after := middle ++ transition.tasks ++ after')
              (read := read) (finish := finish) (by simp [Transition.apply]) wellformed'
              rfl signal'
            refine ⟨transition.event :: events', .step (Step.run (before := before ++ (processId, ⟨read (state.view processId),
              finish⟩) :: middle) (after := after') (by simp) possible) ?_⟩
            have view : transition.state.view processId = state.view processId := by
              simp only [State.view, kept.process.1, kept.process.2.1]
            simpa [Transition.apply, view] using run'
          · obtain ⟨events', run'⟩ := ih terminal (state := transition.state)
              (tasks := before' ++ transition.tasks ++ middle ++
                (processId, ⟨.get read, finish⟩) :: after)
              (finished := transition.finished.orElse fun _ => finished)
              (exhausted := exhausted || transition.exhausted)
              (before := before' ++ transition.tasks ++ middle) (after := after)
              (read := read) (finish := finish) (by simp [Transition.apply]) wellformed'
              rfl signal'
            refine ⟨transition.event :: events', .step (Step.run (before := before') (after := middle ++
              (processId, ⟨read (state.view processId), finish⟩) :: after) (by simp) possible) ?_⟩
            have view : transition.state.view processId = state.view processId := by
              simp only [State.view, kept.process.1, kept.process.2.1]
            simpa [Transition.apply, view] using run'
        | some reason =>
          -- The process now exits, whether or not it read first.
          rcases order with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
          · obtain ⟨events', run'⟩ := twins_run rest terminal wellformed'
              (processId := processId)
              (other := transition.apply (before ++ (processId, ⟨read (state.view processId),
                finish⟩) :: middle) after' finished exhausted)
              ⟨rfl, rfl, rfl, by simp [signal'], before, middle ++ transition.tasks ++ after', β,
                finish, .get read, read (state.view processId), by simp, by simp⟩
            refine ⟨transition.event :: events', .step (Step.run (before := before ++ (processId, ⟨read (state.view processId),
              finish⟩) :: middle) (after := after') (by simp) possible) ?_⟩
            simpa using run'
          · obtain ⟨events', run'⟩ := twins_run rest terminal wellformed'
              (processId := processId)
              (other := transition.apply before' (middle ++ (processId, ⟨read (state.view processId),
                finish⟩) :: after) finished exhausted)
              ⟨rfl, rfl, rfl, by simp [signal'], before' ++ transition.tasks ++ middle, after, β,
                finish, .get read, read (state.view processId), by simp, by simp⟩
            refine ⟨transition.event :: events', .step (Step.run (before := before') (after := middle ++
              (processId, ⟨read (state.view processId), finish⟩) :: after) (by simp) possible) ?_⟩
            simpa using run'

/-! ### Writing the environment first -/

/-- Another process is distinct, and does not spawn a process with the same PID. -/
private theorem other_distinct {state : State} {before after before' after' : List (PID × Task α)}
    {processId other : PID} {task task' : Task α}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state (before ++ (processId, task) :: after) finished exhausted))
    (split : before ++ (processId, task) :: after = before' ++ (other, task') :: after')
    (ne : before ≠ before') :
    other ≠ processId ∧ other ++ [(state.process other).children + 1] ≠ processId := by
  obtain ⟨distinct, fresh, -, -⟩ := wellformed
  have member : (other, task') ∈ before ++ (processId, task) :: after := by rw [split]; simp
  refine ⟨fun equal => ?_, fun equal => ?_⟩
  · rcases split_order split with ⟨same, -, -⟩ | ⟨middle, -, rfl⟩ | ⟨middle, rfl, -⟩
    · exact ne same
    · exact pairwise_between (relation := fun first second : PID × Task α => first.1 ≠ second.1)
        (first := (processId, task)) (second := (other, task')) (by simpa using distinct) equal.symm
    · exact pairwise_between (relation := fun first second : PID × Task α => first.1 ≠ second.1)
        (first := (other, task')) (second := (processId, task)) (by simpa using distinct) equal
  · have := fresh (other, task') member (processId, task) (by simp) _ [] equal.symm
    dsimp only at this
    omega

/-- Configurations that differ only in the environment their root returned
with reach terminal configurations with the same outcomes. -/
private theorem run_finished {first last : Config α} {events : List Event} {outcome : Outcome α}
    (run : Run first events last) (terminal : Terminal last outcome) :
    ∀ {state tasks finished finished' exhausted},
      first = .running state tasks finished exhausted →
      finished'.map Prod.fst = finished.map Prod.fst →
      ∃ events' last', Run (Config.running state tasks finished' exhausted) events' last' ∧
        Terminal last' outcome := by
  induction run with
  | @refl config =>
    intro state tasks finished finished' exhausted equal same
    subst equal
    refine ⟨[], _, .refl, ?_⟩
    cases terminal with
    | exhausted blocked idle => exact .exhausted blocked idle
    | returned idle =>
      rcases finished' with _ | ⟨result, env⟩ <;> simp at same
      subst same; exact .returned idle
    | raised idle =>
      rcases finished' with _ | ⟨result, env⟩ <;> simp at same
      subst same; exact .raised idle
    | deadlock blocked pending idle =>
      exact .deadlock blocked (fun nil => by simpa [pending nil] using same) idle
  | step step rest ih =>
    intro state tasks finished finished' exhausted equal same
    subst equal
    cases step with
    | @run _ _ _ _ _ transition _ _ _ split possible =>
      obtain ⟨events', last', run', terminal'⟩ := ih terminal (state := transition.state)
        (finished' := transition.finished.orElse fun _ => finished') rfl
        (by cases transition.finished <;> simp [same])
      exact ⟨_, last', .step (.run split possible) run', terminal'⟩
    | timer possible =>
      obtain ⟨events', last', run', terminal'⟩ := ih terminal (finished' := finished') rfl same
      exact ⟨_, last', .step (.timer possible) run', terminal'⟩

/-- Erasing keeps pending signals. -/
private theorem signal_of_erase {first second : State} {processId : PID}
    (equal : second.erase processId = first.erase processId) :
    (second.process processId).signal = (first.process processId).signal := by
  rw [← (erase_process_fields (state := second) (processId := processId)
      (other := processId)).2.2.2.2.2.2.1,
    ← (erase_process_fields (state := first) (processId := processId)
      (other := processId)).2.2.2.2.2.2.1, equal]

/-- Configurations that differ in what a process with a pending exit signal was
about to do, and in what it keeps, reach terminal configurations with the same
outcomes: the process exits the same way from both. -/
private theorem run_signaled {first last : Config α} {events : List Event} {outcome : Outcome α}
    (run : Run first events last) (terminal : Terminal last outcome) :
    ∀ {state state' : State} {before after : List (PID × Task α)} {processId : PID} {β : Type}
      {computation computation' : Result β} {finish : Except Exception β → Option (Except Exception α)}
      {finished : Option (Except Exception α × Environment)} {exhausted : Bool},
      first = .running state (before ++ (processId, ⟨computation, finish⟩) :: after) finished
        exhausted →
      Wellformed first → (state.process processId).signal.isSome →
      state'.erase processId = state.erase processId →
      ∃ events' last', Run (Config.running state' (before ++ (processId, ⟨computation', finish⟩) ::
        after) finished exhausted) events' last' ∧ Terminal last' outcome := by
  induction run with
  | @refl config =>
    intro state state' before after processId β computation computation' finish finished exhausted
      equal _ pending _
    subst equal
    obtain ⟨reason, signal⟩ := Option.isSome_iff_exists.mp pending
    exact (not_terminal (Step.run (transition :=
      { event := .exit processId reason, state := state.terminate processId reason, tasks := []
        finished := (finish (.error (.exit reason))).map (·, state.view processId) })
      rfl (by simp [Task.transitions, signal])) terminal).elim
  | step step rest ih =>
    intro state state' before after processId β computation computation' finish finished exhausted
      equal wellformed pending same
    subst equal
    cases step with
    | @run tasks before' stepping task' after' transition _ _ _ split' possible =>
      by_cases sameProcess : before = before'
      · -- The process exits the same way from both, forgetting what it kept.
        subst sameProcess
        have equal := List.append_cancel_left split'
        simp only [List.cons.injEq, Prod.mk.injEq] at equal
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
        obtain ⟨reason, signal⟩ := Option.isSome_iff_exists.mp pending
        simp only [Task.transitions, signal, List.mem_singleton] at possible
        subst possible
        have terminated : state'.terminate processId reason = state.terminate processId reason := by
          rw [← terminate_erase, same, terminate_erase]
        obtain ⟨events', last', run', terminal'⟩ := run_finished rest terminal
          (state := state.terminate processId reason) (tasks := before ++ after)
          (finished := ((finish (.error (.exit reason))).map (·, state.view processId)).orElse
            fun _ => finished) (exhausted := exhausted)
          (finished' := ((finish (.error (.exit reason))).map (·, state'.view processId)).orElse
            fun _ => finished) (by simp [Transition.apply])
          (by cases finish (.error (.exit reason)) <;> simp [Option.orElse])
        refine ⟨.exit processId reason :: events', last', .step (Step.run (transition :=
          { event := .exit processId reason, state := state'.terminate processId reason, tasks := []
            finished := (finish (.error (.exit reason))).map (·, state'.view processId) })
          rfl (by simp [Task.transitions, signal_of_erase same, signal])) ?_, terminal'⟩
        simpa [Transition.apply, terminated] using run'
      · -- Another process steps the same way from both.
        obtain ⟨kept, order⟩ := other_step wellformed split' sameProcess possible
        obtain ⟨ne, fresh⟩ := other_distinct wellformed split' sameProcess
        obtain ⟨moved, possible', event, tasks, finishedEq, exhaustedEq, erased⟩ :=
          transition_of_erase ne fresh same possible
        have wellformed' := Step.wellformed (.run split' possible) wellformed
        have pending' := kept.process.2.2.2.1 pending
        rcases order with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
        · obtain ⟨events', last', run', terminal'⟩ := ih terminal (state := transition.state)
            (state' := moved.state) (before := before) (after := middle ++ transition.tasks ++ after')
            (computation := computation) (computation' := computation') (finish := finish)
            (finished := transition.finished.orElse fun _ => finished)
            (exhausted := exhausted || transition.exhausted)
            (by simp [Transition.apply]) wellformed' pending' erased
          refine ⟨moved.event :: events', last', .step (Step.run (before := before ++ (processId, ⟨computation', finish⟩) ::
            middle) (after := after') (by simp) possible') ?_, terminal'⟩
          simpa [Transition.apply, tasks, finishedEq, exhaustedEq] using run'
        · obtain ⟨events', last', run', terminal'⟩ := ih terminal (state := transition.state)
            (state' := moved.state) (before := before' ++ transition.tasks ++ middle) (after := after)
            (computation := computation) (computation' := computation') (finish := finish)
            (finished := transition.finished.orElse fun _ => finished)
            (exhausted := exhausted || transition.exhausted)
            (by simp [Transition.apply]) wellformed' pending' erased
          refine ⟨moved.event :: events', last', .step (Step.run (before := before') (after := middle ++
            (processId, ⟨computation', finish⟩) :: after) (by simp) possible') ?_, terminal'⟩
          simpa [Transition.apply, tasks, finishedEq, exhaustedEq] using run'
    | timer possible =>
      obtain ⟨next', possible', erased⟩ := timer_of_erase same possible
      obtain ⟨-, -, signal⟩ := timerSteps_keeps possible processId
      obtain ⟨events', last', run', terminal'⟩ := ih terminal rfl
        (Step.wellformed (.timer possible) wellformed) (by rw [signal]; exact pending) erased
      exact ⟨_, last', .step (.timer possible') run', terminal'⟩

/-- What a process stores is what it then keeps. -/
private theorem store_process {state : State} {processId : PID} {env : Environment} :
    ((state.store processId env).process processId).pdict = env.pdict ∧
      ((state.store processId env).process processId).refCounter = env.refCounter := by
  simp [State.store, State.process, State.update]

/-- Every run where a process is about to replace its environment can replace
it first, reaching a terminal configuration with the same outcome. -/
private theorem write_first {first last : Config α} {events : List Event} {outcome : Outcome α}
    (run : Run first events last) (terminal : Terminal last outcome) :
    ∀ {state : State} {before after : List (PID × Task α)} {processId : PID} {β : Type}
      {updated : Environment} {next : Result β}
      {finish : Except Exception β → Option (Except Exception α)}
      {finished : Option (Except Exception α × Environment)} {exhausted : Bool},
      first = .running state (before ++ (processId, ⟨.set updated next, finish⟩) :: after) finished
        exhausted →
      Wellformed first → (state.process processId).signal = none →
      ∃ events' last', Run (Config.running (state.store processId updated)
        (before ++ (processId, ⟨next, finish⟩) :: after) finished exhausted) events' last' ∧
        Terminal last' outcome := by
  induction run with
  | @refl config =>
    intro state before after processId β updated next finish finished exhausted equal _ signal
    subst equal
    exact (not_terminal (Step.run (transition :=
      { event := .internal processId, state := state.store processId updated
        tasks := [(processId, ⟨next, finish⟩)] })
      rfl (by simp [Task.transitions, signal])) terminal).elim
  | step step rest ih =>
    intro state before after processId β updated next finish finished exhausted equal wellformed
      signal
    subst equal
    have live : (state.processes processId).isSome :=
      wellformed.2.2.1 (processId, ⟨.set updated next, finish⟩) (by simp)
    cases step with
    | @run tasks before' stepping task' after' transition _ _ _ split' possible =>
      by_cases sameProcess : before = before'
      · -- The writing process steps: it writes.
        subst sameProcess
        have equal := List.append_cancel_left split'
        simp only [List.cons.injEq, Prod.mk.injEq] at equal
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
        simp only [Task.transitions, signal, List.mem_singleton] at possible
        subst possible
        exact ⟨_, _, by simpa [Transition.apply] using rest, terminal⟩
      · obtain ⟨kept, order⟩ := other_step wellformed split' sameProcess possible
        obtain ⟨ne, fresh⟩ := other_distinct wellformed split' sameProcess
        obtain ⟨moved, possible', event, tasks, finishedEq, exhaustedEq, erased⟩ :=
          transition_of_erase (second := state.store processId updated) ne fresh
            (erase_store live) possible
        -- The step keeps what the writing process keeps, from either state.
        have keptWritten : Keeps processId (state.store processId updated) moved.state := by
          obtain ⟨frame, -, -⟩ := transition_frame possible'
          obtain ⟨-, -, -, spawned⟩ := transition_tasks possible'
          refine frame processId (Ne.symm ne) fun child spawn equal => fresh ?_
          rw [equal, (spawned child (event ▸ spawn)).1]
          simp [State.store, State.process, State.update, ne]
        have wellformed' := Step.wellformed (.run split' possible) wellformed
        cases signal' : (transition.state.process processId).signal with
        | none =>
          have stored : moved.state = transition.state.store processId updated :=
            eq_store_of_erase erased (kept.live live)
              (keptWritten.process.1.trans store_process.1)
              (keptWritten.process.2.1.trans store_process.2)
          rcases order with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
          · obtain ⟨events', last', run', terminal'⟩ := ih terminal (state := transition.state)
              (before := before) (after := middle ++ transition.tasks ++ after')
              (updated := updated) (next := next) (finish := finish)
              (finished := transition.finished.orElse fun _ => finished)
              (exhausted := exhausted || transition.exhausted)
              (by simp [Transition.apply]) wellformed' signal'
            refine ⟨moved.event :: events', last', .step (Step.run (before := before ++
              (processId, ⟨next, finish⟩) :: middle) (after := after') (by simp) possible') ?_,
              terminal'⟩
            simpa [Transition.apply, tasks, finishedEq, exhaustedEq, stored] using run'
          · obtain ⟨events', last', run', terminal'⟩ := ih terminal (state := transition.state)
              (before := before' ++ transition.tasks ++ middle) (after := after)
              (updated := updated) (next := next) (finish := finish)
              (finished := transition.finished.orElse fun _ => finished)
              (exhausted := exhausted || transition.exhausted)
              (by simp [Transition.apply]) wellformed' signal'
            refine ⟨moved.event :: events', last', .step (Step.run (before := before')
              (after := middle ++ (processId, ⟨next, finish⟩) :: after) (by simp) possible') ?_,
              terminal'⟩
            simpa [Transition.apply, tasks, finishedEq, exhaustedEq, stored] using run'
        | some reason =>
          -- The process now exits, whether or not it wrote first.
          rcases order with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
          · obtain ⟨events', last', run', terminal'⟩ := run_signaled rest terminal
              (state := transition.state) (state' := moved.state) (before := before)
              (after := middle ++ transition.tasks ++ after') (computation := .set updated next)
              (computation' := next) (finish := finish)
              (finished := transition.finished.orElse fun _ => finished)
              (exhausted := exhausted || transition.exhausted)
              (by simp [Transition.apply]) wellformed' (by simp [signal']) erased
            refine ⟨moved.event :: events', last', .step (Step.run (before := before ++
              (processId, ⟨next, finish⟩) :: middle) (after := after') (by simp) possible') ?_,
              terminal'⟩
            simpa [Transition.apply, tasks, finishedEq, exhaustedEq] using run'
          · obtain ⟨events', last', run', terminal'⟩ := run_signaled rest terminal
              (state := transition.state) (state' := moved.state)
              (before := before' ++ transition.tasks ++ middle) (after := after)
              (computation := .set updated next) (computation' := next) (finish := finish)
              (finished := transition.finished.orElse fun _ => finished)
              (exhausted := exhausted || transition.exhausted)
              (by simp [Transition.apply]) wellformed' (by simp [signal']) erased
            refine ⟨moved.event :: events', last', .step (Step.run (before := before')
              (after := middle ++ (processId, ⟨next, finish⟩) :: after) (by simp) possible') ?_,
              terminal'⟩
            simpa [Transition.apply, tasks, finishedEq, exhaustedEq] using run'
    | timer possible =>
      obtain ⟨next', possible', erased⟩ := timer_of_erase
        (second := state.store processId updated) (erase_store live) possible
      obtain ⟨kept, -, timerSignal⟩ := timerSteps_keeps possible processId
      obtain ⟨kept', -, -⟩ := timerSteps_keeps possible' processId
      have stored := eq_store_of_erase erased (kept.live live)
        (kept'.process.1.trans store_process.1) (kept'.process.2.1.trans store_process.2)
      obtain ⟨events', last', run', terminal'⟩ := ih terminal rfl
        (Step.wellformed (.timer possible) wellformed) (by rw [timerSignal]; exact signal)
      exact ⟨_ :: events', last', .step (.timer possible') (stored ▸ run'), terminal'⟩

/-! ### Receiving first

Other processes only append to the mailbox of a process, and never read it, so
taking a message that it is about to receive commutes with their steps. -/

/-- A record without one of its messages. -/
private def ProcessState.take (process : ProcessState) (index : Nat) : ProcessState :=
  { process with mailbox := process.mailbox.eraseIdx index }

/-- A state without one message of a process. -/
private def State.take (state : State) (processId : PID) (index : Nat) : State :=
  { state with processes := fun candidate =>
      if candidate = processId then (state.processes candidate).map (·.take index)
      else state.processes candidate }

@[simp] private theorem take_timers {state : State} {processId : PID} {index : Nat} :
    (state.take processId index).timers = state.timers := rfl

@[simp] private theorem take_elapsed {state : State} {processId : PID} {index : Nat} :
    (state.take processId index).elapsed = state.elapsed := rfl

private theorem take_processes {state : State} {processId candidate : PID} {index : Nat} :
    (state.take processId index).processes candidate =
      if candidate = processId then (state.processes candidate).map (·.take index)
      else state.processes candidate := rfl

private theorem take_process_ne {state : State} {processId other : PID} {index : Nat}
    (ne : other ≠ processId) : (state.take processId index).process other = state.process other := by
  simp [State.process, take_processes, ne]

/-- What a process reads does not include its mailbox. -/
private theorem take_view {state : State} {processId other : PID} {index : Nat} :
    (state.take processId index).view other = state.view other := by
  by_cases same : other = processId
  · subst same
    simp only [State.view, State.process, take_processes, ite_true]
    cases state.processes other <;> rfl
  · simp [State.view, take_process_ne same]

/-- Taking a message keeps every field other than the mailbox. -/
private theorem take_process_fields {state : State} {processId other : PID} {index : Nat} :
    ((state.take processId index).process other).links = (state.process other).links ∧
    ((state.take processId index).process other).monitors = (state.process other).monitors ∧
    ((state.take processId index).process other).monitoring = (state.process other).monitoring ∧
    ((state.take processId index).process other).aliases = (state.process other).aliases ∧
    ((state.take processId index).process other).trapExit = (state.process other).trapExit ∧
    ((state.take processId index).process other).signal = (state.process other).signal ∧
    ((state.take processId index).process other).children = (state.process other).children ∧
    ((state.take processId index).process other).refCounter = (state.process other).refCounter := by
  by_cases equal : other = processId
  · subst equal
    simp only [State.process, take_processes, ite_true]
    cases state.processes other <;> simp [ProcessState.take]
  · simp [take_process_ne equal]

private theorem take_isSome {state : State} {processId other : PID} {index : Nat} :
    ((state.take processId index).processes other).isSome = (state.processes other).isSome := by
  simp only [take_processes]; split <;> simp

private theorem take_processes_none {state : State} {processId target : PID} {index : Nat} :
    (state.take processId index).processes target = none ↔ state.processes target = none := by
  rw [take_processes]; split <;> simp

private theorem take_processes_some {state : State} {processId target : PID} {index : Nat}
    {process : ProcessState} (found : state.processes target = some process) :
    ∃ taken, (state.take processId index).processes target = some taken := by
  rw [take_processes]; split <;> simp [found]

private theorem take_update_ne {state : State} {processId other : PID} {index : Nat}
    {process : Option ProcessState} (ne : other ≠ processId) :
    (state.update other process).take processId index =
      (state.take processId index).update other process := by
  refine State.ext' rfl (by simp) fun candidate => ?_
  simp only [take_processes, State.update]
  by_cases first : candidate = other <;> by_cases second : candidate = processId <;> simp_all

private theorem take_modify {state : State} {processId other : PID} {index : Nat}
    {change : ProcessState → ProcessState}
    (oblivious : ∀ process, (change process).take index = change (process.take index)) :
    (state.modify other change).take processId index =
      (state.take processId index).modify other change := by
  refine State.ext' (by simp) (by simp) fun candidate => ?_
  unfold State.modify
  rw [take_processes]
  by_cases same : other = processId
  · subst same
    cases found : state.processes other with
    | none => simp [take_processes, found]
    | some process =>
      simp only [take_processes, found, ite_true, Option.map_some, State.update]
      by_cases equal : candidate = other <;> simp_all [oblivious process]
  · cases found : state.processes other with
    | none => simp [take_processes, found, same]
    | some process =>
      simp only [take_processes, found, same, ite_false, State.update]
      by_cases equal : candidate = other <;> by_cases equal' : candidate = processId <;> simp_all

private theorem take_modify_ne {state : State} {processId other : PID} {index : Nat}
    {change : ProcessState → ProcessState} (ne : other ≠ processId) :
    (state.modify other change).take processId index =
      (state.take processId index).modify other change := by
  refine State.ext' (by simp) (by simp) fun candidate => ?_
  unfold State.modify
  cases found : state.processes other with
  | none => simp [take_processes, found, ne]
  | some process =>
    simp only [take_processes, found, ne, ite_false, State.update]
    by_cases equal : candidate = other <;> by_cases equal' : candidate = processId <;> simp_all

/-- The message is still in the mailbox. -/
private def Holds (state : State) (processId : PID) (index : Nat) : Prop :=
  index < (state.process processId).mailbox.length

/-- Steps of other processes keep the message in the mailbox. -/
private theorem Keeps.holds {state after : State} {processId : PID} {index : Nat}
    (kept : Keeps processId state after) (holds : Holds state processId index) :
    Holds after processId index :=
  Nat.lt_of_lt_of_le holds kept.process.2.2.2.2.length_le

private theorem take_deliver {state : State} {processId other : PID} {index : Nat}
    {message : Term} (holds : Holds state processId index) :
    (state.deliver other message).take processId index =
      (state.take processId index).deliver other message := by
  have : state.deliver other message = state.modify other fun process =>
      { process with mailbox := process.mailbox ++ [message] } := by
    unfold State.deliver State.modify; split <;> rfl
  have : (state.take processId index).deliver other message = (state.take processId index).modify
      other fun process => { process with mailbox := process.mailbox ++ [message] } := by
    unfold State.deliver State.modify; split <;> rfl
  rw [‹state.deliver other message = _›, this]
  by_cases same : other = processId
  · subst same
    refine State.ext' (by simp) (by simp) fun candidate => ?_
    unfold State.modify
    simp only [Holds, State.process] at holds
    cases found : state.processes other with
    | none => simp [found] at holds
    | some process =>
      simp only [found, Option.getD_some] at holds
      simp only [take_processes, found, ite_true, Option.map_some, State.update]
      by_cases equal : candidate = other <;>
        simp_all [ProcessState.take, List.eraseIdx_append_of_lt_length holds]
  · exact take_modify_ne same

private theorem take_kill {state : State} {processId other : PID} {index : Nat} {reason : Term} :
    (state.kill other reason).take processId index =
      (state.take processId index).kill other reason :=
  take_modify (by intro _; rfl)

private theorem take_signal {state : State} {processId target sender : PID} {index : Nat}
    {reason : Term} {untrappable : Bool} (holds : Holds state processId index) :
    (state.signal target sender reason untrappable).take processId index =
      (state.take processId index).signal target sender reason untrappable := by
  have trapExit := (take_process_fields (state := state) (processId := processId) (index := index)
    (other := target)).2.2.2.2.1
  unfold State.signal
  rw [trapExit]
  split
  · exact take_kill
  · split
    · exact take_deliver holds
    · split
      · rfl
      · exact take_kill

private theorem take_foldl {items : List γ} {step : State → γ → State} {processId : PID}
    {index : Nat}
    (each : ∀ state item, Holds state processId index →
      (step state item).take processId index = step (state.take processId index) item)
    (kept : ∀ state item, Keeps processId state (step state item))
    (state : State) (holds : Holds state processId index) :
    (items.foldl step state).take processId index = items.foldl step (state.take processId index) := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ ((kept state item).holds holds), each _ _ holds]

private theorem take_with_timers {state : State} {processId : PID} {index : Nat}
    {timers : List Timer} :
    ({ state with timers } : State).take processId index =
      { state.take processId index with timers } := rfl

private theorem take_terminate {state : State} {processId other : PID} {index : Nat} {reason : Term}
    (ne : other ≠ processId) (holds : Holds state processId index) :
    (state.terminate other reason).take processId index =
      (state.take processId index).terminate other reason := by
  have removed : Holds ({ state.update other none with
      timers := state.timers.filter (·.destination != other) } : State) processId index :=
    (keeps_update_ne (Ne.symm ne)).holds holds
  simp only [State.terminate, take_process_ne ne]
  rw [take_foldl (fun current item holds' => by
      rw [take_modify (by intro _; rfl), take_deliver holds'])
    (fun _ _ => by keeps_chain) _ (by
      refine keeps_foldl (fun current item => ?_) _ |>.holds removed
      keeps_chain)]
  rw [take_foldl (fun current item holds' => by
      rw [take_signal ((show Keeps processId current _ by keeps_chain).holds holds'),
        take_modify (by intro _; rfl)])
    (fun _ _ => by keeps_chain) _ removed]
  rw [take_with_timers, take_update_ne ne]
  rfl

private theorem take_monitor {state : State} {processId other target : PID} {index : Nat}
    {alias : Bool} (ne : other ≠ processId) (holds : Holds state processId index) :
    (state.take processId index).monitor other target alias =
      ((state.monitor other target alias).1,
        (state.monitor other target alias).2.take processId index) := by
  have counting : Holds (state.modify other fun process =>
      { process with refCounter := process.refCounter + 1 }) processId index :=
    (Keeps.modify (.inl (Ne.symm ne)) (Keeps.refl _ _)).holds holds
  simp only [State.monitor, take_process_ne ne]
  rw [← take_modify_ne (change := fun process =>
    { process with refCounter := process.refCounter + 1 }) ne]
  generalize (state.modify other fun process =>
    { process with refCounter := process.refCounter + 1 }) = counted at counting
  rw [take_processes]
  by_cases same : target = processId
  · subst same
    cases found : counted.processes target with
    | none => simp [take_deliver counting]
    | some watched =>
      simp only [ite_true, Option.map_some]
      rw [take_modify_ne ne, take_modify (by intro _; rfl)]
  · cases found : counted.processes target with
    | none => simp [same, take_deliver counting]
    | some watched =>
      simp only [same, ite_false]
      rw [take_modify_ne ne, take_modify (by intro _; rfl)]

private theorem take_request {state : State} {processId other : PID} {index : Nat}
    {query : Request} (ne : other ≠ processId) (holds : Holds state processId index) :
    (state.take processId index).request other query =
      ((state.request other query).1, (state.request other query).2.take processId index) := by
  cases query with
  | monitor target alias =>
    simp only [State.request, take_monitor ne holds]
  | demonitor reference flush =>
    simp only [State.request, take_process_ne ne]
    rw [take_modify_ne ne, take_foldl (fun current item _ => by
        obtain ⟨found, target⟩ := item
        dsimp only
        split
        · exact take_modify (by intro _; rfl)
        · rfl)
      (fun _ _ => by keeps_chain) _ holds]
  | link target =>
    simp only [State.request]
    split
    · rfl
    · cases found : state.processes target with
      | none =>
        simp only [take_processes_none.mpr found, take_process_ne ne]
        split
        · simp [take_deliver holds]
        · rfl
      | some process =>
        obtain ⟨taken, found'⟩ := take_processes_some (processId := processId) (index := index) found
        simp only [found']
        rw [take_modify (by intro _; rfl), take_modify_ne ne]
  | unlink target =>
    simp only [State.request]
    rw [take_modify (by intro _; rfl), take_modify_ne ne]
  | exit target reason =>
    simp only [State.request, take_process_ne ne]
    split
    · simp [take_kill]
    · simp [take_signal holds]
  | trapExit enabled =>
    simp only [State.request, take_process_ne ne, take_modify_ne ne]
  | alive target =>
    simp only [State.request]
    cases found : state.processes target with
    | none => simp [take_processes_none.mpr found]
    | some process =>
      obtain ⟨taken, found'⟩ := take_processes_some (processId := processId) (index := index) found
      simp [found']
  | sendAlias alias message =>
    simp only [State.request, (take_process_fields (state := state) (processId := processId)
      (index := index) (other := alias.dropLast)).2.2.2.1]
    split
    · simp [take_deliver holds]
    · rfl
  | startTimer destination message duration =>
    simp only [State.request, take_process_ne ne, ← take_modify_ne (change := fun process =>
      { process with refCounter := process.refCounter + 1 }) ne]
    generalize (state.modify other fun process =>
      { process with refCounter := process.refCounter + 1 }) = counted
    rw [take_isSome]
    split <;> rfl
  | cancelTimer reference =>
    simp only [State.request, take_timers, take_elapsed, take_process_ne ne]
    split
    · simp only [Prod.mk.injEq, true_and]
      exact (take_modify_ne (state := { state with
        timers := state.timers.filter (·.reference != reference) }) ne).symm
    · rfl

private theorem take_spawnWith {state : State} {processId other : PID} {index : Nat}
    {options : SpawnOptions} (ne : other ≠ processId)
    (fresh : other ++ [(state.process other).children + 1] ≠ processId)
    (holds : Holds state processId index) :
    (state.take processId index).spawnWith other options =
      ((state.spawnWith other options).1, (state.spawnWith other options).2.take processId index) := by
  obtain ⟨link, monitor⟩ := options
  have spawned : Holds ((state.update other (some { state.process other with
      children := (state.process other).children + 1 })).update
      (other ++ [(state.process other).children + 1]) (some {})) processId index :=
    ((keeps_update_ne (Ne.symm ne)).trans (keeps_update_ne (Ne.symm fresh))).holds holds
  simp only [State.spawnWith, State.spawn, take_process_ne ne]
  rw [← take_update_ne ne, ← take_update_ne fresh]
  cases link <;> cases monitor <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · rw [take_monitor ne spawned]
  · rw [← take_modify_ne ne, ← take_modify (by intro _; rfl)]
  · rw [← take_modify_ne ne, ← take_modify (by intro _; rfl),
      take_monitor ne ((show Keeps processId _ _ by keeps_chain).holds spawned)]

private theorem take_timerSteps {state : State} {processId : PID} {index : Nat}
    (holds : Holds state processId index) :
    (state.take processId index).timerSteps =
      state.timerSteps.map fun (event, next) => (event, next.take processId index) := by
  simp only [State.timerSteps, take_timers, List.map_map]
  apply List.map_congr_left
  intro timer _
  simp only [Function.comp_apply]
  split
  · rw [← take_deliver holds]; rfl
  · rfl

/-- Steps of other processes commute with taking a message of a process. -/
private theorem transitions_take {state : State} {processId other : PID} {index : Nat}
    {task : Task α} (ne : other ≠ processId)
    (fresh : other ++ [(state.process other).children + 1] ≠ processId)
    (holds : Holds state processId index) :
    task.transitions (state.take processId index) other =
      (task.transitions state other).map fun transition =>
        { transition with state := transition.state.take processId index } := by
  obtain ⟨computation, finish⟩ := task
  simp only [Task.transitions, take_view, take_process_ne ne]
  split
  · simp [take_terminate ne holds]
  · cases computation with
    | ok => simp [take_terminate ne holds]
    | error exception =>
      cases exception <;> simp [take_terminate ne holds, take_update_ne ne]
    | get => simp
    | set updated next =>
      simp [State.store, take_update_ne ne, take_process_ne ne]
    | schedule options child next =>
      simp only [take_spawnWith ne fresh holds, List.map_cons, List.map_nil]
    | send destination message next => simp [take_deliver holds]
    | receive timeout select next =>
      dsimp only
      split
      · simp [take_update_ne ne]
      · cases timeout <;> simp
    | request query next =>
      simp only [take_request ne holds]
      rfl

/-- Exiting forgets the messages of the process. -/
private theorem terminate_take {state : State} {processId : PID} {index : Nat} {reason : Term} :
    (state.take processId index).terminate processId reason = state.terminate processId reason := by
  have fields := take_process_fields (state := state) (processId := processId) (index := index)
    (other := processId)
  have removed : (state.take processId index).update processId none = state.update processId none := by
    refine State.ext' rfl (by simp) fun candidate => ?_
    simp only [take_processes, State.update]
    split <;> simp_all
  simp only [State.terminate, fields.1, fields.2.1, removed, take_timers]

/-- A step of another process has the same step once a message is taken. -/
private theorem transition_of_take {state : State} {processId other : PID} {index : Nat}
    {task : Task α} {transition : Transition α} (ne : other ≠ processId)
    (fresh : other ++ [(state.process other).children + 1] ≠ processId)
    (holds : Holds state processId index) (possible : transition ∈ task.transitions state other) :
    { transition with state := transition.state.take processId index } ∈
      task.transitions (state.take processId index) other := by
  rw [transitions_take ne fresh holds]
  exact List.mem_map_of_mem possible

/-- A timer step has the same step once a message is taken. -/
private theorem timer_of_take {state next : State} {processId : PID} {index : Nat} {event : Event}
    (holds : Holds state processId index) (possible : (event, next) ∈ state.timerSteps) :
    (event, next.take processId index) ∈ (state.take processId index).timerSteps := by
  rw [take_timerSteps holds]
  exact List.mem_map_of_mem (f := fun (event, next) => (event, next.take processId index)) possible

/-- More messages keep the selected one selected. -/
private theorem selected_extend {select : Term → Option γ} {mailbox mailbox' : List Term}
    {index : Nat} {message : Term} {value : γ}
    (selected : selectMessage select mailbox = some (message, value, mailbox.eraseIdx index))
    (bound : index < mailbox.length) (extended : mailbox <+: mailbox') :
    selectMessage select mailbox' = some (message, value, mailbox'.eraseIdx index) := by
  obtain ⟨extra, rfl⟩ := extended
  obtain ⟨-, -, -, extend⟩ := selectMessage_index selected
  rw [extend extra, List.eraseIdx_append_of_lt_length bound]

/-- Steps of other processes keep what a process reads. -/
private theorem Keeps.view {state after : State} {processId : PID}
    (kept : Keeps processId state after) : after.view processId = state.view processId := by
  simp only [State.view, kept.process.1, kept.process.2.1]

/-- Taking the message a process receives leaves the rest of its mailbox. -/
private theorem take_received {state : State} {processId : PID} {index : Nat}
    {process : ProcessState} (found : state.processes processId = some process) :
    state.update processId (some { process with mailbox := process.mailbox.eraseIdx index }) =
      state.take processId index := by
  refine State.ext' rfl (by simp) fun candidate => ?_
  simp only [take_processes, State.update]
  split <;> simp_all [ProcessState.take]

/-- Every run where a process is about to receive a message already in its
mailbox can receive it first, reaching the same terminal configuration. -/
private theorem receive_first {first last : Config α} {events : List Event} {outcome : Outcome α}
    (run : Run first events last) (terminal : Terminal last outcome) :
    ∀ {state : State} {before after : List (PID × Task α)} {processId : PID} {β γ : Type}
      {timeout : ReceiveTimeout} {select : Environment → Term → Option γ}
      {next : Option γ → Result β} {finish : Except Exception β → Option (Except Exception α)}
      {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {index : Nat}
      {message : Term} {value : γ},
      first = .running state (before ++ (processId, ⟨.receive timeout select next, finish⟩) ::
        after) finished exhausted →
      Wellformed first →
      selectMessage (select (state.view processId)) (state.process processId).mailbox =
        some (message, value, (state.process processId).mailbox.eraseIdx index) →
      Holds state processId index →
      ∃ events', Run (Config.running (state.take processId index)
        (before ++ (processId, ⟨next (some value), finish⟩) :: after) finished exhausted) events' last := by
  induction run with
  | @refl config =>
    intro state before after processId β γ timeout select next finish finished exhausted index
      message value equal wellformed selected holds
    subst equal
    exfalso
    cases signal : (state.process processId).signal with
    | none =>
      exact not_terminal (Step.run (transition :=
        { event := .receive processId message
          state := state.update processId (some { state.process processId with
            mailbox := (state.process processId).mailbox.eraseIdx index })
          tasks := [(processId, ⟨next (some value), finish⟩)] })
        rfl (by simp [Task.transitions, signal, selected])) terminal
    | some reason =>
      exact not_terminal (Step.run (transition :=
        { event := .exit processId reason, state := state.terminate processId reason, tasks := []
          finished := (finish (.error (.exit reason))).map (·, state.view processId) })
        rfl (by simp [Task.transitions, signal])) terminal
  | @step _ _ _ restEvents _ step rest ih =>
    intro state before after processId β γ timeout select next finish finished exhausted index
      message value equal wellformed selected holds
    subst equal
    obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp
      (wellformed.2.2.1 (processId, ⟨.receive timeout select next, finish⟩) (by simp))
    cases step with
    | @run tasks before' stepping task' after' transition _ _ _ split' possible =>
      by_cases sameProcess : before = before'
      · -- The receiving process steps: it receives the message, or exits either way.
        subst sameProcess
        have equal := List.append_cancel_left split'
        simp only [List.cons.injEq, Prod.mk.injEq] at equal
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
        cases signal : (state.process processId).signal with
        | none =>
          have transitions : (⟨.receive timeout select next, finish⟩ : Task α).transitions state
              processId = [{ event := .receive processId message, state := state.take processId index
                             tasks := [(processId, ⟨next (some value), finish⟩)] }] := by
            have process : state.process processId = process := by simp [State.process, found]
            rw [process] at signal selected
            rw [← take_received (index := index) found]
            simp [Task.transitions, process, signal, selected]
          rw [transitions, List.mem_singleton] at possible
          subst possible
          exact ⟨restEvents, by simpa [Transition.apply] using rest⟩
        | some reason =>
          simp only [Task.transitions, signal, List.mem_singleton] at possible
          subst possible
          have signal' : ((state.take processId index).process processId).signal = some reason := by
            rw [(take_process_fields (other := processId)).2.2.2.2.2.1, signal]
          refine ⟨.exit processId reason :: restEvents, .step (Step.run (transition :=
            { event := .exit processId reason
              state := (state.take processId index).terminate processId reason, tasks := []
              finished := (finish (.error (.exit reason))).map
                (·, (state.take processId index).view processId) })
            rfl (by simp [Task.transitions, signal'])) ?_⟩
          simp only [Transition.apply] at rest ⊢
          rw [terminate_take, take_view]
          simpa using rest
      · -- Another process steps the same way, after which the message is still there.
        obtain ⟨kept, order⟩ := other_step wellformed split' sameProcess possible
        obtain ⟨ne, fresh⟩ := other_distinct wellformed split' sameProcess
        have moved := transition_of_take ne fresh holds possible
        have wellformed' := Step.wellformed (.run split' possible) wellformed
        have selected' := selected_extend selected holds kept.process.2.2.2.2
        rw [← kept.view] at selected'
        rcases order with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
        · obtain ⟨events', run'⟩ := ih terminal (state := transition.state) (before := before)
            (after := middle ++ transition.tasks ++ after') (timeout := timeout) (select := select)
            (next := next) (finish := finish) (index := index) (message := message) (value := value)
            (finished := transition.finished.orElse fun _ => finished)
            (exhausted := exhausted || transition.exhausted)
            (by simp [Transition.apply]) wellformed' selected' (kept.holds holds)
          refine ⟨transition.event :: events', .step (Step.run (before := before ++
            (processId, ⟨next (some value), finish⟩) :: middle) (after := after')
            (processId := stepping) (task := task')
            (transition := { transition with state := transition.state.take processId index })
            (by simp) moved) ?_⟩
          simpa [Transition.apply] using run'
        · obtain ⟨events', run'⟩ := ih terminal (state := transition.state)
            (before := before' ++ transition.tasks ++ middle) (after := after) (timeout := timeout)
            (select := select) (next := next) (index := index) (message := message) (value := value)
            (finish := finish) (finished := transition.finished.orElse fun _ => finished)
            (exhausted := exhausted || transition.exhausted)
            (by simp [Transition.apply]) wellformed' selected' (kept.holds holds)
          refine ⟨transition.event :: events', .step (Step.run (before := before') (after := middle ++
            (processId, ⟨next (some value), finish⟩) :: after) (processId := stepping) (task := task')
            (transition := { transition with state := transition.state.take processId index })
            (by simp) moved) ?_⟩
          simpa [Transition.apply] using run'
    | timer possible =>
      obtain ⟨kept, -, -⟩ := timerSteps_keeps possible processId
      have selected' := selected_extend selected holds kept.process.2.2.2.2
      rw [← kept.view] at selected'
      obtain ⟨events', run'⟩ := ih terminal rfl (Step.wellformed (.timer possible) wellformed)
        selected' (kept.holds holds)
      exact ⟨_ :: events', .step (.timer (timer_of_take holds possible)) run'⟩

/-! ### Footprints

A step reads and writes some locations of the state: fields of processes,
whether processes are alive, and the timers. Steps of different processes whose
footprints do not conflict commute. -/

/-- Whether two records agree on a field. -/
private def Field.same : Field → ProcessState → ProcessState → Prop
  | .pdict, first, second => first.pdict = second.pdict
  | .mailbox, first, second => first.mailbox = second.mailbox
  | .refCounter, first, second => first.refCounter = second.refCounter
  | .children, first, second => first.children = second.children
  | .links, first, second => first.links = second.links
  | .monitors, first, second => first.monitors = second.monitors
  | .monitoring, first, second => first.monitoring = second.monitoring
  | .aliases, first, second => first.aliases = second.aliases
  | .trapExit, first, second => first.trapExit = second.trapExit
  | .signal, first, second => first.signal = second.signal
  | .cancels, first, second => first.cancels = second.cancels

private theorem Field.same_refl (field : Field) (process : ProcessState) :
    field.same process process := by
  cases field <;> rfl

private theorem Field.same_symm {field : Field} {first second : ProcessState}
    (same : field.same first second) : field.same second first := by
  cases field <;> exact same.symm

private theorem Field.same_trans {field : Field} {first second third : ProcessState}
    (left : field.same first second) (right : field.same second third) : field.same first third := by
  cases field <;> exact left.trans right

/-- Records agreeing on every field are equal. -/
private theorem ProcessState.ext_fields {first second : ProcessState}
    (same : ∀ field : Field, field.same first second) : first = second := by
  have := same Field.pdict; have := same Field.mailbox; have := same Field.refCounter
  have := same Field.children; have := same Field.links; have := same Field.monitors
  have := same Field.monitoring; have := same Field.aliases; have := same Field.trapExit
  have := same Field.signal; have := same Field.cancels
  cases first; cases second; simp_all [Field.same]

/-- Whether two states agree at a location. -/
private def Agree (first second : State) : Loc → Prop
  | .field processId field =>
      Option.Rel field.same (first.processes processId) (second.processes processId)
  | .alive processId => (first.processes processId).isSome = (second.processes processId).isSome
  | .timersTo processId =>
      first.timers.filter (·.destination == processId) = second.timers.filter (·.destination == processId)
  | .timers => first.timers = second.timers
  | .elapsed => first.elapsed = second.elapsed

private theorem Agree.refl (state : State) (loc : Loc) : Agree state state loc := by
  cases loc with
  | field processId field =>
    simp only [Agree]
    cases found : state.processes processId
    · exact .none
    · exact .some (Field.same_refl _ _)
  | alive => rfl
  | timersTo => rfl
  | timers => rfl
  | elapsed => rfl

private theorem Agree.symm {first second : State} {loc : Loc} (agree : Agree first second loc) :
    Agree second first loc := by
  cases loc with
  | field processId field =>
    simp only [Agree] at *
    generalize first.processes processId = a at agree
    generalize second.processes processId = b at agree
    cases agree with
    | none => exact .none
    | some same => exact .some (Field.same_symm same)
  | alive => exact Eq.symm agree
  | timersTo => exact Eq.symm agree
  | timers => exact Eq.symm agree
  | elapsed => exact Eq.symm agree

private theorem Agree.trans {first second third : State} {loc : Loc}
    (left : Agree first second loc) (right : Agree second third loc) : Agree first third loc := by
  cases loc with
  | field processId field =>
    simp only [Agree] at *
    generalize first.processes processId = a at left
    generalize second.processes processId = b at left right
    generalize third.processes processId = c at right
    cases left with
    | none => exact right
    | some same => cases right with | some same' => exact .some (Field.same_trans same same')
  | alive => exact Eq.trans left right
  | timersTo => exact Eq.trans left right
  | timers => exact Eq.trans left right
  | elapsed => exact Eq.trans left right

/-- States agreeing at every location are equal. -/
private theorem State.ext_agree {first second : State} (agree : ∀ loc, Agree first second loc) :
    first = second := by
  refine State.ext' (agree .timers) (agree .elapsed) fun processId => ?_
  have fields := fun field => agree (.field processId field)
  have alive := agree (.alive processId)
  simp only [Agree] at fields alive
  cases found : first.processes processId with
  | none => cases found' : second.processes processId <;> simp_all
  | some process =>
    cases found' : second.processes processId with
    | none => simp_all
    | some process' =>
      congr 1
      exact ProcessState.ext_fields fun field => by
        have := fields field; rw [found, found'] at this; cases this; assumption

/-- A change of a state that, from states agreeing with this one on some
locations, writes only some other locations, with values that depend only on
the first ones. -/
private def Frames (reads writes : List Loc) (change : State → State) (state : State) : Prop :=
  ∀ other, (∀ loc ∈ reads, Agree state other loc) →
    (∀ loc, loc ∉ writes → Agree (change other) other loc) ∧
    ∀ loc ∈ writes, Agree (change state) (change other) loc

private theorem Frames.keeps {reads writes : List Loc} {change : State → State} {state : State}
    (frames : Frames reads writes change state) {loc : Loc} (out : loc ∉ writes) :
    Agree (change state) state loc :=
  (frames state fun loc _ => Agree.refl state loc).1 loc out

/-- Reading and writing more keeps a frame, when the new writes are read. -/
private theorem Frames.mono {reads writes reads' writes' : List Loc} {change : State → State}
    {state : State} (frames : Frames reads writes change state) (moreReads : reads ⊆ reads')
    (moreWrites : writes ⊆ writes') (read : ∀ loc ∈ writes', loc ∉ writes → loc ∈ reads') :
    Frames reads' writes' change state := by
  intro other agree
  obtain ⟨keeps, determined⟩ := frames other fun loc mem => agree loc (moreReads mem)
  refine ⟨fun loc out => keeps loc fun mem => out (moreWrites mem), fun loc mem => ?_⟩
  by_cases written : loc ∈ writes
  · exact determined loc written
  · exact ((frames.keeps written).trans (agree loc (read loc mem written))).trans
      (keeps loc written).symm

/-- One change after another. -/
private theorem Frames.comp {reads writes reads' writes' : List Loc} {first second : State → State}
    {state : State} (frames : Frames reads writes first state)
    (frames' : ∀ other, (∀ loc ∈ reads ++ reads', Agree state other loc) →
      Frames reads' writes' second (first other)) :
    Frames (reads ++ reads') (writes ++ writes') (second ∘ first) state := by
  intro other agree
  obtain ⟨keeps, determined⟩ := frames other fun loc mem => agree loc (by simp [mem])
  have middle : ∀ loc ∈ reads', Agree (first state) (first other) loc := by
    intro loc mem
    by_cases written : loc ∈ writes
    · exact determined loc written
    · exact ((frames.keeps written).trans (agree loc (by simp [mem]))).trans (keeps loc written).symm
  obtain ⟨keeps', determined'⟩ := frames' state (fun loc _ => Agree.refl state loc) (first other)
    middle
  obtain ⟨keepsOther, -⟩ := frames' other agree (first other) fun loc _ => Agree.refl _ loc
  refine ⟨fun loc out => ?_, fun loc mem => ?_⟩
  · simp only [List.mem_append, not_or] at out
    exact (keepsOther loc out.2).trans (keeps loc out.1)
  · simp only [List.mem_append] at mem
    by_cases written' : loc ∈ writes'
    · exact determined' loc written'
    · rcases mem with written | written
      · exact ((keeps' loc written' |> fun _ =>
          ((frames' state (fun loc _ => Agree.refl state loc)).keeps written')).trans
            (determined loc written)).trans (keepsOther loc written').symm
      · exact absurd written written'

/-- A change of records that writes only some fields, with values that depend
only on some other fields. -/
private def Changes (reads writes : List Field) (change : ProcessState → ProcessState) : Prop :=
  (∀ process field, field ∉ writes → field.same (change process) process) ∧
  ∀ process process', (∀ field ∈ reads, field.same process process') →
    ∀ field ∈ writes, field.same (change process) (change process')

/-- Prove that a record update changes only the fields it lists. -/
local macro "changes" : tactic => `(tactic| (
  refine ⟨fun process field out => ?_, fun process process' same field mem => ?_⟩ <;>
    cases field <;> simp_all [Field.same]))

private theorem agree_process {first second : State} {processId : PID} {field : Field}
    {process process' : ProcessState} (found : first.processes processId = some process)
    (found' : second.processes processId = some process') :
    Agree first second (.field processId field) ↔ field.same process process' := by
  simp only [Agree, found, found']
  exact ⟨fun | .some same => same, .some⟩

private theorem frames_update {state : State} {processId : PID} {process : Option ProcessState} :
    Frames [] (Loc.process processId) (·.update processId process) state := by
  intro other _
  refine ⟨fun loc out => ?_, fun loc mem => ?_⟩
  · cases loc with
    | field candidate field =>
      have ne : candidate ≠ processId := by
        rintro rfl; exact out (by simp [Loc.process, Field.mem_all])
      simp only [Agree, State.update, ne, ite_false]; exact (Agree.refl other (.field _ _))
    | alive candidate =>
      have ne : candidate ≠ processId := by rintro rfl; exact out (by simp [Loc.process])
      simp [Agree, State.update, ne]
    | timersTo => rfl
    | timers => rfl
    | elapsed => simp [Agree]
  · simp only [Loc.process, List.mem_cons, List.mem_map] at mem
    rcases mem with rfl | ⟨field, -, rfl⟩
    · simp [Agree, State.update]
    · simp only [Agree, State.update, ite_true]
      cases process
      · exact .none
      · exact .some (Field.same_refl _ _)

private theorem frames_modify {state : State} {processId : PID}
    {change : ProcessState → ProcessState} {reads writes : List Field}
    (changes : Changes reads writes change) :
    Frames (.alive processId :: reads.map (.field processId)) (writes.map (.field processId))
      (·.modify processId change) state := by
  intro other agree
  have alive := agree (.alive processId) (by simp)
  refine ⟨fun loc out => ?_, fun loc mem => ?_⟩
  · dsimp only
    unfold State.modify
    split
    · rename_i process found
      cases loc with
      | field candidate field =>
        by_cases same : candidate = processId
        · subst same
          have : field ∉ writes := fun mem => out (by simp [mem])
          simp only [Agree, State.update, ite_true, found]
          exact .some (changes.1 process field this)
        · simp only [Agree, State.update, same, ite_false]; exact Agree.refl other (.field _ _)
      | alive candidate => simp only [Agree, State.update]; split <;> simp_all
      | timersTo => rfl
      | timers => rfl
      | elapsed => simp [Agree]
    · exact Agree.refl other loc
  · simp only [List.mem_map] at mem
    obtain ⟨field, mem, rfl⟩ := mem
    dsimp only
    unfold State.modify
    cases found : state.processes processId with
    | none =>
      have : other.processes processId = none := by
        simp only [Agree, found, Option.isSome_none] at alive
        cases h : other.processes processId <;> simp_all
      simp [Agree, found, this]
    | some process =>
      obtain ⟨process', found'⟩ : ∃ process', other.processes processId = some process' := by
        simp only [Agree, found, Option.isSome_some] at alive
        exact Option.isSome_iff_exists.mp alive.symm
      simp only [found, found', Agree, State.update, ite_true]
      refine .some (changes.2 process process' (fun field mem => ?_) field mem)
      exact (agree_process found found').mp (agree _ (by simp [mem]))

private theorem frames_deliver {state : State} {processId : PID} {message : Term} :
    Frames [.alive processId, .field processId .mailbox] [.field processId .mailbox]
      (·.deliver processId message) state := by
  have equal : ∀ state : State, state.deliver processId message = state.modify processId
      fun process => { process with mailbox := process.mailbox ++ [message] } := by
    intro state; unfold State.deliver State.modify; split <;> rfl
  simp only [equal]
  exact frames_modify (reads := [.mailbox]) (writes := [.mailbox]) (by changes)

private theorem frames_kill {state : State} {processId : PID} {reason : Term} :
    Frames [.alive processId, .field processId .signal] [.field processId .signal]
      (·.kill processId reason) state :=
  frames_modify (reads := [.signal]) (writes := [.signal]) (by changes)

/-- States agreeing on a field of a process agree on the field of its record. -/
private theorem Agree.same {first second : State} {processId : PID} {field : Field}
    (agree : Agree first second (.field processId field)) :
    field.same (first.process processId) (second.process processId) := by
  simp only [Agree, State.process] at *
  generalize first.processes processId = a at agree
  generalize second.processes processId = b at agree
  cases agree with
  | none => exact Field.same_refl _ _
  | some same => exact same

private theorem Frames.id {state : State} : Frames [] [] (fun state => state) state :=
  fun _ _ => ⟨fun loc _ => Agree.refl _ loc, fun _ mem => absurd mem List.not_mem_nil⟩

/-- A change that agrees with a framed one on states agreeing with this one. -/
private theorem Frames.congr {reads writes : List Loc} {change change' : State → State}
    {state : State} (frames : Frames reads writes change' state)
    (equal : ∀ other, (∀ loc ∈ reads, Agree state other loc) → change other = change' other) :
    Frames reads writes change state := by
  intro other agree
  rw [equal other agree, equal state (fun loc _ => Agree.refl state loc)]
  exact frames other agree

private theorem Frames.foldl {items : List γ} {step : State → γ → State}
    {reads writes : γ → List Loc}
    (frames : ∀ item ∈ items, ∀ state, Frames (reads item) (writes item) (step · item) state)
    {state : State} :
    Frames (items.flatMap reads) (items.flatMap writes) (fun state => items.foldl step state)
      state := by
  induction items generalizing state with
  | nil => exact Frames.id
  | cons item rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    exact Frames.comp (second := fun state => rest.foldl step state) (frames item (by simp) state)
      fun _ _ => ih fun item mem => frames item (by simp [mem])

/-- Whether some timer sends to a process. -/
private theorem any_timersTo {first second : State} {processId : PID}
    (agree : Agree first second (.timersTo processId)) :
    first.timers.any (·.destination == processId) = second.timers.any (·.destination == processId) := by
  have any : ∀ timers : List Timer, timers.any (·.destination == processId) =
      !(timers.filter (·.destination == processId)).isEmpty := by
    intro timers
    induction timers with
    | nil => rfl
    | cons timer rest ih => simp only [List.any_cons, List.filter_cons, ih]; split <;> simp_all
  simp only [Agree] at agree
  rw [any, any, agree]

/-- Cancel the timers sending to a process. -/
private theorem frames_cancelTimers {state : State} {processId : PID} {some : Bool}
    (decided : state.timers.any (·.destination == processId) = some) :
    Frames (.timersTo processId :: if some then [.timers] else [])
      (if some then [.timers, .timersTo processId] else [])
      (fun state => { state with timers := state.timers.filter (·.destination != processId) })
      state := by
  intro other agree
  have timersTo := agree (.timersTo processId) (by simp)
  simp only [Agree] at timersTo
  subst decided
  split
  · rename_i some
    refine ⟨fun loc out => ?_, fun loc mem => ?_⟩
    · cases loc with
      | timersTo candidate =>
        have ne : candidate ≠ processId := by rintro rfl; simp at out
        simp only [Agree, List.filter_filter]
        congr 1; funext timer
        by_cases equal : timer.destination = candidate <;> simp [equal, ne]
      | timers => simp at out
      | field => exact Agree.refl other (.field _ _)
      | alive => exact Agree.refl other (.alive _)
      | elapsed => simp [Agree]
    · have timers : state.timers = other.timers := agree .timers (by simp [some])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · simp only [Agree, timers]
      · simp only [Agree, timers]
  · rename_i none
    have empty : state.timers.filter (·.destination == processId) = [] := by
      simpa [List.filter_eq_nil_iff] using none
    have kept : other.timers.filter (·.destination != processId) = other.timers := by
      rw [List.filter_eq_self]
      intro timer mem
      have : timer ∉ other.timers.filter (·.destination == processId) := by
        rw [← timersTo, empty]; simp
      simpa [mem] using this
    refine ⟨fun loc _ => ?_, fun loc mem => absurd mem List.not_mem_nil⟩
    simp only [kept]
    exact Agree.refl other loc

/-- Signaling a process, given whether it traps exits. -/
private theorem frames_signal {state : State} {target sender : PID} {reason : Term}
    {untrappable trapping : Bool} (trapped : (state.process target).trapExit = trapping) :
    Frames (Footprint.signal target reason untrappable trapping).reads
      (Footprint.signal target reason untrappable trapping).writes
      (·.signal target sender reason untrappable) state := by
  unfold Footprint.signal
  cases untrappable
  · simp only [Bool.false_eq_true, ite_false]
    have trapExit : ∀ other : State, (∀ loc ∈ [Loc.field target .trapExit], Agree state other loc) →
        (other.process target).trapExit = trapping := fun other agree => by
      rw [← trapped]
      have := Agree.same (agree (.field target .trapExit) (by simp))
      simp only [Field.same] at this
      exact this.symm
    cases trapping
    · simp only [Bool.false_eq_true, ite_false]
      split
      · rename_i normal
        refine Frames.congr (change' := fun state => state)
          (Frames.id.mono (by simp) (by simp) (by simp)) fun other agree => ?_
        have trapping := trapExit other fun loc mem => agree loc (by simp at mem; simp [mem])
        simp [State.signal, trapping, normal]
      · rename_i abnormal
        refine Frames.congr ((frames_kill (processId := target) (reason := reason)).mono
          (by simp) (by simp) (by simp)) fun other agree => ?_
        have trapping := trapExit other fun loc mem => agree loc (by simp at mem; simp [mem])
        simp [State.signal, trapping, abnormal]
    · simp only [ite_true]
      refine Frames.congr ((frames_deliver (processId := target)
        (message := .tuple #[.atom "EXIT", .pid sender, reason])).mono
          (by simp) (by simp) (by simp)) fun other agree => ?_
      have trapping := trapExit other fun loc mem => agree loc (by simp at mem; simp [mem])
      simp [State.signal, trapping]
  · simp only [ite_true]
    exact Frames.congr (frames_kill (processId := target) (reason := .atom "killed"))
      fun other _ => by simp [State.signal]

/-- Signaling a process that is not live changes nothing. -/
private theorem signal_dead {state : State} {target sender : PID} {reason : Term}
    {untrappable : Bool} (dead : state.processes target = none) :
    state.signal target sender reason untrappable = state := by
  have modified : ∀ change : ProcessState → ProcessState, state.modify target change = state :=
    fun change => by simp [State.modify, dead]
  unfold State.signal State.kill State.deliver
  simp only [State.process, dead, Option.getD_none]
  split <;> simp [modified]

/-- Changes of each item that hold for states agreeing with a base on some
locations, which they never write, compose. -/
private theorem Frames.foldlAgree {items : List γ} {step : State → γ → State}
    {reads writes : γ → List Loc} {fixed : List Loc} {base : State}
    (frames : ∀ item ∈ items, ∀ state, (∀ loc ∈ fixed, Agree base state loc) →
      Frames (reads item) (writes item) (step · item) state)
    (disjoint : ∀ item ∈ items, ∀ loc ∈ fixed, loc ∉ writes item) {state : State}
    (agree : ∀ loc ∈ fixed, Agree base state loc) :
    Frames (fixed ++ items.flatMap reads) (items.flatMap writes)
      (fun state => items.foldl step state) state := by
  induction items generalizing state with
  | nil => exact Frames.id.mono (by simp) (by simp) (by simp)
  | cons item rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    have current := frames item (by simp) state agree
    refine (Frames.comp (second := fun state => rest.foldl step state) current
      fun other agreeOther => ih (fun item mem => frames item (by simp [mem]))
        (fun item mem => disjoint item (by simp [mem])) fun loc mem => ?_).mono
      (by intro loc; simp only [List.mem_append]; grind) (by simp) fun loc mem out => absurd mem out
    have stays := (current other fun loc mem => agreeOther loc (by simp [mem])).1 loc
      (disjoint item (by simp) loc mem)
    exact (agree loc mem).trans ((agreeOther loc (by simp [mem])).trans stays.symm)

/-- What a process exiting reads and writes, as `State.exitFootprint` states. -/
private theorem frames_terminate {state : State} {processId : PID} {reason : Term} :
    Frames (state.exitFootprint processId reason).reads (state.exitFootprint processId reason).writes
      (·.terminate processId reason) state := by
  let first := fun state : State => { state.update processId none with
    timers := state.timers.filter (·.destination != processId) }
  let notify := fun (state : State) (linked : PID) =>
    (state.modify linked fun other => { other with links := other.links.erase processId }).signal
      linked processId reason false
  let watched := fun (state : State) (entry : List Nat × PID) =>
    (state.deliver entry.2 (.tuple #[.atom "DOWN", .reference entry.1, .atom "process",
      .pid processId, reason])).modify entry.2 fun other =>
        { other with monitoring := other.monitoring.filter (·.1 != entry.1)
                     aliases := other.aliases.erase entry.1 }
  have firstFrames : Frames (.timersTo processId ::
        if state.timers.any (·.destination == processId) then [.timers] else [])
      (Loc.process processId ++
        if state.timers.any (·.destination == processId) then [.timers, .timersTo processId] else [])
      first state := by
    have := Frames.comp (first := (·.update processId none))
      (second := fun state => { state with timers := state.timers.filter (·.destination != processId) })
      (reads := []) (state := state) frames_update fun other agree => frames_cancelTimers
        ((any_timersTo (agree _ (by simp))).symm)
    exact this.mono (by simp) (by simp) fun loc mem out => absurd mem out
  -- Signals reach linked processes after the exiting one has gone, and each
  -- linked process traps exits as before.
  let fixed : List Loc := .alive processId ::
    (state.process processId).links.map fun linked => .field linked .trapExit
  have signalReads : ∀ linked : PID,
      .alive linked ∈ (Footprint.signal linked reason false (state.process linked).trapExit).reads ∧
      .field linked .trapExit ∈
        (Footprint.signal linked reason false (state.process linked).trapExit).reads ∧
      ∀ loc ∈ (Footprint.signal linked reason false (state.process linked).trapExit).writes,
        loc ∈ (Footprint.signal linked reason false (state.process linked).trapExit).reads :=
    fun linked => by
      unfold Footprint.signal
      simp only [Bool.false_eq_true, ite_false]
      split <;> (try split) <;> simp
  have linkedFrames : ∀ linked' ∈ (state.process processId).links, ∀ current,
      (∀ loc ∈ fixed, Agree (first state) current loc) →
      Frames (.field linked' .links :: (Footprint.signal linked' reason false (state.process linked').trapExit).reads)
        (.field linked' .links :: (Footprint.signal linked' reason false (state.process linked').trapExit).writes) (notify · linked') current := by
    intro linked' member current agree
    cases live : current.processes linked' with
    | none =>
      -- A process that is not live is left alone.
      refine Frames.congr (change' := fun state => state)
        (Frames.id.mono (by simp) (by simp) fun loc mem _ => ?_) fun other agreeOther => ?_
      · simp only [List.mem_cons] at mem ⊢
        rcases mem with rfl | mem
        · exact .inl rfl
        · exact .inr ((signalReads linked').2.2 loc mem)
      have alive := agreeOther (.alive linked') (by simp [(signalReads linked').1])
      simp only [Agree, live, Option.isSome_none] at alive
      have dead : other.processes linked' = none := by
        cases found : other.processes linked'
        · rfl
        · simp [found] at alive
      show (other.modify linked' _).signal linked' processId reason false = other
      simp [State.modify, dead, signal_dead]
    | some record =>
      have ne : linked' ≠ processId := by
        rintro rfl
        have := agree (.alive linked') (by simp [fixed])
        simp [Agree, first, State.update, live] at this
      have trapped : ∀ other : State, Agree current other (.field linked' .trapExit) →
          ((other.modify linked' fun other => { other with links := other.links.erase processId }).process
            linked').trapExit = (state.process linked').trapExit := by
        intro other agreeOther
        have kept : ((other.modify linked' fun other =>
            { other with links := other.links.erase processId }).process linked').trapExit =
            (other.process linked').trapExit := by
          unfold State.modify State.process
          split <;> simp_all [State.update]
        have before := Agree.same (agree (.field linked' .trapExit) (by simp [fixed, member]))
        have after := Agree.same agreeOther
        simp only [Field.same] at before after
        rw [kept, ← after, ← before]
        simp [first, State.process, State.update, ne]
      refine (Frames.comp (frames_modify (processId := linked') (reads := [.links])
        (writes := [.links]) (change := fun other => { other with links := other.links.erase processId })
        (by changes)) fun other agreeOther => frames_signal (trapped other
          (agreeOther _ (by simp [(signalReads linked').2.1])))).mono ?_ ?_ ?_
      · intro loc; simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
          or_false]; grind
      · intro loc; simp
      · intro loc mem out; simp only [List.mem_cons, List.mem_append, List.mem_map] at mem out ⊢
        grind
  have disjoint : ∀ linked' ∈ (state.process processId).links, ∀ loc ∈ fixed,
      loc ∉ .field linked' .links :: (Footprint.signal linked' reason false (state.process linked').trapExit).writes := by
    intro linked' _ loc mem
    simp only [fixed, List.mem_cons, List.mem_map] at mem
    unfold Footprint.signal
    simp only [Bool.false_eq_true, ite_false]
    rcases mem with rfl | ⟨_, _, rfl⟩ <;> split <;> (try split) <;> simp
  have watchedFrames : ∀ entry ∈ (state.process processId).monitors, ∀ state,
      Frames ([.alive entry.2, .field entry.2 .mailbox] ++
          [.alive entry.2, .field entry.2 .monitoring, .field entry.2 .aliases])
        ([.field entry.2 .mailbox] ++ [.field entry.2 .monitoring, .field entry.2 .aliases])
        (watched · entry) state :=
    fun entry _ state => Frames.comp frames_deliver fun _ _ =>
      frames_modify (reads := [.monitoring, .aliases]) (writes := [.monitoring, .aliases]) (by changes)
  have composed := Frames.comp (Frames.comp firstFrames fun other agreeOther =>
    Frames.foldlAgree linkedFrames disjoint fun loc mem => by
      by_cases written : loc ∈ Loc.process processId ++
          if state.timers.any (·.destination == processId) then [.timers, .timersTo processId] else []
      · exact (firstFrames other fun loc' mem' =>
          agreeOther loc' (List.mem_append_left _ mem')).2 loc written
      · exact ((firstFrames.keeps written).trans
          (agreeOther loc (List.mem_append_right _ (List.mem_append_left _ mem)))).trans
          ((firstFrames other fun loc' mem' =>
            agreeOther loc' (List.mem_append_left _ mem')).1 loc written).symm)
    fun _ _ => Frames.foldl watchedFrames
  refine Frames.congr (composed.mono ?_ ?_ ?_) fun other agree => ?_
  all_goals try
    intro loc
    have trapped := fun linked => (signalReads linked).2.1
    have alive : Loc.alive processId ∈ Loc.process processId := by simp [Loc.process]
    simp only [State.exitFootprint, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
      List.not_mem_nil, or_false, fixed]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> grind
  have links : (other.process processId).links = (state.process processId).links :=
    (Agree.same (agree (.field processId .links)
      (by simp [State.exitFootprint, Loc.process, Field.mem_all]))).symm
  have monitors : (other.process processId).monitors = (state.process processId).monitors :=
    (Agree.same (agree (.field processId .monitors)
      (by simp [State.exitFootprint, Loc.process, Field.mem_all]))).symm
  simp only [State.terminate, links, monitors]
  rfl

@[simp] private theorem isSome_modify {state : State} {processId other : PID}
    {change : ProcessState → ProcessState} :
    ((state.modify processId change).processes other).isSome = (state.processes other).isSome := by
  unfold State.modify
  split
  · simp only [State.update]; split <;> simp_all
  · rfl

/-- What starting a monitor reads and writes. -/
private def monitorWrites (processId target : PID) (alias live : Bool) : List Loc :=
  .field processId .refCounter :: if live then
      [.field target .monitors, .field processId .monitoring] ++
        if alias then [.field processId .aliases] else []
    else [.field processId .mailbox]

private theorem frames_monitor {state : State} {processId target : PID} {alias live : Bool}
    (decided : (state.processes target).isSome = live) :
    Frames (.alive processId :: .alive target :: monitorWrites processId target alias live)
      (monitorWrites processId target alias live)
      (fun state => (state.monitor processId target alias).2) state := by
  let reference := processId ++ [(state.process processId).refCounter + 1]
  let count := fun state : State => state.modify processId fun process =>
    { process with refCounter := process.refCounter + 1 }
  have counted : Frames [.alive processId, .field processId .refCounter]
      [.field processId .refCounter] count state :=
    frames_modify (reads := [.refCounter]) (writes := [.refCounter]) (by changes)
  have equal : ∀ other : State,
      (∀ loc ∈ .alive processId :: .alive target :: monitorWrites processId target alias live,
        Agree state other loc) →
      (other.monitor processId target alias).2 = if live then
        ((count other).modify target fun watched =>
          { watched with monitors := watched.monitors ++ [(reference, processId)] }).modify processId
            fun process =>
              { process with monitoring := process.monitoring ++ [(reference, target)]
                             aliases := if alias then process.aliases ++ [reference] else process.aliases }
      else (count other).deliver processId (.tuple #[.atom "DOWN", .reference reference,
        .atom "process", .pid target, .atom "noproc"]) := by
    intro other agree
    have counter : (other.process processId).refCounter = (state.process processId).refCounter :=
      (Agree.same (agree (.field processId .refCounter) (by simp [monitorWrites]))).symm
    have alive : (other.processes target).isSome = live :=
      decided ▸ (agree (.alive target) (by simp)).symm
    have alive' : ((count other).processes target).isSome = live := by simp [count, alive]
    simp only [count] at alive'
    simp only [State.monitor, counter]
    cases live
    · simp only [Bool.false_eq_true, ite_false]
      split
      · rename_i found; simp [found] at alive'
      · rfl
    · simp only [ite_true]
      split
      · rfl
      · rename_i found; simp [found] at alive'
  refine Frames.congr ?_ equal
  cases live
  · exact (Frames.comp counted fun _ _ => frames_deliver).mono (by simp [monitorWrites])
      (by simp [monitorWrites]) (by simp [monitorWrites])
  · cases alias
    · exact (Frames.comp counted fun _ _ => Frames.comp
        (frames_modify (reads := [.monitors]) (writes := [.monitors]) (by changes)) fun _ _ =>
          frames_modify (reads := [.monitoring]) (writes := [.monitoring]) (by changes)).mono
        (by simp [monitorWrites]) (by simp [monitorWrites]) (by simp [monitorWrites])
    · exact (Frames.comp counted fun _ _ => Frames.comp
        (frames_modify (reads := [.monitors]) (writes := [.monitors]) (by changes)) fun _ _ =>
          frames_modify (reads := [.monitoring, .aliases]) (writes := [.monitoring, .aliases])
            (by changes)).mono
        (by simp [monitorWrites]) (by simp [monitorWrites]) (by simp [monitorWrites])

@[simp] private theorem isSome_deliver {state : State} {processId other : PID} {message : Term} :
    ((state.deliver processId message).processes other).isSome = (state.processes other).isSome := by
  unfold State.deliver
  split
  · simp only [State.update]; split <;> simp_all
  · rfl

@[simp] private theorem isSome_monitor {state : State} {processId other target : PID}
    {alias : Bool} :
    ((state.monitor processId target alias).2.processes other).isSome =
      (state.processes other).isSome := by
  simp only [State.monitor]; split <;> simp

/-- What spawning a child writes. -/
private def spawnWrites (processId : PID) (children : Nat) (options : SpawnOptions) : List Loc :=
  .field processId .children :: Loc.process (processId ++ [children + 1]) ++
    (if options.link then [.field processId .links] else []) ++
    if options.monitor then [.field processId .refCounter, .field processId .monitoring] else []

private theorem frames_spawnWith {state : State} {processId : PID} {options : SpawnOptions}
    {process : ProcessState} (found : state.processes processId = some process) :
    Frames (.alive processId :: .field processId .refCounter ::
        spawnWrites processId process.children options)
      (spawnWrites processId process.children options)
      (fun state => (state.spawnWith processId options).2) state := by
  obtain ⟨doLink, doMonitor⟩ := options
  let child := processId ++ [process.children + 1]
  let count := fun state : State => state.modify processId fun process =>
    { process with children := process.children + 1 }
  let linkChild := fun state : State =>
    (state.modify processId fun process =>
      { process with links := insertOnce child process.links }).modify child fun other =>
        { other with links := [processId] }
  have counted : Frames [.alive processId, .field processId .children]
      [.field processId .children] count state :=
    frames_modify (reads := [.children]) (writes := [.children]) (by changes)
  have created := Frames.comp counted fun _ _ =>
    frames_update (processId := child) (process := some {})
  have linked : ∀ state, Frames ([.alive processId, .field processId .links] ++ [.alive child])
      ([.field processId .links] ++ [.field child .links]) linkChild state := fun _ =>
    Frames.comp (frames_modify (reads := [.links]) (writes := [.links]) (by changes))
      fun _ _ => frames_modify (reads := []) (writes := [.links]) (by changes)
  have alive : ∀ other, ((linkChild ((count other).update child (some {}))).processes child).isSome :=
    fun other => by simp [linkChild, State.update]
  have alive' : ∀ other, (((count other).update child (some {})).processes child).isSome :=
    fun other => by simp [State.update]
  refine Frames.congr (change' := fun state =>
      let state := (count state).update child (some {})
      let state := if doLink then linkChild state else state
      if doMonitor then (state.monitor processId child false).2 else state) ?_
    fun other agree => ?_
  · cases doLink <;> cases doMonitor <;>
      simp only [ite_true, ite_false, Bool.false_eq_true]
    · refine created.mono ?_ ?_ ?_
      all_goals intro loc; simp only [spawnWrites, List.mem_append, List.mem_cons,
        Loc.process, List.mem_map, List.not_mem_nil, or_false, ite_false,
        Bool.false_eq_true, child]; grind [Field.mem_all]
    · refine (Frames.comp created fun other _ => frames_monitor (alive' other)).mono ?_ ?_ ?_
      all_goals intro loc; simp only [spawnWrites, monitorWrites, List.mem_append, List.mem_cons,
        Loc.process, List.mem_map, List.not_mem_nil, or_false, ite_true, ite_false,
        Bool.false_eq_true, child]; grind [Field.mem_all]
    · refine (Frames.comp created fun _ _ => linked _).mono ?_ ?_ ?_
      all_goals intro loc; simp only [spawnWrites, List.mem_append, List.mem_cons,
        Loc.process, List.mem_map, List.not_mem_nil, or_false, ite_true, ite_false,
        Bool.false_eq_true, child]; grind [Field.mem_all]
    · refine (Frames.comp (Frames.comp created fun _ _ => linked _) fun other _ =>
        frames_monitor (alive other)).mono ?_ ?_ ?_
      all_goals intro loc; simp only [spawnWrites, monitorWrites, List.mem_append, List.mem_cons,
        Loc.process, List.mem_map, List.not_mem_nil, or_false, ite_true, ite_false,
        Bool.false_eq_true, child]; grind [Field.mem_all]
  · have children : (other.process processId).children = process.children := by
      have := (Agree.same (agree (.field processId .children) (by simp [spawnWrites]))).symm
      simpa [State.process, found] using this
    obtain ⟨process', found'⟩ : ∃ process', other.processes processId = some process' := by
      have := agree (.alive processId) (by simp)
      simp only [Agree, found, Option.isSome_some] at this
      exact Option.isSome_iff_exists.mp this.symm
    have spawned : (other.spawn processId).2 = (count other).update child (some {}) := by
      simp only [State.spawn, count, State.modify, found', child, ← children]
      simp [State.process, found']
    have spawnedPid : (other.spawn processId).1 = child := by
      simp [State.spawn, child, children]
    simp only [State.spawnWith, spawnedPid, spawned]
    rfl

/-- A change of the timers that keeps the timers sending to other processes. -/
private theorem frames_timers {state : State} {change : List Timer → List Timer}
    {destinations : List PID}
    (keeps : ∀ processId ∉ destinations,
      (change state.timers).filter (·.destination == processId) =
        state.timers.filter (·.destination == processId)) :
    Frames [.timers] (.timers :: destinations.map .timersTo)
      (fun state => { state with timers := change state.timers }) state := by
  intro other agree
  have timers : state.timers = other.timers := agree .timers (by simp)
  refine ⟨fun loc out => ?_, fun loc mem => ?_⟩
  · cases loc with
    | timersTo processId =>
      have : processId ∉ destinations := fun mem => out (by simp [mem])
      simp only [Agree]; rw [← timers]; exact keeps processId this
    | timers => simp at out
    | field => exact Agree.refl other (.field _ _)
    | alive => exact Agree.refl other (.alive _)
    | elapsed => simp [Agree]
  · simp only [List.mem_cons, List.mem_map] at mem
    rcases mem with rfl | ⟨_, _, rfl⟩ <;> simp only [Agree, timers]

/-- The timers sending to processes, for timers with a reference. -/
private theorem timersWith_eq {state : State} {reference : List Nat} :
    state.timersWith reference =
      ((state.timers.filter (·.reference == reference)).map (·.destination)).map .timersTo := by
  simp only [State.timersWith]
  induction state.timers with
  | nil => rfl
  | cons timer rest ih => simp only [List.filterMap_cons, List.filter_cons]; split <;> simp_all

/-- Changing only timers with a reference, keeping their destinations, keeps
the timers sending to other processes. -/
private theorem keeps_reference {timers : List Timer} {reference : List Nat} {processId : PID}
    {change : Timer → Option Timer}
    (other : ∀ timer ∈ timers, timer.reference = reference → timer.destination ≠ processId)
    (kept : ∀ timer, timer.reference ≠ reference → change timer = some timer)
    (destination : ∀ timer changed, change timer = some changed →
      changed.destination = timer.destination) :
    (timers.filterMap change).filter (·.destination == processId) =
      timers.filter (·.destination == processId) := by
  induction timers with
  | nil => rfl
  | cons timer rest ih =>
    have rest' := ih fun timer mem => other timer (List.mem_cons_of_mem _ mem)
    by_cases same : timer.reference = reference
    · have ne := other timer List.mem_cons_self same
      cases found : change timer with
      | none => simp [found, ne, rest']
      | some changed =>
        simp [found, ne, rest', destination _ _ found]
    · simp [kept timer same, List.filter_cons, rest']

private theorem not_mem_destinations {timers : List Timer} {reference : List Nat}
    {processId : PID}
    (out : processId ∉ (timers.filter (·.reference == reference)).map (·.destination)) :
    ∀ timer ∈ timers, timer.reference = reference → timer.destination ≠ processId :=
  fun timer mem same equal => out (List.mem_map.mpr ⟨timer, by simp [mem, same], equal⟩)

/-- Removing the timers with a reference keeps the timers sending to other processes. -/
private theorem keeps_filter_reference {timers : List Timer} {reference : List Nat}
    {processId : PID}
    (out : processId ∉ (timers.filter (·.reference == reference)).map (·.destination)) :
    (timers.filter (·.reference != reference)).filter (·.destination == processId) =
      timers.filter (·.destination == processId) := by
  have equal : timers.filter (·.reference != reference) =
      timers.filterMap fun other => if other.reference != reference then some other else none := by
    clear out
    induction timers with
    | nil => rfl
    | cons head rest ih => simp only [List.filter_cons, List.filterMap_cons, ih]; split <;> rfl
  rw [equal]
  exact keeps_reference (not_mem_destinations out) (fun other ne => by simp [ne])
    fun other changed found => by split at found <;> simp at found; subst found; rfl

/-- The state after a timer step. -/
private def State.timerNext (state : State) (timer : Timer) : State :=
  if timer.expired then
    { state.deliver timer.destination timer.message with
      timers := state.timers.filter (·.reference != timer.reference) }
  else
    { state with timers := state.timers.map fun other =>
        if other.reference == timer.reference then { other with expired := true } else other }

private theorem frames_timer {state : State} {timer : Timer} :
    Frames ((timer.footprint state).reads ++ (timer.footprint state).writes)
      (timer.footprint state).writes (·.timerNext timer) state := by
  have expire := frames_timers (state := state) (destinations :=
      (state.timers.filter (·.reference == timer.reference)).map (·.destination))
    (change := List.map fun other =>
      if other.reference == timer.reference then { other with expired := true } else other)
    fun processId out => by
      have equal : ∀ timers : List Timer, timers.map (fun other =>
          if other.reference == timer.reference then { other with expired := true } else other) =
          timers.filterMap fun other => some
            (if other.reference == timer.reference then { other with expired := true } else other) :=
        fun timers => by induction timers <;> simp_all
      rw [equal]
      exact keeps_reference (not_mem_destinations out) (fun other ne => by simp [ne])
        fun other changed found => by
          simp only [Option.some.injEq] at found; subst found; split <;> rfl
  have filter : ∀ other : State, other.timers = state.timers → Frames [.timers]
      (.timers :: ((state.timers.filter (·.reference == timer.reference)).map (·.destination)).map
        .timersTo)
      (fun state => { state with timers := state.timers.filter (·.reference != timer.reference) })
      other := fun other timers => frames_timers (state := other)
    (change := List.filter (·.reference != timer.reference))
    fun processId out => by
      rw [timers]; exact keeps_filter_reference out
  unfold Timer.footprint
  split
  · rename_i expired
    have composed := Frames.comp (first := (·.deliver timer.destination timer.message))
      (state := state) frames_deliver fun other agree => filter _ (by
        rw [State.timers_deliver]; exact (agree .timers (by simp)).symm)
    refine (Frames.congr composed fun other _ => by simp [State.timerNext, expired]).mono
      ?_ ?_ ?_
    all_goals intro loc; simp only [List.mem_append, List.mem_cons, timersWith_eq, List.mem_map,
      List.not_mem_nil, or_false]; grind
  · rename_i expired
    refine (Frames.congr expire fun other _ => by simp [State.timerNext, expired]).mono ?_ ?_ ?_
    all_goals intro loc; simp only [List.mem_append, List.mem_cons, timersWith_eq, List.mem_map,
      List.not_mem_nil, or_false]; grind

/-- A request frames the state and its reply depends only on what it reads. -/
private def RequestFrames (reads writes : List Loc) (state : State) (processId : PID)
    (query : Request) : Prop :=
  Frames reads writes (fun state => (state.request processId query).2) state ∧
    ∀ other, (∀ loc ∈ reads, Agree state other loc) →
      (other.request processId query).1 = (state.request processId query).1

private theorem RequestFrames.mono {reads writes reads' writes' : List Loc} {state : State}
    {processId : PID} {query : Request} (frames : RequestFrames reads writes state processId query)
    (moreReads : reads ⊆ reads') (moreWrites : writes ⊆ writes')
    (read : ∀ loc ∈ writes', loc ∉ writes → loc ∈ reads') :
    RequestFrames reads' writes' state processId query :=
  ⟨frames.1.mono moreReads moreWrites read, fun other agree =>
    frames.2 other fun loc mem => agree loc (moreReads mem)⟩

/-- Prove that one list of locations is included in another. -/
local macro "locs" : tactic => `(tactic| (
  intro loc
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false,
    Loc.process, List.mem_map, monitorWrites]
  grind [Field.mem_all]))

private theorem frames_request {state : State} {processId : PID} {process : ProcessState}
    {query : Request} (found : state.processes processId = some process) :
    RequestFrames (.alive processId :: .field processId .refCounter ::
        (Request.footprint state processId process query).reads ++
          (Request.footprint state processId process query).writes)
      (Request.footprint state processId process query).writes state processId query := by
  have record : state.process processId = process := by simp [State.process, found]
  cases query with
  | monitor target alias =>
    have frames := frames_monitor (state := state) (processId := processId) (target := target)
      (alias := alias) rfl
    refine ⟨Frames.congr (frames.mono ?_ ?_ ?_) fun _ _ => rfl, fun other agree => ?_⟩
    · simp only [Request.footprint, monitorWrites]; locs
    · simp only [Request.footprint, monitorWrites]; locs
    · simp only [Request.footprint, monitorWrites]; locs
    · have counter := Agree.same (agree (.field processId .refCounter) (by simp))
      simp only [Field.same] at counter
      have reference : ∀ state : State, (state.monitor processId target alias).1 =
          processId ++ [(state.process processId).refCounter + 1] := fun state => by
        simp only [State.monitor]; split <;> rfl
      change Term.reference (other.monitor processId target alias).1 =
        Term.reference (state.monitor processId target alias).1
      rw [reference, reference, counter]
  | demonitor reference flush =>
    have monitoring : ∀ other : State,
        (∀ loc ∈ [Loc.field processId .monitoring], Agree state other loc) →
        (other.process processId).monitoring = process.monitoring := fun other agree => by
      have := Agree.same (agree (.field processId .monitoring) (by simp))
      simp only [Field.same] at this; rw [← this, record]
    generalize erase_eq : (flush && !process.monitoring.any (·.1 == reference)) = erase
    let watched := fun (state : State) (entry : List Nat × PID) =>
      if entry.1 == reference then
        state.modify entry.2 fun watched =>
          { watched with monitors := watched.monitors.filter (·.1 != reference) }
      else state
    have unwatched : ∀ state : State, Frames
        (process.monitoring.flatMap fun (found, target) =>
          if found == reference then [.alive target, .field target .monitors] else [])
        (process.monitoring.flatMap fun (found, target) =>
          if found == reference then [.field target .monitors] else [])
        (fun state => process.monitoring.foldl watched state) state := fun state =>
      Frames.foldl fun entry _ state => by
        obtain ⟨found, target⟩ := entry
        show Frames (if found == reference then [.alive target, .field target .monitors] else [])
          (if found == reference then [.field target .monitors] else []) (watched · (found, target))
          state
        by_cases same : found = reference
        · simp only [same, beq_self_eq_true, ite_true]
          exact Frames.congr (frames_modify (processId := target) (reads := [.monitors])
            (writes := [.monitors]) (change := fun watched =>
              { watched with monitors := watched.monitors.filter (·.1 != reference) })
            (by changes)) fun other _ => by simp [watched]
        · have differ : (found == reference) = false := by simpa using same
          simp only [differ, Bool.false_eq_true, ite_false]
          exact Frames.congr Frames.id fun other _ => by
            simp only [watched, differ, Bool.false_eq_true, ite_false]
    have own : ∀ state : State, Frames
        (.alive processId :: ([Field.monitoring, Field.aliases] ++
          if erase then [Field.mailbox] else []).map (.field processId))
        (([Field.monitoring, Field.aliases] ++ if erase then [Field.mailbox] else []).map
          (.field processId))
        (fun state => state.modify processId fun process =>
          { process with
              monitoring := process.monitoring.filter (·.1 != reference)
              aliases := process.aliases.erase reference
              mailbox := if erase then process.mailbox.eraseP (isMonitorMessage reference)
                else process.mailbox }) state := fun state => by
      cases erase
      · exact frames_modify (by changes)
      · exact frames_modify (by changes)
    refine ⟨Frames.congr ((Frames.comp (unwatched state) fun _ _ => own _).mono ?_ ?_ ?_)
        fun other agree => ?_, fun other agree => ?_⟩
    all_goals try (
      simp only [Request.footprint, erase_eq]
      intro loc
      cases erase <;> simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil,
        or_false, ite_true, ite_false, Bool.false_eq_true, List.map_cons,
        List.map_nil, List.append_nil, List.cons_append, List.nil_append] <;> grind)
    all_goals
      have same := monitoring other fun loc mem => agree loc (by
        simp at mem; subst mem; simp [Request.footprint])
      simp only [State.request, same, record, erase_eq]
      try rfl
  | link target =>
    by_cases self : target = processId
    · subst self
      refine ⟨Frames.congr (Frames.id.mono ?_ ?_ ?_) fun other _ => ?_, fun other _ => ?_⟩
      all_goals first | (simp only [Request.footprint]; locs) | simp [State.request]
    obtain ⟨live, alive⟩ : ∃ live, (state.processes target).isSome = live := ⟨_, rfl⟩
    have alive' : ∀ other : State, (∀ loc ∈ [Loc.alive target], Agree state other loc) →
        (other.processes target).isSome = live := fun other agree =>
      alive ▸ (agree (.alive target) (by simp)).symm
    cases live
    · have trapExit : ∀ other : State, (∀ loc ∈ [Loc.field processId .trapExit], Agree state other loc) →
          (other.process processId).trapExit = process.trapExit := fun other agree => by
        have := Agree.same (agree (.field processId .trapExit) (by simp))
        simp only [Field.same] at this; rw [← this, record]
      have none : ∀ other : State, (other.processes target).isSome = false →
          other.processes target = none := fun other => by simp
      cases trap : process.trapExit
      · refine ⟨Frames.congr (change' := fun state => state) (Frames.id.mono ?_ ?_ ?_)
          fun other agree => ?_, fun other agree => ?_⟩
        all_goals try (simp only [Request.footprint, self, alive, trap]; locs)
        all_goals
          have dead := none other (alive' other fun loc mem => agree loc (by
            simp at mem; subst mem; simp [Request.footprint, self, alive, trap]))
          have trapped := trapExit other fun loc mem => agree loc (by
            simp at mem; subst mem; simp [Request.footprint, self, alive, trap])
          simp [State.request, self, dead, trapped, trap, none state alive, record]
      · refine ⟨Frames.congr (frames_deliver (processId := processId)
          (message := .tuple #[.atom "EXIT", .pid target, .atom "noproc"]) |>.mono ?_ ?_ ?_)
          fun other agree => ?_, fun other agree => ?_⟩
        all_goals try (simp only [Request.footprint, self, alive, trap, ite_true]; locs)
        all_goals
          have dead := none other (alive' other fun loc mem => agree loc (by
            simp at mem; subst mem; simp [Request.footprint, self, alive, trap]))
          have trapped := trapExit other fun loc mem => agree loc (by
            simp at mem; subst mem; simp [Request.footprint, self, alive, trap])
          simp [State.request, self, dead, trapped, trap, none state alive, record]
    · have some : ∀ other : State, (other.processes target).isSome = true →
          ∃ process, other.processes target = some process := fun other =>
        Option.isSome_iff_exists.mp
      refine ⟨Frames.congr ((Frames.comp (frames_modify (reads := [.links]) (writes := [.links])
          (processId := processId)
          (change := fun process => { process with links := insertOnce target process.links })
          (by changes)) fun _ _ =>
            frames_modify (reads := [.links]) (writes := [.links]) (processId := target)
              (change := fun other => { other with links := insertOnce processId other.links })
              (by changes)).mono ?_ ?_ ?_)
          fun other agree => ?_, fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint, self, alive]; locs)
      all_goals
        obtain ⟨_, live⟩ := some other (alive' other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint, self, alive]))
        obtain ⟨_, live'⟩ := some state alive
        simp [State.request, self, live, live']
  | unlink target =>
    refine ⟨(Frames.comp (frames_modify (reads := [.links]) (writes := [.links]) (by changes))
      fun _ _ => frames_modify (reads := [.links]) (writes := [.links]) (by changes)).mono
        ?_ ?_ ?_, fun _ _ => rfl⟩
    all_goals simp only [Request.footprint]; locs
  | exit target reason =>
    have trapExit : ∀ other : State, (∀ loc ∈ [Loc.field processId .trapExit], Agree state other loc) →
        (other.process processId).trapExit = process.trapExit := fun other agree => by
      have := Agree.same (agree (.field processId .trapExit) (by simp))
      simp only [Field.same] at this; rw [← this, record]
    by_cases own : (target = processId && isNormal reason && !process.trapExit) = true
    · refine ⟨Frames.congr (frames_kill (processId := processId) (reason := reason) |>.mono ?_ ?_ ?_)
        fun other agree => ?_,
        fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint, own, ite_true]; locs)
      all_goals
        have trapped := trapExit other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint, own])
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at own
        obtain ⟨⟨rfl, normal⟩, trap⟩ := own
        simp [State.request, normal, trap, trapped, record]
    · refine ⟨Frames.congr (frames_signal (target := target) (sender := processId) (reason := reason)
        (untrappable := isKill reason) rfl |>.mono ?_ ?_ fun loc mem out =>
          absurd (by simpa [Request.footprint, own] using mem) out)
        fun other agree => ?_,
        fun other agree => ?_⟩
      · intro loc mem
        simp only [Request.footprint, own, ite_false, Bool.false_eq_true, List.mem_cons,
          List.mem_append] at mem ⊢
        simp [mem]
      · intro loc mem
        simpa [Request.footprint, own] using mem
      all_goals
        have trapped := trapExit other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint, own])
        have cond : (decide (target = processId) && isNormal reason &&
            !(other.process processId).trapExit) = false := by
          rw [trapped]; simpa using own
        have cond' : (decide (target = processId) && isNormal reason &&
            !(state.process processId).trapExit) = false := by
          rw [record]; simpa using own
        simp only [State.request, cond, cond', Bool.false_eq_true, ite_false]
  | trapExit enabled =>
    refine ⟨(frames_modify (reads := []) (writes := [.trapExit]) (by changes)).mono ?_ ?_ ?_,
      fun other agree => ?_⟩
    all_goals try (simp only [Request.footprint]; locs)
    have trapExit := Agree.same (agree (.field processId .trapExit) (by simp [Request.footprint]))
    simp only [Field.same] at trapExit
    simp [State.request, trapExit]
  | alive target =>
    refine ⟨Frames.id.mono ?_ ?_ ?_, fun other agree => ?_⟩
    all_goals try (simp only [Request.footprint]; locs)
    have alive := agree (.alive target) (by simp [Request.footprint])
    simp only [Agree] at alive
    simp [State.request, alive]
  | sendAlias alias message =>
    have aliases : ∀ other : State, (∀ loc ∈ [Loc.field alias.dropLast .aliases], Agree state other loc) →
        (other.process alias.dropLast).aliases = (state.process alias.dropLast).aliases :=
      fun other agree => by
        have := Agree.same (agree (.field alias.dropLast .aliases) (by simp))
        simp only [Field.same] at this; rw [this]
    by_cases active : (state.process alias.dropLast).aliases.contains alias = true
    · refine ⟨Frames.congr (frames_deliver (processId := alias.dropLast) (message := message)
        |>.mono ?_ ?_ ?_) fun other agree => ?_, fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint]; locs)
      all_goals
        have same := aliases other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint])
        simp only [State.request, same, active, ite_true]
    · refine ⟨Frames.congr (Frames.id.mono ?_ ?_ ?_) fun other agree => ?_,
        fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint]; locs)
      all_goals
        have same := aliases other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint])
        simp only [Bool.not_eq_true] at active
        simp only [State.request, same, active, Bool.false_eq_true, ite_false]
  | startTimer destination message duration =>
    let timer : Timer :=
      { reference := processId ++ [process.refCounter + 1], destination, message, duration }
    have counter : ∀ other : State,
        (∀ loc ∈ [Loc.field processId .refCounter], Agree state other loc) →
        (other.process processId).refCounter = process.refCounter := fun other agree => by
      have := Agree.same (agree (.field processId .refCounter) (by simp))
      simp only [Field.same] at this; rw [← this, record]
    have count := frames_modify (processId := processId) (reads := [.refCounter])
      (writes := [.refCounter]) (state := state)
      (change := fun process => { process with refCounter := process.refCounter + 1 }) (by changes)
    obtain ⟨live, alive⟩ : ∃ live, (state.processes destination).isSome = live := ⟨_, rfl⟩
    have alive' : ∀ other : State, (∀ loc ∈ [Loc.alive destination], Agree state other loc) →
        (other.processes destination).isSome = live := fun other agree =>
      alive ▸ (agree (.alive destination) (by simp)).symm
    cases live
    · refine ⟨Frames.congr (count.mono ?_ ?_ ?_) fun other agree => ?_, fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint, alive]; locs)
      all_goals
        have counted := counter other fun loc mem => agree loc (by simp at mem; simp [mem])
        have dead := alive' other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint])
        simp [State.request, counted, dead, record]
    · refine ⟨Frames.congr ((Frames.comp count fun _ _ => frames_timers (destinations := [destination])
          (change := (· ++ [timer])) fun processId out => by
            simp only [List.mem_singleton] at out
            simp [List.filter_append, timer, Ne.symm out]).mono ?_ ?_ ?_) fun other agree => ?_,
        fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint, alive]; locs)
      all_goals
        have counted := counter other fun loc mem => agree loc (by simp at mem; simp [mem])
        have live := alive' other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint])
        simp [State.request, counted, live, record, timer]
  | cancelTimer reference =>
    have timers : ∀ other : State, (∀ loc ∈ [Loc.timers], Agree state other loc) →
        other.timers = state.timers := fun other agree => (agree .timers (by simp)).symm
    cases found' : state.timers.find? fun timer => timer.reference == reference && !timer.expired with
    | none =>
      refine ⟨Frames.congr (Frames.id.mono ?_ ?_ ?_) fun other agree => ?_, fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint]; locs)
      all_goals
        have same := timers other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint])
        simp [State.request, same, found']
    | some timer =>
      have cancels : ∀ other : State,
          (∀ loc ∈ [Loc.elapsed, Loc.field processId .cancels], Agree state other loc) →
          other.elapsed processId (other.process processId).cancels =
            state.elapsed processId (state.process processId).cancels := fun other agree => by
        have elapsed : state.elapsed = other.elapsed := agree .elapsed (by simp)
        have counted := Agree.same (agree (.field processId .cancels) (by simp))
        simp only [Field.same] at counted
        rw [elapsed, counted]
      refine ⟨Frames.congr ((Frames.comp (frames_timers (state := state)
          (destinations := (state.timers.filter (·.reference == reference)).map (·.destination))
          (change := List.filter (·.reference != reference))
          fun processId out => keeps_filter_reference out) fun _ _ =>
            frames_modify (processId := processId) (reads := [.cancels]) (writes := [.cancels])
              (change := fun process => { process with cancels := process.cancels + 1 })
              (by changes)).mono ?_ ?_ ?_)
          fun other agree => ?_, fun other agree => ?_⟩
      all_goals try (simp only [Request.footprint, timersWith_eq]; locs)
      all_goals
        have same := timers other fun loc mem => agree loc (by
          simp at mem; subst mem; simp [Request.footprint])
        have counted := cancels other fun loc mem => agree loc (by
          simp at mem; rcases mem with rfl | rfl <;> simp [Request.footprint])
        simp [State.request, same, found', counted]

/-- Steps of a process from states agreeing on what it reads: the same events,
processes and outcomes, writing the same values and keeping the rest. -/
private def Similar (writes : List Loc) (other : State) (transition transition' : Transition α) :
    Prop :=
  transition'.event = transition.event ∧ transition'.tasks = transition.tasks ∧
    transition'.finished = transition.finished ∧ transition'.exhausted = transition.exhausted ∧
    (∀ loc, loc ∉ writes → Agree transition'.state other loc) ∧
    ∀ loc ∈ writes, Agree transition.state transition'.state loc

private theorem similar_of_frames {reads writes : List Loc} {change : State → State}
    {state other : State} {transition transition' : Transition α}
    (frames : Frames reads writes change state) (agree : ∀ loc ∈ reads, Agree state other loc)
    (before : transition.state = change state) (after : transition'.state = change other)
    (event : transition'.event = transition.event) (tasks : transition'.tasks = transition.tasks)
    (finished : transition'.finished = transition.finished)
    (exhausted : transition'.exhausted = transition.exhausted) :
    Similar writes other transition transition' := by
  obtain ⟨keeps, determined⟩ := frames other agree
  exact ⟨event, tasks, finished, exhausted, fun loc out => after ▸ keeps loc out,
    fun loc mem => before ▸ after ▸ determined loc mem⟩

/-- Lists related elementwise. -/
private inductive Related (relation : γ → δ → Prop) : List γ → List δ → Prop
  | nil : Related relation [] []
  | cons {first : γ} {second : δ} {rest : List γ} {rest' : List δ} :
      relation first second → Related relation rest rest' →
        Related relation (first :: rest) (second :: rest')

private theorem Related.get {relation : γ → δ → Prop} {first : List γ} {second : List δ}
    (related : Related relation first second) {index : Nat} {item' : δ}
    (found : second[index]? = some item') : ∃ item, first[index]? = some item ∧ relation item item' := by
  induction related generalizing index with
  | nil => simp at found
  | cons head _ ih =>
    cases index with
    | zero => simp at found; subst found; exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

private theorem Related.get' {relation : γ → δ → Prop} {first : List γ} {second : List δ}
    (related : Related relation first second) {index : Nat} {item : γ}
    (found : first[index]? = some item) : ∃ item', second[index]? = some item' ∧ relation item item' := by
  induction related generalizing index with
  | nil => simp at found
  | cons head _ ih =>
    cases index with
    | zero => simp at found; subst found; exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

private theorem related_single {relation : γ → δ → Prop} {first : γ} {second : δ}
    (related : relation first second) : Related relation [first] [second] :=
  .cons related .nil

private theorem spawnWith_fst {state : State} {processId : PID} {options : SpawnOptions} :
    (state.spawnWith processId options).1 =
      processId ++ [(state.process processId).children + 1] := rfl

/-- What every step of a live process reads. -/
private def baseReads (processId : PID) : List Loc :=
  [.alive processId, .field processId .signal, .field processId .pdict, .field processId .refCounter]

/-- Steps of a process with a footprint, from states agreeing on what it reads,
are similar. -/
private theorem transitions_similar {state other : State} {processId : PID} {task : Task α}
    {footprint : Footprint} (found : task.footprint state processId = some footprint)
    (agree : ∀ loc ∈ footprint.reads ++ footprint.writes, Agree state other loc) :
    Related (Similar footprint.writes other) (task.transitions state processId)
      (task.transitions other processId) := by
  obtain ⟨computation, finish⟩ := task
  unfold Task.footprint at found
  cases live : state.processes processId with
  | none => simp [live] at found
  | some process =>
  simp only [live, Option.map_eq_some_iff] at found
  obtain ⟨step, stepped, rfl⟩ := found
  have agree' : ∀ loc, loc ∈ baseReads processId ∨ loc ∈ step.reads ∨ loc ∈ step.writes →
      Agree state other loc := fun loc mem => agree loc (by
    simp only [baseReads, List.mem_cons, List.not_mem_nil, or_false] at mem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases mem with (h | h | h | h) | h | h <;> simp [h])
  have base : ∀ loc ∈ baseReads processId, Agree state other loc := fun loc mem =>
    agree' loc (.inl mem)
  have record : state.process processId = process := by simp [State.process, live]
  have signal : (other.process processId).signal = process.signal := by
    have := Agree.same (base (.field processId .signal) (by simp [baseReads]))
    simp only [Field.same] at this; rw [← this, record]
  have view : other.view processId = state.view processId := by
    have pdict := Agree.same (base (.field processId .pdict) (by simp [baseReads]))
    have counter := Agree.same (base (.field processId .refCounter) (by simp [baseReads]))
    simp only [Field.same] at pdict counter
    simp [State.view, pdict, counter]
  have exit : ∀ reason, step = state.exitFootprint processId reason →
      Frames (baseReads processId ++ step.reads ++ step.writes) step.writes
        (·.terminate processId reason) state := fun reason equal => by
    subst equal; exact frames_terminate.mono (by simp) (by simp) fun loc mem out => absurd mem out
  have within : ∀ {reads}, reads ⊆ baseReads processId ++ step.reads ++ step.writes →
      ∀ loc ∈ reads, Agree state other loc := fun sub loc mem => agree' loc (by
    have := sub mem; simp only [List.mem_append] at this; rcases this with (h | h) | h <;> simp [h])
  unfold Task.stepFootprint at stepped
  simp only [Task.transitions, signal, record, view]
  cases found : process.signal with
  | some reason =>
    simp only [found, Option.some.injEq] at stepped
    exact related_single (similar_of_frames (exit reason stepped.symm) (within (by simp)) rfl rfl
      rfl rfl rfl rfl)
  | none =>
  simp only [found] at stepped
  cases computation with
  | ok value =>
    simp only [Option.some.injEq] at stepped
    exact related_single (similar_of_frames (exit _ stepped.symm) (within (by simp)) rfl rfl
      rfl rfl rfl rfl)
  | error exception =>
    cases exception with
    | exhausted =>
      simp only [Option.some.injEq] at stepped
      subst stepped
      exact related_single (similar_of_frames frames_update (within (by simp)) rfl rfl
        rfl rfl rfl rfl)
    | _ =>
      simp only [Option.some.injEq] at stepped
      exact related_single (similar_of_frames (exit _ stepped.symm) (within (by simp)) rfl rfl
        rfl rfl rfl rfl)
  | get next =>
    simp only [Option.some.injEq] at stepped
    subst stepped
    exact related_single (similar_of_frames Frames.id (within (by simp)) rfl rfl
      rfl rfl rfl rfl)
  | set updated next => simp at stepped
  | schedule options child next =>
    simp only [Option.some.injEq] at stepped
    have children : (other.process processId).children = process.children := by
      have := Agree.same (agree' (.field processId .children) (by subst stepped; simp))
      simp only [Field.same] at this; rw [← this, record]
    have spawned : (other.spawnWith processId options).1 = (state.spawnWith processId options).1 := by
      simp only [spawnWith_fst, children, record]
    have frames : Frames (baseReads processId ++ step.reads ++ step.writes) step.writes
        (fun state => (state.spawnWith processId options).2) state := by
      subst stepped
      refine (frames_spawnWith live).mono ?_ ?_ ?_
      all_goals obtain ⟨doLink, doMonitor⟩ := options
      all_goals cases doLink <;> cases doMonitor <;> intro loc <;>
        simp only [spawnWrites, baseReads, List.mem_append, List.mem_cons, Loc.process,
          List.mem_map, List.not_mem_nil, or_false, ite_true, ite_false, Bool.false_eq_true,
          List.cons_append, List.nil_append, List.append_nil] <;> grind
    simp only [spawned]
    exact related_single (similar_of_frames frames (within (by simp)) rfl rfl rfl rfl rfl rfl)
  | send destination message next =>
    simp only [Option.some.injEq] at stepped
    subst stepped
    exact related_single (similar_of_frames frames_deliver (within (by simp)) rfl rfl
      rfl rfl rfl rfl)
  | receive timeout select next =>
    cases unmatched : selectMessage (select (state.view processId)) process.mailbox with
    | some => simp [unmatched] at stepped
    | none =>
      simp only [unmatched, Option.some.injEq] at stepped
      subst stepped
      have mailbox : (other.process processId).mailbox = process.mailbox := by
        have := Agree.same (agree' (.field processId .mailbox) (by simp))
        simp only [Field.same] at this; rw [← this, record]
      simp only [mailbox, unmatched]
      cases timeout with
      | infinity => exact .nil
      | _ => exact related_single (similar_of_frames Frames.id (within (by simp)) rfl rfl
          rfl rfl rfl rfl)
  | request query next =>
    simp only [Option.some.injEq] at stepped
    subst stepped
    have frames := frames_request (query := query) live
    have reads := within (reads := .alive processId :: .field processId .refCounter ::
      (Request.footprint state processId process query).reads ++
        (Request.footprint state processId process query).writes) (by
      intro loc mem; simp only [List.mem_cons, List.mem_append] at mem
      simp only [baseReads, List.mem_append, List.mem_cons]; grind)
    dsimp only
    rw [frames.2 other reads]
    exact related_single (similar_of_frames frames.1 reads rfl rfl rfl rfl rfl rfl)

/-- What a timer step observes. -/
private def Timer.event (timer : Timer) : Event :=
  if timer.expired then .arrive timer.destination timer.message else .expire timer.reference

private theorem timerSteps_eq {state : State} :
    state.timerSteps = state.timers.map fun timer => (timer.event, state.timerNext timer) := by
  simp only [State.timerSteps]
  congr 1; funext timer
  simp only [Timer.event, State.timerNext]
  split <;> rfl

/-- The steps of a running configuration, by key. -/
private theorem mem_steps {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {key : Key}
    {event : Event} {next : Config α} :
    (key, event, next) ∈ (Config.running state tasks finished exhausted).steps ↔
      (∃ before processId task after transition index,
        tasks = before ++ (processId, task) :: after ∧
        (task.transitions state processId)[index]? = some transition ∧
        key = .process processId index ∧ event = transition.event ∧
        next = transition.apply before after finished exhausted) ∨
      ∃ timer index, state.timers[index]? = some timer ∧ key = .timer index ∧
        event = timer.event ∧ next = .running (state.timerNext timer) tasks finished exhausted := by
  have processes : (key, event, next) ∈ ((splits tasks).flatMap fun (before, (processId, task), after) =>
      (task.transitions state processId).zipIdx.map fun (transition, index) =>
        ((Key.process processId index : Key), transition.event,
          transition.apply before after finished exhausted)) ↔
      ∃ before processId task after transition index,
        tasks = before ++ (processId, task) :: after ∧
        (task.transitions state processId)[index]? = some transition ∧
        key = .process processId index ∧ event = transition.event ∧
        next = transition.apply before after finished exhausted := by
    simp only [List.mem_flatMap, List.mem_map, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨before, processId, task, after, split, transition, index, mem, rfl, rfl, rfl⟩
      exact ⟨before, processId, task, after, transition, index, eq_of_mem_splits split,
        List.mem_zipIdx_iff_getElem?.mp mem, rfl, rfl, rfl⟩
    · rintro ⟨before, processId, task, after, transition, index, rfl, found, rfl, rfl, rfl⟩
      exact ⟨before, processId, task, after, mem_splits, transition, index,
        List.mem_zipIdx_iff_getElem?.mpr found, rfl, rfl, rfl⟩
  have timers : (key, event, next) ∈ (state.timerSteps.zipIdx.map fun ((event, after), index) =>
      ((Key.timer index : Key), event, Config.running after tasks finished exhausted)) ↔
      ∃ timer index, state.timers[index]? = some timer ∧ key = .timer index ∧
        event = timer.event ∧ next = .running (state.timerNext timer) tasks finished exhausted := by
    simp only [List.mem_map, Prod.exists, Prod.mk.injEq, timerSteps_eq]
    constructor
    · rintro ⟨event', after, index, mem, rfl, rfl, rfl⟩
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map] at mem
      obtain ⟨timer, found, equal⟩ := Option.map_eq_some_iff.mp mem
      simp only [Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      exact ⟨timer, index, found, rfl, rfl, rfl⟩
    · rintro ⟨timer, index, found, rfl, rfl, rfl⟩
      exact ⟨_, _, index, by rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map, found]; rfl,
        rfl, rfl, rfl⟩
  simp only [Config.steps]
  split
  · rename_i empty
    rw [processes]
    simp [empty]
  · rw [List.mem_append, processes, timers]

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

/-! ### Commuting steps -/

/-- Entries with distinct keys split a list around a key in one way. -/
private theorem split_unique {entries before after before' after' : List (PID × γ)} {key : PID}
    {item item' : γ} (distinct : entries.Pairwise fun first second => first.1 ≠ second.1)
    (split : entries = before ++ (key, item) :: after)
    (split' : entries = before' ++ (key, item') :: after') :
    before = before' ∧ item = item' ∧ after = after' := by
  subst split
  rcases split_order split' with ⟨rfl, same, rfl⟩ | ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
  · simp only [Prod.mk.injEq, true_and] at same; exact ⟨rfl, same, rfl⟩
  · exact absurd rfl (pairwise_between (relation := fun first second : PID × γ => first.1 ≠ second.1)
      (first := (key, item)) (second := (key, item')) (by simpa using distinct))
  · exact absurd rfl (pairwise_between (relation := fun first second : PID × γ => first.1 ≠ second.1)
      (first := (key, item')) (second := (key, item)) (by simpa using distinct))

private theorem lookup_eq {entries : List (PID × γ)} {key : PID} {item : γ}
    (distinct : entries.Pairwise fun first second => first.1 ≠ second.1)
    (mem : (key, item) ∈ entries) : entries.lookup key = some item := by
  induction entries with
  | nil => simp at mem
  | cons head rest ih =>
    obtain ⟨key', item'⟩ := head
    simp only [List.pairwise_cons] at distinct
    simp only [List.mem_cons, Prod.mk.injEq] at mem
    rcases mem with ⟨rfl, rfl⟩ | mem
    · simp [List.lookup]
    · have ne : key ≠ key' := fun equal => distinct.1 (key, item) mem equal.symm
      simp [List.lookup, beq_false_of_ne ne, ih distinct.2 mem]

private theorem mem_of_lookup {entries : List (PID × γ)} {key : PID} {item : γ}
    (found : entries.lookup key = some item) : (key, item) ∈ entries := by
  induction entries with
  | nil => simp [List.lookup] at found
  | cons head rest ih =>
    obtain ⟨key', item'⟩ := head
    simp only [List.lookup] at found
    split at found
    · rename_i same; simp only [beq_iff_eq] at same; subst same
      simp only [Option.some.injEq] at found; subst found; simp
    · exact List.mem_cons_of_mem _ (ih found)

/-- Footprints of commuting steps do not conflict. -/
private theorem independent_footprints {state : State} {tasks : List (PID × Task α)}
    {first second : Key} (independent : Key.independent state tasks first second = true) :
    ∃ footprint footprint', first.footprint state tasks = some footprint ∧
      second.footprint state tasks = some footprint' ∧
      (∀ loc ∈ footprint.writes, loc ∉ footprint'.reads ++ footprint'.writes) ∧
      (∀ loc ∈ footprint'.writes, loc ∉ footprint.reads ++ footprint.writes) := by
  simp only [Key.independent, Bool.and_eq_true] at independent
  obtain ⟨-, independent⟩ := independent
  split at independent
  · rename_i footprint footprint' found found'
    simp only [Bool.not_eq_true'] at independent
    simp [Footprint.conflicts] at independent
    obtain ⟨written, written'⟩ := independent
    refine ⟨footprint, footprint', found, found', fun loc mem out => ?_, fun loc mem out => ?_⟩ <;>
      simp only [List.mem_append] at out
    · rcases out with out | out
      · exact (written loc mem).1 out
      · exact (written loc mem).2 out
    · rcases out with out | out
      · exact written' loc mem out
      · exact (written loc out).2 mem
  · simp at independent

private theorem distinct_keys {state : State} {tasks : List (PID × Task α)} {first second : Key}
    (independent : Key.independent state tasks first second = true) :
    match first, second with
    | .process first _, .process second _ => first ≠ second
    | .timer _, .timer _ => False
    | _, _ => True := by
  simp only [Key.independent, Bool.and_eq_true] at independent
  obtain ⟨distinct, -⟩ := independent
  split <;> simp_all

private theorem process_footprint {state : State} {tasks : List (PID × Task α)} {processId : PID}
    {index : Nat} {footprint : Footprint}
    (found : (Key.process processId index).footprint state tasks = some footprint) :
    ∃ task, tasks.lookup processId = some task ∧ task.footprint state processId = some footprint := by
  simp only [Key.footprint, Option.bind_eq_some_iff] at found
  exact found

/-- A change keeping what it does not write agrees on locations it does not write. -/
private theorem agree_unwritten {state changed : State} {writes locs : List Loc}
    (keeps : ∀ loc, loc ∉ writes → Agree changed state loc) (disjoint : ∀ loc ∈ writes, loc ∉ locs) :
    ∀ loc ∈ locs, Agree state changed loc :=
  fun loc mem => (keeps loc fun written => disjoint loc written mem).symm

/-- Two changes writing disjoint locations, each applied before and after the
other, reach the same state. -/
private theorem commute_agree {state first second firstSecond secondFirst : State}
    {writes writes' : List Loc} (disjoint : ∀ loc ∈ writes, loc ∉ writes')
    (keepsFirst : ∀ loc, loc ∉ writes → Agree first state loc)
    (keepsSecond : ∀ loc, loc ∉ writes' → Agree second state loc)
    (keepsSecondAfter : ∀ loc, loc ∉ writes' → Agree firstSecond first loc)
    (sameSecond : ∀ loc ∈ writes', Agree second firstSecond loc)
    (keepsFirstAfter : ∀ loc, loc ∉ writes → Agree secondFirst second loc)
    (sameFirst : ∀ loc ∈ writes, Agree first secondFirst loc) :
    secondFirst = firstSecond := by
  apply State.ext_agree
  intro loc
  by_cases written : loc ∈ writes
  · exact (sameFirst loc written).symm.trans (keepsSecondAfter loc (disjoint loc written)).symm
  · by_cases written' : loc ∈ writes'
    · exact (keepsFirstAfter loc written).trans (sameSecond loc written')
    · exact (keepsFirstAfter loc written).trans ((keepsSecond loc written').trans
        ((keepsFirst loc written).symm.trans (keepsSecondAfter loc written').symm))

/-- What a step of a process with a footprint keeps. -/
private theorem keeps_of_footprint {state : State} {processId : PID} {task : Task α}
    {footprint : Footprint} (found : task.footprint state processId = some footprint)
    {transition : Transition α} {index : Nat}
    (possible : (task.transitions state processId)[index]? = some transition) :
    ∀ loc, loc ∉ footprint.writes → Agree transition.state state loc := by
  obtain ⟨transition', found', similar⟩ :=
    (transitions_similar found (other := state) fun loc _ => Agree.refl state loc).get' possible
  rw [possible, Option.some.injEq] at found'
  subst found'
  exact similar.2.2.2.2.1

private theorem timer_footprint {state : State} {tasks : List (PID × Task α)} {index : Nat}
    {footprint : Footprint} (found : (Key.timer index).footprint state tasks = some footprint) :
    ∃ timer, state.timers[index]? = some timer ∧ footprint = timer.footprint state := by
  simp only [Key.footprint, Option.map_eq_some_iff] at found
  obtain ⟨timer, found, rfl⟩ := found
  exact ⟨timer, found, rfl⟩

private theorem timers_read {timer : Timer} {state : State} : .timers ∈ (timer.footprint state).reads := by
  unfold Timer.footprint; split <;> simp

private theorem timer_step {state : State} {timer : Timer} {index : Nat}
    (found : state.timers[index]? = some timer) :
    (timer.event, state.timerNext timer) ∈ state.timerSteps := by
  rw [timerSteps_eq, List.mem_map]
  exact ⟨timer, List.mem_of_getElem? found, rfl⟩

private theorem orElse_comm {first second : Option γ} {rest : Option γ}
    (none : first = none ∨ second = none) :
    (first.orElse fun _ => second.orElse fun _ => rest) =
      second.orElse fun _ => first.orElse fun _ => rest := by
  rcases none with rfl | rfl
  · cases second <;> rfl
  · cases first <;> rfl

/-- Steps whose footprints do not conflict commute: when one step follows
another, it can also be taken first, followed by the other. -/
private theorem diamond {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {key key' : Key}
    {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (Config.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (independent : Key.independent state tasks key' key = true)
    (mem' : (key', event', next') ∈ next.steps) :
    ∃ next'', (key', event', next'') ∈ (Config.running state tasks finished exhausted).steps ∧
      Step next'' event next' := by
  have keys := distinct_keys independent
  obtain ⟨footprint', footprint, found', found, disjoint', disjoint⟩ :=
    independent_footprints independent
  have wellformed₀ := wellformed
  obtain ⟨distinct, fresh, -, quiet⟩ := wellformed
  rw [mem_steps] at mem
  rcases mem with ⟨before, processId, task, after, transition, index, split, possible, rfl, rfl, rfl⟩ |
    ⟨timer, index, timerFound, rfl, rfl, rfl⟩
  · obtain ⟨task₀, lookup, taskFootprint⟩ := process_footprint found
    rw [lookup_eq (item := task) distinct (by rw [split]; simp), Option.some.injEq] at lookup
    subst lookup
    have keeps := keeps_of_footprint taskFootprint possible
    have stepped : Step (Config.running state tasks finished exhausted) transition.event
        (transition.apply before after finished exhausted) :=
      Step.run split (List.mem_of_getElem? possible)
    have wellformed₁ := Step.wellformed stepped wellformed₀
    simp only [Transition.apply] at mem' wellformed₁
    rw [mem_steps] at mem'
    rcases mem' with ⟨before', processId', task', after', transition', index', split', possible',
      rfl, rfl, rfl⟩ | ⟨timer', index', timerFound', rfl, rfl, rfl⟩
    · simp only at keys
      obtain ⟨task₁, lookup₁, footprintFound₁⟩ := process_footprint found'
      have mem₁ := mem_of_lookup lookup₁
      obtain ⟨-, origin, -, spawned⟩ := transition_tasks (List.mem_of_getElem? possible)
      -- The other process was there before the step.
      have outside : (processId', task') ∈ before ∨ (processId', task') ∈ after := by
        have : (processId', task') ∈ before ++ transition.tasks ++ after := by rw [split']; simp
        simp only [List.mem_append] at this
        rcases this with (inBefore | inNew) | inAfter
        · exact .inl inBefore
        · exfalso
          rcases origin _ inNew with same | ⟨child, spawn, same⟩
          · exact keys same
          · obtain ⟨childPid, -⟩ := spawned child spawn
            simp only at same
            have := fresh (processId, task) (by rw [split]; simp) (processId', task₁) mem₁
              ((state.process processId).children + 1) [] (by simp [same, childPid])
            simp only at this
            omega
        · exact .inr inAfter
      rw [lookup_eq (item := task') distinct (by rw [split]; rcases outside with h | h <;> simp [h]),
        Option.some.injEq] at lookup₁
      subst lookup₁
      have agreeOther : ∀ loc ∈ footprint'.reads ++ footprint'.writes,
          Agree state transition.state loc := agree_unwritten keeps disjoint
      obtain ⟨transition₀, possible₀, similar₀⟩ :=
        (transitions_similar footprintFound₁ agreeOther).get possible'
      obtain ⟨event₀, tasks₀, finished₀, exhausted₀, keepsAfter₀, same₀⟩ := similar₀
      have keeps₀ := keeps_of_footprint footprintFound₁ possible₀
      have agreeFirst : ∀ loc ∈ footprint.reads ++ footprint.writes,
          Agree state transition₀.state loc := agree_unwritten keeps₀ disjoint'
      obtain ⟨transition₃, possible₃, similar₃⟩ :=
        (transitions_similar taskFootprint agreeFirst).get' possible
      obtain ⟨event₃, tasks₃, finished₃, exhausted₃, keeps₃, same₃⟩ := similar₃
      have states : transition₃.state = transition'.state :=
        commute_agree (fun loc mem out => disjoint loc mem (by simp [out])) keeps keeps₀
          keepsAfter₀ same₀ keeps₃ same₃
      have quietFirst := (transition_frame (List.mem_of_getElem? possible)).2.2
      have quietSecond := (transition_frame (List.mem_of_getElem? possible₀)).2.2
      have finishedComm : (transition₃.finished.orElse fun _ =>
            transition₀.finished.orElse fun _ => finished) =
          transition'.finished.orElse fun _ => transition.finished.orElse fun _ => finished := by
        rw [finished₃, finished₀]
        apply orElse_comm
        have quiet' : task.Quiet ∨ task'.Quiet := by
          rcases outside with inBefore | inAfter
          · obtain ⟨front, middle, rfl⟩ := List.append_of_mem inBefore
            have := pairwise_between (relation := fun first second : PID × Task α =>
              first.2.Quiet ∨ second.2.Quiet) (first := (processId', task'))
              (second := (processId, task)) (by rw [split] at quiet; simpa using quiet)
            exact this.symm
          · obtain ⟨middle, back, rfl⟩ := List.append_of_mem inAfter
            exact pairwise_between (relation := fun first second : PID × Task α =>
              first.2.Quiet ∨ second.2.Quiet) (first := (processId, task))
              (second := (processId', task')) (by rw [split] at quiet; simpa using quiet)
        rcases quiet' with quiet' | quiet'
        · exact .inl (quietFirst quiet')
        · exact .inr (quietSecond quiet')
      have exhaustedComm : ((exhausted || transition₀.exhausted) || transition₃.exhausted) =
          ((exhausted || transition.exhausted) || transition'.exhausted) := by
        rw [exhausted₃, exhausted₀]
        cases exhausted <;> cases transition.exhausted <;> cases transition₀.exhausted <;> rfl
      rcases outside with inBefore | inAfter
      · obtain ⟨front, middle, rfl⟩ := List.append_of_mem inBefore
        obtain ⟨rfl, -, rfl⟩ := split_unique wellformed₁.1
          (show front ++ (processId', task') :: middle ++ transition.tasks ++ after =
            front ++ (processId', task') :: (middle ++ transition.tasks ++ after) by simp)
          split'
        refine ⟨transition₀.apply front (middle ++ (processId, task) :: after) finished exhausted,
          mem_steps.mpr (.inl ⟨front, processId', task', middle ++ (processId, task) :: after,
            transition₀, index', by rw [split]; simp, possible₀, rfl, event₀, rfl⟩), ?_⟩
        have step := Step.run (state := transition₀.state)
          (finished := transition₀.finished.orElse fun _ => finished)
          (exhausted := exhausted || transition₀.exhausted)
          (before := front ++ transition₀.tasks ++ middle) (after := after)
          (tasks := front ++ transition₀.tasks ++ (middle ++ (processId, task) :: after))
          (by simp) (List.mem_of_getElem? possible₃)
        simp only [Transition.apply] at step ⊢
        rw [event₃, states, finishedComm, exhaustedComm, tasks₃] at step
        rw [tasks₀]
        simpa using step
      · obtain ⟨middle, back, rfl⟩ := List.append_of_mem inAfter
        obtain ⟨rfl, -, rfl⟩ := split_unique wellformed₁.1
          (show before ++ transition.tasks ++ (middle ++ (processId', task') :: back) =
            (before ++ transition.tasks ++ middle) ++ (processId', task') :: back by simp)
          split'
        refine ⟨transition₀.apply (before ++ (processId, task) :: middle) back finished exhausted,
          mem_steps.mpr (.inl ⟨before ++ (processId, task) :: middle, processId', task', back,
            transition₀, index', by rw [split]; simp, possible₀, rfl, event₀, rfl⟩), ?_⟩
        have step := Step.run (state := transition₀.state)
          (finished := transition₀.finished.orElse fun _ => finished)
          (exhausted := exhausted || transition₀.exhausted)
          (before := before) (after := middle ++ transition₀.tasks ++ back)
          (tasks := before ++ (processId, task) :: middle ++ transition₀.tasks ++ back)
          (by simp) (List.mem_of_getElem? possible₃)
        simp only [Transition.apply] at step ⊢
        rw [event₃, states, finishedComm, exhaustedComm, tasks₃] at step
        rw [tasks₀]
        simpa using step
    · obtain ⟨timer, timerFound, rfl⟩ := timer_footprint found'
      have timers : transition.state.timers = state.timers :=
        keeps .timers fun written => disjoint .timers written (by simp [timers_read])
      rw [timers, timerFound, Option.some.injEq] at timerFound'
      subst timerFound'
      have timerFrames := frames_timer (state := state) (timer := timer)
      have keepsTimer : ∀ {loc}, loc ∉ (timer.footprint state).writes →
          Agree (state.timerNext timer) state loc := fun out => timerFrames.keeps out
      have agreeTimer : ∀ loc ∈ (timer.footprint state).reads ++ (timer.footprint state).writes,
          Agree state transition.state loc := agree_unwritten keeps disjoint
      have agreeProcess : ∀ loc ∈ footprint.reads ++ footprint.writes,
          Agree state (state.timerNext timer) loc :=
        agree_unwritten (fun loc out => keepsTimer out) disjoint'
      obtain ⟨transition₃, possible₃, similar⟩ :=
        (transitions_similar taskFootprint agreeProcess).get' possible
      obtain ⟨event₃, tasks₃, finished₃, exhausted₃, keeps₃, same₃⟩ := similar
      obtain ⟨keepsAfter, sameAfter⟩ := timerFrames transition.state agreeTimer
      refine ⟨.running (state.timerNext timer) tasks finished exhausted,
        mem_steps.mpr (.inr ⟨timer, index', timerFound, rfl, rfl, rfl⟩), ?_⟩
      have step := Step.run (finished := finished) (exhausted := exhausted) split
        (List.mem_of_getElem? possible₃)
      have equal : transition₃.apply before after finished exhausted =
          .running (transition.state.timerNext timer) (before ++ transition.tasks ++ after)
            (transition.finished.orElse fun _ => finished) (exhausted || transition.exhausted) := by
        simp only [Transition.apply, tasks₃, finished₃, exhausted₃]
        rw [commute_agree (fun loc mem out => disjoint loc mem (by simp [out])) keeps
          (fun loc out => keepsTimer out) keepsAfter sameAfter keeps₃ same₃]
      rw [event₃, equal] at step
      exact step
  · rcases key' with ⟨processId', index'⟩ | index'
    · obtain ⟨timer₀, timerFound₀, rfl⟩ := timer_footprint found
      rw [timerFound, Option.some.injEq] at timerFound₀
      subst timerFound₀
      obtain ⟨task, lookup, taskFootprint⟩ := process_footprint found'
      rw [mem_steps] at mem'
      rcases mem' with ⟨before, processId, task', after, transition', index'', split, possible',
        same, rfl, rfl⟩ | ⟨_, _, _, same, _, _⟩
      · simp only [Key.process.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        rw [lookup_eq (item := task') distinct (by rw [split]; simp), Option.some.injEq] at lookup
        subst lookup
        have timerFrames := frames_timer (state := state) (timer := timer)
        have keepsTimer : ∀ {loc}, loc ∉ (timer.footprint state).writes →
            Agree (state.timerNext timer) state loc := fun out => timerFrames.keeps out
        have agreeProcess : ∀ loc ∈ footprint'.reads ++ footprint'.writes,
            Agree state (state.timerNext timer) loc :=
          agree_unwritten (fun loc out => keepsTimer out) disjoint
        obtain ⟨transition, possible, similar⟩ :=
          (transitions_similar taskFootprint agreeProcess).get possible'
        obtain ⟨event₁, tasks₁, finished₁, exhausted₁, keeps₁, same₁⟩ := similar
        have keeps := keeps_of_footprint taskFootprint possible
        have agreeTimer : ∀ loc ∈ (timer.footprint state).reads ++ (timer.footprint state).writes,
            Agree state transition.state loc := agree_unwritten keeps disjoint'
        obtain ⟨keepsAfter, sameAfter⟩ := timerFrames transition.state agreeTimer
        have timers : transition.state.timers = state.timers :=
          keeps .timers fun written => disjoint' .timers written (by simp [timers_read])
        refine ⟨transition.apply before after finished exhausted, mem_steps.mpr
          (.inl ⟨before, processId', task', after, transition, index', split, possible, rfl,
            event₁, rfl⟩), ?_⟩
        have step := Step.timer (tasks := before ++ transition.tasks ++ after)
          (finished := transition.finished.orElse fun _ => finished)
          (exhausted := exhausted || transition.exhausted)
          (timer_step (state := transition.state) (index := index) (by rw [timers]; exact timerFound))
        simp only [Transition.apply]
        rw [commute_agree (fun loc mem out => disjoint' loc mem (by simp [out])) keeps
          (fun loc out => keepsTimer out) keepsAfter sameAfter keeps₁ same₁]
        simp only [tasks₁, finished₁, exhausted₁]
        exact step
      · cases same
    · simp at keys

/-- Keys name steps: a configuration has at most one step with a key. -/
private theorem steps_unique {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {key : Key}
    {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (Config.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key, event', next') ∈ (Config.running state tasks finished exhausted).steps) :
    next = next' := by
  rw [mem_steps] at mem mem'
  rcases mem with ⟨before, processId, task, after, transition, index, split, found, rfl, rfl, rfl⟩ |
    ⟨timer, index, found, rfl, rfl, rfl⟩ <;>
  rcases mem' with ⟨before', processId', task', after', transition', index', split', found', same,
    rfl, rfl⟩ | ⟨timer', index', found', same, rfl, rfl⟩
  · simp only [Key.process.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    obtain ⟨rfl, rfl, rfl⟩ := split_unique wellformed.1 split split'
    rw [found, Option.some.injEq] at found'
    subst found'
    rfl
  · cases same
  · cases same
  · simp only [Key.timer.injEq] at same
    subst same
    rw [found, Option.some.injEq] at found'
    subst found'
    rfl

private theorem Step.of_mem_steps {config next : Config α} {key : Key} {event : Event}
    (mem : (key, event, next) ∈ config.steps) : Step config event next := by
  cases config with
  | start => simp [Config.steps] at mem
  | running state tasks finished exhausted =>
    rw [mem_steps] at mem
    rcases mem with ⟨before, processId, task, after, transition, index, split, found, -, rfl, rfl⟩ |
      ⟨timer, index, found, -, rfl, rfl⟩
    · exact .run split (List.mem_of_getElem? found)
    · exact .timer (timer_step found)

private theorem Step.keyed {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {event : Event}
    {next : Config α} (step : Step (.running state tasks finished exhausted) event next) :
    ∃ key, (key, event, next) ∈ (Config.running state tasks finished exhausted).steps := by
  cases step with
  | run split possible =>
    obtain ⟨index, bound, found⟩ := List.getElem_of_mem possible
    exact ⟨_, mem_steps.mpr (.inl ⟨_, _, _, _, _, index, split, by simp [bound, found], rfl, rfl,
      rfl⟩)⟩
  | timer possible =>
    rw [timerSteps_eq, List.mem_map] at possible
    obtain ⟨timer, mem, equal⟩ := possible
    simp only [Prod.mk.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    obtain ⟨index, bound, found⟩ := List.getElem_of_mem mem
    exact ⟨_, mem_steps.mpr (.inr ⟨timer, index, by simp [bound, found], rfl, rfl, rfl⟩)⟩

/-! ### Soundness -/

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
    -- Every step from a configuration, with nothing asleep.
    have every : ∀ {config : Config α}, Wellformed config →
        (match config.successors with
          | [] => accept config.outcome
          | successors => successors.all fun (_, next) => checkFrom accept depth [] next) = true →
        Run config events last → accept outcome = true := by
      intro config wellformed checked run
      cases run with
      | refl =>
        simp only [terminal.successors_eq_nil, terminal.outcome_eq] at checked
        exact checked
      | step step rest =>
        have mem := step.mem_successors
        split at checked
        · rename_i empty; simp [empty] at mem
        · simp only [List.all_eq_true, Prod.forall] at checked
          exact ih (Step.wellformed step wellformed) (checked _ _ mem) rest terminal
            (by simp)
    cases first with
    | start env computation =>
      unfold checkFrom at checked
      exact every wellformed checked run
    | running state tasks finished exhausted =>
      unfold checkFrom at checked
      cases found : (splits tasks).find? (fun (_, (processId, task), _) =>
          task.independent state processId) with
      | none =>
        simp only [found] at checked
        cases run with
        | refl =>
          have noSteps : (Config.running state tasks finished exhausted).steps = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            rintro ⟨key, event, next⟩ mem
            have := (Step.of_mem_steps mem).mem_successors
            rw [terminal.successors_eq_nil] at this
            simp at this
          simp only [noSteps, terminal.outcome_eq] at checked
          exact checked
        | step step rest =>
          obtain ⟨key, mem⟩ := Step.keyed step
          cases steps : (Config.running state tasks finished exhausted).steps with
          | nil => rw [steps] at mem; simp at mem
          | cons entry rest' =>
            simp only [steps] at checked
            rw [← steps] at checked
            exact explore_sound (goal := accept outcome = true)
              (fun key event next mem sleep' visited reaches asleep' =>
                let ⟨_, run'⟩ := reaches
                ih (Step.wellformed (Step.of_mem_steps mem) wellformed) visited run' terminal
                  asleep')
              (fun key event next mem key' independent event' next' mem' =>
                diamond wellformed mem independent mem')
              (fun key event event' next next' mem mem' => steps_unique wellformed mem mem')
              asleep ⟨key, _, _, mem, _, rest⟩ checked
      | some split =>
        simp only [found] at checked
        obtain ⟨before, ⟨processId, ⟨computation, finish⟩⟩, after⟩ := split
        have reads := List.find?_some found
        have split := eq_of_mem_splits (List.mem_of_find?_eq_some found)
        cases computation with
        | get read =>
          simp only [Task.independent, Bool.and_true, Option.isNone_iff_eq_none] at reads
          -- Every run can read first.
          obtain ⟨events', run'⟩ := read_first run terminal rfl wellformed split reads
          have possible := read_transitions (finish := finish) (read := read) (state := state)
            (other := state) (processId := processId) rfl rfl reads
          let readStep : Transition α :=
            { event := .internal processId, state := state
              tasks := [(processId, ⟨read (state.view processId), finish⟩)] }
          have step : Step (.running state tasks finished exhausted) readStep.event
              (readStep.apply before after finished exhausted) :=
            Step.run split (by rw [possible]; exact List.mem_singleton_self _)
          simp only [Config.reduced, found, possible, List.map_cons, List.map_nil] at checked
          simp only [List.all_cons, List.all_nil, Bool.and_true] at checked
          refine ih (events := events') (Step.wellformed step wellformed) checked ?_ terminal (by simp)
          simpa [Transition.apply, readStep] using run'
        | set updated next =>
          simp only [Task.independent, Bool.and_true, Option.isNone_iff_eq_none] at reads
          -- Every run can write first, ending the same way.
          obtain ⟨events', last', run', terminal'⟩ :=
            write_first run terminal (by rw [split]) (split ▸ wellformed) reads
          let writeStep : Transition α :=
            { event := .internal processId, state := state.store processId updated
              tasks := [(processId, ⟨next, finish⟩)] }
          have possible : (⟨.set updated next, finish⟩ : Task α).transitions state processId =
              [writeStep] := by
            simp [Task.transitions, reads, writeStep]
          have step : Step (.running state tasks finished exhausted) writeStep.event
              (writeStep.apply before after finished exhausted) :=
            Step.run split (by rw [possible]; exact List.mem_singleton_self _)
          simp only [Config.reduced, found, possible, List.map_cons, List.map_nil] at checked
          simp only [List.all_cons, List.all_nil, Bool.and_true] at checked
          refine ih (events := events') (Step.wellformed step wellformed) checked ?_ terminal' (by simp)
          simpa [Transition.apply, writeStep] using run'
        | receive timeout select next =>
          simp only [Task.independent, Bool.and_eq_true, Option.isNone_iff_eq_none,
            Option.isSome_iff_exists] at reads
          obtain ⟨signal, ⟨message, value, remaining⟩, selected⟩ := reads
          obtain ⟨index, bound, rfl, -⟩ := selectMessage_index selected
          obtain ⟨process, live⟩ := Option.isSome_iff_exists.mp
            (wellformed.2.2.1 (processId, ⟨.receive timeout select next, finish⟩)
              (by rw [split]; simp))
          -- Every run can receive the message first, reaching the same configuration.
          obtain ⟨events', run'⟩ :=
            receive_first run terminal (by rw [split]) (split ▸ wellformed) selected bound
          have possible : (⟨.receive timeout select next, finish⟩ : Task α).transitions state
              processId = [{ event := .receive processId message, state := state.take processId index
                             tasks := [(processId, ⟨next (some value), finish⟩)] }] := by
            have process : state.process processId = process := by simp [State.process, live]
            rw [process] at signal selected
            rw [← take_received (index := index) live]
            simp [Task.transitions, process, signal, selected]
          have step := Step.run (finished := finished) (exhausted := exhausted) split
            (by rw [possible]; exact List.mem_singleton_self _)
          simp only [Config.reduced, found, possible, List.map_cons, List.map_nil] at checked
          simp only [List.all_cons, List.all_nil, Bool.and_true] at checked
          refine ih (events := events') (Step.wellformed step wellformed) checked ?_ terminal (by simp)
          simpa [Transition.apply] using run'
        | _ => simp [Task.independent] at reads

/-- `check` accepts the outcome of every run of a computation. -/
theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {env : Environment}
    {computation : Result α} {elapsed : PID → Nat → Nat} {last : Config α} {events : List Event}
    {outcome : Outcome α} (checked : check accept depth (.start env computation elapsed) = true)
    (run : Run (.start env computation elapsed) events last) (terminal : Terminal last outcome) :
    accept outcome = true :=
  check_wellformed (show Wellformed (Config.start env computation elapsed) from trivial) checked run
    terminal (by simp)

end Lynx.Concurrent
