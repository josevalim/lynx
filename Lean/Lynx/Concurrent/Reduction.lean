module

public import Lynx.Concurrent

/-! `check` follows a process about to read its environment before any other
step. Reading changes nothing other processes observe, and their steps cannot
change what it reads, so every run can take the read first and reach the same
terminal configuration. This module proves that `check` is sound. -/

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
      simp only [Task.transitions, signal, List.mem_map] at possible
      obtain ⟨_, _, rfl⟩ := possible
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
    (equal : ∀ candidate, first.processes candidate = second.processes candidate) :
    first = second := by
  cases first; cases second; simp_all; funext candidate; exact equal candidate

@[simp] private theorem erase_timers {state : State} {processId : PID} :
    (state.erase processId).timers = state.timers := rfl

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
  refine State.ext' rfl fun candidate => ?_
  simp only [erase_processes, State.update]
  by_cases first : candidate = other <;> by_cases second : candidate = processId <;> simp_all

private theorem erase_update_self {state : State} {processId : PID} :
    (state.update processId none).erase processId = (state.erase processId).update processId none := by
  refine State.ext' rfl fun candidate => ?_
  simp only [erase_processes, State.update]
  by_cases first : candidate = processId <;> simp_all

private theorem erase_modify {state : State} {processId other : PID}
    {change : ProcessState → ProcessState} (oblivious : Oblivious change) :
    (state.modify other change).erase processId = (state.erase processId).modify other change := by
  refine State.ext' (by simp) fun candidate => ?_
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
  refine State.ext' (by simp) fun candidate => ?_
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
    simp only [State.request, erase_timers]
    split <;> rfl

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
      simp only [erase_request ne, List.map_map]
      rfl

/-- Storing the environment of a live process only changes what erasing removes. -/
private theorem erase_store {state : State} {processId : PID} {env : Environment}
    (live : (state.processes processId).isSome) :
    (state.store processId env).erase processId = state.erase processId := by
  refine State.ext' rfl fun candidate => ?_
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
  refine State.ext' timers fun candidate => ?_
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
    refine State.ext' rfl fun candidate => ?_
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
  refine State.ext' rfl fun candidate => ?_
  simp only [take_processes, State.update]
  by_cases first : candidate = other <;> by_cases second : candidate = processId <;> simp_all

private theorem take_modify {state : State} {processId other : PID} {index : Nat}
    {change : ProcessState → ProcessState}
    (oblivious : ∀ process, (change process).take index = change (process.take index)) :
    (state.modify other change).take processId index =
      (state.take processId index).modify other change := by
  refine State.ext' (by simp) fun candidate => ?_
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
  refine State.ext' (by simp) fun candidate => ?_
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
    refine State.ext' (by simp) fun candidate => ?_
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
    simp only [State.request, take_timers]
    split <;> rfl

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
      simp only [take_request ne holds, List.map_map]
      rfl

/-- Exiting forgets the messages of the process. -/
private theorem terminate_take {state : State} {processId : PID} {index : Nat} {reason : Term} :
    (state.take processId index).terminate processId reason = state.terminate processId reason := by
  have fields := take_process_fields (state := state) (processId := processId) (index := index)
    (other := processId)
  have removed : (state.take processId index).update processId none = state.update processId none := by
    refine State.ext' rfl fun candidate => ?_
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
  refine State.ext' rfl fun candidate => ?_
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

/-! ### Soundness -/

/-- One level of `check` where it follows every step. -/
private theorem check_successors {accept : Outcome α → Bool} {depth : Nat} {config last : Config α}
    {events : List Event} {outcome : Outcome α}
    (ih : ∀ {first last : Config α} {events : List Event} {outcome : Outcome α},
      Wellformed first → check accept depth first = true → Run first events last →
      Terminal last outcome → accept outcome = true)
    (wellformed : Wellformed config) (reduced : config.reduced = config.successors)
    (checked : check accept (depth + 1) config = true) (run : Run config events last)
    (terminal : Terminal last outcome) : accept outcome = true := by
  unfold check at checked
  rw [reduced] at checked
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

private theorem check_wellformed {accept : Outcome α → Bool} :
    ∀ {depth : Nat} {first last : Config α} {events : List Event} {outcome : Outcome α},
      Wellformed first → check accept depth first = true → Run first events last →
      Terminal last outcome → accept outcome = true := by
  intro depth
  induction depth with
  | zero => intro _ _ _ _ _ checked; simp [check] at checked
  | succ depth ih =>
    intro first last events outcome wellformed checked run terminal
    cases first with
    | start env computation =>
      exact check_successors ih wellformed rfl checked run terminal
    | running state tasks finished exhausted =>
      cases found : (splits tasks).find? (fun (_, (processId, task), _) =>
          task.independent state processId) with
      | none =>
        exact check_successors ih wellformed (by simp [Config.reduced, found]) checked run terminal
      | some split =>
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
          unfold check at checked
          simp only [Config.reduced, found, possible, List.map_cons, List.map_nil] at checked
          simp only [List.all_cons, List.all_nil, Bool.and_true] at checked
          refine ih (events := events') (Step.wellformed step wellformed) checked ?_ terminal
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
          unfold check at checked
          simp only [Config.reduced, found, possible, List.map_cons, List.map_nil] at checked
          simp only [List.all_cons, List.all_nil, Bool.and_true] at checked
          refine ih (events := events') (Step.wellformed step wellformed) checked ?_ terminal'
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
          unfold check at checked
          simp only [Config.reduced, found, possible, List.map_cons, List.map_nil] at checked
          simp only [List.all_cons, List.all_nil, Bool.and_true] at checked
          refine ih (events := events') (Step.wellformed step wellformed) checked ?_ terminal
          simpa [Transition.apply] using run'
        | _ => simp [Task.independent] at reads

/-- `check` accepts the outcome of every run of a computation. -/
theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {env : Environment}
    {computation : Result α} {last : Config α} {events : List Event} {outcome : Outcome α}
    (checked : check accept depth (.start env computation) = true)
    (run : Run (.start env computation) events last) (terminal : Terminal last outcome) :
    accept outcome = true :=
  check_wellformed (show Wellformed (Config.start env computation) from trivial) checked run terminal

end Lynx.Concurrent
