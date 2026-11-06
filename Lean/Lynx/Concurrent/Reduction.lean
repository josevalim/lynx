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
children it spawned, and a pending exit signal. -/
private def Unchanged (before after : ProcessState) : Prop :=
  after.pdict = before.pdict ∧ after.refCounter = before.refCounter ∧
    after.children = before.children ∧ (before.signal.isSome → after.signal.isSome)

private theorem Unchanged.refl (process : ProcessState) : Unchanged process process :=
  ⟨rfl, rfl, rfl, id⟩

private theorem Unchanged.trans {first second third : ProcessState}
    (left : Unchanged first second) (right : Unchanged second third) : Unchanged first third :=
  ⟨right.1.trans left.1, right.2.1.trans left.2.1, right.2.2.1.trans left.2.2.1,
    fun pending => right.2.2.2 (left.2.2.2 pending)⟩

/-- A state change keeps a process's record. -/
private def Keeps (processId : PID) (before after : State) : Prop :=
  Unchanged (before.process processId) (after.process processId)

private theorem Keeps.refl (processId : PID) (state : State) : Keeps processId state state :=
  Unchanged.refl _

private theorem Keeps.trans {processId : PID} {first second third : State}
    (left : Keeps processId first second) (right : Keeps processId second third) :
    Keeps processId first third :=
  Unchanged.trans left right

private theorem State.process_update {state : State} {processId other : PID}
    {process : Option ProcessState} :
    (state.update other process).process processId =
      if processId = other then process.getD {} else state.process processId := by
  simp only [State.process, State.update]
  split <;> rfl

private theorem keeps_update_ne {state : State} {processId other : PID}
    {process : Option ProcessState} (ne : processId ≠ other) :
    Keeps processId state (state.update other process) := by
  simp only [Keeps, State.process_update, ne, ite_false]
  exact Unchanged.refl _

private theorem keeps_modify {state : State} {processId other : PID}
    {change : ProcessState → ProcessState}
    (kept : processId ≠ other ∨ ∀ process, Unchanged process (change process)) :
    Keeps processId state (state.modify other change) := by
  unfold State.modify
  split
  · rename_i process found
    by_cases equal : processId = other
    · subst equal
      simp only [Keeps, State.process_update, ite_true, Option.getD_some]
      have : state.process processId = process := by simp [State.process, found]
      rw [this]
      rcases kept with ne | kept
      · exact absurd rfl ne
      · exact kept process
    · exact keeps_update_ne equal
  · exact Keeps.refl _ _

private theorem keeps_deliver {state : State} {processId other : PID} {message : Term} :
    Keeps processId state (state.deliver other message) := by
  unfold State.deliver
  split
  · rename_i process found
    by_cases equal : processId = other
    · subst equal
      simp only [Keeps, State.process_update, ite_true, Option.getD_some]
      have : state.process processId = process := by simp [State.process, found]
      rw [this]
      exact ⟨rfl, rfl, rfl, id⟩
    · exact keeps_update_ne equal
  · exact Keeps.refl _ _

private theorem keeps_kill {state : State} {processId other : PID} {reason : Term} :
    Keeps processId state (state.kill other reason) :=
  keeps_modify (.inr fun process => ⟨rfl, rfl, rfl, fun pending => by
    cases signal : process.signal <;> simp_all⟩)

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

/-! Each lemma below extended a kept record through one more operation, so
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
private theorem unchanged_fields (process : ProcessState) (mailbox : List Term)
    (links : List PID) (monitors monitoring : List (List Nat × PID)) (aliases : List (List Nat)) :
    Unchanged process { process with mailbox, links, monitors, monitoring, aliases } :=
  ⟨rfl, rfl, rfl, id⟩

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
      | (apply Keeps.modify (.inr fun process => unchanged_fields process _ _ _ _ _))
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
  split
  · exact keeps_monitor ne (by keeps_chain)
  · keeps_chain

/-! ### Children of the stepping process -/

/-- A state change keeps the number of children a process spawned. -/
private def KeepsChildren (processId : PID) (before after : State) : Prop :=
  (after.process processId).children = (before.process processId).children

private theorem KeepsChildren.refl (processId : PID) (state : State) :
    KeepsChildren processId state state := rfl

private theorem KeepsChildren.update {state before : State} {processId other : PID}
    {process : Option ProcessState}
    (same : processId ≠ other ∨ (process.getD {}).children = (before.process other).children)
    (kept : KeepsChildren processId state before) :
    KeepsChildren processId state (before.update other process) := by
  unfold KeepsChildren at *
  rw [State.process_update]
  split
  · rename_i equal
    subst equal
    rcases same with ne | same
    · exact absurd rfl ne
    · rw [same, kept]
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

/-! ### Transitions -/

/-- The children of a spawning process, and the PID of its new child. -/
private theorem spawnWith_children {state : State} {processId : PID} {options : SpawnOptions} :
    (state.spawnWith processId options).1 = processId ++ [(state.process processId).children + 1] ∧
      ((state.spawnWith processId options).2.process processId).children =
        (state.process processId).children + 1 := by
  refine ⟨rfl, ?_⟩
  have spawned : ((state.spawn processId).2.process processId).children =
      (state.process processId).children + 1 := by
    simp only [State.spawn, State.process_update]
    have : processId ≠ processId ++ [(state.process processId).children + 1] := by
      intro equal
      have := congrArg List.length equal
      simp at this
    simp [this]
  have kept : KeepsChildren processId (state.spawn processId).2
      (state.spawnWith processId options).2 := by
    simp only [State.spawnWith]
    split
    · apply KeepsChildren.monitor
      children_chain
    · children_chain
  exact kept.trans spawned

/-- How a step of a process changes the shared state and the processes. -/
private theorem transition_frame {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.transitions state processId) :
    (∀ other, other ≠ processId →
      (∀ child, transition.event = .spawn processId child → other ≠ child) →
      Keeps other state transition.state) ∧
    (transition.tasks = [] ∨
      (∃ next, transition.tasks = [(processId, next)] ∧
        KeepsChildren processId state transition.state) ∨
      ∃ next child spawned, transition.tasks = [(processId, next), (child, spawned)] ∧
        transition.event = .spawn processId child ∧
        child = processId ++ [(state.process processId).children + 1] ∧
        (transition.state.process processId).children = (state.process processId).children + 1) := by
  obtain ⟨computation, finish⟩ := task
  rcases signal : (state.process processId).signal with _ | reason
  · cases computation with
    | ok value =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun other ne _ => keeps_terminate ne, .inl rfl⟩
    | error exception =>
      cases exception <;> simp only [Task.transitions, signal, List.mem_singleton] at possible <;>
        subst possible <;>
        first
        | exact ⟨fun other ne _ => keeps_terminate ne, .inl rfl⟩
        | exact ⟨fun other ne _ => keeps_update_ne ne, .inl rfl⟩
    | get next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun _ _ _ => Keeps.refl _ _, .inr (.inl ⟨_, rfl, KeepsChildren.refl _ _⟩)⟩
    | set updated next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      refine ⟨fun other ne _ => keeps_update_ne ne, .inr (.inl ⟨_, rfl, ?_⟩)⟩
      exact KeepsChildren.update (.inr rfl) (KeepsChildren.refl _ _)
    | schedule options child next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      obtain ⟨childPid, children⟩ := spawnWith_children (state := state) (processId := processId)
        (options := options)
      refine ⟨fun other ne fresh => keeps_spawnWith ne (fresh _ rfl), .inr (.inr ?_)⟩
      exact ⟨_, _, _, rfl, rfl, childPid, children⟩
    | send destination message next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun _ _ _ => keeps_deliver, .inr (.inl ⟨_, rfl, (KeepsChildren.refl _ _).deliver⟩)⟩
    | receive timeout select next =>
      simp only [Task.transitions, signal] at possible
      split at possible
      · simp only [List.mem_singleton] at possible
        subst possible
        refine ⟨fun other ne _ => keeps_update_ne ne, .inr (.inl ⟨_, rfl, ?_⟩)⟩
        exact KeepsChildren.update (.inr rfl) (KeepsChildren.refl _ _)
      · split at possible <;> simp only [List.mem_singleton, List.not_mem_nil] at possible <;>
          subst possible <;>
          exact ⟨fun _ _ _ => Keeps.refl _ _, .inr (.inl ⟨_, rfl, KeepsChildren.refl _ _⟩)⟩
    | request query next =>
      simp only [Task.transitions, signal, List.mem_singleton] at possible
      subst possible
      exact ⟨fun other ne _ => keeps_request ne, .inr (.inl ⟨_, rfl, keepsChildren_request⟩)⟩
  · simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    exact ⟨fun other ne _ => keeps_terminate ne, .inl rfl⟩

/-! ### Well-formed configurations -/

/-- Facts every reachable configuration satisfies: processes have distinct PIDs,
and each process has spawned every child PID that another process extended. -/
private def Wellformed : Config α → Prop
  | .start .. => True
  | .running state tasks _ _ =>
      tasks.Pairwise (fun first second => first.1 ≠ second.1) ∧
      ∀ parent ∈ tasks, ∀ descendant ∈ tasks, ∀ index rest,
        descendant.1 = parent.1 ++ index :: rest → index ≤ (state.process parent.1).children

private theorem ne_append_cons (processId : PID) (index : Nat) (rest : List Nat) :
    processId ≠ processId ++ index :: rest := by
  intro equal
  have := congrArg List.length equal
  simp at this

/-- A spawned PID either extended its parent or ends below it. -/
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
  obtain ⟨-, shape⟩ := transition_frame possible
  rcases shape with empty | ⟨next, single, kept⟩ | ⟨next, child, spawned, pair, event, childPid, children⟩
  · refine ⟨by simp [empty], by simp [empty], .inr empty, fun child spawn => ?_⟩
    -- Exits are not spawns.
    obtain ⟨computation, finish⟩ := task
    simp only [Task.transitions] at possible
    split at possible
    · simp only [List.mem_singleton] at possible; subst possible; cases spawn
    · split at possible <;> (try split at possible) <;> (try split at possible) <;>
        simp_all
  · refine ⟨by simp [single], by simp [single], .inl (Nat.le_of_eq kept.symm), fun child spawn => ?_⟩
    obtain ⟨computation, finish⟩ := task
    simp only [Task.transitions] at possible
    split at possible
    · simp only [List.mem_singleton] at possible; subst possible; cases spawn
    · split at possible <;> (try split at possible) <;> (try split at possible) <;>
        simp_all
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
  obtain ⟨distinct, fresh⟩ := wellformed
  obtain ⟨frame, -⟩ := transition_frame possible
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
      child_new child spawn entry (old entry mem)).2.2.1
  simp only [Transition.apply, Wellformed]
  refine ⟨pairwise_replace distinct inner ?_ ?_, ?_⟩
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
    refine ⟨by simp, ?_⟩
    simp only [List.mem_singleton]
    rintro _ rfl _ rfl index rest extended
    exact absurd extended (ne_append_cons _ _ _)
  | run split possible =>
    subst split
    exact wellformed_apply wellformed possible

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
  obtain ⟨distinct, fresh⟩ := wellformed
  have order := split_order split
  rcases order with ⟨same, -, -⟩ | later | earlier
  · exact absurd same ne
  all_goals refine ⟨?_, by first | exact .inl later | exact .inr earlier⟩
  all_goals
    obtain ⟨frame, -⟩ := transition_frame possible
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
        have pending' : (transition.state.process processId).signal.isSome := kept.2.2.2 pending
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
              simp only [State.view, kept.1, kept.2.1]
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
              simp only [State.view, kept.1, kept.2.1]
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
          task.reads state processId) with
      | none =>
        exact check_successors ih wellformed (by simp [Config.reduced, found]) checked run terminal
      | some split =>
        obtain ⟨before, ⟨processId, ⟨computation, finish⟩⟩, after⟩ := split
        have reads := List.find?_some found
        have split := eq_of_mem_splits (List.mem_of_find?_eq_some found)
        cases computation with
        | get read =>
          simp only [Task.reads, Bool.and_true, Option.isNone_iff_eq_none] at reads
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
        | _ => simp [Task.reads] at reads

/-- `check` accepts the outcome of every run of a computation. -/
theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {env : Environment}
    {computation : Result α} {last : Config α} {events : List Event} {outcome : Outcome α}
    (checked : check accept depth (.start env computation) = true)
    (run : Run (.start env computation) events last) (terminal : Terminal last outcome) :
    accept outcome = true :=
  check_wellformed (show Wellformed (Config.start env computation) from trivial) checked run terminal

end Lynx.Concurrent
