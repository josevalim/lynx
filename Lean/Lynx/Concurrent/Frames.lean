module

public import Lynx.Concurrent.Diamond

/-! Steps that `Config.apart` lets commute without evaluating them. Each step
does an effect on the records it changes (`Effect`), a function of their old
records decided at the configuration. Frames describe the effects: what each
writes, and what its decisions and changes read. -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-! ### Effects -/

/-- What a step does to records and timers: the change of each record it
touches (the first entry of a process counts), and the timers, if it changes them. -/
private structure Effect where
  records : List (PID × (Option ProcessState → Option ProcessState)) := []
  timers : Option (List Timer → List Timer) := none

/-- The first change of a process in a list of changes. -/
private def changeOf : List (PID × (Option ProcessState → Option ProcessState)) → PID →
    Option ProcessState → Option ProcessState
  | [], _ => id
  | (other, change) :: rest, processId => if other = processId then change else changeOf rest processId

/-- How an effect changes the record of a process. -/
private def Effect.record (effect : Effect) (processId : PID) : Option ProcessState → Option ProcessState :=
  changeOf effect.records processId

private theorem changeOf_of_missing {changes : List (PID × (Option ProcessState → Option ProcessState))}
    {processId : PID} (missing : processId ∉ changes.map (·.1)) : changeOf changes processId = id := by
  induction changes with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨other, change⟩ := head
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    simp [changeOf, Ne.symm missing.1, ih missing.2]

/-- Replace or remove the record of a process. -/
private def State.put (state : State) (processId : PID) : Option ProcessState → State
  | some process => state.set processId process
  | none => state.remove processId

private theorem State.record_put (state : State) (processId other : PID) (record : Option ProcessState) :
    (state.put processId record).record other = if other = processId then record else state.record other := by
  cases record <;> simp [State.put, State.record_set, State.record_remove]

/-- The state after an effect. -/
private def Effect.apply (effect : Effect) (state : State) : State :=
  (effect.records.map (·.1)).foldl (fun changed processId =>
      changed.put processId (effect.record processId (state.record processId)))
    { state with timers := (effect.timers.getD id) state.timers }

private theorem foldl_put_record (change : PID → Option ProcessState) (processId : PID) :
    ∀ (processes : List PID) (start : State),
      (processes.foldl (fun changed other => changed.put other (change other)) start).record processId =
        if processId ∈ processes then change processId else start.record processId
  | [], start => by simp
  | head :: rest, start => by
      simp only [List.foldl_cons, foldl_put_record change processId rest, State.record_put, List.mem_cons]
      by_cases inside : processId ∈ rest
      · simp [inside]
      · by_cases equal : processId = head
        · subst equal; simp [inside]
        · simp [inside, equal]

private theorem Effect.record_apply (effect : Effect) (state : State) (processId : PID) :
    (effect.apply state).record processId = effect.record processId (state.record processId) := by
  simp only [Effect.apply, foldl_put_record]
  split
  · rfl
  · rename_i missing
    simp only [Effect.record, changeOf_of_missing missing]
    rfl

private theorem Effect.timers_apply (effect : Effect) (state : State) :
    (effect.apply state).timers = (effect.timers.getD id) state.timers := by
  simp only [Effect.apply]
  generalize (effect.records.map (·.1)) = processes
  have : ∀ (start : State), (processes.foldl (fun changed other =>
      changed.put other (effect.record other (state.record other))) start).timers = start.timers := by
    induction processes with
    | nil => intro; rfl
    | cons head rest ih =>
      intro start
      simp only [List.foldl_cons]
      rw [ih]
      cases effect.record head (state.record head) <;> rfl
  rw [this]

private theorem Effect.elapsed_apply (effect : Effect) (state : State) :
    (effect.apply state).elapsed = state.elapsed := by
  simp only [Effect.apply]
  generalize (effect.records.map (·.1)) = processes
  have : ∀ (start : State), (processes.foldl (fun changed other =>
      changed.put other (effect.record other (state.record other))) start).elapsed = start.elapsed := by
    induction processes with
    | nil => intro; rfl
    | cons head rest ih =>
      intro start
      simp only [List.foldl_cons]
      rw [ih]
      cases effect.record head (state.record head) <;> rfl
  rw [this]

/-- One effect after another. -/
private def Effect.andThen (first second : Effect) : Effect where
  records := (first.records.map fun (processId, change) => (processId, second.record processId ∘ change)) ++
    second.records
  timers := match first.timers, second.timers with
    | some change, some change' => some (change' ∘ change)
    | some change, none => some change
    | none, change' => change'

private theorem changeOf_append (first second : List (PID × (Option ProcessState → Option ProcessState)))
    (outer : PID → Option ProcessState → Option ProcessState) (processId : PID)
    (outer_eq : ∀ processId, outer processId = changeOf second processId) :
    changeOf ((first.map fun (other, change) => (other, outer other ∘ change)) ++ second) processId =
      changeOf second processId ∘ changeOf first processId := by
  induction first with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨other, change⟩ := head
    by_cases equal : other = processId
    · subst equal; simp [changeOf, outer_eq]
    · simp [changeOf, equal, ih]

private theorem Effect.record_andThen (first second : Effect) (processId : PID) :
    (first.andThen second).record processId = second.record processId ∘ first.record processId := by
  simp only [Effect.record, Effect.andThen]
  exact changeOf_append _ _ _ _ fun _ => rfl

private theorem Effect.timers_andThen (first second : Effect) :
    ((first.andThen second).timers.getD id) = (second.timers.getD id) ∘ (first.timers.getD id) := by
  simp only [Effect.andThen]
  cases first.timers <;> cases second.timers <;> rfl

/-- Change the record of a process that has one. -/
private def Effect.modify (processId : PID) (change : ProcessState → ProcessState) : Effect :=
  { records := [(processId, Option.map change)] }

private theorem Effect.record_modify (processId other : PID) (change : ProcessState → ProcessState) :
    (Effect.modify processId change).record other = if other = processId then Option.map change else id := by
  by_cases equal : other = processId
  · subst equal; simp [Effect.record, Effect.modify, changeOf]
  · simp [Effect.record, Effect.modify, changeOf, Ne.symm equal, equal]

end Lynx.Concurrent
