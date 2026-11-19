module

public import Lynx.Concurrent.Frames
import all Lynx.Concurrent.Diamond
import all Lynx.Concurrent.Frames

/-! Following runs with sleep sets (`checkSleep`) covers every run. Each step
of a configuration has a key naming it (`Config.taggedSteps`), a step asleep
stays asleep after another it commutes with or absorbs (`Config.staysAfter`),
and a forced step is taken alone as every run can take it first. -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-! ### Steps by key -/

private theorem head?_of_length {items : List γ} {item : γ} (mem : item ∈ items) (length : items.length ≤ 1) :
    items.head? = some item := by
  match items, mem with
  | [_], mem => simp at mem; simp [mem]
  | _ :: _ :: _, _ => simp at length

private theorem Task.own_length (state : State) (processId : PID) (task : Task α) :
    (task.own state processId).length ≤ 1 := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own]
  | none =>
    cases computation <;> simp only [Task.own]
    case receive timeout select next =>
      split
      · simp
      · split
        · simp
        · split <;> simp
    case request query next =>
      split <;> simp
    case error exception => cases exception <;> simp
    all_goals simp

private theorem Task.handle_length (state : State) (processId : PID) (task : Task α) :
    (task.handle state processId).length ≤ 1 := by
  simp only [Task.handle]
  split
  · simp
  · split
    · simp
    · split <;> simp

private theorem splitAt_of_mem {processId : PID} :
    ∀ {tasks : List (PID × Task α)} {before after : List (PID × Task α)} {task : Task α},
      tasks.Pairwise (fun entry entry' => entry.1 ≠ entry'.1) →
      (before, (processId, task), after) ∈ splits tasks → splitAt processId tasks = some (before, task, after)
  | [], _, _, _, _, mem => by simp [splits] at mem
  | (other, task') :: rest, before, after, task, distinct, mem => by
    simp only [splits, Kernel.map_eq, List.mem_cons, List.mem_map, Prod.mk.injEq] at mem
    rcases mem with ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ | ⟨⟨before', item, after'⟩, mem', rfl, equal, rfl⟩
    · simp [splitAt]
    · subst equal
      have differ : other ≠ processId := by
        have := List.rel_of_pairwise_cons (a' := (processId, task)) distinct
          (by rw [eq_of_mem_splits mem']; simp)
        exact this
      simp only [splitAt, beq_iff_eq, differ, ↓reduceIte, splitAt_of_mem (List.pairwise_cons.mp distinct).2 mem',
        Option.map_some]

private theorem firstOfEach_unseen :
    ∀ {seen : List (List Nat)} {timers : List Timer} {timer : Timer}, timer ∈ firstOfEach seen timers →
      timer.reference ∉ seen
  | _, [], _, mem => by simp [firstOfEach] at mem
  | seen, head :: rest, timer, mem => by
    simp only [firstOfEach] at mem
    split at mem
    · exact firstOfEach_unseen mem
    · rename_i fresh
      simp only [List.mem_cons] at mem
      rcases mem with rfl | mem
      · simpa [Kernel.contains_eq] using fresh
      · exact fun inside => firstOfEach_unseen mem (List.mem_cons_of_mem _ inside)

/-- The timers that can fire have one reference each. -/
private theorem find?_firstOfEach :
    ∀ {seen : List (List Nat)} {timers : List Timer} {timer : Timer}, timer ∈ firstOfEach seen timers →
      Kernel.find? (·.reference == timer.reference) (firstOfEach seen timers) = some timer
  | _, [], _, mem => by simp [firstOfEach] at mem
  | seen, head :: rest, timer, mem => by
    simp only [firstOfEach] at mem ⊢
    split at mem
    · rename_i seenHead; simp only [seenHead, ↓reduceIte]; exact find?_firstOfEach mem
    · rename_i fresh
      simp only [fresh, Bool.false_eq_true, ↓reduceIte]
      simp only [List.mem_cons] at mem
      rcases mem with rfl | mem
      · simp [Kernel.find?_eq]
      · have differ : head.reference ≠ timer.reference := fun same =>
          firstOfEach_unseen mem (same ▸ List.mem_cons_self)
        have found := find?_firstOfEach mem
        simp only [Kernel.find?_eq] at found ⊢
        simp [List.find?_cons, differ, found]

/-- A tagged step of a configuration whose processes have one task each is the
step with its key. -/
private theorem Config.stepOf_of_tagged {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key : Key} {event : Event} {next : Config α} {forced : Bool}
    (distinct : (Config.running state tasks finished false).distinctTasks = true)
    (mem : (key, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps) :
    (Config.running state tasks finished false).stepOf key = some (event, next) := by
  have pairwise := distinct_of_distinctTasks distinct
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at mem
  rcases mem with (((⟨⟨before, ⟨processId, task⟩, after⟩, split, own | handle⟩ | ⟨⟨processId, _⟩, -, link | phase⟩) |
    ⟨⟨processId, _⟩, -, unpark⟩) | ⟨timer, firing, rfl, rfl, rfl, -⟩)
  · obtain ⟨transition, mem, rfl, rfl, rfl, -⟩ := own
    simp [Config.stepOf, splitAt_of_mem pairwise split, head?_of_length mem (Task.own_length ..)]
  · obtain ⟨transition, mem, rfl, rfl, rfl, -⟩ := handle
    simp [Config.stepOf, splitAt_of_mem pairwise split, head?_of_length mem (Task.handle_length ..)]
  · obtain ⟨target, -, found⟩ := link
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨phased, linked, rfl, rfl, rfl, -⟩ := found
    simp [Config.stepOf, linked]
  · split at phase
    · rename_i phased found
      simp only [List.mem_singleton, Prod.mk.injEq] at phase
      obtain ⟨rfl, rfl, rfl, -⟩ := phase
      simp [Config.stepOf, found]
    · simp at phase
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at unpark
    obtain ⟨_, parked, rfl, rfl, rfl, -⟩ := unpark
    simp [Config.stepOf, parked]
  · have found := find?_firstOfEach (seen := []) (timers := state.timers) firing
    simp only [Config.stepOf, State.firing, found, Option.map_some]

/-- Every step of a running configuration is tagged with a key. -/
private theorem Config.tagged_of_step {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {event : Event} {next : Config α}
    (step : Step (.running state tasks finished false) event next) :
    ∃ key forced, (key, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps := by
  simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at step
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq]
  rcases step with (((⟨⟨before, ⟨processId, task⟩, after⟩, split, transition, mem, rfl, rfl⟩ |
    ⟨⟨processId, record⟩, mem, phased, phases, rfl, rfl⟩) | ⟨⟨processId, record⟩, mem, unpark⟩) |
    ⟨timer, firing, rfl, rfl⟩)
  · simp only [Task.transitions, Kernel.append_eq, List.mem_append] at mem
    rcases mem with own | handle
    · exact ⟨_, _, .inl (.inl (.inl ⟨_, split, .inl ⟨transition, own, rfl, rfl, rfl, rfl⟩⟩))⟩
    · exact ⟨_, _, .inl (.inl (.inl ⟨_, split, .inr ⟨transition, handle, rfl, rfl, rfl, rfl⟩⟩))⟩
  · simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at phases
    rcases phases with ⟨target, linked, found⟩ | found
    · exact ⟨.link processId target, false, .inl (.inl (.inr ⟨_, mem, .inl ⟨target, linked, by simp [found]⟩⟩))⟩
    · split at found
      · rename_i phased' found'
        simp only [List.mem_singleton] at found; subst found
        exact ⟨.phase processId, state.dropsDown processId, .inl (.inl (.inr ⟨_, mem, .inr (by simp [found'])⟩))⟩
      · simp at found
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at unpark
    obtain ⟨parked, found, rfl, rfl⟩ := unpark
    exact ⟨.unpark processId, false, .inl (.inr ⟨_, mem, by simp [found]⟩)⟩
  · exact ⟨_, _, .inr ⟨timer, firing, rfl, rfl, rfl, rfl⟩⟩

/-- The step with a key is tagged with it. -/
private theorem Config.tagged_of_stepOf {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key : Key} {event : Event} {next : Config α}
    (found : (Config.running state tasks finished false).stepOf key = some (event, next)) :
    ∃ forced, (key, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq]
  cases key with
  | own processId =>
    simp only [Config.stepOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨⟨before, task, after⟩, split, transition, head, rfl, rfl⟩ := found
    have split' : (before, (processId, task), after) ∈ splits tasks := by rw [splitAt_eq split]; exact mem_splits
    exact ⟨_, .inl (.inl (.inl ⟨_, split', .inl ⟨transition, List.mem_of_head? head, rfl, rfl, rfl, rfl⟩⟩))⟩
  | handle processId =>
    simp only [Config.stepOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨⟨before, task, after⟩, split, transition, head, rfl, rfl⟩ := found
    have split' : (before, (processId, task), after) ∈ splits tasks := by rw [splitAt_eq split]; exact mem_splits
    exact ⟨_, .inl (.inl (.inl ⟨_, split', .inr ⟨transition, List.mem_of_head? head, rfl, rfl, rfl, rfl⟩⟩))⟩
  | link processId target =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨next', phase, rfl, rfl⟩ := found
    obtain ⟨process, record, linked⟩ := State.record_of_linkPhase phase
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    exact ⟨false, .inl (.inl (.inr ⟨(processId, record'), mem, .inl ⟨target, linked, by simp [phase]⟩⟩))⟩
  | phase processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨next', phase, rfl, rfl⟩ := found
    obtain ⟨process, record⟩ := State.record_of_phase phase
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    exact ⟨state.dropsDown processId, .inl (.inl (.inr ⟨(processId, record'), mem, .inr (by simp [phase])⟩))⟩
  | unpark processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨parked, found, rfl, rfl⟩ := found
    have record : ∃ process, state.record processId = some process := by
      cases record : state.record processId with
      | none => simp [State.process, record] at found
      | some process => exact ⟨process, rfl⟩
    obtain ⟨process, record⟩ := record
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    exact ⟨false, .inl (.inr ⟨(processId, record'), mem, by simp [found]⟩)⟩
  | fire reference =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨timer, found, rfl, rfl⟩ := found
    have equal := List.find?_some (by simpa [Kernel.find?_eq] using found)
    have mem := List.mem_of_find?_eq_some (by simpa [Kernel.find?_eq] using found)
    simp only [beq_iff_eq] at equal
    subst equal
    exact ⟨false, .inr ⟨timer, mem, rfl, rfl, rfl, rfl⟩⟩

end Lynx.Concurrent
