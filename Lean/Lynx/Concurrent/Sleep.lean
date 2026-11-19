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

/-! ### Absorbing a step -/

private theorem lookup_rewriteTask_removed {processId : PID} :
    ∀ {tasks : List (PID × Task α)}, tasks.Pairwise (fun entry entry' => entry.1 ≠ entry'.1) →
      Kernel.lookup processId (rewriteTask processId (fun _ => []) tasks) = none
  | [], _ => rfl
  | (other, task) :: rest, distinct => by
    simp only [rewriteTask]
    split
    · rename_i same; subst same
      simp only [List.nil_append, Kernel.lookup_eq]
      apply List.lookup_eq_none_iff.mpr
      intro entry mem
      simpa [bne_iff_ne] using List.rel_of_pairwise_cons distinct mem
    · rename_i differ
      have rest' := lookup_rewriteTask_removed (processId := processId) (List.pairwise_cons.mp distinct).2
      simp only [Kernel.lookup_eq] at rest' ⊢
      have differ' : (processId == other) = false := by simpa using Ne.symm differ
      simp [List.lookup_cons, differ', rest']

/-- A step that leaves every process's computation as it is leaves the tasks
and the result as they are. -/
private theorem Config.next_of_keepsTasks {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key : Key} {event : Event} {next : Config α}
    (distinct : (Config.running state tasks finished false).distinctTasks = true)
    (keeps : (Config.running state tasks finished false).keepsTasks key next = true)
    (step : (Config.running state tasks finished false).stepOf key = some (event, next)) :
    ∃ state', next = .running state' tasks finished false := by
  cases key with
  | own => simp [Config.keepsTasks] at keeps
  | handle processId =>
    obtain ⟨task, view, lookup, -, state', task', lookup', rfl⟩ := Config.changes_handle step
    simp only [handleTaskChange] at lookup'
    rw [lookup] at lookup'; simp only [Option.some.injEq] at lookup'; subst lookup'
    simp only [Config.keepsTasks, lookup, handleTaskChange, Bool.and_eq_true, Option.isNone_iff_eq_none] at keeps
    obtain ⟨waiting, kept⟩ := keeps
    obtain ⟨exits, resumed⟩ := view
    cases exits with
    | some reason =>
      have removed : handleChange (α := α) processId (some reason, resumed) = fun _ => [] := rfl
      rw [removed, lookup_rewriteTask_removed (distinct_of_distinctTasks distinct)] at kept
      simp at kept
    | none =>
      refine ⟨state', ?_⟩
      have same : handleChange processId (none, resumed) task = [(processId, task)] := by
        obtain ⟨_, _, wait⟩ := task
        simp only at waiting; subst waiting
        cases resumed <;> rfl
      simp only [handleTaskChange, handleFinished, Option.orElse_none]
      rw [rewriteTask_of_lookup lookup, same, ← rewriteTask_of_lookup (change := fun task => [(processId, task)])
        lookup, rewriteTask_keep]
  | link | phase | unpark | fire =>
    obtain ⟨state', rfl⟩ := Config.changes_keeps rfl step
    exact ⟨state', rfl⟩

/-- A step absorbs a step that leaves every process's computation as it is,
when taking it after reads the same and reaches the same configuration as
taking it alone. -/
private theorem Config.absorbs {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key other : Key} {event event' event₃ : Event}
    {next next' last : Config α} (within : state.Within elapsed)
    (distinct : (Config.running state tasks finished false).distinctTasks = true)
    (keeps : (Config.running state tasks finished false).keepsTasks key next = true)
    (step : (Config.running state tasks finished false).stepOf key = some (event, next))
    (step' : (Config.running state tasks finished false).stepOf other = some (event', next'))
    (after : next.stepOf other = some (event₃, last))
    (view : (Config.running state tasks finished false).sameView next other = true)
    (same : last.sameAfter next' = true) : last = next' := by
  have within' : next'.Within elapsed :=
    Config.Within.step (config := .running state tasks finished false) within (Config.step_of_stepOf step')
  have withinNext : next.Within elapsed :=
    Config.Within.step (config := .running state tasks finished false) within (Config.step_of_stepOf step)
  have within₃ : last.Within elapsed := Config.Within.step withinNext (Config.step_of_stepOf after)
  have finish : ∀ {first second : State} {tasks' : List (PID × Task α)} {finished' : Option (Except Exception α)}
      {exhausted : Bool}, last = .running first tasks' finished' exhausted →
      next' = .running second tasks' finished' exhausted → last = next' := by
    intro first second tasks' finished' exhausted equal equal'
    subst equal equal'
    simp only [Config.sameAfter, Bool.and_eq_true] at same
    rw [State.eq_of_identical same.2 (within₃.2.trans within'.2.symm)]
  obtain ⟨state₁, rfl⟩ := Config.next_of_keepsTasks distinct keeps step
  have elapsed₁ : state.elapsed = state₁.elapsed := within.2.trans withinNext.2.symm
  cases other with
  | own processId =>
    obtain ⟨task, transition, lookup, head, equal⟩ := Config.stepOf_own step'
    obtain ⟨task₁, transition₁, lookup₁, head₁, equal₁⟩ := Config.stepOf_own after
    rw [lookup] at lookup₁; simp only [Option.some.injEq] at lookup₁; subst lookup₁
    simp only [Config.sameView, lookup] at view
    obtain ⟨transition₂, head₂, tasksEqual, finishedEqual, exhaustedEqual⟩ :=
      (Task.own_shape view elapsed₁).head head
    rw [head₁] at head₂; simp only [Option.some.injEq] at head₂; subst head₂
    subst equal equal₁
    rw [← exhaustedEqual, ← tasksEqual, ← finishedEqual] at finish
    rw [← exhaustedEqual, ← tasksEqual, ← finishedEqual]
    cases exhausted : transition.exhausted
    · simp only [exhausted, Bool.false_eq_true, ↓reduceIte] at finish ⊢
      exact finish rfl rfl
    · simp only [exhausted, ↓reduceIte] at finish ⊢
      exact finish rfl rfl
  | handle processId =>
    obtain ⟨task, read, lookup, -, changes, changes₁⟩ := Config.changes_handle_transfer step' after view
    obtain ⟨state₂, task₂, lookup₂, rfl⟩ := changes
    obtain ⟨state₃, task₃, lookup₃, rfl⟩ := changes₁
    simp only [handleTaskChange] at lookup₂ lookup₃
    rw [lookup] at lookup₂ lookup₃
    simp only [Option.some.injEq] at lookup₂ lookup₃
    subst lookup₂ lookup₃
    exact finish rfl rfl
  | link | phase | unpark | fire =>
    obtain ⟨state₂, rfl⟩ := Config.changes_keeps rfl step'
    obtain ⟨state₃, rfl⟩ := Config.changes_keeps rfl after
    exact finish rfl rfl

end Lynx.Concurrent
