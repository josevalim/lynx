module

public import Lynx.Concurrent.Frames
import all Lynx.Concurrent.Diamond
import all Lynx.Concurrent.Frames

/-! Following runs with sleep sets (`checkSleep`) covers every run. Each step
of a configuration has a key naming it (`Config.taggedSteps`), a step asleep
stays asleep after another it commutes with or absorbs (`Config.staysAfter`),
and a forced step is taken alone as every run can take it first
(`Lynx.Concurrent.Forced`). -/

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
        simp [differ, found]

/-- A tagged step of a configuration whose processes have one task each is the
step with its key. -/
private theorem Config.stepOf_of_tagged {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key : Key} {event : Event} {next : Config α} {forced : Bool}
    (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (mem : (key, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps) :
    (Config.running state tasks finished false).stepOf key = some (event, next) := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at mem
  rcases mem with ((((⟨⟨before, ⟨processId, task⟩, after⟩, split, own | handle⟩ | ⟨⟨processId, _⟩, -, link | phase⟩) |
    ⟨⟨processId, _⟩, -, unpark⟩) | ⟨timer, firing, rfl, rfl, rfl, -⟩) | ⟨update, staged, rfl, rfl, rfl, -⟩)
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
  · simp only [Option.mem_toList] at staged
    simp [Config.stepOf, staged]

/-- Every step of a running configuration is tagged with a key. -/
private theorem Config.tagged_of_step {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {event : Event} {next : Config α}
    (step : Step (.running state tasks finished false) event next) :
    ∃ key forced, (key, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps := by
  simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at step
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq]
  rcases step with ((((⟨⟨before, ⟨processId, task⟩, after⟩, split, transition, mem, rfl, rfl⟩ |
    ⟨⟨processId, record⟩, mem, phased, phases, rfl, rfl⟩) | ⟨⟨processId, record⟩, mem, unpark⟩) |
    ⟨timer, firing, rfl, rfl⟩) | ⟨update, staged, rfl, rfl⟩)
  · simp only [Task.transitions, Kernel.append_eq, List.mem_append] at mem
    rcases mem with own | handle
    · exact ⟨_, _, .inl (.inl (.inl (.inl ⟨_, split, .inl ⟨transition, own, rfl, rfl, rfl, rfl⟩⟩)))⟩
    · exact ⟨_, _, .inl (.inl (.inl (.inl ⟨_, split, .inr ⟨transition, handle, rfl, rfl, rfl, rfl⟩⟩)))⟩
  · simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at phases
    rcases phases with ⟨target, linked, found⟩ | found
    · exact ⟨.link processId target, false, .inl (.inl (.inl (.inr ⟨_, mem, .inl ⟨target, linked, by simp [found]⟩⟩)))⟩
    · split at found
      · rename_i phased' found'
        simp only [List.mem_singleton] at found; subst found
        exact ⟨.phase processId, state.dropsDown processId, .inl (.inl (.inl (.inr ⟨_, mem, .inr (by simp [found'])⟩)))⟩
      · simp at found
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at unpark
    obtain ⟨parked, found, rfl, rfl⟩ := unpark
    exact ⟨.unpark processId, false, .inl (.inl (.inr ⟨_, mem, by simp [found]⟩))⟩
  · exact ⟨_, _, .inl (.inr ⟨timer, firing, rfl, rfl, rfl, rfl⟩)⟩
  · exact ⟨_, _, .inr ⟨update, staged, rfl, rfl, rfl, rfl⟩⟩

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
    exact ⟨_, .inl (.inl (.inl (.inl ⟨_, split', .inl ⟨transition, List.mem_of_head? head, rfl, rfl, rfl, rfl⟩⟩)))⟩
  | handle processId =>
    simp only [Config.stepOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨⟨before, task, after⟩, split, transition, head, rfl, rfl⟩ := found
    have split' : (before, (processId, task), after) ∈ splits tasks := by rw [splitAt_eq split]; exact mem_splits
    exact ⟨_, .inl (.inl (.inl (.inl ⟨_, split', .inr ⟨transition, List.mem_of_head? head, rfl, rfl, rfl, rfl⟩⟩)))⟩
  | link processId target =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨next', phase, rfl, rfl⟩ := found
    obtain ⟨process, record, linked⟩ := State.record_of_linkPhase phase
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    exact ⟨false, .inl (.inl (.inl (.inr ⟨(processId, record'), mem, .inl ⟨target, linked, by simp [phase]⟩⟩)))⟩
  | phase processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨next', phase, rfl, rfl⟩ := found
    obtain ⟨process, record⟩ := State.record_of_phase phase
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    exact ⟨state.dropsDown processId, .inl (.inl (.inl (.inr ⟨(processId, record'), mem, .inr (by simp [phase])⟩)))⟩
  | unpark processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨parked, found, rfl, rfl⟩ := found
    have record : ∃ process, state.record processId = some process := by
      cases record : state.record processId with
      | none => simp [State.process, record] at found
      | some process => exact ⟨process, rfl⟩
    obtain ⟨process, record⟩ := record
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    exact ⟨false, .inl (.inl (.inr ⟨(processId, record'), mem, by simp [found]⟩))⟩
  | fire reference =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨timer, found, rfl, rfl⟩ := found
    have equal := List.find?_some (by simpa [Kernel.find?_eq] using found)
    have mem := List.mem_of_find?_eq_some (by simpa [Kernel.find?_eq] using found)
    simp only [beq_iff_eq] at equal
    subst equal
    exact ⟨false, .inl (.inr ⟨timer, mem, rfl, rfl, rfl, rfl⟩)⟩
  | commit =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨update, staged, rfl, rfl⟩ := found
    exact ⟨false, .inr ⟨update, by simp [staged], rfl, rfl, rfl, rfl⟩⟩

/-! ### Absorbing a step -/

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
      rw [removed, lookup_rewriteTask_remove (distinct_of_distinctTasks distinct)] at kept
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
  | link | phase | unpark | fire | commit =>
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
  | link | phase | unpark | fire | commit =>
    obtain ⟨state₂, rfl⟩ := Config.changes_keeps rfl step'
    obtain ⟨state₃, rfl⟩ := Config.changes_keeps rfl after
    exact finish rfl rfl

/-! ### Steps that stay asleep -/

/-- What every configuration a run reaches satisfies, as far as commuting steps need. -/
private def Config.Commuting (elapsed : PID → Nat → Nat) (config : Config α) : Prop :=
  config.Within elapsed ∧ config.Normalized ∧ config.FinishesOnce

/-- A configuration reaches another by some run. -/
private def Reaches (first last : Config α) : Prop := ∃ events, Run first events last

private theorem Reaches.step {first next last : Config α} {event : Event}
    (step : Step first event next) (reaches : Reaches next last) : Reaches first last :=
  let ⟨events, run⟩ := reaches; ⟨event :: events, .step step run⟩

/-- A step that stays asleep after another is enabled before and after it,
and after it reaches what it reaches alone, or what the other reaches after it. -/
private theorem Config.stays {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {steps : List (Key × Event × Config α)} {key other : Key}
    {event : Event} {next : Config α}
    (reachable : (Config.running state tasks finished false).Commuting elapsed)
    (distinct : (Config.running state tasks finished false).distinctTasks = true)
    (tagged : ∀ key event next, (key, event, next) ∈ steps →
      (Config.running state tasks finished false).stepOf key = some (event, next))
    (step : (Config.running state tasks finished false).stepOf key = some (event, next))
    (stays : (Config.running state tasks finished false).staysAfter steps key next other = true) :
    ∃ event' next', (Config.running state tasks finished false).stepOf other = some (event', next') ∧
      ∃ event₃ last, next.stepOf other = some (event₃, last) ∧
        (last = next' ∨ ∃ event₄, next'.stepOf key = some (event₄, last)) := by
  obtain ⟨within, normalized, once⟩ := reachable
  simp only [Config.staysAfter] at stays
  split at stays
  · rename_i found event' next' equal
    have mem := List.mem_of_find?_eq_some (by simpa [Kernel.find?_eq] using equal)
    have same : found = other := by
      have := List.find?_some (by simpa [Kernel.find?_eq] using equal)
      exact eq_of_beq this
    subst same
    have step' := tagged _ _ _ mem
    refine ⟨_, _, step', ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true] at stays
    rcases stays with commutes | ⟨keeps, absorbs⟩
    · obtain ⟨event₃, event₄, last, after, after'⟩ :=
        Config.commutes_of_commutesAfter within normalized once commutes step step'
      exact ⟨event₃, last, after, .inr ⟨event₄, after'⟩⟩
    · split at absorbs
      · rename_i event₃ last after
        simp only [Bool.and_eq_true] at absorbs
        exact ⟨event₃, last, after,
          .inl (Config.absorbs within distinct keeps step step' after absorbs.1 absorbs.2)⟩
      · simp at absorbs
  · simp at stays

/-! ### Exploring with sleep sets -/

/-- `explore` follows a step from which the run continues, with a sleep set
that excludes the run: steps asleep before it cannot start the run, and of
the steps it follows first, none starts it. -/
private theorem explore_sound {visit : List Key → Config α → Bool} {stays : Key → Config α → Key → Bool}
    {sleep : List Key} {steps : List (Key × Event × Config α)} {last : Config α} {goal : Prop}
    (visited : ∀ key event next, (key, event, next) ∈ steps → ∀ sleep', visit sleep' next = true →
      (∀ key' ∈ sleep', stays key next key' = true) → Reaches next last →
      (∀ key' ∈ sleep', ∀ event' next', next.stepOf key' = some (event', next') → ¬Reaches next' last) →
      goal)
    (diamond : ∀ key event next, (key, event, next) ∈ steps → ∀ key', stays key next key' = true →
      ∀ event' next', next.stepOf key' = some (event', next') → Reaches next' last →
        ∃ event₀ next₀, (key', event₀, next₀) ∈ steps ∧ Reaches next₀ last)
    (unique : ∀ key event event' next next', (key, event, next) ∈ steps →
      (key, event', next') ∈ steps → next = next')
    (asleep : ∀ key ∈ sleep, ∀ event next, (key, event, next) ∈ steps → ¬Reaches next last)
    (first : ∃ key event next, (key, event, next) ∈ steps ∧ Reaches next last)
    (explored : explore visit stays sleep [] steps = true) : goal := by
  suffices ∀ (earlier rest : List (Key × Event × Config α)) (done : List Key), steps = earlier ++ rest →
      (∀ key ∈ done, ∃ event next, (key, event, next) ∈ earlier) →
      (∀ key event next, (key, event, next) ∈ earlier → key ∉ sleep → ¬Reaches next last) →
      explore visit stays sleep done rest = true → goal from
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
    simp only [explore, Kernel.contains_eq, Kernel.filter_eq, Kernel.append_eq] at explored
    split at explored
    · rename_i slept
      refine ih _ done extend (fun key mem => ?_) (fun key' event' next' mem' out => ?_) explored
      · obtain ⟨event, next, mem⟩ := found key mem; exact ⟨event, next, by simp [mem]⟩
      · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at mem'
        rcases mem' with mem' | ⟨rfl, rfl, rfl⟩
        · exact unreached _ _ _ mem' out
        · exact absurd (List.elem_iff.mp slept) out
    · simp only [Bool.and_eq_true] at explored
      by_cases reaches : Reaches next last
      · refine visited key event next mem _ explored.1 (fun key' slept => (List.mem_filter.mp slept).2)
          reaches fun key' slept event' next' after reaches' => ?_
        simp only [List.mem_filter, List.mem_append] at slept
        obtain ⟨slept | finished, stays'⟩ := slept
        · obtain ⟨event₀, next₀, mem₀, reaches₀⟩ := diamond key event next mem key' stays' event' next' after reaches'
          exact asleep key' slept event₀ next₀ mem₀ reaches₀
        · obtain ⟨event₀, next₀, mem₀, reaches₀⟩ := diamond key event next mem key' stays' event' next' after reaches'
          obtain ⟨event₁, next₁, mem₁⟩ := found key' finished
          have same := unique key' event₁ event₀ next₁ next₀ (by rw [equal]; simp [mem₁]) mem₀
          subst same
          by_cases slept : key' ∈ sleep
          · exact asleep key' slept event₀ next₁ mem₀ reaches₀
          · exact unreached key' event₁ next₁ mem₁ slept reaches₀
      · refine ih _ _ extend (fun key' mem' => ?_) (fun key' event' next' mem' out => ?_) explored.2
        · simp only [List.mem_append, List.mem_singleton] at mem'
          rcases mem' with mem' | rfl
          · obtain ⟨event, next, mem⟩ := found key' mem'; exact ⟨event, next, by simp [mem]⟩
          · exact ⟨event, next, by simp⟩
        · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at mem'
          rcases mem' with mem' | ⟨rfl, rfl, rfl⟩
          · exact unreached _ _ _ mem' out
          · exact reaches

/-! ### Every process has one task

The steps that every run can take first are argued along runs `checkSleep`
does not follow, so that each process has one task must hold of every
configuration a run reaches, not only of those it checks. A child's PID
extends its parent's with the parent's count of children, which only spawning
changes; so no task's PID extends a PID its parent has not spawned yet. -/

/-- An effect that keeps every live record live and with the same count of
children, except those of `actor`. -/
private def Effect.Steady (effect : Effect) (actor : PID → Prop) : Prop :=
  ∀ processId, ¬actor processId → ∀ process : ProcessState, process.exiting = none →
    ∃ process', effect.record processId (some process) = some process' ∧ process'.exiting = none ∧
      process'.children = process.children

private theorem Effect.Steady.empty {actor : PID → Prop} : ({} : Effect).Steady actor :=
  fun _ _ process none => ⟨process, rfl, none, rfl⟩

private theorem Effect.Steady.reshare {actor : PID → Prop} {change : PersistentTerms → PersistentTerms} :
    (Effect.reshare change).Steady actor :=
  fun _ _ process none => ⟨process, rfl, none, rfl⟩

private theorem Effect.Steady.andThen {first second : Effect} {actor : PID → Prop}
    (one : first.Steady actor) (two : second.Steady actor) : (first.andThen second).Steady actor := by
  intro processId outside process none
  obtain ⟨process', found, none', children⟩ := one processId outside process none
  obtain ⟨process'', found', none'', children'⟩ := two processId outside process' none'
  refine ⟨process'', ?_, none'', children'.trans children⟩
  rw [Effect.record_andThen]; simp [found, found']

private theorem Effect.Steady.ite {first second : Effect} {actor : PID → Prop} (condition : Prop)
    [Decidable condition] (one : first.Steady actor) (two : second.Steady actor) :
    (if condition then first else second).Steady actor := by
  split
  · exact one
  · exact two

private theorem Effect.Steady.mono {effect : Effect} {actor actor' : PID → Prop} (steady : effect.Steady actor)
    (more : ∀ processId, actor processId → actor' processId) : effect.Steady actor' :=
  fun processId outside => steady processId fun inside => outside (more _ inside)

private theorem Effect.Steady.modify {processId : PID} {change : ProcessState → ProcessState} {actor : PID → Prop}
    (keeps : ∀ process : ProcessState, process.exiting = none →
      (change process).exiting = none ∧ (change process).children = process.children) :
    (Effect.modify processId change).Steady actor := by
  intro other _ process none
  rw [Effect.record_modify]
  split
  · exact ⟨change process, rfl, (keeps process none).1, (keeps process none).2⟩
  · exact ⟨process, rfl, none, rfl⟩

private theorem Effect.Steady.retime (change : List Timer → List Timer) {actor : PID → Prop} :
    (Effect.retime change).Steady actor :=
  fun _ _ process none => ⟨process, rfl, none, rfl⟩

private theorem Effect.Steady.put {processId : PID} {process : ProcessState} {actor : PID → Prop}
    (inside : actor processId) : (Effect.put processId process).Steady actor := by
  intro other outside process' none
  have differ : other ≠ processId := fun same => outside (same ▸ inside)
  exact ⟨process', by simp [Effect.put, Effect.record, changeOf, Ne.symm differ], none, rfl⟩

local syntax "steady_modify" : tactic
macro_rules
  | `(tactic| steady_modify) => `(tactic|
      (refine Effect.Steady.modify fun process none => ?_; simp [none, queueAt, setDowns]))

local syntax "steady" : tactic
macro_rules
  | `(tactic| steady) => `(tactic|
      (repeat' first
        | exact Effect.Steady.empty
        | exact Effect.Steady.retime _
        | refine Effect.Steady.andThen ?_ ?_
        | refine Effect.Steady.ite _ ?_ ?_
        | steady_modify))

private theorem State.fallbackEffect_steady (state : State) (source target : PID) (signal : Signal)
    {actor : PID → Prop} : (state.fallbackEffect source target signal).Steady actor := by
  cases signal <;> simp only [State.fallbackEffect] <;> first | exact Effect.Steady.empty | steady_modify

private theorem State.enqueueEffect_steady (state : State) (source target : PID) (signal : Signal)
    {actor : PID → Prop} : (state.enqueueEffect source target signal).Steady actor := by
  unfold State.enqueueEffect
  split
  · split
    · steady_modify
    · exact State.fallbackEffect_steady _ _ _ _
  · exact State.fallbackEffect_steady _ _ _ _

private theorem State.unparkEffect_steady (state : State) (processId : PID) {actor : PID → Prop} :
    (state.unparkEffect processId).Steady actor := by
  unfold State.unparkEffect
  split
  · exact (by steady_modify : Effect.Steady _ _).andThen (State.enqueueEffect_steady _ _ _ _)
  · exact Effect.Steady.empty

private theorem State.sendEffect_steady (state : State) (source target : PID) (signal : Signal)
    {actor : PID → Prop} : (state.sendEffect source target signal).Steady actor := by
  unfold State.sendEffect
  split
  · split
    · exact (State.unparkEffect_steady _ _).andThen (State.enqueueEffect_steady _ _ _ _)
    · exact State.enqueueEffect_steady _ _ _ _
  · exact State.enqueueEffect_steady _ _ _ _

private theorem State.linkExitEffect_steady (state : State) (processId target : PID) (reason : Term)
    {actor : PID → Prop} : (state.linkExitEffect processId target reason).Steady actor := by
  unfold State.linkExitEffect
  split
  · steady_modify
  · exact State.sendEffect_steady _ _ _ _

private theorem State.answerEffect_steady (state : State) (processId : PID) (entry : Entry)
    {actor : PID → Prop} : (state.answerEffect processId entry).Steady actor := by
  unfold State.answerEffect
  split <;> first | exact State.sendEffect_steady _ _ _ _ | exact Effect.Steady.empty

private theorem chainEffect_steady {step : State → γ → State} {effect : State → γ → Effect} {actor : PID → Prop}
    (each : ∀ state item, (effect state item).Steady actor) :
    ∀ (items : List γ) (state : State), (chainEffect step effect state items).Steady actor
  | [], _ => Effect.Steady.empty
  | item :: rest, state => (each state item).andThen (chainEffect_steady each rest (step state item))

private theorem State.terminateEffect_steady (state : State) (processId : PID) (reason : Term)
    {actor : PID → Prop} (inside : actor processId) : (state.terminateEffect processId reason).Steady actor := by
  unfold State.terminateEffect
  refine ((Effect.Steady.ite _ (Effect.Steady.retime _) Effect.Steady.empty).andThen
    (Effect.Steady.put inside)).andThen (chainEffect_steady (fun state target => ?_) _ _)
  unfold State.eagerExitEffect
  split
  · refine Effect.Steady.andThen ?_ (State.linkExitEffect_steady _ _ _ _)
    refine Effect.Steady.modify fun process none => ?_
    simp [none]
  · exact Effect.Steady.empty

private theorem State.requestEffect_steady (state : State) (processId : PID) (query : Request)
    {actor : PID → Prop} : (state.requestEffect processId query).Steady actor := by
  have allocated : (allocateEffect processId).Steady actor := by unfold allocateEffect; steady_modify
  cases query <;> simp only [State.requestEffect]
  · exact allocated.andThen (Effect.Steady.ite _ Effect.Steady.empty
      ((State.unparkEffect_steady _ _).andThen (by steady_modify)))
  · steady_modify
  · repeat' split
    all_goals first
      | exact Effect.Steady.empty
      | exact (by steady_modify : Effect.Steady _ _).andThen (State.sendEffect_steady _ _ _ _)
  · repeat' split
    all_goals first
      | exact Effect.Steady.empty
      | exact (by steady_modify : Effect.Steady _ _).andThen (State.sendEffect_steady _ _ _ _)
  · repeat' split
    all_goals exact State.sendEffect_steady _ _ _ _
  · split
    · exact Effect.Steady.empty
    · steady_modify
  · repeat' split
    all_goals first
      | exact Effect.Steady.empty
      | exact State.enqueueEffect_steady _ _ _ _
  · repeat' split
    all_goals first
      | exact Effect.Steady.empty
      | exact State.enqueueEffect_steady _ _ _ _
  · exact State.sendEffect_steady _ _ _ _
  · exact allocated.andThen (Effect.Steady.ite _ (Effect.Steady.retime _) Effect.Steady.empty)
  · split
    · exact (Effect.Steady.retime _).andThen (by steady_modify)
    · exact Effect.Steady.empty
  all_goals
    repeat' split
    all_goals first | exact Effect.Steady.empty | exact Effect.Steady.reshare

/-- Spawning keeps every live record but the parent's and the child's. -/
private theorem State.spawnEffect_steady (state : State) (processId : PID) (options : SpawnOptions)
    {actor : PID → Prop} (parent : actor processId)
    (child : actor (Kernel.append processId [(state.process processId).children + 1])) :
    (state.spawnEffect processId options).Steady actor := by
  unfold State.spawnEffect
  refine (((Effect.Steady.put parent).andThen (Effect.Steady.put child)).andThen
    (Effect.Steady.ite _ ((by steady_modify : Effect.Steady _ _).andThen (by steady_modify))
      Effect.Steady.empty)).andThen (Effect.Steady.ite _ ?_ Effect.Steady.empty)
  unfold allocateEffect
  exact (by steady_modify : Effect.Steady _ _).andThen
    ((by steady_modify : Effect.Steady _ _).andThen (by steady_modify))

private theorem State.exitSignalEffect_steady (state : State) (target source : PID) (reason : Term)
    (linked normalKills : Bool) {actor : PID → Prop} :
    (state.exitSignalEffect target source reason linked normalKills).Steady actor := by
  unfold State.exitSignalEffect
  dsimp only
  repeat' split
  all_goals steady

private theorem State.handleEffect_steady (state : State) (processId : PID) (entry : Entry)
    {actor : PID → Prop} : (state.handleEffect processId entry).Steady actor := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp only [State.handleEffect]
  · unfold appendEffect; steady_modify
  · split
    · unfold appendEffect; steady_modify
    · exact Effect.Steady.empty
  · exact State.exitSignalEffect_steady _ _ _ _ _ _
  · split
    · exact Effect.Steady.empty
    · steady_modify
  · split
    · exact (by steady_modify : Effect.Steady _ _).andThen (State.sendEffect_steady _ _ _ _)
    · exact State.sendEffect_steady _ _ _ _
  · split
    · steady_modify
    · exact Effect.Steady.empty
  · steady_modify
  · refine (Effect.Steady.ite _ (by steady_modify) Effect.Steady.empty).andThen
      (Effect.Steady.ite _ ((by steady_modify : Effect.Steady _ _).andThen ?_) Effect.Steady.empty)
    unfold appendEffect; steady_modify
  · exact State.sendEffect_steady _ _ _ _
  · exact Effect.Steady.empty
  · exact Effect.Steady.empty

private theorem State.phaseEffect_steady (state : State) (processId : PID) {actor : PID → Prop} :
    (state.phaseEffect processId).Steady actor := by
  unfold State.phaseEffect
  dsimp only
  repeat' split
  all_goals first
    | exact Effect.Steady.empty
    | (refine Effect.Steady.andThen ?_ (State.sendEffect_steady _ _ _ _); steady_modify)
    | (refine Effect.Steady.andThen ?_ (State.answerEffect_steady _ _ _); steady_modify)

private theorem State.fireEffect_steady (state : State) (timer : Timer) {actor : PID → Prop} :
    (state.fireEffect timer).Steady actor :=
  (Effect.Steady.retime _).andThen (State.enqueueEffect_steady _ _ _ _)

/-- A process's own step keeps every live record but its own and a child's it
spawns, and its own too when it continues without spawning. -/
private theorem Task.ownEffect_steady {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (mem : transition ∈ task.own state processId) :
    (task.ownEffect state processId).Steady
        (fun other => other = processId ∨ other = Kernel.append processId [(state.process processId).children + 1]) ∧
      ((∃ task', (processId, task') ∈ transition.tasks) →
        (∀ options child next, task.computation ≠ .schedule options child next) →
        (task.ownEffect state processId).Steady fun _ => False) := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    have all : (Task.ownEffect state processId ⟨computation, finish, none⟩).Steady (fun _ => False) →
        (Task.ownEffect state processId ⟨computation, finish, none⟩).Steady
          (fun other => other = processId ∨ other = Kernel.append processId [(state.process processId).children + 1]) ∧
        ((∃ task', (processId, task') ∈ transition.tasks) →
          (∀ options child next, computation ≠ .schedule options child next) →
          (Task.ownEffect state processId ⟨computation, finish, none⟩).Steady fun _ => False) :=
      fun steady => ⟨steady.mono fun _ => False.elim, fun _ _ => steady⟩
    have ends : ∀ reason, transition.tasks = [] → (state.terminateEffect processId reason).Steady
        (fun other => other = processId ∨ other = Kernel.append processId [(state.process processId).children + 1]) ∧
        ((∃ task', (processId, task') ∈ transition.tasks) →
          (∀ options child next, computation ≠ .schedule options child next) →
          (state.terminateEffect processId reason).Steady fun _ => False) :=
      fun reason none => ⟨State.terminateEffect_steady _ _ _ (.inl rfl), fun ⟨_, inside⟩ => by simp [none] at inside⟩
    cases computation with
    | ok => simp [Task.own, Task.ended] at mem; subst mem; exact ends _ rfl
    | error exception =>
      cases exception
      case exhausted =>
        simp [Task.own] at mem; subst mem
        refine ⟨fun other outside process live => ?_, fun ⟨_, inside⟩ => by simp at inside⟩
        have differ : other ≠ processId := fun same => outside (.inl same)
        exact ⟨process, by simp [Task.ownEffect, Effect.record, changeOf, Ne.symm differ], live, rfl⟩
      all_goals (simp [Task.own, Task.ended] at mem; subst mem; exact ends _ rfl)
    | schedule options child next =>
      exact ⟨State.spawnEffect_steady _ _ _ (.inl rfl) (.inr rfl),
        fun _ spawns => absurd rfl (spawns options child next)⟩
    | get => exact all Effect.Steady.empty
    | set => exact all (by simp only [Task.ownEffect]; steady_modify)
    | send => exact all (State.sendEffect_steady _ _ _ _)
    | receive =>
      refine all ?_
      simp only [Task.ownEffect]
      split
      · steady_modify
      · exact Effect.Steady.empty
    | request => exact all (State.requestEffect_steady _ _ _)

private theorem append_ne_self (processId : PID) (index : Nat) : Kernel.append processId [index] ≠ processId := by
  intro same
  have := congrArg List.length same
  simp at this

/-- The records after putting a process's record and a child's, then changes
that keep live records. -/
private theorem putTwice_records {first second rest rest' : Effect} {processId child : PID}
    {process : ProcessState} (put : first = Effect.put processId process) (put' : second = Effect.put child {})
    (steady : rest.Steady fun _ => False) (steady' : rest'.Steady fun _ => False) (differ : child ≠ processId)
    (live : process.exiting = none) (record record' : Option ProcessState) :
    (∃ process', (((first.andThen second).andThen rest).andThen rest').record processId record = some process' ∧
      process'.exiting = none ∧ process'.children = process.children) ∧
    ∃ process', (((first.andThen second).andThen rest).andThen rest').record child record' = some process' ∧
      process'.exiting = none := by
  subst put put'
  simp only [Effect.record_andThen, Function.comp]
  have atParent : (Effect.put processId process).record processId record = some process := by
    simp [Effect.put, Effect.record, changeOf]
  have childAtParent : (Effect.put child ({} : ProcessState)).record processId = id := by
    funext record; simp [Effect.put, Effect.record, changeOf, differ]
  have atChild : ∀ record, (Effect.put child ({} : ProcessState)).record child record = some {} := by
    intro record; simp [Effect.put, Effect.record, changeOf]
  constructor
  · rw [atParent, childAtParent]
    obtain ⟨process₁, found₁, live₁, children₁⟩ := steady processId id process live
    obtain ⟨process₂, found₂, live₂, children₂⟩ := steady' processId id process₁ live₁
    exact ⟨process₂, by simp [found₁, found₂], live₂, children₂.trans children₁⟩
  · rw [atChild]
    obtain ⟨process₁, found₁, live₁, -⟩ := steady child id {} rfl
    obtain ⟨process₂, found₂, live₂, -⟩ := steady' child id process₁ live₁
    exact ⟨process₂, by simp [found₁, found₂], live₂⟩

/-- Spawning leaves the parent live, with one more child, and the child live. -/
private theorem State.spawnEffect_records (state : State) (processId : PID) (options : SpawnOptions)
    {process : ProcessState} (found : state.record processId = some process) (live : process.exiting = none)
    (record : Option ProcessState) :
    (∃ process', (state.spawnEffect processId options).record processId (some process) = some process' ∧
      process'.exiting = none ∧ process'.children = process.children + 1) ∧
    ∃ process', (state.spawnEffect processId options).record
      (Kernel.append processId [(state.process processId).children + 1]) record = some process' ∧
      process'.exiting = none := by
  have same : state.process processId = process := by simp [State.process, found]
  unfold State.spawnEffect
  dsimp only
  rw [same]
  refine putTwice_records (process := { process with children := process.children + 1 }) rfl rfl ?_ ?_
    (append_ne_self _ _) live _ _
  · steady
  · unfold allocateEffect; steady

/-- Whether a state keeps every live record of another live, with the same
count of children, except those of `actor`. -/
private def State.KeepsLive (state next : State) (actor : PID → Prop) : Prop :=
  ∀ processId, ¬actor processId → ∀ process, state.record processId = some process → process.exiting = none →
    ∃ process', next.record processId = some process' ∧ process'.exiting = none ∧
      process'.children = process.children

private theorem Realizes.keepsLive {effect : Effect} {state next : State} {actor : PID → Prop}
    (realizes : Realizes effect state next) (steady : effect.Steady actor) : state.KeepsLive next actor := by
  intro processId outside process found live
  rw [realizes.record, found]
  exact steady processId outside process live

private theorem State.KeepsLive.trans {first second third : State} {actor actor' : PID → Prop}
    (one : first.KeepsLive second actor) (two : second.KeepsLive third actor') :
    first.KeepsLive third fun processId => actor processId ∨ actor' processId := by
  intro processId outside process found live
  obtain ⟨process', found', live', children'⟩ := one processId (fun inside => outside (.inl inside)) process found live
  obtain ⟨process'', found'', live'', children''⟩ :=
    two processId (fun inside => outside (.inr inside)) process' found' live'
  exact ⟨process'', found'', live'', children''.trans children'⟩

private theorem State.KeepsLive.mono {state next : State} {actor actor' : PID → Prop}
    (keeps : state.KeepsLive next actor) (more : ∀ processId, actor processId → actor' processId) :
    state.KeepsLive next actor' :=
  fun processId outside => keeps processId fun inside => outside (more _ inside)

/-- Normalizing keeps every live record live, with the same count of children. -/
private theorem State.keepsLive_normalize {state : State} (sorted : state.Sorted) :
    state.KeepsLive state.normalize fun _ => False := by
  intro processId _ process found live
  rw [State.record_normalize' sorted, found]
  have finished : (normRecord state.gone processId process).finished = false := by
    cases equal : (normRecord state.gone processId process).finished
    · rfl
    · have := ProcessState.finished_exiting equal
      simp [normRecord, live] at this
  refine ⟨normRecord state.gone processId process, ?_, by simp [normRecord, live], by simp [normRecord, live]⟩
  simp [Option.filter, finished]

/-- Handling a signal keeps every live record but the process's, and its own
too when it continues. -/
private theorem Task.handleEffect_steady {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (mem : transition ∈ task.handle state processId) :
    (task.handleEffect state processId).Steady (· = processId) ∧
      ((∃ task', (processId, task') ∈ transition.tasks) → (task.handleEffect state processId).Steady fun _ => False) := by
  simp only [Task.handle] at mem
  simp only [Task.handleEffect]
  cases queue : (state.process processId).queue with
  | nil => simp [queue] at mem
  | cons entry rest =>
    simp only [queue] at mem ⊢
    have handled : ∀ actor : PID → Prop, ((Effect.modify processId fun process =>
        { process with queue := process.queue.drop 1 }).andThen
        ((state.set processId { state.process processId with queue := rest }).handleEffect processId entry)).Steady
        actor := fun _ => (by steady_modify : Effect.Steady _ _).andThen (State.handleEffect_steady _ _ _)
    generalize (State.set _ _ _).handle _ _ _ = result at mem ⊢
    obtain ⟨handledState, resumed, exits⟩ := result
    cases exits with
    | some reason =>
      simp only [List.mem_singleton] at mem; subst mem
      exact ⟨(handled _).andThen (State.terminateEffect_steady _ _ _ rfl),
        fun ⟨_, inside⟩ => by simp [Task.ended] at inside⟩
    | none => exact ⟨handled _, fun _ => handled _⟩

/-- A link phase keeps every live record but the ended process's. -/
private theorem State.linkPhase_keepsLive {state next : State} {processId target : PID}
    (phase : state.linkPhase processId target = some next) : state.KeepsLive next (· = processId) := by
  unfold State.linkPhase at phase
  split at phase
  · rename_i process found
    split at phase
    · rename_i exiting exits
      split at phase
      · simp only [Option.some.injEq] at phase; subst phase
        have set := Realizes.set found fun process : ProcessState => { process with exiting := some { exiting with
          links := Kernel.filter (· != target) exiting.links } }
        refine (set.andThen (Realizes.linkExit _ _ _ _)).keepsLive ?_
        refine Effect.Steady.andThen ?_ (State.linkExitEffect_steady _ _ _ _)
        intro other outside process' live
        rw [Effect.record_modify]
        simp only [outside, ↓reduceIte]
        exact ⟨process', rfl, live, rfl⟩
      · simp at phase
    · simp at phase
  · simp at phase

/-- No process has two tasks, every process with a task is live, and no
task's PID extends a PID its parent has not spawned yet. -/
private def TasksFresh (state : State) (tasks : List (PID × Task α)) : Prop :=
  tasks.Pairwise (fun entry entry' => entry.1 ≠ entry'.1) ∧ (∀ entry ∈ tasks, state.alive entry.1 = true) ∧
    ∀ entry ∈ tasks, ∀ entry' ∈ tasks, ∀ index, (state.process entry.1).children < index →
      ¬Kernel.append entry.1 [index] <+: entry'.1

private theorem not_append_prefix (processId : PID) (index : Nat) : ¬processId ++ [index] <+: processId :=
  fun extended => by have := extended.length_le; simp at this; omega

private theorem State.alive_iff {state : State} {processId : PID} :
    state.alive processId = true ↔ ∃ process, state.record processId = some process ∧ process.exiting = none := by
  unfold State.alive
  cases state.record processId with
  | none => simp
  | some process => simp [Option.isNone_iff_eq_none]

private theorem State.process_of_record {state : State} {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) : state.process processId = process := by
  simp [State.process, found]

/-- Replacing a process's task by tasks of itself and of the child it spawns
keeps the tasks fresh, when the step keeps every other live record, leaves the
process live with at least as many children, more when it spawns, and the child live. -/
private theorem TasksFresh.replace {state state' : State} {before after replacement : List (PID × Task α)}
    {processId : PID} {task : Task α} (fresh : TasksFresh state (before ++ (processId, task) :: after))
    (pids : ∀ entry ∈ replacement, entry.1 = processId ∨
      entry.1 = Kernel.append processId [(state.process processId).children + 1])
    (distinct : replacement.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (keeps : state.KeepsLive state' fun other => other = processId ∨
      other = Kernel.append processId [(state.process processId).children + 1])
    (own : ∀ entry ∈ replacement, entry.1 = processId → state'.alive processId = true ∧
      (state.process processId).children ≤ (state'.process processId).children ∧
      (∀ entry' ∈ replacement, entry'.1 = Kernel.append processId [(state.process processId).children + 1] →
        (state.process processId).children < (state'.process processId).children))
    (spawned : ∀ entry ∈ replacement,
      entry.1 = Kernel.append processId [(state.process processId).children + 1] →
      state'.alive entry.1 = true) :
    TasksFresh state' (before ++ replacement ++ after) := by
  obtain ⟨pairwise, alive, extends'⟩ := fresh
  generalize hc : (state.process processId).children = count at pids keeps own spawned
  generalize hchild : Kernel.append processId [count + 1] = child at pids keeps own spawned
  have mine : (processId, task) ∈ before ++ (processId, task) :: after := by simp
  -- No task's PID extends the child's.
  have unspawned : ∀ entry ∈ before ++ (processId, task) :: after, ¬child <+: entry.1 := by
    intro entry mem
    rw [← hchild]
    exact extends' _ mine entry mem (count + 1) (by rw [hc]; exact Nat.lt_succ_self _)
  -- The other tasks are of neither the process nor its child.
  have others : ∀ entry ∈ before ++ after, entry ∈ before ++ (processId, task) :: after ∧
      entry.1 ≠ processId ∧ entry.1 ≠ child := by
    intro entry mem
    have old : entry ∈ before ++ (processId, task) :: after := by
      simp only [List.mem_append, List.mem_cons] at mem ⊢
      rcases mem with mem | mem
      · exact .inl mem
      · exact .inr (.inr mem)
    refine ⟨old, fun same => ?_, fun same => unspawned entry old (same ▸ List.prefix_refl _)⟩
    simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons] at pairwise
    simp only [List.mem_append] at mem
    rcases mem with mem | mem
    · exact pairwise.2.2 entry mem (processId, task) (.inl rfl) same
    · exact pairwise.2.1.1 entry mem same.symm
  -- The other tasks keep their processes live, with the same children.
  have kept : ∀ entry ∈ before ++ after, ∃ process process', state.record entry.1 = some process ∧
      state'.record entry.1 = some process' ∧ process'.exiting = none ∧ process'.children = process.children := by
    intro entry mem
    obtain ⟨old, notMine, notChild⟩ := others entry mem
    obtain ⟨process, found, live⟩ := State.alive_iff.mp (alive entry old)
    obtain ⟨process', found', live', children⟩ :=
      keeps entry.1 (fun inside => inside.elim notMine notChild) process found live
    exact ⟨process, process', found, found', live', children⟩
  have membership : ∀ entry ∈ before ++ replacement ++ after, entry ∈ before ++ after ∨ entry ∈ replacement := by
    intro entry mem
    simp only [List.mem_append] at mem ⊢
    rcases mem with (mem | mem) | mem
    · exact .inl (.inl mem)
    · exact .inr mem
    · exact .inl (.inr mem)
  -- Every task is of a process with a task before, or of the child.
  have targets : ∀ entry ∈ before ++ replacement ++ after,
      (∃ old ∈ before ++ (processId, task) :: after, old.1 = entry.1) ∨ (entry.1 = child ∧ entry ∈ replacement) := by
    intro entry mem
    rcases membership entry mem with mem | mem
    · exact .inl ⟨entry, (others entry mem).1, rfl⟩
    · rcases pids entry mem with same | same
      · exact .inl ⟨(processId, task), mine, same.symm⟩
      · exact .inr ⟨same, mem⟩
  refine ⟨?_, fun entry mem => ?_, fun entry mem entry' mem' index above => ?_⟩
  · simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons] at pairwise ⊢
    obtain ⟨pairBefore, ⟨headAfter, pairAfter⟩, cross⟩ := pairwise
    refine ⟨⟨pairBefore, distinct, fun entry mem entry' mem' => ?_⟩, pairAfter, fun entry mem entry' mem' => ?_⟩
    · obtain ⟨-, notMine, notChild⟩ := others entry (List.mem_append_left _ mem)
      rcases pids entry' mem' with same | same <;> rw [same] <;> assumption
    · rcases List.mem_append.mp mem with mem | mem
      · exact cross entry mem entry' (.inr mem')
      · obtain ⟨-, notMine, notChild⟩ := others entry' (List.mem_append_right _ mem')
        rcases pids entry mem with same | same <;> rw [same] <;> exact Ne.symm (by assumption)
  · rcases membership entry mem with other | mem
    · obtain ⟨process, process', -, found', live', -⟩ := kept entry other
      exact State.alive_iff.mpr ⟨process', found', live'⟩
    · rcases pids entry mem with same | same
      · rw [same]; exact (own entry mem same).1
      · exact spawned entry mem same
  · simp only [Kernel.append_eq] at above ⊢ hchild extends'
    rcases membership entry mem with other | mine'
    · -- A task of another process keeps its children.
      obtain ⟨process, process', found, found', -, children⟩ := kept entry other
      rw [State.process_of_record found', children] at above
      have above' : (state.process entry.1).children < index := by rw [State.process_of_record found]; exact above
      have old := (others entry other).1
      rcases targets entry' mem' with ⟨old', inside, same⟩ | ⟨same, -⟩
      · rw [← same]; exact extends' entry old old' inside index above'
      · rw [same, ← hchild]
        intro extended
        rcases List.prefix_concat_iff.mp extended with equal | extended
        · exact (others entry other).2.1 (List.append_singleton_inj.mp equal).1
        · exact extends' entry old (processId, task) mine index above' (by simpa using extended)
    · rcases pids entry mine' with same | same
      · -- The process itself has at least as many children.
        obtain ⟨-, atLeast, more⟩ := own entry mine' same
        rw [same] at above ⊢
        rcases targets entry' mem' with ⟨old', inside, same'⟩ | ⟨same', inside⟩
        · rw [← same']
          exact extends' _ mine old' inside index (by rw [hc]; omega)
        · have more := more entry' inside same'
          rw [same', ← hchild]
          intro extended
          rcases List.prefix_concat_iff.mp extended with equal | extended
          · have := (List.append_singleton_inj.mp equal).2; omega
          · exact not_append_prefix processId index (by simpa using extended)
      · -- The child's PID extends no task's but its own.
        rw [same]
        rcases targets entry' mem' with ⟨old', inside, same'⟩ | ⟨same', -⟩
        · rw [← same']
          intro extended
          exact unspawned old' inside ((List.prefix_append child [index]).trans extended)
        · rw [same']
          exact not_append_prefix child index

/-- A step that keeps the tasks keeps them fresh, when it keeps every live
record of a process with a task. -/
private theorem TasksFresh.keep {state state' : State} {tasks : List (PID × Task α)} {actor : PID → Prop}
    (fresh : TasksFresh state tasks) (keeps : state.KeepsLive state' actor)
    (holders : ∀ entry ∈ tasks, ¬actor entry.1) : TasksFresh state' tasks := by
  obtain ⟨pairwise, alive, extends'⟩ := fresh
  have kept : ∀ entry ∈ tasks, ∃ process process', state.record entry.1 = some process ∧
      state'.record entry.1 = some process' ∧ process'.exiting = none ∧ process'.children = process.children := by
    intro entry mem
    obtain ⟨process, found, live⟩ := State.alive_iff.mp (alive entry mem)
    obtain ⟨process', found', live', children⟩ := keeps entry.1 (holders entry mem) process found live
    exact ⟨process, process', found, found', live', children⟩
  refine ⟨pairwise, fun entry mem => ?_, fun entry mem entry' mem' index above => ?_⟩
  · obtain ⟨-, process', -, found', live', -⟩ := kept entry mem
    exact State.alive_iff.mpr ⟨process', found', live'⟩
  · obtain ⟨process, process', found, found', -, children⟩ := kept entry mem
    rw [State.process_of_record found', children] at above
    exact extends' entry mem entry' mem' index (by rw [State.process_of_record found]; exact above)

/-- A process with a task is not one that ended. -/
private theorem TasksFresh.not_exiting {state : State} {tasks : List (PID × Task α)} (fresh : TasksFresh state tasks)
    {processId : PID} {exiting : Exiting} {process : ProcessState} (found : state.record processId = some process)
    (exits : process.exiting = some exiting) : ∀ entry ∈ tasks, ¬entry.1 = processId := by
  intro entry mem same
  obtain ⟨process', found', live⟩ := State.alive_iff.mp (fresh.2.1 entry mem)
  rw [same, found] at found'
  simp only [Option.some.injEq] at found'
  subst found'
  rw [exits] at live
  simp at live

private theorem Task.own_pairwise {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.own state processId) :
    transition.tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1 := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    cases computation with
    | schedule options child next =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      simp [State.spawnWith]
    | receive =>
      simp only [Task.own] at mem
      repeat' split at mem
      all_goals (simp only [List.mem_singleton, List.not_mem_nil] at mem; try (subst mem; simp))
    | request =>
      simp only [Task.own] at mem
      split at mem <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;> simp
    | error exception =>
      cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;> simp [Task.ended]
    | _ => simp only [Task.own, List.mem_singleton] at mem; subst mem; simp [Task.ended]

private theorem Task.handle_pids {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.handle state processId) :
    (∀ entry ∈ transition.tasks, entry.1 = processId) ∧
      transition.tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1 := by
  obtain ⟨view, -, changed, -⟩ := Task.handle_change mem
  rw [changed]
  unfold handleChange
  split
  · simp
  · split <;> simp

private theorem entry_of_pid {processId : PID} {entry : PID × Task α} {tasks : List (PID × Task α)}
    (inside : entry ∈ tasks) (same : entry.1 = processId) : ∃ task, (processId, task) ∈ tasks := by
  obtain ⟨_, task⟩ := entry
  simp only at same; subst same
  exact ⟨task, inside⟩

/-- A process's own step keeps the tasks fresh. -/
private theorem TasksFresh.own {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {processId : PID} {task : Task α} {transition : Transition α} (within : state.Within elapsed)
    (fresh : TasksFresh state tasks) (lookup : Kernel.lookup processId tasks = some task)
    (head : (task.own state processId).head? = some transition) :
    TasksFresh transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks) := by
  have mem := List.mem_of_head? head
  obtain ⟨before, after, split⟩ := splitAt_of_lookup lookup
  rw [rewriteTask_of_splitAt split]
  rw [splitAt_eq split] at fresh
  have realizes := Realizes.own mem
  obtain ⟨steady, steadyKept⟩ := Task.ownEffect_steady mem
  have normal := State.keepsLive_normalize (within.own mem).1
  have mine : (processId, task) ∈ before ++ (processId, task) :: after := by simp
  obtain ⟨process, found, live⟩ := State.alive_iff.mp (fresh.2.1 _ mine)
  have spawnedLive : ∀ options child next, task.computation = .schedule options child next →
      (∃ parent, transition.state.normalize.record processId = some parent ∧ parent.exiting = none ∧
        parent.children = process.children + 1) ∧
      ∃ started, transition.state.normalize.record
        (Kernel.append processId [(state.process processId).children + 1]) = some started ∧
        started.exiting = none := by
    intro options child next computes
    have effect : task.ownEffect state processId = state.spawnEffect processId options := by
      have waiting := Task.own_waiting head
      obtain ⟨computation, finish, wait⟩ := task
      simp only at computes waiting
      subst waiting
      simp only [Task.ownEffect, computes]
    rw [effect] at realizes
    obtain ⟨⟨parent, atParent, liveParent, childrenParent⟩, started, atChild, liveChild⟩ :=
      State.spawnEffect_records state processId options found live
        (state.record (Kernel.append processId [(state.process processId).children + 1]))
    have rawParent : transition.state.record processId = some parent := by
      rw [realizes.record, found]; exact atParent
    have rawChild : transition.state.record (Kernel.append processId [(state.process processId).children + 1]) =
        some started := by
      rw [realizes.record]; exact atChild
    obtain ⟨parent', atParent', liveParent', childrenParent'⟩ := normal processId id parent rawParent liveParent
    obtain ⟨started', atChild', liveChild', -⟩ := normal _ id started rawChild liveChild
    exact ⟨⟨parent', atParent', liveParent', childrenParent'.trans childrenParent⟩, started', atChild', liveChild'⟩
  refine TasksFresh.replace fresh (fun entry inside => ?_) (Task.own_pairwise mem)
    (((realizes.keepsLive steady).trans normal).mono fun _ inside => inside.elim id False.elim)
    (fun entry inside same => ?_) (fun entry inside same => ?_)
  · rcases Task.own_pids mem entry inside with same | ⟨same, -⟩
    · exact .inl same
    · exact .inr same
  · by_cases spawns : ∃ options child next, task.computation = .schedule options child next
    · obtain ⟨options, child, next, computes⟩ := spawns
      obtain ⟨⟨parent, atParent, liveParent, childrenParent⟩, -⟩ := spawnedLive options child next computes
      rw [State.process_of_record atParent, childrenParent, State.process_of_record found]
      exact ⟨State.alive_iff.mpr ⟨parent, atParent, liveParent⟩, by omega, fun _ _ _ => by omega⟩
    · have notSpawn : ∀ options child next, task.computation ≠ .schedule options child next :=
        fun options child next computes => spawns ⟨options, child, next, computes⟩
      obtain ⟨process', found', live', children⟩ :=
        ((realizes.keepsLive (steadyKept (entry_of_pid inside same) notSpawn)).trans normal) processId
          (fun inside => inside.elim id id) process found live
      rw [State.process_of_record found', children, State.process_of_record found]
      refine ⟨State.alive_iff.mpr ⟨process', found', live'⟩, Nat.le_refl _, fun entry' inside' same' => ?_⟩
      exfalso
      rcases Task.own_pids mem entry' inside' with same'' | ⟨-, options, child, next, computes⟩
      · rw [same''] at same'; exact append_ne_self _ _ same'.symm
      · exact notSpawn options child next computes
  · rcases Task.own_pids mem entry inside with same' | ⟨-, options, child, next, computes⟩
    · exfalso; rw [same'] at same; exact append_ne_self _ _ same.symm
    · obtain ⟨-, started, atChild, liveChild⟩ := spawnedLive options child next computes
      rw [same]
      exact State.alive_iff.mpr ⟨started, atChild, liveChild⟩

/-- Handling a signal keeps the tasks fresh. -/
private theorem TasksFresh.handle {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {processId : PID} {task : Task α} {transition : Transition α} (within : state.Within elapsed)
    (fresh : TasksFresh state tasks) (lookup : Kernel.lookup processId tasks = some task)
    (head : (task.handle state processId).head? = some transition) :
    TasksFresh transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks) := by
  have mem := List.mem_of_head? head
  obtain ⟨before, after, split⟩ := splitAt_of_lookup lookup
  rw [rewriteTask_of_splitAt split]
  rw [splitAt_eq split] at fresh
  have realizes := Realizes.handleStep mem
  obtain ⟨steady, steadyKept⟩ := Task.handleEffect_steady mem
  obtain ⟨pids, distinct⟩ := Task.handle_pids mem
  have normal := State.keepsLive_normalize (within.handleStep mem).1
  have mine : (processId, task) ∈ before ++ (processId, task) :: after := by simp
  obtain ⟨process, found, live⟩ := State.alive_iff.mp (fresh.2.1 _ mine)
  refine TasksFresh.replace fresh (fun entry inside => .inl (pids entry inside)) distinct
    (((realizes.keepsLive steady).trans normal).mono fun _ inside => inside.elim .inl False.elim)
    (fun entry inside same => ?_) (fun entry inside same => ?_)
  · obtain ⟨process', found', live', children⟩ :=
      ((realizes.keepsLive (steadyKept (entry_of_pid inside same))).trans normal) processId
        (fun inside => inside.elim id id) process found live
    rw [State.process_of_record found', children, State.process_of_record found]
    refine ⟨State.alive_iff.mpr ⟨process', found', live'⟩, Nat.le_refl _, fun entry' inside' same' => ?_⟩
    exfalso
    rw [pids entry' inside'] at same'
    exact append_ne_self _ _ same'.symm
  · exfalso
    rw [pids entry inside] at same
    exact append_ne_self _ _ same.symm

/-- Whether the tasks of a running configuration are fresh (`TasksFresh`). -/
private def Config.Fresh : Config α → Prop
  | .start .. => True
  | .running state tasks _ _ => TasksFresh state tasks

private theorem TasksFresh.nil (state : State) : TasksFresh state ([] : List (PID × Task α)) :=
  ⟨.nil, by simp, by simp⟩

/-- Every step keeps each process with one task. -/
private theorem Config.Fresh.step {elapsed : PID → Nat → Nat} {config next : Config α} {event : Event}
    (within : config.Within elapsed) (fresh : config.Fresh) (step : Step config event next) : next.Fresh := by
  match config with
  | .start env computation elapsed' =>
    simp only [Step, Config.successors] at step
    split at step
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · split at step
      · simp only [List.mem_singleton, Prod.mk.injEq] at step
        obtain ⟨-, rfl⟩ := step
        refine ⟨List.pairwise_singleton _ _, fun entry mem => ?_, fun entry mem entry' mem' index _ => ?_⟩
        · simp only [List.mem_singleton] at mem; subst mem
          simp [State.alive, State.initial, State.record, Kernel.lookup_eq]
        · simp only [List.mem_singleton] at mem mem'; subst mem mem'
          exact not_append_prefix _ _ ∘ (by simpa using ·)
      · simp at step
  | .running _ _ _ true => simp [Step, Config.successors] at step
  | .running state tasks finished false =>
    have within : state.Within elapsed := within
    have fresh : TasksFresh state tasks := fresh
    obtain ⟨key, forced, mem⟩ := Config.tagged_of_step step
    have found := Config.stepOf_of_tagged fresh.1 mem
    cases key with
    | own processId =>
      obtain ⟨task, transition, lookup, head, rfl⟩ := Config.stepOf_own found
      split
      · exact TasksFresh.nil _
      · exact TasksFresh.own within fresh lookup head
    | handle processId =>
      obtain ⟨task, transition, lookup, head, rfl⟩ := Config.stepOf_handle found
      split
      · exact TasksFresh.nil _
      · exact TasksFresh.handle within fresh lookup head
    | link processId target =>
      simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨phased, phase, -, rfl⟩ := found
      obtain ⟨process, record, linked⟩ := State.record_of_linkPhase phase
      have exits : ∃ exiting, process.exiting = some exiting := by
        simp only [State.exitLinks, State.process_of_record record] at linked
        split at linked
        · rename_i exiting found'; exact ⟨exiting, found'⟩
        · simp at linked
      obtain ⟨exiting, exits⟩ := exits
      exact fresh.keep ((State.linkPhase_keepsLive phase).trans
        (State.keepsLive_normalize (within.linkPhase phase).1)) fun entry mem inside =>
          inside.elim (fresh.not_exiting record exits entry mem) id
    | phase processId =>
      simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨phased, phase, -, rfl⟩ := found
      exact fresh.keep (((Realizes.phase phase).keepsLive (State.phaseEffect_steady _ _ (actor := fun _ => False))).trans
        (State.keepsLive_normalize (within.phase phase).1)) fun _ _ inside => inside.elim id id
    | unpark processId =>
      simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨-, -, -, rfl⟩ := found
      exact fresh.keep (((Realizes.unpark state processId).keepsLive
        (State.unparkEffect_steady _ _ (actor := fun _ => False))).trans
        (State.keepsLive_normalize (within.unpark processId).1)) fun _ _ inside => inside.elim id id
    | fire reference =>
      simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨timer, -, -, rfl⟩ := found
      exact fresh.keep (((Realizes.fire state timer).keepsLive
        (State.fireEffect_steady _ _ (actor := fun _ => False))).trans
        (State.keepsLive_normalize (within.fire timer).1)) fun _ _ inside => inside.elim id id
    | commit =>
      simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨update, -, -, rfl⟩ := found
      exact fresh.keep (((Realizes.commit state).keepsLive (Effect.Steady.reshare (actor := fun _ => False))).trans
        (State.keepsLive_normalize within.commit.1)) fun _ _ inside => inside.elim id id

/-! ### Steps every run can take first -/

/-- What every configuration a run reaches satisfies. -/
private def Config.Reachable (elapsed : PID → Nat → Nat) (config : Config α) : Prop :=
  config.Commuting elapsed ∧ config.Fresh

private theorem Config.Reachable.step {elapsed : PID → Nat → Nat} {config next : Config α} {event : Event}
    (reachable : config.Reachable elapsed) (step : Step config event next) : next.Reachable elapsed :=
  ⟨⟨reachable.1.1.step step, Config.Normalized.step reachable.1.1 step, reachable.1.2.2.step step⟩,
    Config.Fresh.step reachable.1.1 reachable.2 step⟩

private theorem Config.Reachable.running {config : Config α} {key : Key}
    {event : Event} {next : Config α} {forced : Bool} (mem : (key, event, next, forced) ∈ config.taggedSteps) :
    ∃ state tasks finished, config = .running state tasks finished false := by
  match config with
  | .start .. => simp [Config.taggedSteps] at mem
  | .running _ _ _ true => simp [Config.taggedSteps] at mem
  | .running state tasks finished false => exact ⟨state, tasks, finished, rfl⟩

/-- A tagged step of a configuration a run reaches is the step with its key. -/
private theorem Config.Reachable.stepOf {elapsed : PID → Nat → Nat} {config : Config α} {key : Key}
    {event : Event} {next : Config α} {forced : Bool} (reachable : config.Reachable elapsed)
    (mem : (key, event, next, forced) ∈ config.taggedSteps) : config.stepOf key = some (event, next) := by
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running mem
  exact Config.stepOf_of_tagged reachable.2.1 mem

end Lynx.Concurrent
