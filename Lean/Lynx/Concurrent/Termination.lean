module

public import Lynx.Concurrent

/-! Every run ends. Each step of a process replaces its computation by what
follows it, possibly with a spawned child, or ends the process, as an exit
signal arriving can. Every other step, a signal arriving or a timer firing,
leaves the processes as they are and lowers the weight of the signals in
transit and the timers. So statements about the runs that can no longer step
cover every run. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- The steps a signal in transit has left: links and monitors reaching a
process that is not live are answered with one more signal. -/
def Envelope.weight (envelope : Envelope) : Nat :=
  match envelope.signal with
  | .link | .monitor _ => 2
  | _ => 1

/-- The steps the signals in transit and the timers have left: a timer fires
and its message then arrives. -/
def State.weight (state : State) : Nat :=
  (state.inTransit.map Envelope.weight).sum + 2 * state.timers.length

/-! Taking a signal changes the records of processes only. -/

@[simp] theorem State.inTransit_update {state : State} {processId : PID}
    {process : Option ProcessState} : (state.update processId process).inTransit = state.inTransit := rfl

@[simp] theorem State.timers_update {state : State} {processId : PID}
    {process : Option ProcessState} : (state.update processId process).timers = state.timers := rfl

@[simp] theorem State.inTransit_modify {state : State} {processId : PID}
    {change : ProcessState → ProcessState} :
    (state.modify processId change).inTransit = state.inTransit := by
  unfold State.modify; split <;> rfl

@[simp] theorem State.timers_modify {state : State} {processId : PID}
    {change : ProcessState → ProcessState} : (state.modify processId change).timers = state.timers := by
  unfold State.modify; split <;> rfl

@[simp] theorem State.inTransit_append {state : State} {processId : PID} {message : Term} :
    (state.append processId message).inTransit = state.inTransit := by
  simp [State.append]

@[simp] theorem State.timers_append {state : State} {processId : PID} {message : Term} :
    (state.append processId message).timers = state.timers := by
  simp [State.append]

theorem State.inTransit_exitSignal {state : State} {target source : PID} {reason : Term}
    {linked : Bool} : (state.exitSignal target source reason linked).1.inTransit = state.inTransit := by
  unfold State.exitSignal
  cases linked <;> simp only [Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true] <;>
    repeat' (first | split | simp)

theorem State.timers_exitSignal {state : State} {target source : PID} {reason : Term}
    {linked : Bool} : (state.exitSignal target source reason linked).1.timers = state.timers := by
  unfold State.exitSignal
  cases linked <;> simp only [Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true] <;>
    repeat' (first | split | simp)

theorem State.inTransit_receive {state : State} {envelope : Envelope} :
    (state.receive envelope).1.inTransit = state.inTransit := by
  unfold State.receive
  split
  all_goals first | exact State.inTransit_exitSignal | (repeat' (first | split | simp))

theorem State.timers_receive {state : State} {envelope : Envelope} :
    (state.receive envelope).1.timers = state.timers := by
  unfold State.receive
  split
  all_goals first | exact State.timers_exitSignal | (repeat' (first | split | simp))

/-- An arriving signal is one of those in transit, and the others stay. -/
theorem mem_deliverableFrom {before : List Envelope} {seen : List (PID × PID)}
    {inTransit : List Envelope} {envelope : Envelope} {rest : List Envelope}
    (mem : (envelope, rest) ∈ deliverableFrom before seen inTransit) :
    ∃ pre post, inTransit = pre ++ envelope :: post ∧ rest = before ++ pre ++ post := by
  induction inTransit generalizing before seen with
  | nil => simp [deliverableFrom] at mem
  | cons head tail ih =>
    simp only [deliverableFrom, Kernel.append_eq, Kernel.contains_eq] at mem
    split at mem
    · obtain ⟨pre, post, rfl, rfl⟩ := ih mem
      exact ⟨head :: pre, post, rfl, by simp⟩
    · simp only [List.mem_cons, Prod.mk.injEq] at mem
      rcases mem with ⟨rfl, rfl⟩ | mem
      · exact ⟨[], tail, rfl, by simp⟩
      · obtain ⟨pre, post, rfl, rfl⟩ := ih mem
        exact ⟨head :: pre, post, rfl, by simp⟩

theorem mem_deliverable {inTransit : List Envelope} {envelope : Envelope} {rest : List Envelope}
    (mem : (envelope, rest) ∈ deliverable inTransit) :
    ∃ pre post, inTransit = pre ++ envelope :: post ∧ rest = pre ++ post := by
  simpa using mem_deliverableFrom mem

theorem weight_enqueue (envelope : Envelope) (inTransit : List Envelope) :
    ((enqueue envelope inTransit).map Envelope.weight).sum =
      envelope.weight + (inTransit.map Envelope.weight).sum := by
  induction inTransit with
  | nil => simp [enqueue]
  | cons head rest ih =>
    simp only [enqueue]
    split <;> simp [ih] <;> omega

/-- Taking a signal lowers the weight. -/
theorem State.weight_receive {state : State} {envelope : Envelope} {rest : List Envelope}
    (mem : (envelope, rest) ∈ deliverable state.inTransit) :
    ({ state with inTransit := rest }.receive envelope).1.weight < state.weight := by
  obtain ⟨pre, post, split, rfl⟩ := mem_deliverable mem
  simp only [State.weight, State.inTransit_receive, State.timers_receive, split, List.map_append,
    List.map_cons, List.sum_append, List.sum_cons]
  have : 0 < envelope.weight := by unfold Envelope.weight; split <;> simp
  omega

/-- A signal reaching a process that is not live lowers the weight. -/
theorem State.weight_bounce {state : State} {envelope : Envelope} {rest : List Envelope}
    (mem : (envelope, rest) ∈ deliverable state.inTransit) :
    ({ state with inTransit := rest }.bounce envelope).weight < state.weight := by
  obtain ⟨pre, post, split, rfl⟩ := mem_deliverable mem
  unfold State.bounce
  split <;> rename_i signal <;>
    simp only [State.weight, State.emit, weight_enqueue, split, List.map_append, List.map_cons,
      List.sum_append, List.sum_cons, Envelope.weight, signal] <;> omega

theorem mem_firstOfEach {seen : List (List Nat)} {timers : List Timer} {timer : Timer}
    (mem : timer ∈ firstOfEach seen timers) : timer ∈ timers := by
  induction timers generalizing seen with
  | nil => simp [firstOfEach] at mem
  | cons head rest ih =>
    simp only [firstOfEach, Kernel.contains_eq] at mem
    split at mem
    · exact List.mem_cons_of_mem _ (ih mem)
    · simp only [List.mem_cons] at mem
      rcases mem with rfl | mem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih mem)

/-- A timer firing lowers the weight. -/
theorem State.weight_fire {state : State} {timer : Timer} (mem : timer ∈ state.timers) :
    (state.fire timer).weight < state.weight := by
  have shorter : (state.timers.filter (·.reference != timer.reference)).length <
      state.timers.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨timer, mem, by simp⟩
  simp only [State.weight, State.fire, State.emit, weight_enqueue, Envelope.weight,
      Kernel.filter_eq]
  omega

/-- A computation and what follows it: the continuation of its request, or a
child it spawns. -/
private inductive Follows : (Σ β, Result β) → (Σ β, Result β) → Prop where
  | get : Follows ⟨β, next env⟩ ⟨β, .get next⟩
  | set : Follows ⟨β, next⟩ ⟨β, .set env next⟩
  | spawned : Follows ⟨β, next child⟩ ⟨β, Result.schedule options computation next⟩
  | child : Follows ⟨Term, computation⟩ ⟨β, Result.schedule options computation next⟩
  | send : Follows ⟨β, next⟩ ⟨β, .send destination message next⟩
  | receive : Follows ⟨β, next value⟩ ⟨β, .receive timeout select next⟩
  | request : Follows ⟨β, next reply⟩ ⟨β, .request query next⟩

private theorem follows_acc {β : Type} (computation : Result β) :
    Acc Follows ⟨β, computation⟩ := by
  induction computation with
  | ok | error => exact ⟨_, fun _ follows => by cases follows⟩
  | get next ih => exact ⟨_, fun _ follows => by cases follows; exact ih _⟩
  | set env next ih => exact ⟨_, fun _ follows => by cases follows; exact ih⟩
  | schedule options child next childIh nextIh =>
    exact ⟨_, fun _ follows => by cases follows <;> first | exact nextIh _ | exact childIh⟩
  | send destination message next ih => exact ⟨_, fun _ follows => by cases follows; exact ih⟩
  | receive timeout select next ih => exact ⟨_, fun _ follows => by cases follows; exact ih _⟩
  | request query next ih => exact ⟨_, fun _ follows => by cases follows; exact ih _⟩

/-- One item of a list replaced by any number of items below it. -/
private def Replaces (below : γ → γ → Prop) (next current : List γ) : Prop :=
  ∃ before item after replacement, current = before ++ item :: after ∧
    next = before ++ replacement ++ after ∧ ∀ new ∈ replacement, below new item

private theorem replaces_cons {below : γ → γ → Prop} {next rest : List γ} {head : γ}
    (replaces : Replaces below next (head :: rest)) :
    (∃ replacement, next = replacement ++ rest ∧ ∀ new ∈ replacement, below new head) ∨
      ∃ next', next = head :: next' ∧ Replaces below next' rest := by
  obtain ⟨before, item, after, replacement, current, rfl, smaller⟩ := replaces
  cases before with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at current
    obtain ⟨rfl, rfl⟩ := current
    exact .inl ⟨replacement, by simp, smaller⟩
  | cons first before =>
    simp only [List.cons_append, List.cons.injEq] at current
    obtain ⟨rfl, rfl⟩ := current
    exact .inr ⟨before ++ replacement ++ after, by simp, before, item, after, replacement, rfl, rfl,
      smaller⟩

/-- Replacing items by items below them, where nothing descends forever, ends. -/
private theorem replaces_acc {below : γ → γ → Prop} :
    ∀ items : List γ, (∀ item ∈ items, Acc below item) → Acc (Replaces below) items := by
  intro items
  induction items with
  | nil =>
    intro _
    refine ⟨_, fun next replaces => ?_⟩
    obtain ⟨before, item, after, -, current, -⟩ := replaces
    simp at current
  | cons head rest ih =>
    intro accessible
    have restAcc := ih fun item mem => accessible item (by simp [mem])
    -- Prepending an accessible item keeps a list accessible.
    suffices prepend : ∀ head, Acc below head → ∀ rest, Acc (Replaces below) rest →
        Acc (Replaces below) (head :: rest) from
      prepend head (accessible head (by simp)) rest restAcc
    intro head headAcc
    induction headAcc with
    | intro head _ headIh =>
      intro rest restAcc
      induction restAcc with
      | intro rest restSmaller restIh =>
        refine ⟨_, fun next replaces => ?_⟩
        rcases replaces_cons replaces with ⟨replacement, rfl, smaller⟩ | ⟨next', rfl, replaces'⟩
        · have : ∀ replacement : List γ, (∀ new ∈ replacement, below new head) →
              Acc (Replaces below) (replacement ++ rest) := by
            intro replacement smaller
            induction replacement with
            | nil => exact ⟨_, restSmaller⟩
            | cons new others ih =>
              exact headIh new (smaller new (by simp)) _
                (ih fun item mem => smaller item (by simp [mem]))
          exact this replacement smaller
        · exact restIh next' replaces'

/-- A process's computation. -/
private def entry (item : PID × Task α) : Σ β, Result β := ⟨item.2.β, item.2.computation⟩

/-- The computations of the processes, and the weight of the signals in
transit and the timers. -/
private def measure (state : State) (tasks : List (PID × Task α)) :
    List (Σ β, Result β) × Nat :=
  (tasks.map entry, state.weight)

/-- What a step of a process itself leaves follows its computation. -/
private theorem own_follows {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.own state processId) :
    ∀ item ∈ transition.tasks, Follows (entry item) (entry (processId, task)) := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | ok | error =>
    intro item mem
    simp only [Task.own] at possible
    (try split at possible) <;> simp_all [Task.ended]
  | get | set | send =>
    simp only [Task.own, List.mem_singleton] at possible; subst possible
    simp only [List.mem_singleton, forall_eq]; constructor
  | schedule options child next =>
    simp only [Task.own, List.mem_singleton] at possible; subst possible
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨.spawned, .child⟩
  | receive timeout select next =>
    simp only [Task.own] at possible
    split at possible
    · simp only [List.mem_singleton] at possible; subst possible
      simp only [List.mem_singleton, forall_eq]; exact .receive
    · split at possible <;> simp only [List.mem_singleton, List.not_mem_nil] at possible <;>
        subst possible <;> simp only [List.mem_singleton, forall_eq] <;> exact .receive
  | request query next =>
    simp only [Task.own] at possible
    split at possible
    · simp at possible
    · simp only [List.mem_singleton] at possible; subst possible
      simp only [List.mem_singleton, forall_eq]; exact .request
    · simp only [List.mem_singleton] at possible; subst possible; simp [Task.ended]

/-- A signal a process takes leaves it as it is, or ends it. -/
private theorem deliveries_tasks {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.deliveries state processId) :
    ∃ envelope rest, (envelope, rest) ∈ deliverable state.inTransit ∧
      ((transition.tasks = [(processId, task)] ∧
        transition.state = ({ state with inTransit := rest }.receive envelope).1) ∨
       transition.tasks = []) := by
  simp only [Task.deliveries, Task.delivery, List.mem_filterMap] at possible
  obtain ⟨⟨envelope, rest⟩, mem, found⟩ := possible
  refine ⟨envelope, rest, mem, ?_⟩
  split at found
  · simp at found
  · split at found <;> simp only [Option.some.injEq] at found <;> subst found
    · rename_i exits
      exact .inl ⟨rfl, rfl⟩
    · exact .inr (by simp [Task.ended])

/-- Each step of a running configuration lowers its measure. -/
private theorem step_measure {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {event : Event}
    {next : Config α} (step : Step (.running state tasks finished exhausted) event next) :
    ∃ state' tasks' finished' exhausted', next = .running state' tasks' finished' exhausted' ∧
      Prod.Lex (Replaces Follows) (· < ·) (measure state' tasks') (measure state tasks) := by
  simp only [Step, Config.successors, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filterMap, Prod.exists] at step
  rcases step with (⟨before, processId, task, after, split, transition, possible, same⟩ |
    ⟨envelope, rest, mem, bounced⟩) | ⟨timer, mem, same⟩
  · simp only [Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    have tasks_eq := eq_of_mem_splits split
    simp only [Task.transitions, List.mem_append] at possible
    rcases possible with possible | possible
    · refine ⟨_, _, _, _, rfl, .left _ _ ⟨before.map entry, entry (processId, task), after.map entry,
        transition.tasks.map entry, ?_, ?_, ?_⟩⟩
      · simp [tasks_eq]
      · simp
      · intro new mem
        simp only [List.mem_map] at mem
        obtain ⟨item, mem, rfl⟩ := mem
        exact own_follows possible item mem
    · obtain ⟨envelope, rest, mem, (⟨tasks', state'⟩ | tasks')⟩ := deliveries_tasks possible
      · refine ⟨_, _, _, _, rfl, ?_⟩
        have first : (Kernel.append (Kernel.append before transition.tasks) after).map entry =
            tasks.map entry := by
          simp [tasks_eq, tasks']
        simp only [measure, first]
        exact .right _ (state' ▸ State.weight_receive mem)
      · refine ⟨_, _, _, _, rfl, .left _ _ ⟨before.map entry, entry (processId, task),
          after.map entry, [], ?_, ?_, by simp⟩⟩
        · simp [tasks_eq]
        · simp [tasks']
  · split at bounced
    · simp at bounced
    · simp only [Option.some.injEq, Prod.mk.injEq] at bounced
      obtain ⟨-, rfl⟩ := bounced
      exact ⟨_, _, _, _, rfl, .right _ (State.weight_bounce mem)⟩
  · simp only [Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    exact ⟨_, _, _, _, rfl, .right _ (State.weight_fire (mem_firstOfEach mem))⟩

private theorem running_acc :
    ∀ (state : State) (tasks : List (PID × Task α))
      (finished : Option (Except Exception α)) (exhausted : Bool),
      Acc (fun next first => ∃ event, Step first event next)
        (Config.running state tasks finished exhausted) := by
  intro state tasks finished exhausted
  have accessible : Acc (Prod.Lex (Replaces Follows) (· < ·)) (measure state tasks) :=
    Prod.lexAccessible (replaces_acc _ fun _ _ => follows_acc _) (fun _ => Nat.lt_wfRel.wf.apply _) _
  generalize equal : measure state tasks = current at accessible
  induction accessible generalizing state tasks finished exhausted with
  | intro current _ ih =>
    refine ⟨_, fun next ⟨event, step⟩ => ?_⟩
    obtain ⟨state', tasks', finished', exhausted', rfl, lower⟩ := step_measure step
    exact ih _ (equal ▸ lower) _ _ _ _ rfl

/-- No run goes on forever: steps are well-founded. -/
theorem Config.terminates :
    WellFounded (fun next first : Config α => ∃ event, Step first event next) := by
  refine ⟨fun config => ?_⟩
  cases config with
  | running state tasks finished exhausted => exact running_acc state tasks finished exhausted
  | start env computation =>
    have accessible := follows_acc computation
    generalize equal : (⟨α, computation⟩ : Σ β, Result β) = current at accessible
    induction accessible generalizing env computation with
    | intro current _ ih =>
      refine ⟨_, fun next ⟨event, step⟩ => ?_⟩
      simp only [Step, Config.successors] at step
      cases computation with
      | get next =>
        simp only [List.mem_singleton, Prod.mk.injEq] at step
        obtain ⟨-, rfl⟩ := step
        exact ih _ (equal ▸ .get) _ _ rfl
      | set env' next =>
        simp only [List.mem_singleton, Prod.mk.injEq] at step
        obtain ⟨-, rfl⟩ := step
        exact ih _ (equal ▸ .set) _ _ rfl
      | _ =>
        simp [isRequest] at step <;> obtain ⟨-, rfl⟩ := step <;> exact running_acc _ _ _ _

end Lynx.Concurrent
