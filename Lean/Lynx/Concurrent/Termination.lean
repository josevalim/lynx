module

public import Lynx.Concurrent

/-! Every run ends: each step of a process replaces its computation by what
follows it, possibly with a spawned child, and each step of a timer leaves its
timers fewer steps to take. So statements about the runs that can no longer
step cover every run. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- The steps the timers have left: an armed timer expires and then arrives. -/
def State.timerWeight (state : State) : Nat :=
  (state.timers.map fun timer => if timer.expired then 1 else 2).sum

private theorem sum_filter_lt {items : List γ} {weight : γ → Nat} {keep : γ → Bool} {item : γ}
    (mem : item ∈ items) (dropped : keep item = false) (positive : 0 < weight item) :
    ((items.filter keep).map weight).sum < (items.map weight).sum := by
  induction items with
  | nil => simp at mem
  | cons head rest ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · have : ((rest.filter keep).map weight).sum ≤ (rest.map weight).sum := by
        clear ih; induction rest with
        | nil => simp
        | cons next tail ih => simp only [List.filter_cons]; split <;> simp <;> omega
      simp [dropped]; omega
    · have := ih mem
      simp only [List.filter_cons]; split <;> simp <;> omega

private theorem sum_map_lt {items : List γ} {weight : γ → Nat} {change : γ → γ} {item : γ}
    (mem : item ∈ items) (smaller : weight (change item) < weight item)
    (le : ∀ other, weight (change other) ≤ weight other) :
    (items.map (weight ∘ change)).sum < (items.map weight).sum := by
  induction items with
  | nil => simp at mem
  | cons head rest ih =>
    simp only [List.mem_cons] at mem
    have bound : (rest.map (weight ∘ change)).sum ≤ (rest.map weight).sum := by
      clear ih mem
      induction rest with
      | nil => simp
      | cons next tail ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply]
        have := le next
        omega
    simp only [List.map_cons, List.sum_cons, Function.comp_apply]
    rcases mem with rfl | mem
    · omega
    · have := ih mem
      have := le head
      omega

/-- Each timer step leaves fewer steps to the timers. -/
theorem State.timerWeight_lt {state next : State} {event : Event}
    (possible : (event, next) ∈ state.timerSteps) : next.timerWeight < state.timerWeight := by
  simp only [State.timerSteps, List.mem_map] at possible
  obtain ⟨timer, mem, step⟩ := possible
  split at step <;> simp only [Prod.mk.injEq] at step <;> obtain ⟨-, rfl⟩ := step
  · exact sum_filter_lt mem (by simp) (by split <;> simp)
  · rename_i armed
    simp only [State.timerWeight, List.map_map]
    refine sum_map_lt mem (by simp [armed]) fun other => ?_
    by_cases same : (other.reference == timer.reference) = true <;>
      cases expired : other.expired <;> simp [same, expired]

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

/-- The computations of the processes, and the steps left to the timers. -/
private def measure (state : State) (tasks : List (PID × Task α)) :
    List (Σ β, Result β) × Nat :=
  (tasks.map fun entry => ⟨entry.2.β, entry.2.computation⟩, state.timerWeight)

/-- What a step of a process leaves follows its computation. -/
private theorem transition_follows {state : State} {processId : PID} {task : Task α}
    {transition : Transition α} (possible : transition ∈ task.transitions state processId) :
    ∀ entry ∈ transition.tasks,
      Follows ⟨entry.2.β, entry.2.computation⟩ ⟨task.β, task.computation⟩ := by
  obtain ⟨computation, finish⟩ := task
  simp only [Task.transitions] at possible
  split at possible
  · simp only [List.mem_singleton] at possible; subst possible; simp
  · -- Only steps that continue the process leave tasks.
    have single : ∀ {transitions : List (Transition α)} {entry : Transition α → Prop},
        transition ∈ transitions → (∀ other ∈ transitions, entry other) → entry transition :=
      fun mem all => all _ mem
    refine single (entry := fun transition : Transition α => ∀ entry ∈ transition.tasks,
      Follows ⟨entry.2.β, entry.2.computation⟩ ⟨_, computation⟩) possible ?_
    cases computation with
    | ok => simp
    | error exception => cases exception <;> simp
    | get next => simp only [List.mem_singleton, forall_eq]; first | exact Follows.get | exact fun _ => Follows.get
    | set env next => simp only [List.mem_singleton, forall_eq]; first | exact Follows.set | exact fun _ => Follows.set
    | schedule options child next =>
      simp only [forall_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
      exact ⟨.spawned, .child⟩
    | send destination message next =>
      simp only [List.mem_singleton, forall_eq]; first | exact Follows.send | exact fun _ => Follows.send
    | receive timeout select next =>
      dsimp only
      split
      · simp only [List.mem_singleton, forall_eq]; first | exact Follows.receive | exact fun _ => Follows.receive
      · split <;> simp only [List.mem_singleton, forall_eq, List.not_mem_nil] <;>
          first | exact Follows.receive | exact fun _ => Follows.receive | simp
    | request query next =>
      simp only [List.mem_map]
      rintro _ ⟨reply, -, rfl⟩ entry mem
      simp only [List.mem_singleton] at mem
      subst mem
      exact .request

/-- Each step of a running configuration lowers its measure. -/
private theorem step_measure {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} {event : Event}
    {next : Config α} (step : Step (.running state tasks finished exhausted) event next) :
    ∃ state' tasks' finished' exhausted', next = .running state' tasks' finished' exhausted' ∧
      Prod.Lex (Replaces Follows) (· < ·) (measure state' tasks') (measure state tasks) := by
  cases step with
  | run split possible =>
    rename_i before processId task after transition
    let entry := fun entry : PID × Task α => (⟨entry.2.β, entry.2.computation⟩ : Σ β, Result β)
    refine ⟨_, _, _, _, rfl, .left _ _ ⟨before.map entry, entry (processId, task), after.map entry,
      transition.tasks.map entry, ?_, ?_, ?_⟩⟩
    · rw [split, List.map_append, List.map_cons]
    · simp only [List.map_append]; rfl
    · intro new mem
      simp only [List.mem_map] at mem
      obtain ⟨entry, mem, rfl⟩ := mem
      exact transition_follows possible entry mem
  | timer possible =>
    exact ⟨_, _, _, _, rfl, .right _ (State.timerWeight_lt possible)⟩

private theorem running_acc :
    ∀ (state : State) (tasks : List (PID × Task α))
      (finished : Option (Except Exception α × Environment)) (exhausted : Bool),
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
      cases step with
      | get => exact ih _ (equal ▸ .get) _ _ rfl
      | set => exact ih _ (equal ▸ .set) _ _ rfl
      | enter => exact running_acc _ _ _ _

end Lynx.Concurrent
