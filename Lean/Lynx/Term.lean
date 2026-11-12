module

public import Lynx.Term.DataTypes
public import Lynx.Term.Except
public import Lynx.Term.Result
public import Lynx.Term.Compare
public import Lynx.Term.Maps
public import Lynx.Term.Runner
public import Lynx.Term.Induction
public import Lynx.Term.Order
public import Lynx.Term.Eval
public import Lynx.Concurrent.Reduction
public import Lynx.Concurrent.Confluence
public import Lynx.Concurrent.Trace
public import Lynx.Concurrent.Termination

namespace Lynx

/-- Call a definition that is not pure with the dispatcher of a program's
function table, up to the given call depth. -/
@[expose] public def apply (definition : Dispatcher → α) (table : Term.FunTable) (depth : Nat) : α :=
  definition (Dispatcher.ofTable table depth)

@[simp] public theorem apply_eq (definition : Dispatcher → α) (table : Term.FunTable) (depth : Nat) :
    apply definition table depth = definition (Dispatcher.ofTable table depth) := rfl

/-- Run a complete process tree from a fresh runtime using the supplied
scheduler choices.
An `ok` or `error` outcome means every spawned process has finished, except
that an `Exception.exhausted` error means some process did not return, such as
a dynamic call exceeding its dispatcher's depth; it is not an Erlang exception.
`deadlock` means the modeled process tree is stuck. -/
public def concurrent (computation : Result α) (schedule : List ScheduleChoice := []) :
    Outcome α :=
  (computation.run {} schedule).1

/-- Run a computation from a fresh runtime without scheduler choices.
Computations that make no process requests never consult a schedule; use
`concurrent` to range over scheduler choices. -/
public def sequential (computation : Result α) : Outcome α :=
  concurrent computation []

end Lynx

namespace Lynx.Term

@[simp, expose] public def «true» : Term := .atom "true"

@[simp, expose] public def «false» : Term := .atom "false"

end Lynx.Term

namespace Lynx

/-- Every schedule of the runner is a run to a terminal configuration with the
same outcome. -/
public theorem concurrent_reaches (computation : Result α) (choices : List ScheduleChoice) :
    ∃ events last, Concurrent.Run (.start {} computation) events last ∧
      Concurrent.Terminal last (concurrent computation choices) :=
  Result.run_reaches computation {} choices

/-- Every run of a computation from a fresh runtime ends with the outcome,
whatever time elapses before timers are canceled. Runs end once no step
remains, and no run goes on forever (`Lynx.Concurrent.Config.terminates`).
Concurrent laws are stated this way: over every interleaving of the processes
and every step of their timers, which the runner's schedules need not reach. -/
public def always (computation : Result α) (outcome : Outcome α) : Prop :=
  ∀ elapsed events last result,
    Concurrent.Run (.start {} computation elapsed) events last →
      Concurrent.Terminal last result → result = outcome

/-- The runner follows one run, so it ends with the outcome of every run. -/
public theorem concurrent_of_always {computation : Result α} {outcome : Outcome α}
    (always : always computation outcome) (choices : List ScheduleChoice) :
    concurrent computation choices = outcome := by
  obtain ⟨_, _, run, final⟩ := concurrent_reaches computation choices
  exact always _ _ _ _ run final

/-- Whether an outcome is `ok true`, the outcome laws expect. -/
@[expose] public def Outcome.isTrue : Outcome Term → Bool
  | .ok (.atom "true") => true
  | _ => false

public theorem Outcome.eq_of_isTrue {outcome : Outcome Term} (accepted : outcome.isTrue = true) :
    outcome = .ok Term.true := by
  unfold Outcome.isTrue at accepted
  split at accepted
  · rfl
  · contradiction

/-- An outcome of every terminal configuration satisfying an invariant is the
outcome of every run. -/
public theorem always_of_invariant (computation : Result α)
    (invariant : Concurrent.Config α → Prop) {outcome : Outcome α}
    (initial : ∀ elapsed, invariant (.start {} computation elapsed))
    (preserved : ∀ first event next, invariant first → Concurrent.Step first event next →
      invariant next)
    (terminal : ∀ config result, invariant config → Concurrent.Terminal config result →
      result = outcome) :
    always computation outcome :=
  fun elapsed _ last result run final =>
    terminal last result (run.invariant preserved (initial elapsed)) final

/-- Exploring every run of a closed program establishes its outcome. Prove
`checked` by evaluation for an unknown elapsed time, with a depth bounding the
steps of each run, and an `accept` that only accepts the outcome, such as
`Lynx.Outcome.isTrue`. -/
public theorem always_of_check (computation : Result α) (accept : Outcome α → Bool)
    (depth : Nat)
    (checked : ∀ elapsed, Concurrent.check accept depth (.start {} computation elapsed) = true)
    {outcome : Outcome α} (accepted : ∀ result, accept result = true → result = outcome) :
    always computation outcome :=
  fun elapsed _ _ result run final =>
    accepted result (Concurrent.check_sound (checked elapsed) run final)

/-- Without races, one run to a terminal configuration determines the outcome of
every run: steps of different processes commute, so all runs end alike. -/
public theorem always_of_raceFree (computation : Result α) {outcome : Outcome α}
    (raceFree : ∀ elapsed, (Concurrent.Config.start {} computation elapsed).RaceFree)
    (run : ∀ elapsed, ∃ events last, Concurrent.Run (.start {} computation elapsed) events last ∧
      Concurrent.Terminal last outcome) : always computation outcome :=
  fun elapsed _ _ _ run' terminal' =>
    let ⟨_, _, run, terminal⟩ := run elapsed
    (raceFree elapsed).outcome_eq run terminal run' terminal'

/-- Without races, taking the first available steps until none remain evaluates
the outcome of every run. -/
public theorem always_advance (computation : Result α) (steps : Nat) {outcome : Outcome α}
    (raceFree : ∀ elapsed, (Concurrent.Config.start {} computation elapsed).RaceFree)
    (advanced : ∀ elapsed,
      ((Concurrent.Config.start {} computation elapsed).advance steps).successors.isEmpty ∧
        ((Concurrent.Config.start {} computation elapsed).advance steps).outcome = outcome) :
    always computation outcome := by
  refine always_of_raceFree computation raceFree fun elapsed => ?_
  obtain ⟨stuck, reached⟩ := advanced elapsed
  obtain ⟨_, run⟩ := Concurrent.Config.run_advance steps (.start {} computation elapsed)
  exact ⟨_, _, run, reached ▸
    Concurrent.Config.terminal_of_successors_eq_nil (List.isEmpty_iff.mp stuck)⟩

@[simp] public theorem concurrent_ok (value : α) (choices : List ScheduleChoice) :
    concurrent (.ok value) choices = .ok value := by
  simp [concurrent]

@[simp] public theorem concurrent_error (exception : Exception) (choices : List ScheduleChoice) :
    concurrent (.error exception : Result α) choices = .error exception := by
  simp [concurrent]

/-- A pure computation runs to `ok` exactly when it returns that value. -/
@[simp] public theorem IsPure.concurrent_eq_ok_iff {computation : Result α}
    (pure : computation.IsPure) {choices : List ScheduleChoice} {value : α} :
    concurrent computation choices = .ok value ↔ computation = .ok value := by
  cases computation <;> simp_all [Result.IsPure]

@[simp] public theorem sequential_ok (value : α) : sequential (.ok value) = .ok value :=
  concurrent_ok value []

@[simp] public theorem sequential_error (exception : Exception) :
    sequential (.error exception : Result α) = .error exception :=
  concurrent_error exception []

/-- A pure computation runs to `ok` exactly when it returns that value. -/
@[simp] public theorem IsPure.sequential_eq_ok_iff {computation : Result α}
    (pure : computation.IsPure) {value : α} :
    sequential computation = .ok value ↔ computation = .ok value :=
  IsPure.concurrent_eq_ok_iff pure

end Lynx
