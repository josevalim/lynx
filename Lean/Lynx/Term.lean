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
public import Lynx.Concurrent.Trace
public import Lynx.Concurrent.Termination

namespace Lynx

/-- Call a definition that is not pure with the dispatcher of a program's
function table, up to the given call depth. -/
@[expose] public def apply (definition : Dispatcher → α) (table : Term.FunTable) (depth : Nat) : α :=
  definition (Dispatcher.ofTable table depth)

@[simp] public theorem apply_eq (definition : Dispatcher → α) (table : Term.FunTable) (depth : Nat) :
    apply definition table depth = definition (Dispatcher.ofTable table depth) := rfl

/-- Run a computation from a fresh runtime. Computations that make no process
requests have a single run; use `concurrent` to state what every run of the
others ends with. An `ok` or `error` outcome means every spawned process has
finished, except that an `Exception.exhausted` error means some process did not
return, such as a dynamic call exceeding its dispatcher's depth; it is not an
Erlang exception. -/
public def sequential (computation : Result α) : Outcome α :=
  (computation.run {} []).1

end Lynx

namespace Lynx.Term

@[simp, expose] public def «true» : Term := .atom "true"

@[simp, expose] public def «false» : Term := .atom "false"

end Lynx.Term

namespace Lynx

/-- Every run of a computation from a fresh runtime ends with the outcome,
whatever time elapses before timers are canceled. Runs end once no step
remains, and no run goes on forever (`Lynx.Concurrent.Config.terminates`).
Concurrent laws are stated this way: over every interleaving of the processes
and every step of their timers. -/
public def concurrent (computation : Result α) (outcome : Outcome α) : Prop :=
  ∀ elapsed events last result,
    Concurrent.Run (.start {} computation elapsed) events last →
      Concurrent.Terminal last result → result = outcome

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
public theorem concurrent_of_invariant (computation : Result α)
    (invariant : Concurrent.Config α → Prop) {outcome : Outcome α}
    (initial : ∀ elapsed, invariant (.start {} computation elapsed))
    (preserved : ∀ first event next, invariant first → Concurrent.Step first event next →
      invariant next)
    (terminal : ∀ config result, invariant config → Concurrent.Terminal config result →
      result = outcome) :
    concurrent computation outcome :=
  fun elapsed _ last result run final =>
    terminal last result (run.invariant preserved (initial elapsed)) final

/-- Exploring every run of a closed program establishes its outcome. Prove
`checked` by evaluation for an unknown elapsed time, with a depth bounding the
steps of each run, and an `accept` that only accepts the outcome, such as
`Lynx.Outcome.isTrue`. -/
public theorem concurrent_of_check (computation : Result α) (accept : Outcome α → Bool)
    (depth : Nat)
    (checked : ∀ elapsed, Concurrent.check accept depth (.start {} computation elapsed) = true)
    {outcome : Outcome α} (accepted : ∀ result, accept result = true → result = outcome) :
    concurrent computation outcome :=
  fun elapsed _ _ result run final =>
    accepted result (Concurrent.check_sound (checked elapsed) run final)

@[simp] public theorem sequential_ok (value : α) : sequential (.ok value) = .ok value := by
  simp [sequential]

@[simp] public theorem sequential_error (exception : Exception) :
    sequential (.error exception : Result α) = .error exception := by
  simp [sequential]

/-- A pure computation runs to `ok` exactly when it returns that value. -/
@[simp] public theorem IsPure.sequential_eq_ok_iff {computation : Result α}
    (pure : computation.IsPure) {value : α} :
    sequential computation = .ok value ↔ computation = .ok value := by
  cases computation <;> simp_all [Result.IsPure, sequential]

end Lynx
