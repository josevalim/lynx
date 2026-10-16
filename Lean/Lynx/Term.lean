module

public import Lynx.Term.DataTypes
public import Lynx.Term.Compare
public import Lynx.Term.Maps
public import Lynx.Term.Runner
public import Lynx.Term.Induction
public import Lynx.Term.Order

namespace Lynx

/-- Run a complete process tree from a fresh runtime using the supplied
scheduler choices.
An `ok` or `error` outcome means every spawned process has finished.
`deadlock` means the modeled process tree is stuck. `exhausted` means a dynamic
call exceeded `callDepth`; it is not an Erlang exception. The immutable table
is separate from process state. -/
public def run (computation : Result α) (schedule : List ScheduleChoice := [])
    (table : Term.FunTable := #[]) (callDepth : Nat := 100) : Outcome α :=
  if table.isEmpty then (computation.run { schedule }).1
  else (computation.runWith table callDepth { schedule }).1

end Lynx

namespace Lynx.Term

@[simp, expose] public def «true» : Term := .atom "true"

@[simp, expose] public def «false» : Term := .atom "false"

end Lynx.Term

namespace Lynx

/-- Pure computations ignore the scheduler and the program table. -/
public theorem run_of_isPure (computation : Result α) (pure : computation.IsPure)
    (schedule : List ScheduleChoice) (table : Term.FunTable) (callDepth : Nat) :
    run computation schedule table callDepth = (computation { schedule }).1 := by
  unfold run
  split
  · rfl
  · rw [Result.runWith_apply, Result.resolve_of_isPure _ _ _ pure]

@[simp] public theorem run_ok (value : α) (schedule : List ScheduleChoice)
    (table : Term.FunTable) (callDepth : Nat) :
    run (.ok value) schedule table callDepth = .ok value := by
  simp [run_of_isPure]

@[simp] public theorem run_error (exception : Exception) (schedule : List ScheduleChoice)
    (table : Term.FunTable) (callDepth : Nat) :
    run (.error exception : Result α) schedule table callDepth = .error exception := by
  simp [run_of_isPure]

/-- A pure computation runs to `ok` exactly when it returns that value. -/
@[simp] public theorem IsPure.run_eq_ok_iff {computation : Result α} (pure : computation.IsPure)
    {schedule : List ScheduleChoice} {table : Term.FunTable} {callDepth : Nat} {value : α} :
    run computation schedule table callDepth = .ok value ↔ computation = .ok value := by
  rw [run_of_isPure _ pure]
  cases computation <;> simp_all [Result.IsPure]

/-- A law holds under every schedule once its expectation returns `true`. -/
public theorem law_of_pure {ensures : Result} (proof : ensures = .ok Term.true)
    {schedule : List ScheduleChoice} {table : Term.FunTable} {callDepth : Nat} :
    run ensures schedule table callDepth = .ok Term.true := by
  simp [proof]

/-- A law with a pure precondition holds under every schedule when the precondition,
holding under some schedule, implies the expectation. -/
public theorem law_of_pure_requires {requires ensures : Result}
    (requiresPure : requires.IsPure)
    (proof : requires = .ok Term.true → ensures = .ok Term.true)
    {table : Term.FunTable} {callDepth : Nat}
    (holds : ∃ schedule, run requires schedule table callDepth = .ok Term.true)
    {schedule : List ScheduleChoice} :
    run ensures schedule table callDepth = .ok Term.true :=
  let ⟨_, holds⟩ := holds
  law_of_pure (proof ((IsPure.run_eq_ok_iff requiresPure).mp holds))

end Lynx
