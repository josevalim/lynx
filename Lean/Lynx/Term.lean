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
public def schedule (computation : Result α) (schedule : List ScheduleChoice := [])
    (table : Term.FunTable := #[]) (callDepth : Nat := 100) : Outcome α :=
  if table.isEmpty then (computation.run { schedule }).1
  else (computation.runWith table callDepth { schedule }).1

/-- Run a computation from a fresh runtime without scheduler choices, resolving
its dynamic calls against the table. Computations that make no process requests
never consult a schedule; use `schedule` to range over scheduler choices. -/
public def run (computation : Result α) (table : Term.FunTable := #[])
    (callDepth : Nat := 100) : Outcome α :=
  schedule computation [] table callDepth

end Lynx

namespace Lynx.Term

@[simp, expose] public def «true» : Term := .atom "true"

@[simp, expose] public def «false» : Term := .atom "false"

end Lynx.Term

namespace Lynx

/-- Pure computations ignore the scheduler and the program table. -/
public theorem schedule_of_isPure (computation : Result α) (pure : computation.IsPure)
    (choices : List ScheduleChoice) (table : Term.FunTable) (callDepth : Nat) :
    schedule computation choices table callDepth = (computation { schedule := choices }).1 := by
  unfold schedule
  split
  · rfl
  · rw [Result.runWith_apply, Result.resolve_of_isPure _ _ _ pure]

@[simp] public theorem schedule_ok (value : α) (choices : List ScheduleChoice)
    (table : Term.FunTable) (callDepth : Nat) :
    schedule (.ok value) choices table callDepth = .ok value := by
  simp [schedule_of_isPure]

@[simp] public theorem schedule_error (exception : Exception) (choices : List ScheduleChoice)
    (table : Term.FunTable) (callDepth : Nat) :
    schedule (.error exception : Result α) choices table callDepth = .error exception := by
  simp [schedule_of_isPure]

/-- A computation whose dynamic calls resolve to a value against a program table
runs to that value under every schedule. -/
public theorem schedule_of_resolve {computation : Result α} {table : Term.FunTable}
    {callDepth : Nat} {value : α} (nonempty : table.isEmpty = false)
    (resolved : Result.resolve table callDepth computation = .ok value)
    (choices : List ScheduleChoice) :
    schedule computation choices table callDepth = .ok value := by
  simp [schedule, nonempty, Result.runWith_apply, resolved]

/-- A pure computation runs to `ok` exactly when it returns that value. -/
@[simp] public theorem IsPure.schedule_eq_ok_iff {computation : Result α}
    (pure : computation.IsPure) {choices : List ScheduleChoice} {table : Term.FunTable}
    {callDepth : Nat} {value : α} :
    schedule computation choices table callDepth = .ok value ↔ computation = .ok value := by
  rw [schedule_of_isPure _ pure]
  cases computation <;> simp_all [Result.IsPure]

/-- A partial computation runs to `ok` exactly when it returns that value: it
makes no runtime requests, and an exhausted computation does not return. -/
@[simp] public theorem IsPartial.schedule_eq_ok_iff {computation : Result α}
    (partiality : computation.IsPartial) {choices : List ScheduleChoice} {table : Term.FunTable}
    {callDepth : Nat} {value : α} :
    schedule computation choices table callDepth = .ok value ↔ computation = .ok value := by
  unfold schedule
  split <;> (try rw [Result.runWith_apply, Result.resolve_of_isPartial _ _ _ partiality]) <;>
    cases computation <;> simp_all [Result.IsPartial]

/-- Pure computations ignore the program table. -/
public theorem run_of_isPure (computation : Result α) (pure : computation.IsPure)
    (table : Term.FunTable) (callDepth : Nat) :
    run computation table callDepth = (computation {}).1 :=
  schedule_of_isPure computation pure [] table callDepth

@[simp] public theorem run_ok (value : α) (table : Term.FunTable) (callDepth : Nat) :
    run (.ok value) table callDepth = .ok value :=
  schedule_ok value [] table callDepth

@[simp] public theorem run_error (exception : Exception) (table : Term.FunTable)
    (callDepth : Nat) :
    run (.error exception : Result α) table callDepth = .error exception :=
  schedule_error exception [] table callDepth

/-- A computation whose dynamic calls resolve to a value against a program table
runs to that value. -/
public theorem run_of_resolve {computation : Result α} {table : Term.FunTable}
    {callDepth : Nat} {value : α} (nonempty : table.isEmpty = false)
    (resolved : Result.resolve table callDepth computation = .ok value) :
    run computation table callDepth = .ok value :=
  schedule_of_resolve nonempty resolved []

/-- A partial computation runs to `ok` exactly when it returns that value. -/
@[simp] public theorem IsPartial.run_eq_ok_iff {computation : Result α}
    (partiality : computation.IsPartial) {table : Term.FunTable} {callDepth : Nat} {value : α} :
    run computation table callDepth = .ok value ↔ computation = .ok value :=
  IsPartial.schedule_eq_ok_iff partiality

/-- A pure computation runs to `ok` exactly when it returns that value. -/
@[simp] public theorem IsPure.run_eq_ok_iff {computation : Result α} (pure : computation.IsPure)
    {table : Term.FunTable} {callDepth : Nat} {value : α} :
    run computation table callDepth = .ok value ↔ computation = .ok value :=
  IsPure.schedule_eq_ok_iff pure

end Lynx
