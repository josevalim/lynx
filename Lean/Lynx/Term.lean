module

public import Lynx.Term.DataTypes
public import Lynx.Term.Except
public import Lynx.Term.Result
public import Lynx.Term.Compare
public import Lynx.Term.Maps
public import Lynx.Term.Runner
public import Lynx.Term.Induction
public import Lynx.Term.Order

namespace Lynx

/-- Call a definition that is not pure with the dispatcher of a program's
function table, up to a call depth of 100. -/
@[expose] public def apply (definition : Dispatcher → α) (table : Term.FunTable) : α :=
  definition (Dispatcher.ofTable table 100)

@[simp] public theorem apply_eq (definition : Dispatcher → α) (table : Term.FunTable) :
    apply definition table = definition (Dispatcher.ofTable table 100) := rfl

/-- Run a complete process tree from a fresh runtime using the supplied
scheduler choices.
An `ok` or `error` outcome means every spawned process has finished, except
that an `Exception.exhausted` error means some process did not return, such as
a dynamic call exceeding its dispatcher's depth; it is not an Erlang exception.
`deadlock` means the modeled process tree is stuck. -/
public def concurrent (computation : Result α) (schedule : List ScheduleChoice := []) :
    Outcome α :=
  (computation.run { schedule }).1

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
