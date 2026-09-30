module

public import Lynx.Term.DataTypes
public import Lynx.Term.Compare
public import Lynx.Term.Runner
public import Lynx.Term.Induction

namespace Lynx

/-- Run a complete process tree from a fresh runtime using the supplied
scheduler choices.
An `ok` or `error` outcome means every spawned process has finished.
`deadlock` means the modeled process tree is stuck. `exhausted` means a dynamic
call exceeded `callDepth`; it is not an Erlang exception. The immutable table
is separate from process state. -/
public def run (computation : Result α) (schedule : List ScheduleChoice := [])
    (table : Term.FunTable := #[]) (callDepth : Nat := 100) : Outcome α :=
  if table.isEmpty then computation.run { schedule }
  else computation.runWith table callDepth { schedule }

end Lynx

namespace Lynx.Term

@[expose] public def «true» : Term := .atom "true"

@[expose] public def «false» : Term := .atom "false"

/-- Apply a function to native arguments. Build an Erlang argument list only
when reporting an arity mismatch. -/
public def apply (function : Term) (arguments : Array Term) : Result :=
  match function with
  | .function _ arity _ =>
      if arguments.size = arity then
        .apply function arguments fun
          | .ok value => .ok value
          | .error exception => .error exception
      else
        .error (.error (.tuple #[.atom "badarity", .tuple #[function,
          arguments.toList.foldr Term.cons Term.nil]]))
  | _ => .error (.error (.tuple #[.atom "badfun", function]))

end Lynx.Term
