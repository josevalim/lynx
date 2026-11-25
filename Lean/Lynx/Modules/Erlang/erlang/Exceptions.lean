module

public import Lynx.Term

public section

namespace Lynx.Term

/-- Whether a term is a stack trace `erlang:raise/3` accepts: a proper list of
`{Fun, Args}`, `{Fun, Args, Location}`, `{Module, Function, Arity}`, and
`{Module, Function, Arity, Location}` entries, whose locations are lists. -/
@[expose] def isStacktrace : Term → Bool
  | .nil => Bool.true
  | .cons (.tuple entry) rest =>
    (match entry.toList with
     | [.function _ _ _ _ _, _] => Bool.true
     | [.function _ _ _ _ _, _, .nil] | [.function _ _ _ _ _, _, .cons _ _] => Bool.true
     | [.atom _, .atom _, _] => Bool.true
     | [.atom _, .atom _, _, .nil] | [.atom _, .atom _, _, .cons _ _] => Bool.true
     | _ => Bool.false) && isStacktrace rest
  | _ => Bool.false

end Lynx.Term

namespace Erlang.erlang
open Lynx

/-- The argument list only supplies stack trace metadata, which Result does not model. -/
@[expose] def «error/2» (reason _arguments : Term) : Except Exception Term := .error (.error reason)

/-- Error options describe stack trace formatting, which Result does not model. -/
@[expose] def «error/3» (reason _arguments _options : Term) : Except Exception Term := .error (.error reason)

@[expose] def «throw/1» (reason : Term) : Except Exception Term := .error (.throw reason)

@[expose] def «exit/1» (reason : Term) : Except Exception Term := .error (.exit reason)


/-- Raise an exception of the given class. The stack trace is checked but not
recorded. As in OTP, an invalid class or stack trace returns `badarg` instead of
raising. -/
@[expose] def «raise/3» (kind reason stacktrace : Term) : Except Exception Term :=
  if !stacktrace.isStacktrace then .ok (.atom "badarg") else
  match kind with
  | .atom "error" => .error (.error reason)
  | .atom "throw" => .error (.throw reason)
  | .atom "exit" => .error (.exit reason)
  | _ => .ok (.atom "badarg")

end Erlang.erlang
