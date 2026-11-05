module

public import Lynx.Term

public section

namespace Lynx.Term

/-- Whether a term is a proper list. -/
@[expose] def isProperList : Term → Bool
  | .nil => Bool.true
  | .cons _ tail => isProperList tail
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


/-- Raise an exception of the given class. The stack trace must be a list and is
not recorded. -/
@[expose] def «raise/3» (kind reason stacktrace : Term) : Except Exception Term :=
  if !stacktrace.isProperList then .error (.error (.atom "badarg")) else
  match kind with
  | .atom "error" => .error (.error reason)
  | .atom "throw" => .error (.throw reason)
  | .atom "exit" => .error (.exit reason)
  | _ => .error (.error (.atom "badarg"))

end Erlang.erlang
