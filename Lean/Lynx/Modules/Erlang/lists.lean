module

public import Lynx.Term
public import Lynx.Pure

public section

namespace Erlang.lists
open Lynx

/-- Reverse a proper list onto an arbitrary tail, or raise `badarg`. -/
#lynx_pure @[expose] def «reverse/2» : Term → Term → Result
  | .nil, tail => .ok tail
  | .cons head rest, tail => «reverse/2» rest (.cons head tail)
  | _, _ => .error (.error (.atom "badarg"))

end Erlang.lists
