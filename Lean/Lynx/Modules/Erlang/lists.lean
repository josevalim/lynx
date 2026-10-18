module

public import Lynx.Term
public import Lynx.Purity

public section

namespace Erlang.lists

-- Other modules use these lemmas constantly, including while checking
-- well-founded recursion, so they are proved once, here.
set_option lynx.lazyPurity false
open Lynx

/-- Reverse a proper list onto an arbitrary tail, or raise `badarg`. -/
#lynx_pure @[expose] def «reverse/2» : Term → Term → Result
  | .nil, tail => .ok tail
  | .cons head rest, tail => «reverse/2» rest (.cons head tail)
  | _, _ => .error (.error (.atom "badarg"))

/-- Test membership by exact equality, returning at the first match. Reaching an
improper tail or a non-list raises `badarg`. -/
#lynx_pure @[expose] def «member/2» : Term → Term → Result
  | _, .nil => .ok Term.false
  | element, .cons head tail =>
    if Term.exactCompare element head = .eq then .ok Term.true else «member/2» element tail
  | _, _ => .error (.error (.atom "badarg"))

end Erlang.lists
