import Lynx.Attribute
import Lynx.Term
import Lynx.Term.Order

/-! Executable Erlang operations, independent of contract/tactic machinery. -/

namespace Lynx.Modules.Erlang

open Lynx

def is_integer : Term → Result
  | .integer _ => .ok Term.true
  | _ => .ok Term.false

def is_list : Term → Result
  | .nil => .ok Term.true
  | .cons _ _ => .ok Term.true
  | _ => .ok Term.false

def add : Term → Term → Result
  | .integer x, .integer y => .ok (.integer (x + y))
  | _, _ => throw (.error (.atom "badarith"))

def equal (left right : Term) : Result :=
  .ok (if left = right then Term.true else Term.false)

def less_than (left right : Term) : Result :=
  .ok (if (Term.compare left right).isLT then Term.true else Term.false)

def greater_than (left right : Term) : Result :=
  .ok (if (Term.compare left right).isGT then Term.true else Term.false)

def less_than_or_equal (left right : Term) : Result :=
  .ok (if (Term.compare left right).isLE then Term.true else Term.false)

def greater_than_or_equal (left right : Term) : Result :=
  .ok (if (Term.compare left right).isGE then Term.true else Term.false)

@[lynx_opaque] def append : Term → Term → Result
  | .nil, right => .ok right
  | .cons head tail, right => do
      let rest ← append tail right
      .ok (.cons head rest)
  | _, _ => throw (.error (.atom "badarg"))

def andalso
    (left : Result)
    (right : Unit → Result) : Result :=
  match left with
  | .ok (.atom "true") => right ()
  | .ok (.atom "false") => .ok Term.false
  | .ok _ => .error (.error (.atom "badarg"))
  | .error exception => .error exception

end Lynx.Modules.Erlang
