import Lynx.Contract
import Lynx.Term
import Lynx.Term.Order

namespace Lynx.Modules.Erlang

open Lynx

def is_integer : Term → Outcome Term
  | .integer _ => .value Term.true
  | _ => .value Term.false

def is_list : Term → Outcome Term
  | .nil => .value Term.true
  | .cons _ _ => .value Term.true
  | _ => .value Term.false

def add : Term → Term → Outcome Term
  | .integer x, .integer y => .value (.integer (x + y))
  | _, _ => throw (.error (.atom "badarith"))

def equal (left right : Term) : Outcome Term :=
  .value (if left = right then Term.true else Term.false)

def less_than (left right : Term) : Outcome Term :=
  .value (if (Term.compare left right).isLT then Term.true else Term.false)

def greater_than (left right : Term) : Outcome Term :=
  .value (if (Term.compare left right).isGT then Term.true else Term.false)

def less_than_or_equal (left right : Term) : Outcome Term :=
  .value (if (Term.compare left right).isLE then Term.true else Term.false)

def greater_than_or_equal (left right : Term) : Outcome Term :=
  .value (if (Term.compare left right).isGE then Term.true else Term.false)

def append : Term → Term → Outcome Term
  | .nil, right => .value right
  | .cons head tail, right => do
      let rest ← append tail right
      .value (.cons head rest)
  | _, _ => throw (.error (.atom "badarg"))

def andalso
    (left : Outcome Term)
    (right : Unit → Outcome Term) : Outcome Term :=
  match left with
  | .value (.atom "true") => right ()
  | .value (.atom "false") => .value Term.false
  | .value _ => .raised (.error (.atom "badarg"))
  | .raised exception => .raised exception

end Lynx.Modules.Erlang
