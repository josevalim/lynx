import Lynx.Contract
import Lynx.Term

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

/-- A direct logical view of `andalso`, proved from its executable definition
and used by the verifier to avoid repeatedly unfolding its runtime cases. -/
theorem accepted_andalso (left : Outcome Term) (right : Unit → Outcome Term) :
    Accepted (andalso left right) ↔ Accepted left ∧ Accepted (right ()) := by
  cases left with
  | raised exception => simp [Accepted, andalso]
  | value value =>
    cases value with
    | atom name =>
      by_cases ht : name = "true"
      · subst name; simp [Accepted, andalso, Term.true]
      · by_cases hf : name = "false"
        · subst name; simp [Accepted, andalso, Term.true, Term.false]
        · simp [Accepted, andalso, Term.true, ht, hf]
    | integer n => simp [Accepted, andalso, Term.true]
    | nil => simp [Accepted, andalso, Term.true]
    | cons head tail => simp [Accepted, andalso, Term.true]

end Lynx.Modules.Erlang
