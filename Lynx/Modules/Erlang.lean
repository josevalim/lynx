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

/-- A logical shortcut proved directly from the executable definition.
State it in the unfolded `Accepted`/`Term.true` form so simp can still match it
after unfolding executable wrappers. -/
@[simp] theorem andalso_spec (left : Outcome Term) (right : Unit → Outcome Term) :
    andalso left right = .value (.atom "true") ↔
      left = .value (.atom "true") ∧ right () = .value (.atom "true") := by
  cases left with
  | raised exception => simp [andalso]
  | value value =>
    cases value with
    | atom name =>
      by_cases ht : name = "true"
      · subst name; simp [andalso]
      · by_cases hf : name = "false"
        · subst name; simp [andalso, Term.false]
        · simp [andalso, ht, hf]
    | integer n => simp [andalso]
    | nil => simp [andalso]
    | cons head tail => simp [andalso]

end Lynx.Modules.Erlang
