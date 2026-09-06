import Lynx.Tactic

namespace LynxTest.Integration.Sum

open Lynx Lynx.Modules

/-!
Operational translation of `sum([]) = 0` and `sum([x | xs]) = x + sum(xs)`.
The recursive call is evaluated before addition, propagating tail exceptions.
-/
def sumTerm : Term → Outcome Term
  | .nil => .value (.integer 0)
  | .cons x xs => do
      let subtotal ← sumTerm xs
      Erlang.add x subtotal
  | _ => throw (.error (.atom "function_clause"))

/-! Translated integer-list expectation and integer-result guarantee. -/
def sumExpects (arg : Term) : Outcome Term :=
  Extensions.is_proper_list Erlang.is_integer arg

def sumEnsures (_arg result : Term) : Outcome Term :=
  Erlang.is_integer result

theorem sum_satisfies_contract :
    Satisfies sumTerm sumExpects sumEnsures := by
  lynx_verify

/-- Both operands of the property must satisfy the function's expectation. -/
def appendExpects (args : Term × Term) : Outcome Term :=
  Erlang.andalso (sumExpects args.1) (fun _ => sumExpects args.2)

/-- Translated `sum(l) + sum(r) == sum(l ++ r)`. -/
def appendExpression (args : Term × Term) : Outcome Term := do
  let left ← sumTerm args.1
  let right ← sumTerm args.2
  let total ← Erlang.add left right
  let joined ← Erlang.append args.1 args.2
  let combined ← sumTerm joined
  Erlang.equal total combined

theorem sum_append_property : Property appendExpects appendExpression := by
  lynx_verify

end LynxTest.Integration.Sum
