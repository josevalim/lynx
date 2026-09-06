/-
defmodule Sum do
  expects is_proper_list(list, &is_integer/1)
  ensures (result -> is_integer(result))
  property sum(l) + sum(r) == sum(l ++ r)
  def sum(list)
  def sum([]), do: 0
  def sum([x | xs]), do: x + sum(xs)
end
-/
import LynxTest.Bench

namespace LynxTest.Integration.Sum
open Lynx Lynx.Modules
set_option Elab.async false

def sumTerm : Term → Outcome Term
  | .nil => .value (.integer 0)
  | .cons x xs => do
      let subtotal ← sumTerm xs
      Erlang.add x subtotal
  | _ => throw (.error (.atom "function_clause"))

/-! Translated integer-list expectation and integer-result guarantee. -/
def sumExpects (arg : Term) : Outcome Term :=
  Extensions.is_proper_list_with Erlang.is_integer arg

def sumEnsures (_arg result : Term) : Outcome Term :=
  Erlang.is_integer result

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

#bench "erlang/sum-contract"
theorem sum_satisfies_contract : Satisfies sumTerm sumExpects sumEnsures := by
  lynx_verify

#bench "erlang/sum-append"
theorem sum_append_property : Property appendExpects appendExpression := by
  lynx_verify

end LynxTest.Integration.Sum
