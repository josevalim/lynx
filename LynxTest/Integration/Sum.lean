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

#lynx_pure def isProperIntegerList : Term → Result
  | .nil => .ok Term.true
  | .cons head tail => do
      match ← Erlang.is_integer_1 head with
      | .atom "true" => isProperIntegerList tail
      | _ => .ok Term.false
  | _ => .ok Term.false

#lynx_pure def sum_1 : Term → Result
  | .nil => .ok (.integer 0)
  | .cons x xs => do
      let subtotal ← sum_1 xs
      Erlang.add_2 x subtotal
  | _ => throw (.error (.atom "function_clause"))

private theorem sum_1_integer_or_error (input : Term) :
    (∃ value, sum_1 input = .ok (.integer value)) ∨
      ∃ exception, sum_1 input = .error exception := by
  induction input using Term.induct with
  | cons head tail _ tailIh =>
    rcases tailIh with ⟨subtotal, returned⟩ | ⟨exception, returned⟩
    · cases head <;> simp [sum_1, returned, Erlang.add_2]
    · simp [sum_1, returned]
  | _ => simp [sum_1]

@[simp] theorem sum_1_ne_float (input : Term) (value : Term.FiniteFloat) :
    sum_1 input ≠ .ok (.float value) := by
  rcases sum_1_integer_or_error input with ⟨integer, returned⟩ | ⟨exception, returned⟩ <;>
    simp [returned]

/-! Translated integer-list expectation and integer-result guarantee. -/
def sumExpects (arg : Term) : Result :=
  isProperIntegerList arg

def sumEnsures (_arg result : Term) : Result :=
  Erlang.is_integer_1 result

/-- Both operands of the property must satisfy the function's expectation. -/
def appendExpects (args : Term × Term) : Result :=
  Erlang.andalso_2 (sumExpects args.1) (fun _ => sumExpects args.2)

/-- Translated `sum(l) + sum(r) == sum(l ++ r)`. -/
def appendExpression (args : Term × Term) : Result := do
  let left ← sum_1 args.1
  let right ← sum_1 args.2
  let total ← Erlang.add_2 left right
  let joined ← Erlang.append_2 args.1 args.2
  let combined ← sum_1 joined
  Erlang.equal_2 total combined

#bench "erlang/sum-contract"
theorem sum_satisfies_contract : Satisfies sum_1 sumExpects sumEnsures := by
  lynx_verify

#bench "erlang/sum-append"
theorem sum_append_property : Property appendExpects appendExpression := by
  lynx_verify

end LynxTest.Integration.Sum
