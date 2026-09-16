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

@[grind →] private theorem append_preserves_isProperIntegerList
    (left right joined : Term)
    (leftProper : isProperIntegerList left = .ok Term.true)
    (rightProper : isProperIntegerList right = .ok Term.true)
    (appended : Erlang.append_2 left right = .ok joined) :
    isProperIntegerList joined = .ok Term.true := by
  induction left using Term.induct generalizing joined with
  | cons head tail _ tailIh =>
    have appendPure := Erlang.append_2_pure tail right
    cases returned : Erlang.append_2 tail right
    case ok rest =>
      cases head
      case integer value =>
        simp [isProperIntegerList, Erlang.is_integer_1, Erlang.append_2,
          returned, Term.true, Term.false] at leftProper appended
        subst joined
        have restProper := tailIh rest leftProper returned
        simpa [isProperIntegerList, Erlang.is_integer_1, Term.true, Term.false]
          using restProper
      all_goals simp_all [isProperIntegerList, Erlang.is_integer_1,
        Erlang.append_2, Term.true, Term.false]
    all_goals simp_all [Erlang.append_2]
  | _ => simp_all [isProperIntegerList, Erlang.append_2, Term.true, Term.false]

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
