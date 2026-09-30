module

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
import all Erlang.erlang
import all Erlang.erlang.Guards
import all Lynx.Term
import all Lynx.Term.DataTypes
import LynxTest.Bench

namespace LynxTest.Integration.Sum
open Lynx
set_option Elab.async false

@[simp] private def integerFunctions : Term.FunTable := #[
  .pure fun _ args =>
    match args.toList with
    | [value] => Result.toExcept (Erlang.erlang.«is_integer/1» value) (by simp)
    | _ => .error (.error (.atom "badarg"))
]

attribute [local simp] Term.pureApply Result.toExcept Result.ofExcept

def is_proper_list_2 (table : Term.FunTable) (predicate : Term) : Term → Result
  | .nil => .ok Term.true
  | .cons head tail => do
      match ← Term.pureApply table predicate #[head] with
      | .atom "true" => is_proper_list_2 table predicate tail
      | _ => .ok Term.false
  | _ => .ok Term.false

attribute [local simp] is_proper_list_2

#lynx_pure def isProperIntegerList : Term → Result
  | .nil => .ok Term.true
  | .cons head tail => do
      match ← Term.pureApply integerFunctions (.function 0 1 #[]) #[head] with
      | .atom "true" => isProperIntegerList tail
      | _ => .ok Term.false
  | _ => .ok Term.false

/-- Specializing the generic callback traversal preserves its semantics. -/
theorem integer_callback_specialization (xs : Term) :
    is_proper_list_2 integerFunctions (.function 0 1 #[]) xs =
      isProperIntegerList xs := by
  induction xs using Term.induct <;> simp_all [isProperIntegerList]

theorem requested_example :
    is_proper_list_2 integerFunctions (.function 0 1 #[])
      (.cons (.integer 1) (.cons (.integer 2) (.cons (.integer 3) .nil))) = .ok Term.true := by
  simp [Term.true]

theorem rejected_inputs :
    isProperIntegerList (.cons (.atom "no") .nil) = .ok Term.false ∧
    isProperIntegerList (.cons (.integer 1) (.integer 2)) = .ok Term.false := by
  simp [isProperIntegerList, Term.true, Term.false]

#lynx_pure def sum_1 : Term → Result
  | .nil => .ok (.integer 0)
  | .cons x xs => do
      let subtotal ← sum_1 xs
      Erlang.erlang.«+/2» x subtotal
  | _ => throw (.error (.atom "function_clause"))

@[grind →] private theorem append_preserves_isProperIntegerList
    (left right joined : Term)
    (leftProper : isProperIntegerList left = .ok Term.true)
    (rightProper : isProperIntegerList right = .ok Term.true)
    (appended : Erlang.erlang.«++/2» left right = .ok joined) :
    isProperIntegerList joined = .ok Term.true := by
  induction left using Term.induct generalizing joined with
  | cons head tail _ tailIh =>
    have appendPure := Erlang.erlang.«++/2_pure» tail right
    cases returned : Erlang.erlang.«++/2» tail right
    case ok rest =>
      cases head
      case integer value =>
        simp [isProperIntegerList, Erlang.erlang.«++/2»,
          returned, Term.true, Term.false] at leftProper appended
        subst joined
        have restProper := tailIh rest leftProper returned
        simpa [isProperIntegerList, Term.true, Term.false]
          using restProper
      all_goals simp_all [isProperIntegerList,
        Erlang.erlang.«++/2», Term.true, Term.false]
    all_goals simp_all [Erlang.erlang.«++/2»]
  | _ => simp_all [isProperIntegerList, Erlang.erlang.«++/2», Term.true, Term.false]

/-! Translated integer-list expectation and integer-result guarantee. -/
def sumExpects (arg : Term) : Result :=
  isProperIntegerList arg

def sumEnsures (_arg result : Term) : Result :=
  Erlang.erlang.«is_integer/1» result

/-- Both operands must satisfy the function's expectation. -/
def appendExpects (args : Term × Term) : Result := do
  match ← sumExpects args.1 with
  | .atom "true" => sumExpects args.2
  | .atom "false" => .ok Term.false
  | _ => throw (.error (.atom "badarg"))

/-- Translated `sum(l) + sum(r) == sum(l ++ r)`. -/
def appendExpression (args : Term × Term) : Result := do
  let left ← sum_1 args.1
  let right ← sum_1 args.2
  let total ← Erlang.erlang.«+/2» left right
  let joined ← Erlang.erlang.«++/2» args.1 args.2
  let combined ← sum_1 joined
  Erlang.erlang.«==/2» total combined

#bench "erlang/sum-contract"
theorem sum_satisfies_contract : Satisfies sum_1 sumExpects sumEnsures := by
  lynx_verify

#bench "erlang/sum-append"
theorem sum_append_property : Property appendExpects appendExpression := by
  lynx_verify

end LynxTest.Integration.Sum
