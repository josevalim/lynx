module

/-
defmodule Sum do
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

/- law sum_result(list),
     requires: is_proper_list(list, &is_integer/1),
     expects: (result -> is_integer(result)) -/
#bench "erlang/sum-result"
theorem sum_result (input : Term)
    (valid : isProperIntegerList input = .ok Term.true) :
    ∃ value : Int, sum_1 input = .ok (.integer value) := by
  induction input using Term.induct with
  | nil => exact ⟨0, rfl⟩
  | cons head tail headIh ih =>
    clear headIh
    cases head
    case integer value =>
      have tailValid : isProperIntegerList tail = .ok Term.true := by
        simpa [isProperIntegerList, Term.true] using valid
      obtain ⟨subtotal, returned⟩ := ih tailValid
      exact ⟨value + subtotal, by simp [sum_1, returned]⟩
    all_goals simp [isProperIntegerList, Term.true, Term.false] at valid
  | _ => simp [isProperIntegerList, Term.true, Term.false] at valid

/- law sum_append(l, r),
     requires: is_proper_list(l, &is_integer/1) and is_proper_list(r, &is_integer/1),
     expects: sum(l) + sum(r) == sum(l ++ r) -/
def appendExpression (left right : Term) : Result := do
  let l ← sum_1 left
  let r ← sum_1 right
  let total ← Erlang.erlang.«+/2» l r
  let joined ← Erlang.erlang.«++/2» left right
  let combined ← sum_1 joined
  Erlang.erlang.«==/2» total combined

#bench "erlang/sum-append"
theorem sum_append (left right : Term)
    (leftValid : isProperIntegerList left = .ok Term.true)
    (rightValid : isProperIntegerList right = .ok Term.true) :
    appendExpression left right = .ok Term.true := by
  obtain ⟨rightSum, rightReturned⟩ := sum_result right rightValid
  have append_ok (input : Term) (valid : isProperIntegerList input = .ok Term.true) :
      ∃ leftSum joined,
        sum_1 input = .ok (.integer leftSum) ∧
        Erlang.erlang.«++/2» input right = .ok joined ∧
        sum_1 joined = .ok (.integer (leftSum + rightSum)) := by
    induction input using Term.induct with
    | nil => exact ⟨0, right, rfl, rfl, by simpa using rightReturned⟩
    | cons head tail headIh ih =>
      clear headIh
      cases head
      case integer value =>
        have tailValid : isProperIntegerList tail = .ok Term.true := by
          simpa [isProperIntegerList, Term.true] using valid
        obtain ⟨subtotal, joined, returned, appended, combined⟩ := ih tailValid
        refine ⟨value + subtotal, .cons (.integer value) joined, ?_, ?_, ?_⟩
        · simp [sum_1, returned]
        · simp [Erlang.erlang.«++/2», appended]
        · simp [sum_1, combined, Int.add_assoc]
      all_goals simp [isProperIntegerList, Term.true, Term.false] at valid
    | _ => simp [isProperIntegerList, Term.true, Term.false] at valid
  obtain ⟨leftSum, joined, leftReturned, appended, combined⟩ := append_ok left leftValid
  simp [appendExpression, leftReturned, rightReturned, appended, combined,
    Erlang.erlang.«==/2»]

end LynxTest.Integration.Sum
