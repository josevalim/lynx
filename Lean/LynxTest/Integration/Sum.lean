module

/-
defmodule Sum do
  def sum(list)
  def sum([]), do: 0
  def sum([x | xs]), do: x + sum(xs)

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
-/
import Erlang.erlang
import Lynx.Term
import LynxTest.Bench

namespace LynxTest.Integration.Sum
open Lynx
set_option Elab.async false

section
attribute [local simp] Erlang.erlang.«is_integer/1»

#lynx_pure def is_integer_list_1 : Term → Result
  | .cons head tail => do
      match ← Erlang.erlang.«is_integer/1» head with
      | .atom "true" => is_integer_list_1 tail
      | .atom "false" => .ok Term.false
      | other => .error (.error (.tuple #[.atom "badbool", .atom "and", other]))
  | .nil => .ok Term.true
  | _ => .ok Term.false
end

theorem requested_example :
    is_integer_list_1
      (.cons (.integer 1) (.cons (.integer 2) (.cons (.integer 3) .nil))) = .ok Term.true := by
  simp [is_integer_list_1, Erlang.erlang.«is_integer/1»]

theorem rejected_inputs :
    is_integer_list_1 (.cons (.atom "no") .nil) = .ok Term.false ∧
    is_integer_list_1 (.cons (.integer 1) (.integer 2)) = .ok Term.false := by
  simp [is_integer_list_1, Erlang.erlang.«is_integer/1»]

#lynx_pure def sum_1 : Term → Result
  | .nil => .ok (.integer 0)
  | .cons x xs => do
      let subtotal ← sum_1 xs
      Erlang.erlang.«+/2» x subtotal
  | _ => throw (.error (.atom "function_clause"))

/- law sum_result(list),
     requires: is_integer_list(list),
     expects: (result -> is_integer(result)) -/
#bench "erlang/sum-result"
theorem sum_result (input : Term)
    (valid : is_integer_list_1 input = .ok Term.true) :
    ∃ value : Int, sum_1 input = .ok (.integer value) := by
  -- Follow recursion on the list tail, rather than every nested Term field.
  induction input using sum_1.induct with
  | case1 => exact ⟨0, rfl⟩
  | case2 head tail ih =>
    simp only [is_integer_list_1, Erlang.erlang.«is_integer/1»] at valid
    split at valid
    next value =>
      have tailValid : is_integer_list_1 tail = .ok Term.true := by
        simpa only [Result.ok_bind, Term.true] using valid
      obtain ⟨subtotal, returned⟩ := ih tailValid
      exact ⟨value + subtotal, by simp [sum_1, returned]⟩
    next => simp at valid
  | case3 input notNil notCons => simp [is_integer_list_1] at valid

/- law sum_append(l, r),
     requires: is_integer_list(l) and is_integer_list(r),
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
    (leftValid : is_integer_list_1 left = .ok Term.true)
    (rightValid : is_integer_list_1 right = .ok Term.true) :
    appendExpression left right = .ok Term.true := by
  obtain ⟨rightSum, rightReturned⟩ := sum_result right rightValid
  have append_ok (input : Term) (valid : is_integer_list_1 input = .ok Term.true) :
      ∃ leftSum joined,
        sum_1 input = .ok (.integer leftSum) ∧
        Erlang.erlang.«++/2» input right = .ok joined ∧
        sum_1 joined = .ok (.integer (leftSum + rightSum)) := by
    induction input using sum_1.induct with
    | case1 => exact ⟨0, right, rfl, rfl, by simpa using rightReturned⟩
    | case2 head tail ih =>
      simp only [is_integer_list_1, Erlang.erlang.«is_integer/1»] at valid
      split at valid
      next value =>
        have tailValid : is_integer_list_1 tail = .ok Term.true := by
          simpa only [Result.ok_bind, Term.true] using valid
        obtain ⟨subtotal, joined, returned, appended, combined⟩ := ih tailValid
        refine ⟨value + subtotal, .cons (.integer value) joined, ?_, ?_, ?_⟩
        · simp [sum_1, returned]
        · simp [Erlang.erlang.«++/2», appended]
        · simp [sum_1, combined, Int.add_assoc]
      next => simp at valid
    | case3 input notNil notCons => simp [is_integer_list_1] at valid
  obtain ⟨leftSum, joined, leftReturned, appended, combined⟩ := append_ok left leftValid
  simp [appendExpression, leftReturned, rightReturned, appended, combined,
    Erlang.erlang.«==/2»]

end LynxTest.Integration.Sum
