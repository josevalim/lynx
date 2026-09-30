module

/-
defmodule Sum do
  def sum(list)
  def sum([]), do: 0
  def sum([x | xs]), do: x + sum(xs)
end
-/
import Erlang.erlang
import Lynx.Term
import LynxTest.Bench

namespace LynxTest.Integration.Sum
open Lynx
set_option Elab.async false

private def integerPredicate (captures args : Array Term) : Except Exception Term :=
  match captures, args with
  | #[], #[value] => Result.toExcept (Erlang.erlang.«is_integer/1» value) (by simp)
  | _, _ => .error (.error (.atom "badarg"))

private def integerFunctions : Term.FunTable := #[.pure integerPredicate]

-- Mirrored output of the function-table generator.
@[simp↓] private theorem integerFunctions_apply_0_bind {α : Type} (depth : Nat) (arg1 : Term)
    (next : Term → Result α) :
    Result.resolve integerFunctions depth (Term.apply (.function 0 1 #[]) #[arg1] >>= next) =
      Result.resolve integerFunctions depth (Erlang.erlang.«is_integer/1» arg1 >>= next) := by
  rw [Result.resolve_apply_pure integerFunctions depth 0 1 #[] #[arg1] integerPredicate next
    (by rfl) (by rfl)]
  change Result.resolve integerFunctions depth
    (Result.ofExcept (Result.toExcept (Erlang.erlang.«is_integer/1» arg1) (by simp)) >>= next) = _
  rw [Result.ofExcept_toExcept]

@[simp↓] private theorem integerFunctions_apply_0_bind_explicit {α : Type} (depth : Nat)
    (arg1 : Term) (next : Term → Result α) :
    Result.resolve integerFunctions depth
      (Result.bind (Term.apply (.function 0 1 #[]) #[arg1]) next) =
      Result.resolve integerFunctions depth (Result.bind (Erlang.erlang.«is_integer/1» arg1) next) := by
  exact integerFunctions_apply_0_bind depth arg1 next

@[simp] private theorem integerFunctions_apply_0 (depth : Nat) (arg1 : Term) :
    Result.resolve integerFunctions depth (Term.apply (.function 0 1 #[]) #[arg1]) =
      Erlang.erlang.«is_integer/1» arg1 := by
  simpa only [Result.bind_ok, Result.resolve_of_isPure integerFunctions depth
    (Erlang.erlang.«is_integer/1» arg1) (by simp)] using
    integerFunctions_apply_0_bind depth arg1 Result.ok

def is_proper_list_2 (predicate : Term) : Term → Result
  | .nil => .ok Term.true
  | .cons head tail => do
      match ← Term.apply predicate #[head] with
      | .atom "true" => is_proper_list_2 predicate tail
      | _ => .ok Term.false
  | _ => .ok Term.false

-- The law's predicate uses the translated traversal and its program table.
def isProperIntegerList (input : Term) : Result :=
  Result.resolve integerFunctions 0 (is_proper_list_2 (.function 0 1 #[]) input)

theorem requested_example :
    Result.resolve integerFunctions 0 (is_proper_list_2 (.function 0 1 #[])
      (.cons (.integer 1) (.cons (.integer 2) (.cons (.integer 3) .nil)))) = .ok Term.true := by
  simp [is_proper_list_2, Erlang.erlang.«is_integer/1», Term.true]

theorem rejected_inputs :
    isProperIntegerList (.cons (.atom "no") .nil) = .ok Term.false ∧
    isProperIntegerList (.cons (.integer 1) (.integer 2)) = .ok Term.false := by
  simp [isProperIntegerList, is_proper_list_2, Erlang.erlang.«is_integer/1», Term.true, Term.false]

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
        simpa [isProperIntegerList, is_proper_list_2, Erlang.erlang.«is_integer/1», Term.true] using valid
      obtain ⟨subtotal, returned⟩ := ih tailValid
      exact ⟨value + subtotal, by simp [sum_1, returned]⟩
    all_goals simp [isProperIntegerList, is_proper_list_2, Erlang.erlang.«is_integer/1», Term.true, Term.false] at valid
  | _ => simp [isProperIntegerList, is_proper_list_2, Term.true, Term.false] at valid

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
          simpa [isProperIntegerList, is_proper_list_2, Erlang.erlang.«is_integer/1», Term.true] using valid
        obtain ⟨subtotal, joined, returned, appended, combined⟩ := ih tailValid
        refine ⟨value + subtotal, .cons (.integer value) joined, ?_, ?_, ?_⟩
        · simp [sum_1, returned]
        · simp [Erlang.erlang.«++/2», appended]
        · simp [sum_1, combined, Int.add_assoc]
      all_goals simp [isProperIntegerList, is_proper_list_2, Erlang.erlang.«is_integer/1», Term.true, Term.false] at valid
    | _ => simp [isProperIntegerList, is_proper_list_2, Term.true, Term.false] at valid
  obtain ⟨leftSum, joined, leftReturned, appended, combined⟩ := append_ok left leftValid
  simp [appendExpression, leftReturned, rightReturned, appended, combined,
    Erlang.erlang.«==/2»]

end LynxTest.Integration.Sum
