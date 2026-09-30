module

/-
defmodule Reverse do
  def reverse(list), do: reverse_aux(list, [])

  defp reverse_aux([], acc), do: acc
  defp reverse_aux([head | tail], acc), do: reverse_aux(tail, [head | acc])

  defp is_reversible_list([]), do: true
  defp is_reversible_list([_ | tail]), do: is_reversible_list(tail)
  defp is_reversible_list(_), do: false
end
-/
import Erlang.erlang
import LynxTest.Bench

namespace LynxTest.Integration.Reverse
open Lynx
set_option Elab.async false

#lynx_pure def is_reversible_list_1 : Term → Result
  | .nil => .ok Term.true
  | .cons _ tail => is_reversible_list_1 tail
  | _ => .ok Term.false

private theorem append_success (left right : Term)
    (accepted : is_reversible_list_1 left = .ok Term.true) :
    ∃ joined, Erlang.erlang.«++/2» left right = .ok joined := by
  have reject : (Result.ok Term.false : Result) ≠ .ok Term.true := by
    simp
  induction left with
  | nil => exact ⟨right, rfl⟩
  | cons head tail _ ih =>
    obtain ⟨joined, returned⟩ := ih accepted
    exact ⟨.cons head joined, by simp only [Erlang.erlang.«++/2», returned, Result.ok_bind]⟩
  | _ => exact False.elim (reject accepted)

@[simp] private theorem append_nil (input : Term)
    (accepted : is_reversible_list_1 input = .ok Term.true) :
    Erlang.erlang.«++/2» input .nil = .ok input := by
  have reject : (Result.ok Term.false : Result) ≠ .ok Term.true := by
    simp
  induction input with
  | nil => rfl
  | cons head tail _ ih => simp only [Erlang.erlang.«++/2», ih accepted, Result.ok_bind]
  | _ => exact False.elim (reject accepted)

private theorem append_assoc (left right suffix : Term)
    (accepted : is_reversible_list_1 left = .ok Term.true) :
    (Erlang.erlang.«++/2» left right >>= fun joined => Erlang.erlang.«++/2» joined suffix) =
      (Erlang.erlang.«++/2» right suffix >>= Erlang.erlang.«++/2» left) := by
  have reject : (Result.ok Term.false : Result) ≠ .ok Term.true := by
    simp
  induction left with
  | nil =>
    simp only [Erlang.erlang.«++/2», Result.ok_bind]
    exact (bind_pure (Erlang.erlang.«++/2» right suffix)).symm
  | cons head tail _ ih =>
    simpa only [Erlang.erlang.«++/2», bind_assoc, Result.ok_bind] using
      congrArg (fun outcome => outcome >>= fun rest => Result.ok (Term.cons head rest))
        (ih accepted)
  | _ => exact False.elim (reject accepted)

#lynx_pure def reverse_aux_2 : Term → Term → Result
  | .nil, acc => .ok acc
  | .cons head tail, acc => reverse_aux_2 tail (.cons head acc)
  | _, _ => .error (.error (.atom "function_clause"))

#lynx_pure def reverse_1 (input : Term) : Result := reverse_aux_2 input .nil

-- Handwritten Lean support, using the standard simp attribute.
@[simp] theorem reverse_aux_proper (input acc : Term)
    (accepted : is_reversible_list_1 input = .ok (.atom "true"))
    (accAccepted : is_reversible_list_1 acc = .ok (.atom "true")) :
    ∃ result, reverse_aux_2 input acc = .ok result ∧ is_reversible_list_1 result = .ok (.atom "true") := by
  have reject : (Result.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by simp
  induction input generalizing acc with
  | nil => exact ⟨acc, rfl, accAccepted⟩
  | cons head tail _ ih => exact ih (.cons head acc) accepted accAccepted
  | _ => exact False.elim (reject accepted)

@[simp] theorem reverse_aux_reverse (input acc : Term)
    (next : Term → Result α) (accepted : is_reversible_list_1 input = .ok (.atom "true")) :
    (do let result ← reverse_aux_2 input acc; let restored ← reverse_aux_2 result .nil; next restored) =
      (reverse_aux_2 acc input >>= next) := by
  have reject : (Result.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by simp
  induction input generalizing acc with
  | nil => rfl
  | cons head tail _ ih => exact ih (.cons head acc) accepted
  | _ => exact False.elim (reject accepted)

/- law reverse_result(list), requires: is_reversible_list(list),
     expects: (result -> is_reversible_list(result)) -/
#bench "erlang/reverse-result"
theorem reverse_result (input : Term) (valid : is_reversible_list_1 input = .ok Term.true) :
    ∃ result, reverse_1 input = .ok result ∧ is_reversible_list_1 result = .ok Term.true := by
  exact reverse_aux_proper input .nil valid rfl

/- law reverse_involution(list), requires: is_reversible_list(list),
     expects: reverse(reverse(list)) == list -/
def reverseInvolution (input : Term) : Result := do
  let reversed ← reverse_1 input
  let restored ← reverse_1 reversed
  Erlang.erlang.«==/2» restored input

#bench "erlang/reverse-involution"
theorem reverse_involution (input : Term) (valid : is_reversible_list_1 input = .ok Term.true) :
    reverseInvolution input = .ok Term.true := by
  unfold reverseInvolution reverse_1
  rw [reverse_aux_reverse input .nil _ valid]
  simp [reverse_aux_2, Erlang.erlang.«==/2»]

/-- The accumulator is appended after reversing the input. -/
theorem reverse_aux_acc (input acc : Term) :
    reverse_aux_2 input acc = (reverse_1 input >>= fun result => Erlang.erlang.«++/2» result acc) := by
  suffices ∀ start suffix extended, Erlang.erlang.«++/2» start suffix = .ok extended →
      reverse_aux_2 input extended =
        (reverse_aux_2 input start >>= fun result => Erlang.erlang.«++/2» result suffix) from
    this .nil acc acc rfl
  induction input with
  | nil => intro start suffix extended appended; exact appended.symm
  | cons head tail _ ih =>
    intro start suffix extended appended
    apply ih (.cons head start) suffix (.cons head extended)
    simp only [Erlang.erlang.«++/2», appended, Result.ok_bind]
  | _ => intros; rfl

/- law reverse_append(left, right),
     requires: is_reversible_list(left) and is_reversible_list(right),
     expects: reverse(left ++ right) == reverse(right) ++ reverse(left) -/
def reverseAppend (left right : Term) : Result := do
  let joined ← Erlang.erlang.«++/2» left right
  let reversed ← reverse_1 joined
  let right ← reverse_1 right
  let left ← reverse_1 left
  let expected ← Erlang.erlang.«++/2» right left
  Erlang.erlang.«==/2» reversed expected

#bench "erlang/reverse-append"
theorem reverse_append (left right : Term)
    (leftValid : is_reversible_list_1 left = .ok Term.true)
    (rightValid : is_reversible_list_1 right = .ok Term.true) :
    reverseAppend left right = .ok Term.true := by
  obtain ⟨reversedRight, rightReturned, rightProper⟩ := reverse_aux_proper right .nil rightValid rfl
  have step (head tail : Term) :
      reverse_1 (.cons head tail) =
        (reverse_1 tail >>= fun result => Erlang.erlang.«++/2» result (.cons head .nil)) :=
    reverse_aux_acc tail (.cons head .nil)
  have law (input : Term) (inputAccepted : is_reversible_list_1 input = .ok (.atom "true")) :
      (Erlang.erlang.«++/2» input right >>= reverse_1) =
        (reverse_1 input >>= Erlang.erlang.«++/2» reversedRight) := by
    have reject : (Result.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by simp
    induction input with
    | nil =>
      simp only [Erlang.erlang.«++/2», reverse_1, reverse_aux_2, Result.ok_bind,
        rightReturned, append_nil reversedRight rightProper]
    | cons head tail _ ih =>
      have assoc (middle : Term) :=
        append_assoc reversedRight middle (.cons head .nil) rightProper
      simpa only [Erlang.erlang.«++/2», step, bind_assoc, Result.ok_bind,
        assoc] using
        congrArg (fun output => output >>= fun result => Erlang.erlang.«++/2» result (.cons head .nil))
          (ih inputAccepted)
    | _ => exact False.elim (reject inputAccepted)
  obtain ⟨joined, appended⟩ := append_success left right leftValid
  obtain ⟨reversedLeft, leftReturned, _⟩ := reverse_aux_proper left .nil leftValid rfl
  obtain ⟨result, resultReturned⟩ := append_success reversedRight reversedLeft rightProper
  have joinedReturned := law left leftValid
  simp only [appended, reverse_1, leftReturned, Result.ok_bind, resultReturned] at joinedReturned
  simp [reverseAppend, reverse_1, appended, joinedReturned, leftReturned,
    rightReturned, resultReturned, Erlang.erlang.«==/2»]

end LynxTest.Integration.Reverse
