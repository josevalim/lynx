/-
defmodule Reverse do
  expects is_proper_list(list)
  ensures (result -> is_proper_list(result))
  property reverse(reverse(list)) == list
  def reverse(list), do: reverse_aux(list, [])

  defp reverse_aux([], acc), do: acc
  defp reverse_aux([head | tail], acc), do: reverse_aux(tail, [head | acc])
end
-/
import LynxTest.Bench

namespace LynxTest.Integration.Reverse
open Lynx Lynx.Modules
set_option Elab.async false

abbrev properList (input : Term) : Outcome Term :=
  Extensions.is_proper_list input

def reverseAux : Term → Term → Outcome Term
  | .nil, acc => .value acc
  | .cons head tail, acc => reverseAux tail (.cons head acc)
  | _, _ => .raised (.error (.atom "function_clause"))

def reverseTerm (input : Term) : Outcome Term := reverseAux input .nil

def reverseEnsures (_input result : Term) : Outcome Term := properList result

def reverseInvolution (input : Term) : Outcome Term := do
  let reversed ← reverseTerm input
  let restored ← reverseTerm reversed
  Erlang.equal restored input

-- Handwritten Lean support, using the standard simp attribute.
@[simp] theorem reverseAux_proper_spec (input acc : Term)
    (accepted : properList input = .value (.atom "true"))
    (accAccepted : properList acc = .value (.atom "true")) :
    ∃ result, reverseAux input acc = .value result ∧ properList result = .value (.atom "true") := by
  have reject : ¬ Accepted (.value (.atom "false")) := by decide
  induction input generalizing acc with
  | nil => exact ⟨acc, rfl, accAccepted⟩
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih => exact ih (.cons head acc) accepted accAccepted

@[simp] theorem reverseAux_reverse_spec (input acc : Term)
    (next : Term → Outcome α) (accepted : properList input = .value (.atom "true")) :
    (do let result ← reverseAux input acc; let restored ← reverseAux result .nil; next restored) =
      (reverseAux acc input >>= next) := by
  have reject : ¬ Accepted (.value (.atom "false")) := by decide
  induction input generalizing acc with
  | nil => rfl
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih => exact ih (.cons head acc) accepted

#bench "erlang/reverse-contract"
theorem reverse_contract_spec : Satisfies reverseTerm properList reverseEnsures := by
  lynx_verify
  exact reverseAux_proper_spec _ _ ‹_› rfl

#bench "erlang/reverse-involution"
theorem reverse_involution_spec : Property properList reverseInvolution := by
  lynx_verify

end LynxTest.Integration.Reverse
