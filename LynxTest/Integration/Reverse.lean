/-
defmodule Reverse do
  expects is_proper_list(list)
  ensures (result -> is_proper_list(result))
  property reverse(reverse(list)) == list
  property reverse(left ++ right) == reverse(right) ++ reverse(left)
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

/-- Both lists must satisfy the reverse expectation. -/
def reverseAppendExpects (args : Term × Term) : Outcome Term :=
  Erlang.andalso (properList args.1) (fun _ => properList args.2)

def reverseAppend (args : Term × Term) : Outcome Term := do
  let joined ← Erlang.append args.1 args.2
  let reversed ← reverseTerm joined
  let right ← reverseTerm args.2
  let left ← reverseTerm args.1
  let expected ← Erlang.append right left
  Erlang.equal reversed expected

/-- The accumulator is appended after reversing the input. -/
theorem reverseAux_acc_spec (input acc : Term) :
    reverseAux input acc = (reverseTerm input >>= fun result => Erlang.append result acc) := by
  suffices ∀ start suffix extended, Erlang.append start suffix = .value extended →
      reverseAux input extended =
        (reverseAux input start >>= fun result => Erlang.append result suffix) from
    this .nil acc acc rfl
  induction input with
  | nil => intro start suffix extended appended; exact appended.symm
  | integer _ => intros; rfl
  | atom _ => intros; rfl
  | cons head tail _ ih =>
    intro start suffix extended appended
    apply ih (.cons head start) suffix (.cons head extended)
    simp only [Erlang.append, appended, Outcome.bind_value_spec]

#bench "erlang/reverse-append"
theorem reverse_append_spec : Property reverseAppendExpects reverseAppend := by
  constructor
  · exact ⟨(.nil, .nil), rfl⟩
  · intro ⟨left, right⟩ accepted
    have both : properList left = .value (.atom "true") ∧
        properList right = .value (.atom "true") := by
      change Accepted (Erlang.andalso (properList left) (fun _ => properList right)) at accepted
      unfold Erlang.andalso at accepted
      split at accepted
      · exact ⟨‹_›, accepted⟩
      all_goals simp_all [Accepted, Term.true, Term.false]
    obtain ⟨reversedRight, rightReturned, rightProper⟩ := reverseAux_proper_spec right .nil both.2 rfl
    have step (head tail : Term) :
        reverseTerm (.cons head tail) =
          (reverseTerm tail >>= fun result => Erlang.append result (.cons head .nil)) :=
      reverseAux_acc_spec tail (.cons head .nil)
    have law (input : Term) (inputAccepted : properList input = .value (.atom "true")) :
        (Erlang.append input right >>= reverseTerm) =
          (reverseTerm input >>= Erlang.append reversedRight) := by
      have reject : ¬ Accepted (.value (.atom "false")) := by decide
      induction input with
      | nil =>
        simp only [Erlang.append, reverseTerm, reverseAux, Outcome.bind_value_spec,
          rightReturned, Erlang.append_nil_spec reversedRight rightProper]
      | integer _ => exact False.elim (reject inputAccepted)
      | atom _ => exact False.elim (reject inputAccepted)
      | cons head tail _ ih =>
        have assoc (middle : Term) :=
          Erlang.append_assoc_spec reversedRight middle (.cons head .nil) rightProper
        simpa only [Erlang.append, step, Outcome.bind_assoc_spec, Outcome.bind_value_spec,
          assoc] using
          congrArg (fun output => output >>= fun result => Erlang.append result (.cons head .nil))
            (ih inputAccepted)
    obtain ⟨joined, appended⟩ := Erlang.append_success_spec left right both.1
    obtain ⟨reversedLeft, leftReturned, _⟩ := reverseAux_proper_spec left .nil both.1 rfl
    obtain ⟨result, resultReturned⟩ := Erlang.append_success_spec reversedRight reversedLeft rightProper
    have joinedReturned := law left both.1
    simp only [appended, reverseTerm, leftReturned, Outcome.bind_value_spec, resultReturned] at joinedReturned
    simp only [Accepted, reverseAppend, reverseTerm, appended, Outcome.bind_value_spec,
      joinedReturned, leftReturned, rightReturned, resultReturned, Erlang.equal, ite_true, Term.true]

end LynxTest.Integration.Reverse
