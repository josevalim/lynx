import Lynx.Contract
import Lynx.Modules.Erlang
import Lynx.Term

namespace LynxTest.Integration.TermSum

open Lynx Lynx.Modules

/-!
An operational translation of:

    def sum([]), do: 0
    def sum([x | xs]), do: x + sum(xs)

The recursive call is evaluated before `Erlang.add`, matching the evaluation of
`x + sum(xs)`. Monadic sequencing propagates any exception from the tail.
-/
def sumTerm : Term → Outcome Term
  | .nil => .value (.integer 0)
  | .cons x xs => do
      let subtotal ← sumTerm xs
      Erlang.add x subtotal
  | _ => throw (.error (.atom "function_clause"))

/-! Small assumed translation of `Enum.all?/2` used by the contract. -/

def enumAllTerm (predicate : Term → Outcome Term) : Term → Outcome Term
  | .nil => .value Term.true
  | .cons head tail => do
      let predicateResult ← predicate head
      match predicateResult with
      | .atom "false" => .value Term.false
      | .nil => .value Term.false
      | _ => enumAllTerm predicate tail
  | _ => throw (.error (.atom "badarg"))

/-!
Translations of:

    expects is_list(arg) and Enum.all?(arg, &is_integer/1)
    ensures (result -> is_integer(result))
-/
def sumPre (arg : Term) : Outcome Term :=
  Erlang.andalso (Erlang.is_list arg) (fun _ => enumAllTerm Erlang.is_integer arg)

def sumPost (_arg result : Term) : Outcome Term :=
  Erlang.is_integer result

/-!
`SatisfiesUnary` is the generic contract shape shared by unary functions. This
theorem is the proof obligation specific to `sum`: starting only from the fact
that the translated precondition returned `true`, it follows the same cases and
recursion as `sumTerm` and proves that the translated postcondition returns
`true` for the actual result.

The proof is deliberately explicit for now. A verifier can later generate this
proof term or replace the body with a tactic such as `lynx_verify` that performs
the same symbolic case analysis and induction automatically.
-/
theorem sum_satisfies_contract :
    SatisfiesUnary sumTerm sumPre sumPost := by
  intro input accepted
  induction input with
  | integer n =>
      simp_all [accepts, sumPre, Erlang.is_list, Erlang.andalso,
        Term.true, Term.false]
  | atom name =>
      simp_all [accepts, sumPre, Erlang.is_list, Erlang.andalso,
        Term.true, Term.false]
  | nil =>
      exact ⟨.integer 0, rfl, rfl⟩
  | cons head tail headHypothesis tailHypothesis =>
      cases head with
      | integer x =>
          have tailAccepted : accepts (sumPre tail) := by
            cases tail <;>
              simp [accepts, sumPre, Erlang.is_list, Erlang.is_integer,
                enumAllTerm, Erlang.andalso, Term.true, Term.false] at accepted ⊢ <;>
              assumption
          obtain ⟨result, tailResult, postAccepted⟩ :=
            tailHypothesis tailAccepted
          cases result with
          | integer total =>
              exact ⟨.integer (x + total), by
                simp [sumTerm, tailResult, Erlang.add], rfl⟩
          | atom name =>
              simp [accepts, sumPost, Erlang.is_integer, Term.true, Term.false]
                at postAccepted
          | nil =>
              simp [accepts, sumPost, Erlang.is_integer, Term.true, Term.false]
                at postAccepted
          | cons nestedHead nestedTail =>
              simp [accepts, sumPost, Erlang.is_integer, Term.true, Term.false]
                at postAccepted
      | atom name =>
          simp [accepts, sumPre, Erlang.is_list, Erlang.is_integer,
            enumAllTerm, Erlang.andalso, Term.true, Term.false] at accepted
      | nil =>
          simp [accepts, sumPre, Erlang.is_list, Erlang.is_integer,
            enumAllTerm, Erlang.andalso, Term.true, Term.false] at accepted
      | cons nestedHead nestedTail =>
          simp [accepts, sumPre, Erlang.is_list, Erlang.is_integer,
            enumAllTerm, Erlang.andalso, Term.true, Term.false] at accepted

end LynxTest.Integration.TermSum
