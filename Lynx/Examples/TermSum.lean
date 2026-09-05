import Lynx.Contract
import Lynx.Term

namespace Lynx.Examples.TermSum

open Lynx

def addTerm : Term → Term → Outcome
  | .integer x, .integer y => .value (.integer (x + y))
  | _, _ => .raised (.error (.atom "badarith"))

/-!
An operational translation of:

    def sum([]), do: 0
    def sum([x | xs]), do: x + sum(xs)

The recursive call is evaluated before `addTerm`, matching the evaluation of
`x + sum(xs)`. Any exception from the tail is propagated.
-/
def sumTerm : Term → Outcome
  | .nil => .value (.integer 0)
  | .cons x xs =>
      match sumTerm xs with
      | .value subtotal => addTerm x subtotal
      | .raised exception => .raised exception
  | _ => .raised (.error (.atom "function_clause"))

def encodeIntList : List Int → Term
  | [] => .nil
  | x :: xs => .cons (.integer x) (encodeIntList xs)

/-! Small assumed translations of the Elixir operations used by the contract. -/

def isIntegerTerm : Term → Outcome
  | .integer _ => .value trueTerm
  | _ => .value falseTerm

def isListTerm : Term → Outcome
  | .nil => .value trueTerm
  | .cons _ _ => .value trueTerm
  | _ => .value falseTerm

def enumAllTerm (predicate : Term → Outcome) : Term → Outcome
  | .nil => .value trueTerm
  | .cons head tail =>
      match predicate head with
      | .value (.atom "false") => .value falseTerm
      | .value .nil => .value falseTerm
      | .value _ => enumAllTerm predicate tail
      | .raised exception => .raised exception
  | _ => .raised (.error (.atom "badarg"))

def andTerm (left : Outcome) (right : Unit → Outcome) : Outcome :=
  match left with
  | .value (.atom "true") => right ()
  | .value (.atom "false") => .value falseTerm
  | .value _ => .raised (.error (.atom "badarg"))
  | .raised exception => .raised exception

/-!
Translations of:

    @pre "is_list(arg) and Enum.all?(arg, &is_integer/1)"
    @post "is_integer(result)"
-/
def sumPre (arg : Term) : Outcome :=
  andTerm (isListTerm arg) (fun _ => enumAllTerm isIntegerTerm arg)

def sumPost (_arg result : Term) : Outcome :=
  isIntegerTerm result

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
      simp_all [accepts, sumPre, isListTerm, andTerm, trueTerm, falseTerm]
  | atom name =>
      simp_all [accepts, sumPre, isListTerm, andTerm, trueTerm, falseTerm]
  | nil =>
      exact ⟨.integer 0, rfl, rfl⟩
  | cons head tail headHypothesis tailHypothesis =>
      cases head with
      | integer x =>
          have tailAccepted : accepts (sumPre tail) := by
            cases tail <;>
              simp [accepts, sumPre, isListTerm, isIntegerTerm,
                enumAllTerm, andTerm, trueTerm, falseTerm] at accepted ⊢ <;>
              assumption
          obtain ⟨result, tailResult, postAccepted⟩ :=
            tailHypothesis tailAccepted
          cases result with
          | integer total =>
              exact ⟨.integer (x + total), by
                simp [sumTerm, tailResult, addTerm], rfl⟩
          | atom name =>
              simp [accepts, sumPost, isIntegerTerm, trueTerm, falseTerm]
                at postAccepted
          | nil =>
              simp [accepts, sumPost, isIntegerTerm, trueTerm, falseTerm]
                at postAccepted
          | cons nestedHead nestedTail =>
              simp [accepts, sumPost, isIntegerTerm, trueTerm, falseTerm]
                at postAccepted
      | atom name =>
          simp [accepts, sumPre, isListTerm, isIntegerTerm,
            enumAllTerm, andTerm, trueTerm, falseTerm] at accepted
      | nil =>
          simp [accepts, sumPre, isListTerm, isIntegerTerm,
            enumAllTerm, andTerm, trueTerm, falseTerm] at accepted
      | cons nestedHead nestedTail =>
          simp [accepts, sumPre, isListTerm, isIntegerTerm,
            enumAllTerm, andTerm, trueTerm, falseTerm] at accepted

end Lynx.Examples.TermSum
