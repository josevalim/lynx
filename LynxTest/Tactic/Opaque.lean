import Lynx

namespace LynxTest.Tactic.Opaque
open Lynx

@[lynx_opaque] def copy : Term → Outcome Term
  | .cons head tail => do
    let copied ← copy tail
    .value (.cons head copied)
  | input => .value input

-- The annotation supplies neither a specification nor permission to inspect
-- the recursive implementation. This claim is true but needs a library lemma.
theorem missing_specification : True := by
  fail_if_success
    have : ∀ input, copy input = .value input := by lynx_verify
  trivial

@[simp] theorem copy_spec (input : Term) : copy input = .value input := by
  induction input <;> simp_all [copy]

def twice (input : Term) : Outcome Term := do copy (← copy input)

theorem through_wrapper (input : Term) : twice input = .value input := by lynx_verify

theorem rejects_false_claim : True := by
  fail_if_success
    have : copy (.integer 1) = .value (.integer 2) := by lynx_verify
  trivial

@[lynx_opaque] def guarded (f : Nat → Nat) : Outcome Term := .value (.integer (f 0))

@[simp] theorem guarded_spec (f : Nat → Nat) (h : ∀ n, f n = n) :
    guarded f = .value (.integer 0) := by simp [guarded, h]

theorem quantified_premise (f : Nat → Nat) (h : ∀ n, f n = n) :
    guarded f = .value (.integer 0) := by lynx_verify

@[lynx_opaque] def expectsInteger : Term → Outcome Term
  | .integer _ => .value (.atom "true")
  | _ => .value (.atom "false")

@[simp] theorem expectsInteger_spec (input : Term) :
    expectsInteger input = .value (.atom "true") ↔ ∃ n, input = .integer n := by
  cases input <;> simp [expectsInteger]

@[lynx_opaque] def increment : Term → Outcome Term
  | .integer n => .value (.integer (n + 1))
  | _ => .raised (.error (.atom "badarith"))

@[simp] theorem increment_spec (n : Int) :
    increment (.integer n) = .value (.integer (n + 1)) := rfl

theorem representation_equality (input : Term) (h : Accepted (expectsInteger input)) :
    ∃ n, increment input = .value (.integer (n + 1)) := by lynx_verify

end LynxTest.Tactic.Opaque
