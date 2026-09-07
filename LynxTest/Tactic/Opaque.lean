import Lynx

namespace LynxTest.Tactic.Opaque
open Lynx

@[lynx_opaque] def copy : Term → Result
  | .cons head tail => do
    let copied ← copy tail
    .ok (.cons head copied)
  | input => .ok input

-- The annotation supplies neither a specification nor permission to inspect
-- the recursive implementation. This claim is true but needs a library lemma.
theorem missing_specification : True := by
  fail_if_success
    have : ∀ input, copy input = .ok input := by lynx_verify
  trivial

@[simp] theorem copy_eq (input : Term) : copy input = .ok input := by
  induction input <;> simp_all [copy]

def twice (input : Term) : Result := do copy (← copy input)

theorem through_wrapper (input : Term) : twice input = .ok input := by lynx_verify

theorem rejects_false_claim : True := by
  fail_if_success
    have : copy (.integer 1) = .ok (.integer 2) := by lynx_verify
  trivial

@[lynx_opaque] def guarded (f : Nat → Nat) : Result := .ok (.integer (f 0))

@[simp] theorem guarded_eq (f : Nat → Nat) (h : ∀ n, f n = n) :
    guarded f = .ok (.integer 0) := by simp [guarded, h]

theorem quantified_premise (f : Nat → Nat) (h : ∀ n, f n = n) :
    guarded f = .ok (.integer 0) := by lynx_verify

@[lynx_opaque] def expectsInteger : Term → Result
  | .integer _ => .ok (.atom "true")
  | _ => .ok (.atom "false")

@[simp] theorem expectsInteger_iff (input : Term) :
    expectsInteger input = .ok (.atom "true") ↔ ∃ n, input = .integer n := by
  cases input <;> simp [expectsInteger]

@[lynx_opaque] def increment : Term → Result
  | .integer n => .ok (.integer (n + 1))
  | _ => .error (.error (.atom "badarith"))

@[simp] theorem increment_eq (n : Int) :
    increment (.integer n) = .ok (.integer (n + 1)) := rfl

theorem representation_equality (input : Term) (h : Accepted (expectsInteger input)) :
    ∃ n, increment input = .ok (.integer (n + 1)) := by lynx_verify

end LynxTest.Tactic.Opaque
