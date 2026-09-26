module

import Lynx
meta import all Lynx.Tactic
meta import LynxTest.ProofAudit

namespace LynxTest.Tactic.Specifications
open Lynx Lynx.Modules
set_option Elab.async false

-- One operation has several result shapes. The caller's domain determines
-- which specification is usable; neither its name nor its body is special.
#lynx_pure def next : Term → Result
  | .integer n => .ok (.integer (n + 1))
  | .tuple values => .ok (.tuple values)
  | _ => .error (.error (.atom "badarg"))

@[simp↓] theorem next_integer (n : Int) :
    next (.integer n) = .ok (.integer (n + 1)) := by rfl

@[simp] theorem next_tuple (values : Array Term) :
    next (.tuple values) = .ok (.tuple values) := by rfl

-- Check discovery itself, so successful proofs cannot mask missing hints.
private meta def checkShapes (function : Lean.Name) (expected : Array Lean.Name) :
    Lean.Elab.Command.CommandElabM Unit := Lean.Elab.Command.liftTermElabM do
  let actual ← Lynx.Tactic.returnConstructors function #[← Lean.Meta.getSimpTheorems]
  unless actual.size == expected.size && expected.all actual.contains do
    throwError "unexpected return shapes: {actual} (expected {expected})"

run_cmd checkShapes ``next #[``Term.integer, ``Term.tuple]

section
attribute [-simp] next_tuple
run_cmd checkShapes ``next #[``Term.integer]
end

run_cmd checkShapes ``next #[``Term.integer, ``Term.tuple]

@[lynx_opaque] def hidden (_ : Term) : Result := .ok (.integer 0)
theorem hidden_eq (input : Term) : hidden input = .ok (.integer 0) := rfl

run_cmd checkShapes ``hidden #[]
section
attribute [local simp] hidden_eq
run_cmd checkShapes ``hidden #[``Term.integer]
end
run_cmd checkShapes ``hidden #[]

-- A transparent function's simp rule does not create an opaque boundary.
def transparent (_ : Term) : Result := .ok (.integer 0)
@[simp] theorem transparent_eq (input : Term) :
    transparent input = .ok (.integer 0) := rfl
run_cmd checkShapes ``transparent #[``Term.integer]

-- A wrapper's own theorem and its callee's theorem both contribute candidates.
def wrapper : Term → Result
  | .nil => .ok .nil
  | input => next input
@[simp] theorem wrapper_nil : wrapper .nil = .ok .nil := rfl
run_cmd checkShapes ``wrapper #[``Term.nil, ``Term.integer, ``Term.tuple]

-- Opacity stops body traversal without suppressing the wrapper's own rules.
attribute [lynx_opaque] wrapper
run_cmd checkShapes ``wrapper #[``Term.nil]

#lynx_pure def count : Term → Result
  | .nil => .ok (.integer 0)
  | .cons _ tail => do next (← count tail)
  | _ => .error (.error (.atom "function_clause"))

#lynx_pure def properList : Term → Result
  | .nil => .ok Term.true
  | .cons _ tail => properList tail
  | _ => .ok Term.false

def integerResult (_ result : Term) : Result := Erlang.is_integer_1 result

theorem count_contract : Satisfies count properList integerResult := by
  lynx_verify

theorem tuple_rule (values : Array Term) :
    next (.tuple values) = .ok (.tuple values) := by lynx_solve

-- A specification with a premise cannot justify calls outside its domain.
@[lynx_opaque] def positive (n : Int) : Result :=
  if n > 0 then .ok (.integer n) else .error (.error (.atom "badarg"))

@[simp] theorem positive_spec (n : Int) (h : n > 0) :
    positive n = .ok (.integer n) := by simp [positive, h]

theorem guarded_rule (n : Int) (h : n > 0) :
    positive n = .ok (.integer n) := by lynx_solve

@[simp] theorem positive_zero : positive 0 = .error (.error (.atom "badarg")) := by
  simp [positive]

theorem outside_specification : positive 0 = .error (.error (.atom "badarg")) := by
  lynx_solve

theorem rejects_invalid_claims : True := by
  fail_if_success
    have : ∀ n, positive n = .ok (.integer n) := by lynx_solve
  fail_if_success
    have : Satisfies count properList (fun _ result => Erlang.is_float_1 result) := by
      lynx_verify
  fail_if_success
    have : Satisfies count (fun _ => .ok Term.true) integerResult := by lynx_verify
  trivial

end LynxTest.Tactic.Specifications

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Tactic.Specifications
