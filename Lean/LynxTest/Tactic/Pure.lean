module

import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.Tactic.Pure
open Lynx

-- The coercion exposes only the named operation, not the scheduler body.
theorem callable_result (computation : Result) (env : Environment) :
    computation env = computation.run env := rfl

theorem run_ok (value : Term) (env : Environment) :
    (Result.ok value).run env = .ok value env := by simp

theorem one_bit_size :
    Modules.Erlang.bit_size_1 (.bitstring ⟨#[128]⟩ 1) = .ok (.integer 1) := by
  rfl

theorem float_zero_value :
    Term.FiniteFloat.toRat ⟨false, 0, 0⟩ = 0 := rfl

theorem binary_is_bitstring (input : Term)
    (accepted : Accepted (Modules.Erlang.is_binary_1 input)) :
    Accepted (Modules.Erlang.is_bitstring_1 input) := by
  lynx_solve

theorem bitstring_size_is_integer (input : Term)
    (accepted : Accepted (Modules.Erlang.is_bitstring_1 input)) :
    Accepted (do
      let size ← Modules.Erlang.bit_size_1 input
      Modules.Erlang.is_integer_1 size) := by
  lynx_solve

theorem bitstring_byte_size_is_integer (input : Term)
    (accepted : Accepted (Modules.Erlang.is_bitstring_1 input)) :
    Accepted (do
      let size ← Modules.Erlang.byte_size_1 input
      Modules.Erlang.is_integer_1 size) := by
  lynx_solve

#lynx_pure def classify (input : Term) : Result :=
  .ok (match input with | .integer _ => Term.true | _ => Term.false)

/-- Purity composes through calls already checked by `#lynx_pure`. -/
#lynx_pure def classifyTwice (input : Term) : Result := do
  let first ← classify input
  classify first

/-- Unary structural recursion can be checked automatically. -/
#lynx_pure def proper : Term → Result
  | .nil => .ok Term.true
  | .cons _ tail => proper tail
  | _ => .ok Term.false

/-- Nested matching on list elements remains structurally recursive on the tail. -/
#lynx_pure def properIntegers : Term → Result
  | .nil => .ok Term.true
  | .cons (.integer _) tail => properIntegers tail
  | .cons _ _ => .ok Term.false
  | _ => .ok Term.false

theorem execution_reuses_purity (input : Term) (env final : Environment) :
    classifyTwice input env = .ok Term.false final ↔
      classifyTwice input = .ok Term.false ∧ env = final := by
  simp

run_cmd do
  let some doc ← Lean.findSimpleDocString? (← Lean.getEnv) ``LynxTest.Tactic.Pure.classifyTwice
    | throwError "classifyTwice documentation was not registered"
  unless doc.startsWith "Purity composes through calls already checked by `#lynx_pure`." do
    throwError "unexpected classifyTwice documentation: {doc}"

end LynxTest.Tactic.Pure

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Tactic.Pure
