module

import all Erlang.erlang
import all Erlang.erlang.Guards
import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.Pure
open Lynx

-- The coercion exposes only the named operation, not the scheduler body.
theorem callable_result (computation : Result) (env : Environment) :
    computation env = computation.run env := rfl

theorem run_ok (value : Term) (env : Environment) :
    (Result.ok value).run env = .ok value env := by simp

theorem one_bit_size :
    Erlang.erlang.«bit_size/1» (.bitstring ⟨#[128]⟩ 1) = .ok (.integer 1) := by
  rfl

theorem float_zero_value :
    Term.FiniteFloat.toRat ⟨false, 0, 0⟩ = 0 := rfl

-- The integer shortcut must retain symbolic float and mixed-addition proofs.
theorem float_addition (left right result : Term.FiniteFloat)
    (sum : left.add right = some result) :
    Erlang.erlang.«+/2» (.float left) (.float right) = .ok (.float result) := by
  simp [Erlang.erlang.«+/2», Erlang.erlang.floatResult, sum]

theorem mixed_addition (integer : Int) (converted right result : Term.FiniteFloat)
    (conversion : Term.FiniteFloat.ofInt integer = some converted)
    (sum : converted.add right = some result) :
    Erlang.erlang.«+/2» (.integer integer) (.float right) = .ok (.float result) := by
  simp [Erlang.erlang.«+/2», Erlang.erlang.floatResult, conversion, sum]

theorem mixed_addition_reversed (integer : Int) (converted left result : Term.FiniteFloat)
    (conversion : Term.FiniteFloat.ofInt integer = some converted)
    (sum : left.add converted = some result) :
    Erlang.erlang.«+/2» (.float left) (.integer integer) = .ok (.float result) := by
  simp [Erlang.erlang.«+/2», Erlang.erlang.floatResult, conversion, sum]


theorem binary_is_bitstring (input : Term)
    (accepted : Erlang.erlang.«is_binary/1» input = .ok Term.true) :
    Erlang.erlang.«is_bitstring/1» input = .ok Term.true := by
  cases input <;> simp_all [Erlang.erlang.«is_binary/1»,
    Erlang.erlang.«is_bitstring/1», Term.true, Term.false]

theorem bitstring_size_is_integer (input : Term)
    (accepted : Erlang.erlang.«is_bitstring/1» input = .ok Term.true) :
    (do let size ← Erlang.erlang.«bit_size/1» input
        Erlang.erlang.«is_integer/1» size) = .ok Term.true := by
  cases input <;> simp_all [Erlang.erlang.«is_bitstring/1»,
    Erlang.erlang.«bit_size/1», Erlang.erlang.«is_integer/1», Term.true, Term.false]

theorem bitstring_byte_size_is_integer (input : Term)
    (accepted : Erlang.erlang.«is_bitstring/1» input = .ok Term.true) :
    (do let size ← Erlang.erlang.«byte_size/1» input
        Erlang.erlang.«is_integer/1» size) = .ok Term.true := by
  cases input <;> simp_all [Erlang.erlang.«is_bitstring/1»,
    Erlang.erlang.«byte_size/1», Erlang.erlang.«is_integer/1», Term.true, Term.false]

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

-- Explicit binds in translated mutual calls retain the group's induction hypotheses.
#lynx_pure mutual
  def sumLeft : Term → Result
    | .nil => .ok (.integer 0)
    | .cons x xs => Result.bind (sumRight xs) fun total => Erlang.erlang.«+/2» x total
    | _ => .error (.error (.atom "function_clause"))
  def sumRight : Term → Result
    | .nil => .ok (.integer 0)
    | .cons x xs => Result.bind (sumLeft xs) fun total => Erlang.erlang.«+/2» x total
    | _ => .error (.error (.atom "function_clause"))
end

example (input : Term) : Result.IsPure (sumLeft input) := by simp
example (input : Term) : Result.IsPure (sumRight input) := by simp

theorem execution_reuses_purity (input : Term) (env final : Environment) :
    classifyTwice input env = .ok Term.false final ↔
      classifyTwice input = .ok Term.false ∧ env = final := by
  simp

run_cmd do
  let some doc ← Lean.findSimpleDocString? (← Lean.getEnv) ``LynxTest.Pure.classifyTwice
    | throwError "classifyTwice documentation was not registered"
  unless doc.startsWith "Purity composes through calls already checked by `#lynx_pure`." do
    throwError "unexpected classifyTwice documentation: {doc}"

-- Failed purity checks must never register an incomplete purity theorem.
/--
error: unsolved goals
⊢ False
---
error: #lynx_pure could not prove purity; refusing an incomplete proof
-/
#guard_msgs in
#lynx_pure def readsEnvironment : Result := .get fun _ => .ok .nil

/--
error: unsolved goals
⊢ False
---
error: #lynx_pure could not prove purity; refusing an incomplete proof
-/
#guard_msgs in
#lynx_pure def writesEnvironment : Result := .set {} (.ok .nil)

end LynxTest.Pure

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Pure
