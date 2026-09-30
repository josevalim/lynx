module

public import Lynx.Term
public import Lynx.Term.Bitstring
public import Lynx.Pure

public section

/-! Stateless Erlang operators and their generated purity proofs. -/

namespace Erlang.erlang

open Lynx

#lynx_pure @[expose] def «is_integer/1» (input : Term) : Result :=
  .ok (match input with | .integer _ => Term.true | _ => Term.false)

#lynx_pure @[expose] def «is_float/1» (input : Term) : Result :=
  .ok (match input with | .float _ => Term.true | _ => Term.false)

#lynx_pure @[expose] def «is_bitstring/1» : Term → Result
  | .bitstring _ _ => .ok Term.true
  | _ => .ok Term.false

#lynx_pure @[expose] def «is_binary/1» : Term → Result
  | .bitstring bytes lastBits =>
      .ok (if bytes.size = 0 ∨ lastBits = 0 then Term.true else Term.false)
  | _ => .ok Term.false

#lynx_pure @[expose] def «bit_size/1» : Term → Result
  | .bitstring bytes lastBits =>
      .ok (.integer (Term.Bitstring.bitSize bytes lastBits))
  | _ => throw (.error (.atom "badarg"))

/-- Partial final bytes count as one byte, as in Erlang's `byte_size/1`. -/
#lynx_pure @[expose] def «byte_size/1» : Term → Result
  | .bitstring bytes _ => .ok (.integer bytes.size)
  | _ => throw (.error (.atom "badarg"))

/-- Expose the state-preserving callback even when passed without its argument. -/
@[simp] theorem «is_integer/1_function» :
    «is_integer/1» = fun input => Result.ok
      (match input with | .integer _ => Term.true | _ => Term.false) := rfl

#lynx_pure @[expose] def «is_list/1» : Term → Result
  | .nil => .ok Term.true
  | .cons _ _ => .ok Term.true
  | _ => .ok Term.false

-- Convert a successful binary64 operation or raise badarith.
#lynx_pure private def floatResult (value : Option Term.FiniteFloat) : Result :=
  match value with
  | some value => .ok (.float value)
  | none => throw (.error (.atom "badarith"))

@[simp] private theorem floatResult_ok_iff (value : Option Term.FiniteFloat) (result : Term) :
    floatResult value = .ok result ↔ ∃ f, value = some f ∧ result = .float f := by
  cases value <;> simp [floatResult, eq_comm]

#lynx_pure def «+/2» : Term → Term → Result
  | .integer x, .integer y => .ok (.integer (x + y))
  | .float x, .float y => floatResult (x.add y)
  | .integer x, .float y => floatResult (Term.FiniteFloat.ofInt x >>= (·.add y))
  | .float x, .integer y => floatResult (Term.FiniteFloat.ofInt y >>= x.add)
  | _, _ => throw (.error (.atom "badarith"))

@[simp↓] theorem «+/2_integers» (left right : Int) :
    «+/2» (.integer left) (.integer right) = .ok (.integer (left + right)) := by rfl

/-- An integer sum can only come from two integer operands. -/
@[simp↓] theorem «+/2_integer_ok_iff» (left right : Term) (sum : Int) :
    «+/2» left right = .ok (.integer sum) ↔
      ∃ x y, left = .integer x ∧ right = .integer y ∧ x + y = sum := by
  cases left <;> cases right <;> simp [«+/2», floatResult_ok_iff]

@[simp] theorem «+/2_floats» (left right : Term.FiniteFloat) :
    «+/2» (.float left) (.float right) =
      (match left.add right with
      | some result => .ok (.float result)
      | none => .error (.error (.atom "badarith"))) := by rfl

@[simp] theorem «+/2_integer_float» (left : Int) (right : Term.FiniteFloat) :
    «+/2» (.integer left) (.float right) =
      (match Term.FiniteFloat.ofInt left >>= (·.add right) with
      | some result => .ok (.float result)
      | none => .error (.error (.atom "badarith"))) := by rfl

@[simp] theorem «+/2_float_integer» (left : Term.FiniteFloat) (right : Int) :
    «+/2» (.float left) (.integer right) =
      (match Term.FiniteFloat.ofInt right >>= left.add with
      | some result => .ok (.float result)
      | none => .error (.error (.atom "badarith"))) := by rfl

#lynx_pure @[expose] def «==/2» (left right : Term) : Result :=
  .ok (if Term.compare left right = .eq then Term.true else Term.false)

#lynx_pure @[expose] def «/=/2» (left right : Term) : Result :=
  .ok (if Term.compare left right = .eq then Term.false else Term.true)

#lynx_pure @[expose] def «=:=/2» (left right : Term) : Result :=
  .ok (if Term.exactCompare left right = .eq then Term.true else Term.false)

#lynx_pure @[expose] def «=/=/2» (left right : Term) : Result :=
  .ok (if Term.exactCompare left right = .eq then Term.false else Term.true)

#lynx_pure @[expose] def «</2» (left right : Term) : Result :=
  .ok (if (Term.compare left right).isLT then Term.true else Term.false)

#lynx_pure @[expose] def «>/2» (left right : Term) : Result :=
  .ok (if (Term.compare left right).isGT then Term.true else Term.false)

#lynx_pure @[expose] def «=</2» (left right : Term) : Result :=
  .ok (if (Term.compare left right).isLE then Term.true else Term.false)

#lynx_pure @[expose] def «>=/2» (left right : Term) : Result :=
  .ok (if (Term.compare left right).isGE then Term.true else Term.false)

#lynx_pure @[expose] def «++/2» : Term → Term → Result
  | .nil, right => .ok right
  | .cons head tail, right => do
      let rest ← «++/2» tail right
      .ok (.cons head rest)
  | _, _ => throw (.error (.atom "badarg"))

end Erlang.erlang
