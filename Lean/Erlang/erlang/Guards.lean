module

public import Lynx.Term
public import Lynx.Term.Bitstring
public import Lynx.Tactic

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

-- Keep binary64 rounding out of proof search over Erlang result shapes.
#lynx_pure @[lynx_opaque] private def floatResult (value : Option Term.FiniteFloat) : Result :=
  match value with
  | some value => .ok (.float value)
  | none => throw (.error (.atom "badarith"))

@[simp] private theorem floatResult_ok_iff (value : Option Term.FiniteFloat) (result : Term) :
    floatResult value = .ok result ↔ ∃ f, value = some f ∧ result = .float f := by
  cases value <;> simp [floatResult, eq_comm]

-- Preserve unknown operands until their numeric types are known. In particular,
-- integer-list proofs should not split the float cases before applying induction.
#lynx_pure @[lynx_opaque] def «+/2» : Term → Term → Result
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

/-- Short-circuit conjunction `Left andalso Right`.

The right operand is a thunk (`Unit → Result`), so it only runs when the left
operand evaluates to `true`. A non-boolean left operand `V` raises
`error({badarg, V})`, exactly like the Core Erlang that the Erlang compiler
generates for `andalso` (a `case` whose fallback clause calls
`erlang:error({badarg, V})`). Earlier versions raised the bare atom `badarg`,
which dropped the offending value and did not match Erlang. -/
-- Keep short-circuit branching behind its specification during proof search.
@[expose, lynx_opaque] def «andalso/2»
    (left : Result)
    (right : Unit → Result) : Result := do
  match ← left with
  | .atom "true" => right ()
  | .atom "false" => .ok Term.false
  | value => .error (.error (.tuple #[.atom "badarg", value]))

/-- Successful short-circuit conjunction records the actual intermediate state.
The right operand may return any term, not just a boolean. For acceptance goals
(`value = true`), simplification also eliminates the false-left branch. -/
@[simp low] theorem «andalso/2_run_ok_iff» (left : Result) (right : Unit → Result)
    (env final : Environment) (value : Term) (pure : Result.IsPure left) :
    «andalso/2» left right env = .ok value final ↔
      (left env = .ok (.atom "false") final ∧ value = .atom "false") ∨
      ∃ next, left env = .ok (.atom "true") next ∧
        right () next = .ok value final := by
  unfold «andalso/2»
  cases left <;> simp_all [Result.IsPure, Term.false, eq_comm, and_comm]
  split <;> simp_all [eq_comm, and_comm]

@[simp low] theorem «andalso/2_ok_iff» (left : Result) (right : Unit → Result)
    (value : Term) :
    «andalso/2» left right = .ok value ↔
      (left = .ok (.atom "false") ∧ value = .atom "false") ∨
      (left = .ok (.atom "true") ∧ right () = .ok value) := by
  cases left <;> simp_all [«andalso/2», Term.false, eq_comm, and_comm]
  split <;> simp_all [eq_comm, and_comm]

@[simp] theorem «andalso/2_pure» (left : Result) (right : Unit → Result)
    (leftPure : Result.IsPure left) (rightPure : Result.IsPure (right ())) :
    Result.IsPure («andalso/2» left right) := by
  unfold «andalso/2»
  apply Result.IsPure.bind left _ leftPure
  intro value
  cases value <;> simp [Result.IsPure]
  rename_i name
  by_cases isTrue : name = "true"
  · subst name; exact rightPure
  · by_cases isFalse : name = "false"
    · subst name; simp
    · simp [isTrue, isFalse]

end Erlang.erlang
