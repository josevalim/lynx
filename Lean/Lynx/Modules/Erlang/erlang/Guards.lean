module

public import Lynx.Term
public import Lynx.Term.Bitstring

public section

/-! Stateless Erlang operators and their generated purity proofs. -/

namespace Erlang.erlang

open Lynx

@[expose] def «and/2» : Term → Term → Except Exception Term
  | .atom "true", .atom "true" => .ok Term.true
  | .atom "true", .atom "false" | .atom "false", .atom "true"
  | .atom "false", .atom "false" => .ok Term.false
  | _, _ => .error (.error (.atom "badarg"))

@[expose] def «or/2» : Term → Term → Except Exception Term
  | .atom "false", .atom "false" => .ok Term.false
  | .atom "true", .atom "true" | .atom "true", .atom "false"
  | .atom "false", .atom "true" => .ok Term.true
  | _, _ => .error (.error (.atom "badarg"))

@[expose] def «not/1» : Term → Except Exception Term
  | .atom "true" => .ok Term.false
  | .atom "false" => .ok Term.true
  | _ => .error (.error (.atom "badarg"))

@[expose] def «is_atom/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .atom _ => Term.true | _ => Term.false)

@[expose] def «is_tuple/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .tuple _ => Term.true | _ => Term.false)

@[expose] def «tuple_size/1» : Term → Except Exception Term
  | .tuple entries => .ok (.integer entries.size)
  | _ => throw (.error (.atom "badarg"))

/-- Erlang tuple positions start at one; invalid positions raise badarg. -/
@[expose] def «element/2» : Term → Term → Except Exception Term
  | .integer index, .tuple entries =>
      match if 1 ≤ index then entries[index.toNat - 1]? else none with
      | some value => .ok value
      | none => throw (.error (.atom "badarg"))
  | _, _ => throw (.error (.atom "badarg"))

/-- Replace an existing entry using Erlang's one-based tuple positions. -/
@[expose] def «setelement/3» (index input value : Term) : Except Exception Term :=
  match index, input with
  | .integer n, .tuple entries =>
    if valid : 1 ≤ n ∧ n ≤ entries.size then
      .ok (.tuple (entries.set (n.toNat - 1) value (h := by omega)))
    else throw (.error (.atom "badarg"))
  | _, _ => throw (.error (.atom "badarg"))

@[expose] def «is_pid/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .pid _ => Term.true | _ => Term.false)

@[expose] def «is_reference/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .reference _ => Term.true | _ => Term.false)

@[expose] def «is_function/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .function _ _ _ => Term.true | _ => Term.false)

@[expose] def «is_number/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .integer _ | .float _ => Term.true | _ => Term.false)

@[expose] def «is_boolean/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .atom "true" | .atom "false" => Term.true | _ => Term.false)

@[expose] def «is_integer/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .integer _ => Term.true | _ => Term.false)

/-- Inclusive integer bounds. Invalid bounds raise badarg, even for noninteger inputs. -/
@[expose] def «is_integer/3» (input lower upper : Term) : Except Exception Term :=
  match lower, upper with
  | .integer lo, .integer hi =>
    .ok (match input with
      | .integer n => if lo ≤ n ∧ n ≤ hi then Term.true else Term.false
      | _ => Term.false)
  | _, _ => throw (.error (.atom "badarg"))

@[expose] def «is_map/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .map _ => Term.true | _ => Term.false)

@[expose] def «is_float/1» (input : Term) : Except Exception Term :=
  .ok (match input with | .float _ => Term.true | _ => Term.false)

@[expose] def «is_bitstring/1» : Term → Except Exception Term
  | .bitstring _ _ _ => .ok Term.true
  | _ => .ok Term.false

@[expose] def «is_binary/1» : Term → Except Exception Term
  | .bitstring _ 0 _ => .ok Term.true
  | _ => .ok Term.false

@[expose] def «bit_size/1» : Term → Except Exception Term
  | .bitstring bytes lastBits _ =>
      .ok (.integer (Term.Bitstring.bitSize bytes lastBits))
  | _ => throw (.error (.atom "badarg"))

/-- Partial final bytes count as one byte, as in Erlang's `byte_size/1`. -/
@[expose] def «byte_size/1» : Term → Except Exception Term
  | .bitstring bytes _ _ => .ok (.integer bytes.size)
  | _ => throw (.error (.atom "badarg"))

@[expose] def «is_list/1» : Term → Except Exception Term
  | .nil => .ok Term.true
  | .cons _ _ => .ok Term.true
  | _ => .ok Term.false

-- Convert a successful binary64 operation or raise badarith.
private def floatResult (value : Option Term.FiniteFloat) : Except Exception Term :=
  match value with
  | some value => .ok (.float value)
  | none => throw (.error (.atom "badarith"))

@[simp] private theorem floatResult_ok_iff (value : Option Term.FiniteFloat) (result : Term) :
    floatResult value = .ok result ↔ ∃ f, value = some f ∧ result = .float f := by
  cases value <;> simp [floatResult, eq_comm]

def «+/2» : Term → Term → Except Exception Term
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

def «-/2» : Term → Term → Except Exception Term
  | .integer x, .integer y => .ok (.integer (x - y))
  | .float x, .float y => floatResult (x.sub y)
  | .integer x, .float y => floatResult (Term.FiniteFloat.ofInt x >>= (·.sub y))
  | .float x, .integer y => floatResult (Term.FiniteFloat.ofInt y >>= x.sub)
  | _, _ => throw (.error (.atom "badarith"))

@[simp↓] theorem «-/2_integers» (left right : Int) :
    «-/2» (.integer left) (.integer right) = .ok (.integer (left - right)) := by rfl

/-- Integer subtraction results cannot originate from a float or another term kind. -/
@[simp] theorem «-/2_integer_result» (left : Term) (right value : Int) :
    «-/2» left (.integer right) = .ok (.integer value) ↔ left = .integer (value + right) := by
  cases left <;> simp [«-/2», floatResult]
  · omega
  · split <;> simp_all

def «//2» : Term → Term → Except Exception Term
  | .float x, .float y => floatResult (x.div y)
  | .integer x, .float y => floatResult (Term.FiniteFloat.ofInt x >>= (·.div y))
  | .float x, .integer y => floatResult (Term.FiniteFloat.ofInt y >>= x.div)
  | .integer x, .integer y => floatResult
      (Term.FiniteFloat.ofInt x >>= fun a => Term.FiniteFloat.ofInt y >>= a.div)
  | _, _ => throw (.error (.atom "badarith"))

def «*/2» : Term → Term → Except Exception Term
  | .integer x, .integer y => .ok (.integer (x * y))
  | .float x, .float y => floatResult (x.mul y)
  | .integer x, .float y => floatResult (Term.FiniteFloat.ofInt x >>= (·.mul y))
  | .float x, .integer y => floatResult (Term.FiniteFloat.ofInt y >>= x.mul)
  | _, _ => throw (.error (.atom "badarith"))

@[simp↓] theorem «*/2_integers» (left right : Int) :
    «*/2» (.integer left) (.integer right) = .ok (.integer (left * right)) := by rfl

/-- Erlang remainder uses division truncated toward zero, including negative operands. -/
@[expose] def «rem/2» : Term → Term → Except Exception Term
  | .integer x, .integer y =>
      if y = 0 then throw (.error (.atom "badarith"))
      else .ok (.integer (x.tmod y))
  | _, _ => throw (.error (.atom "badarith"))

/-- Infinite two's complement AND. For mixed signs, clear the bits of the
nonnegative operand selected by the complement of the negative operand. -/
@[expose] def «band/2» : Term → Term → Except Exception Term
  | .integer (.ofNat x), .integer (.ofNat y) => .ok (.integer (.ofNat (x &&& y)))
  | .integer (.ofNat x), .integer (.negSucc y) => .ok (.integer (.ofNat (x ^^^ (x &&& y))))
  | .integer (.negSucc x), .integer (.ofNat y) => .ok (.integer (.ofNat (y ^^^ (y &&& x))))
  | .integer (.negSucc x), .integer (.negSucc y) => .ok (.integer (.negSucc (x ||| y)))
  | _, _ => throw (.error (.atom "badarith"))

/-- A negative shift count reverses direction; right shifts preserve the sign. -/
@[expose] def «bsr/2» : Term → Term → Except Exception Term
  | .integer x, .integer (.ofNat n) => .ok (.integer (x >>> n))
  | .integer x, .integer (.negSucc n) => .ok (.integer (x <<< (n + 1)))
  | _, _ => throw (.error (.atom "badarith"))

@[expose] def «bsl/2» : Term → Term → Except Exception Term
  | .integer x, .integer (.ofNat n) => .ok (.integer (x <<< n))
  | .integer x, .integer (.negSucc n) => .ok (.integer (x >>> (n + 1)))
  | _, _ => throw (.error (.atom "badarith"))

/-- Masking a nonnegative integer to a word is Euclidean remainder. -/
theorem «band/2_mask» (value : Int) (bits : Nat) (nonnegative : 0 ≤ value) :
    «band/2» (.integer value) (.integer (2 ^ bits - 1)) =
      .ok (.integer (value % 2 ^ bits)) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
  have mask : (2 ^ bits - 1 : Int) = Int.ofNat (2 ^ bits - 1) := by
    have bound : 1 ≤ (2 : Nat) ^ bits := Nat.one_le_pow bits 2 (by decide)
    simp [Int.ofNat_eq_natCast, Int.natCast_sub bound]
  rw [mask]
  simp [«band/2», Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod]

@[expose] def «==/2» (left right : Term) : Except Exception Term :=
  .ok (if Term.compare left right = .eq then Term.true else Term.false)

@[expose] def «/=/2» (left right : Term) : Except Exception Term :=
  .ok (if Term.compare left right = .eq then Term.false else Term.true)

@[expose] def «=:=/2» (left right : Term) : Except Exception Term :=
  .ok (if Term.exactCompare left right = .eq then Term.true else Term.false)

@[expose] def «=/=/2» (left right : Term) : Except Exception Term :=
  .ok (if Term.exactCompare left right = .eq then Term.false else Term.true)

@[expose] def «</2» (left right : Term) : Except Exception Term :=
  .ok (if (Term.compare left right).isLT then Term.true else Term.false)

@[expose] def «>/2» (left right : Term) : Except Exception Term :=
  .ok (if (Term.compare left right).isGT then Term.true else Term.false)

@[expose] def «=</2» (left right : Term) : Except Exception Term :=
  .ok (if (Term.compare left right).isLE then Term.true else Term.false)

@[expose] def «>=/2» (left right : Term) : Except Exception Term :=
  .ok (if (Term.compare left right).isGE then Term.true else Term.false)

@[simp] theorem «>=/2_integers» (x y : Int) :
    «>=/2» (.integer x) (.integer y) = .ok (if y ≤ x then Term.true else Term.false) := by
  simp [«>=/2», Int.isGE_compare]

@[simp] theorem «</2_integers» (x y : Int) :
    «</2» (.integer x) (.integer y) = .ok (if x < y then Term.true else Term.false) := by
  simp [«</2», Ordering.isLT_iff_eq_lt, Int.compare_eq_lt]

@[simp] theorem «=</2_integers» (x y : Int) :
    «=</2» (.integer x) (.integer y) = .ok (if x ≤ y then Term.true else Term.false) := by
  simp [«=</2», Int.isLE_compare]

@[expose] def «++/2» : Term → Term → Except Exception Term
  | .nil, right => .ok right
  | .cons head tail, right => do
      let rest ← «++/2» tail right
      .ok (.cons head rest)
  | _, _ => throw (.error (.atom "badarg"))

@[expose] def «xor/2» : Term → Term → Except Exception Term
  | .atom "true", .atom "false" | .atom "false", .atom "true" => .ok Term.true
  | .atom "true", .atom "true" | .atom "false", .atom "false" => .ok Term.false
  | _, _ => throw (.error (.atom "badarg"))

/-- No port values are represented by the local runtime. -/
@[expose] def «is_port/1» (_ : Term) : Except Exception Term := .ok Term.false

@[expose] def «is_function/2» (input arity : Term) : Except Exception Term :=
  match arity with
  | .integer n =>
    if n < 0 then throw (.error (.atom "badarg"))
    else .ok (match input with
      | .function _ a _ => if (a : Int) = n then Term.true else Term.false
      | _ => Term.false)
  | _ => throw (.error (.atom "badarg"))

@[expose] def «hd/1» : Term → Except Exception Term
  | .cons head _ => .ok head
  | _ => throw (.error (.atom "badarg"))

@[expose] def «tl/1» : Term → Except Exception Term
  | .cons _ tail => .ok tail
  | _ => throw (.error (.atom "badarg"))

/-- Unlike is_list/1, length/1 requires a proper list. -/
@[expose] def «length/1» : Term → Except Exception Term
  | .nil => .ok (.integer 0)
  | .cons _ tail => do
    let .integer n ← «length/1» tail | throw (.error (.atom "badarg"))
    .ok (.integer (n + 1))
  | _ => throw (.error (.atom "badarg"))

/-- Construct a tuple within the BEAM arity limit. -/
@[expose] def «make_tuple/2» (size value : Term) : Except Exception Term :=
  match size with
  | .integer n =>
    if 0 ≤ n ∧ n ≤ 16777215 then .ok (.tuple (Array.replicate n.toNat value))
    else throw (.error (.atom "badarg"))
  | _ => throw (.error (.atom "badarg"))

/-- Tuple arity or the number of complete bytes in a bitstring. -/
@[expose] def «size/1» : Term → Except Exception Term
  | .tuple entries => .ok (.integer entries.size)
  | .bitstring bytes lastBits _ =>
    .ok (.integer (Term.Bitstring.bitSize bytes lastBits / 8))
  | _ => throw (.error (.atom "badarg"))

@[expose] def «map_get/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries =>
    match entries.find? (fun entry => decide (Term.exactCompare key entry.1 = .eq)) with
    | some entry => .ok entry.2
    | none => throw (.error (.tuple #[.atom "badkey", key]))
  | _ => throw (.error (.tuple #[.atom "badmap", input]))

@[expose] def «is_map_key/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries => .ok (if entries.any (fun entry => Term.exactCompare key entry.1 == .eq)
    then Term.true else Term.false)
  | _ => throw (.error (.tuple #[.atom "badmap", input]))

/-- The map representation retains shadowed entries, which count only once. -/
@[expose] def «map_size/1» : Term → Except Exception Term
  | .map entries => .ok (.integer
      ((entries.map Prod.fst).eraseDupsBy (fun a b => Term.exactCompare a b == .eq)).length)
  | input => throw (.error (.tuple #[.atom "badmap", input]))

@[expose] def «min/2» (left right : Term) : Except Exception Term :=
  .ok (if (Term.compare left right).isLE then left else right)

@[expose] def «max/2» (left right : Term) : Except Exception Term :=
  .ok (if (Term.compare left right).isGE then left else right)

/-- The runtime models a local node with distribution disabled. -/
@[expose] def «node/0» : Except Exception Term := .ok (.atom "nonode@nohost")

@[expose] def «node/1» : Term → Except Exception Term
  | .pid _ | .reference _ => «node/0»
  | _ => throw (.error (.atom "badarg"))

/-- Negative lengths select bytes preceding the supplied position. -/
@[expose] def «binary_part/3» : Term → Term → Term → Except Exception Term
  | .bitstring bytes 0 _, .integer position, .integer length =>
    let start := if length < 0 then position + length else position
    let stop := if length < 0 then position else position + length
    if 0 ≤ start ∧ start ≤ stop ∧ stop ≤ (bytes.size : Int) then
      .ok (.bitstring (bytes.extract start.toNat stop.toNat) 0)
    else throw (.error (.atom "badarg"))
  | _, _, _ => throw (.error (.atom "badarg"))

/-- The part spanning a whole binary is the binary itself. -/
theorem binary_part_whole (bytes : ByteArray) :
    «binary_part/3» (.bitstring bytes 0 (Term.Bitstring.valid_aligned _)) (.integer 0) (.integer bytes.size) =
      .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned _)) := by
  have nonneg : ¬ ((bytes.size : Int) < 0) := by omega
  simp [«binary_part/3», nonneg, ByteArray.extract_zero_size]

@[expose] def «binary_part/2» (input range : Term) : Except Exception Term :=
  match range with
  | .tuple entries =>
    match entries.toList with
    | [position, length] => «binary_part/3» input position length
    | _ => throw (.error (.atom "badarg"))
  | _ => throw (.error (.atom "badarg"))

@[expose] def «+/1» : Term → Except Exception Term
  | .integer n => .ok (.integer n)
  | .float f => .ok (.float f)
  | _ => throw (.error (.atom "badarith"))

@[expose] def «-/1» : Term → Except Exception Term
  | .integer n => .ok (.integer (-n))
  | .float f => .ok (.float { f with negative := !f.negative })
  | _ => throw (.error (.atom "badarith"))

@[expose] def «abs/1» : Term → Except Exception Term
  | .integer n => .ok (.integer n.natAbs)
  | .float f => .ok (.float { f with negative := false })
  | _ => throw (.error (.atom "badarg"))

@[expose] def «float/1» : Term → Except Exception Term
  | .float f => .ok (.float f)
  | .integer n => match Term.FiniteFloat.ofInt n with
    | some f => .ok (.float f)
    | none => throw (.error (.atom "badarg"))
  | _ => throw (.error (.atom "badarg"))

@[expose] def «floor/1» : Term → Except Exception Term
  | .integer n => .ok (.integer n)
  | .float f => .ok (.integer f.toRat.floor)
  | _ => throw (.error (.atom "badarg"))

@[expose] def «ceil/1» : Term → Except Exception Term
  | .integer n => .ok (.integer n)
  | .float f => .ok (.integer f.toRat.ceil)
  | _ => throw (.error (.atom "badarg"))

@[expose] def «trunc/1» : Term → Except Exception Term
  | .integer n => .ok (.integer n)
  | .float f => .ok (.integer (f.toRat.num.tdiv f.toRat.den))
  | _ => throw (.error (.atom "badarg"))

/-- Round ties away from zero, rather than IEEE's ties to even. -/
@[expose] def «round/1» : Term → Except Exception Term
  | .integer n => .ok (.integer n)
  | .float f =>
    let magnitude := (f.magnitude + (1 / 2 : Rat)).floor
    .ok (.integer (if f.negative then -magnitude else magnitude))
  | _ => throw (.error (.atom "badarg"))

@[expose] def «div/2» : Term → Term → Except Exception Term
  | .integer x, .integer y =>
    if y = 0 then throw (.error (.atom "badarith"))
    else .ok (.integer (x.tdiv y))
  | _, _ => throw (.error (.atom "badarith"))

@[expose] def «bnot/1» : Term → Except Exception Term
  | .integer x => .ok (.integer (-x - 1))
  | _ => throw (.error (.atom "badarith"))

@[expose] def «bor/2» : Term → Term → Except Exception Term
  | .integer (.ofNat x), .integer (.ofNat y) => .ok (.integer (.ofNat (x ||| y)))
  | .integer (.ofNat x), .integer (.negSucc y) => .ok (.integer (.negSucc (y ^^^ (y &&& x))))
  | .integer (.negSucc x), .integer (.ofNat y) => .ok (.integer (.negSucc (x ^^^ (x &&& y))))
  | .integer (.negSucc x), .integer (.negSucc y) => .ok (.integer (.negSucc (x &&& y)))
  | _, _ => throw (.error (.atom "badarith"))

@[expose] def «bxor/2» : Term → Term → Except Exception Term
  | .integer (.ofNat x), .integer (.ofNat y) => .ok (.integer (.ofNat (x ^^^ y)))
  | .integer (.ofNat x), .integer (.negSucc y) => .ok (.integer (.negSucc (x ^^^ y)))
  | .integer (.negSucc x), .integer (.ofNat y) => .ok (.integer (.negSucc (x ^^^ y)))
  | .integer (.negSucc x), .integer (.negSucc y) => .ok (.integer (.ofNat (x ^^^ y)))
  | _, _ => throw (.error (.atom "badarith"))

end Erlang.erlang
