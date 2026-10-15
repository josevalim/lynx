module

public import Lynx.Term.Bitstring.Construction

namespace Lynx.Term.Bitstring

/-- Extract an integer and leave the unconsumed bits. Invalid sizes, operand
kinds, and short inputs fail the pattern rather than raising an exception. -/
@[expose] public def matchInteger (input size : Term) (unit : Nat)
    (signed little : Bool) : Option (Term × Term) :=
  match input, size with
  | .bitstring bytes last _, .integer size =>
    if 0 ≤ size ∧ 1 ≤ unit ∧ unit ≤ 256 then
      let bits := toBits bytes last
      let width := size.toNat * unit
      if width ≤ bits.length then
        let value := decodeInteger (bits.take width) little
        let integer := if signed && width > 0 && value ≥ 2 ^ (width - 1)
          then Int.ofNat value - (2 : Int) ^ width else Int.ofNat value
        some (.integer integer, ofBits (bits.drop width))
      else none
    else none
  | _, _ => none

/-- Extract a known prefix and preserve its remaining bits. -/
public theorem matchInteger_prefix (head tail : List Bool) :
    matchInteger (ofBits (head ++ tail)) (.integer head.length) 1 Bool.false Bool.false =
      some (.integer (decodeInteger head Bool.false), ofBits tail) := by
  simp only [matchInteger, ofBits, pack_toBits]
  simp

/-- Decode a field from a big-endian integer encoding. -/
public theorem matchInteger_big (n left right : Nat) :
    matchInteger (ofBits (integerBits n (left + right) Bool.false)) (.integer left) 1 Bool.false Bool.false =
      some (.integer (((n >>> right) % 2 ^ left : Nat) : Int), ofBits (integerBits n right Bool.false)) := by
  rw [integerBits_add]
  have eq := matchInteger_prefix (integerBits ((n : Int) >>> right) left Bool.false) (integerBits n right Bool.false)
  simp only [integerBits_length] at eq
  rw [eq, ← Int.natCast_shiftRight, decodeInteger_integerBits]

/-- Constructing binary64 and extracting its integer fields recovers the encoding. -/
public theorem floatSegment_fields (value : Term.FiniteFloat) :
    ∃ encoded : Nat,
      floatSegment (.float value) 64 Bool.false = .ok (ofBits (integerBits encoded 64 Bool.false)) ∧
      matchInteger (ofBits (integerBits encoded 64 Bool.false)) (.integer 1) 1 Bool.false Bool.false =
        some (.integer (if value.negative then 1 else 0), ofBits (integerBits encoded 63 Bool.false)) ∧
      matchInteger (ofBits (integerBits encoded 63 Bool.false)) (.integer 11) 1 Bool.false Bool.false =
        some (.integer value.exponent.val, ofBits (integerBits encoded 52 Bool.false)) ∧
      matchInteger (ofBits (integerBits encoded 52 Bool.false)) (.integer 52) 1 Bool.false Bool.false =
        some (.integer value.fraction.val, ofBits []) := by
  let encoded : Nat := (if value.negative then 2 ^ 63 else 0) +
    value.exponent.val * 2 ^ 52 + value.fraction.val
  have frac := value.fraction.isLt
  have exp := value.exponent.isLt
  have fields : encoded / 2 ^ 63 % 2 = (if value.negative then 1 else 0) ∧
      encoded / 2 ^ 52 % 2048 = value.exponent.val ∧
      encoded % 2 ^ 52 = value.fraction.val := by
    dsimp [encoded]
    cases value.negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  refine ⟨encoded, rfl, ?_, ?_, ?_⟩
  · have result := matchInteger_big encoded 1 63
    simpa only [Nat.reduceAdd, Nat.reducePow, Nat.shiftRight_eq_div_pow, fields.1, apply_ite, Int.cast_ofNat_Int] using result
  · have result := matchInteger_big encoded 11 52
    simpa only [Nat.reduceAdd, Nat.reducePow, Int.cast_ofNat_Int, Nat.shiftRight_eq_div_pow, fields.2.1] using result
  · have result := matchInteger_big encoded 52 0
    simpa only [Nat.add_zero, Nat.shiftRight_zero, Int.cast_ofNat_Int, fields.2.2,
      integerBits, List.range_zero, List.map_nil] using result

/-- Extract a finite binary64 float. Non-finite encodings fail the pattern.
Binary16 and binary32 decoding are not implemented yet. -/
@[expose] public def matchFloat (input : Term) (width : Nat) (little : Bool) :
    Option (Term × Term) := do
  if width != 64 then none else do
    let (.integer value, rest) ← matchInteger input (.integer 64) 1 Bool.false little | none
    let encoded := value.toNat
    let exponent := encoded / 2 ^ 52 % 2048
    if h : exponent < 2047 then
      some (.float ⟨encoded / 2 ^ 63 != 0, ⟨exponent, h⟩,
        ⟨encoded % 2 ^ 52, Nat.mod_lt _ (by decide)⟩⟩, rest)
    else none

/-- Validate a trailing binary or bitstring. The segment's unit constrains its
length; binary uses eight and bitstring uses one. Alignment is relative to the
captured segment, so an unaligned start is allowed. Explicit sizes must
consume exactly the remaining bits. -/
@[expose] public def matchTail (input size : Term) (unit : Nat) : Bool :=
  match input with
  | .bitstring bytes last _ =>
    if 1 ≤ unit ∧ unit ≤ 256 then
      match size with
      | .atom "all" => bitSize bytes last % unit == 0
      | .integer width => decide (0 ≤ width ∧ bitSize bytes last = width.toNat * unit)
      | _ => Bool.false
    else Bool.false
  | _ => Bool.false

/-- A pattern without a trailing capture must consume the whole bitstring. -/
@[expose] public def matchEnd (input : Term) : Bool :=
  match input with
  | .bitstring bytes last _ => bitSize bytes last == 0
  | _ => Bool.false

end Lynx.Term.Bitstring
