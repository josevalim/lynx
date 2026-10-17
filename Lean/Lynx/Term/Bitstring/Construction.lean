module

public import Lynx.Purity
public import Lynx.Term.Bitstring

namespace Lynx.Term.Bitstring

/-- Pack transmission-order bits as a term. The empty list produces the empty binary. -/
@[expose] public def ofBits (bits : List Bool) : Term :=
  .bitstring (pack bits) ⟨bits.length % 8, Nat.mod_lt _ (by decide)⟩ (pack_valid bits)

/-- Packing preserves the number of meaningful bits. -/
@[simp] public theorem ofBits_bitSize (bits : List Bool) :
    (match ofBits bits with
      | .bitstring bytes last _ => bitSize bytes last
      | _ => 0) = bits.length := by
  exact pack_bitSize bits

/-- Bitstrings measure their meaningful bits, offset by a constant. -/
public theorem bitstring_sizeOf (bytes : ByteArray) (last : Fin 8) (valid : Valid bytes last) :
    sizeOf (Term.bitstring bytes last valid) = 9 + bitSize bytes last := by
  simp only [Term.bitstring.sizeOf_spec]
  show 1 + 8 * bytes.size + (if last = 0 then 8 else last.val) + 0 = _
  unfold bitSize
  by_cases empty : bytes.size = 0
  · simp [empty, valid.1 empty]
  · by_cases aligned : last = 0
    · simp [empty, aligned]
      omega
    · simp [empty, aligned]
      omega

public theorem ofBits_sizeOf (bits : List Bool) : sizeOf (ofBits bits) = 9 + bits.length := by
  simp only [ofBits, bitstring_sizeOf, pack_bitSize]

/-- Packing preserves every bit in transmission order. -/
@[simp] public theorem ofBits_toBits (bits : List Bool) :
    (match ofBits bits with
      | .bitstring bytes last _ => toBits bytes last
      | _ => []) = bits := by
  exact pack_toBits bits

/-- Repacking a binary preserves its canonical storage. -/
public theorem ofBits_toBits_aligned (bytes : ByteArray) : ofBits (toBits bytes 0) =
    .bitstring bytes 0 (valid_aligned bytes) := by
  have aligned : (toBits bytes 0).length % 8 = 0 := by rw [toBits_length_aligned]; omega
  simp only [ofBits]
  have last : (⟨(toBits bytes 0).length % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) = 0 := Fin.ext aligned
  congr 1
  exact pack_toBits_aligned bytes

/-- Build an integer segment. Segment sizes count `unit` bits and must be
nonnegative integers; the Core unit is a compile-time value in `1..256`. -/
#lynx_pure @[expose] public def integerSegment (value size : Term) (unit : Nat)
    (little : Bool) : Result :=
  match value, size with
  | .integer value, .integer size =>
    if 0 ≤ size ∧ 1 ≤ unit ∧ unit ≤ 256 then
      .ok (ofBits (integerBits value (size.toNat * unit) little))
    else .error (.error (.atom "badarg"))
  | _, _ => .error (.error (.atom "badarg"))

/-- Encode binary64 fields without rounding. Integer operands are first rounded
into binary64, failing with badarg if conversion overflows. Binary16 and
binary32 are not modeled yet and currently return badarg. -/
#lynx_pure @[expose] public def floatSegment (value : Term) (width : Nat) (little : Bool) : Result :=
  if width != 64 then .error (.error (.atom "badarg"))
  else
    let converted := match value with
      | .float value => some value
      | .integer value => Term.FiniteFloat.ofInt value
      | _ => none
    match converted with
    | some value =>
      let encoded : Nat := (if value.negative then 2 ^ 63 else 0) +
        value.exponent.val * 2 ^ 52 + value.fraction.val
      integerSegment (.integer (Int.ofNat encoded)) (.integer 64) 1 little
    | none => .error (.error (.atom "badarg"))

/-- Encode one Unicode scalar as UTF-8. Endianness does not affect UTF-8. -/
#lynx_pure @[expose] public def utf8Segment (value : Term) : Result :=
  match value with
  | .integer value =>
    if 0 ≤ value ∧ value ≤ 0x10ffff ∧ (value < 0xd800 ∨ 0xdfff < value) then
      let value := value.toNat
      let bytes := if value < 0x80 then [value]
        else if value < 0x800 then [0xc0 + value / 64, 0x80 + value % 64]
        else if value < 0x10000 then
          [0xe0 + value / 4096, 0x80 + value / 64 % 64, 0x80 + value % 64]
        else [0xf0 + value / 262144, 0x80 + value / 4096 % 64,
          0x80 + value / 64 % 64, 0x80 + value % 64]
      .ok (ofBits (bytes.flatMap fun byte => integerBits (Int.ofNat byte) 8 Bool.false))
    else .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

/-- Encode one Unicode scalar as UTF-16, ordering bytes within each code unit.
Supplementary scalars emit the high surrogate before the low surrogate. -/
#lynx_pure @[expose] public def utf16Segment (value : Term) (little : Bool) : Result :=
  match value with
  | .integer value =>
    if 0 ≤ value ∧ value ≤ 0x10ffff ∧ (value < 0xd800 ∨ 0xdfff < value) then
      let value := value.toNat
      let bits := if value < 0x10000 then integerBits value 16 little
        else integerBits (0xd800 + (value - 0x10000) / 1024) 16 little ++
          integerBits (0xdc00 + (value - 0x10000) % 1024) 16 little
      .ok (ofBits bits)
    else .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

/-- Encode one Unicode scalar as UTF-32 without integer-segment truncation. -/
#lynx_pure @[expose] public def utf32Segment (value : Term) (little : Bool) : Result :=
  match value with
  | .integer value =>
    if 0 ≤ value ∧ value ≤ 0x10ffff ∧ (value < 0xd800 ∨ 0xdfff < value) then
      .ok (ofBits (integerBits value 32 little))
    else .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

/-- Copy a whole bitstring or a sized prefix. Whole segments must have a bit
length divisible by their unit; sized segments may consume an unaligned input. -/
#lynx_pure @[expose] public def binarySegment (value size : Term) (unit : Nat) : Result :=
  match value with
  | .bitstring bytes last _ =>
    if 1 ≤ unit ∧ unit ≤ 256 then
      let length := bitSize bytes last
      match size with
      | .atom "all" =>
        if length % unit = 0 then .ok value else .error (.error (.atom "badarg"))
      | .integer size =>
        if 0 ≤ size ∧ size.toNat * unit ≤ length then
          .ok (ofBits ((toBits bytes last).take (size.toNat * unit)))
        else .error (.error (.atom "badarg"))
      | _ => .error (.error (.atom "badarg"))
    else .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

/-- Concatenate meaningful bits, including segments that cross byte boundaries. -/
#lynx_pure @[expose] public def append (left right : Term) : Result :=
  match left, right with
  | .bitstring a ab _, .bitstring b bb _ =>
      .ok (ofBits (toBits a ab ++ toBits b bb))
  | _, _ => .error (.error (.atom "badarg"))

/-- A well-sized integer field constructs exactly its low transmission bits. -/
public theorem integerSegment_bits (value : Int) (width : Nat) :
    integerSegment (.integer value) (.integer width) 1 Bool.false =
      .ok (ofBits (integerBits value width Bool.false)) := by
  simp [integerSegment]

public theorem binarySegment_bits (bits : List Bool) :
    binarySegment (ofBits bits) (.atom "all") 1 = .ok (ofBits bits) := by
  simp [binarySegment, ofBits, pack_bitSize, Nat.mod_one]

public theorem append_bits (left right : List Bool) :
    append (ofBits left) (ofBits right) = .ok (ofBits (left ++ right)) := by
  simp [append, ofBits, pack_toBits]

end Lynx.Term.Bitstring
