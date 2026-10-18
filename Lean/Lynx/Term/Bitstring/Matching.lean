module

public meta import Lean
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

/-- Extract one canonical UTF-8 sequence. Invalid leaders, continuation bytes,
overlong encodings, surrogate code points, and incomplete sequences fail the pattern.
The unconsumed suffix may contain arbitrary bits. -/
@[expose] public def matchUtf8 (input : Term) : Option (Term × Term) :=
  match input with
  | .bitstring bytes last _ =>
    let bits := toBits bytes last
    let byte := fun i => decodeInteger ((bits.drop (i * 8)).take 8) Bool.false
    let first := byte 0
    let count := if first < 0x80 then 1
      else if 0xc2 ≤ first ∧ first ≤ 0xdf then 2
      else if 0xe0 ≤ first ∧ first ≤ 0xef then 3
      else if 0xf0 ≤ first ∧ first ≤ 0xf4 then 4 else 0
    let value := if count = 1 then first
      else (List.range (count - 1)).foldl
        (fun value i => value * 64 + byte (i + 1) % 64) (first % 2 ^ (7 - count))
    let minimum := if count = 1 then 0 else if count = 2 then 0x80
      else if count = 3 then 0x800 else 0x10000
    if count ≠ 0 ∧ count * 8 ≤ bits.length ∧
        ((List.range (count - 1)).all fun i => 0x80 ≤ byte (i + 1) && byte (i + 1) ≤ 0xbf) ∧
        minimum ≤ value ∧ value ≤ 0x10ffff ∧ (value < 0xd800 ∨ 0xdfff < value) then
      some (.integer value, ofBits (bits.drop (count * 8)))
    else none
  | _ => none

/-- Extract one UTF-16 scalar, consuming a high/low surrogate pair together.
Endianness applies to each code unit, including at unaligned bit positions. -/
@[expose] public def matchUtf16 (input : Term) (little : Bool) : Option (Term × Term) :=
  match input with
  | .bitstring bytes last _ =>
    let bits := toBits bytes last
    let first := decodeInteger (bits.take 16) little
    let paired := 0xd800 ≤ first ∧ first ≤ 0xdbff
    let second := decodeInteger ((bits.drop 16).take 16) little
    let width := if paired then 32 else 16
    let value := if paired then 0x10000 + (first - 0xd800) * 1024 + (second - 0xdc00)
      else first
    if width ≤ bits.length ∧ (paired → 0xdc00 ≤ second ∧ second ≤ 0xdfff) ∧
        value ≤ 0x10ffff ∧ (value < 0xd800 ∨ 0xdfff < value) then
      some (.integer value, ofBits (bits.drop width))
    else none
  | _ => none

/-- Extract a UTF-32 scalar. Surrogates and values above U+10FFFF fail the pattern. -/
@[expose] public def matchUtf32 (input : Term) (little : Bool) : Option (Term × Term) :=
  match input with
  | .bitstring bytes last _ =>
    let bits := toBits bytes last
    let value := decodeInteger (bits.take 32) little
    if 32 ≤ bits.length ∧ value ≤ 0x10ffff ∧ (value < 0xd800 ∨ 0xdfff < value) then
      some (.integer value, ofBits (bits.drop 32))
    else none
  | _ => none

/-- UTF-8 construction followed by matching recovers every Unicode scalar and
leaves an arbitrary bit suffix untouched. The encoding is byte aligned. -/
public theorem matchUtf8_construct (value : Nat) (tail : List Bool)
    (bounded : value ≤ 0x10ffff) (scalar : value < 0xd800 ∨ 0xdfff < value) :
    ∃ encoded : List Bool,
      utf8Segment (.integer value) = .ok (ofBits encoded) ∧
      encoded.length % 8 = 0 ∧
      matchUtf8 (ofBits (encoded ++ tail)) = some (.integer value, ofBits tail) := by
  have takeByte (n : Int) : (integerBits n 8 Bool.false).take 8 = integerBits n 8 Bool.false := by
    exact List.take_of_length_le (by simp)
  have dropByte (n : Int) (width : Nat) (enough : 8 ≤ width) :
      (integerBits n 8 Bool.false).drop width = [] := by
    exact List.drop_eq_nil_of_le (by simpa using enough)
  have valid : (0 : Int) ≤ value ∧ (value : Int) ≤ 0x10ffff ∧
      ((value : Int) < 0xd800 ∨ 0xdfff < (value : Int)) := by omega
  simp only [utf8Segment, valid, and_self, ↓reduceIte, Int.toNat_natCast]
  split <;> rename_i bound1
  · refine ⟨_, rfl, ?_, ?_⟩
    · simp [integerBits_length]
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      simp only [matchUtf8, ofBits, pack_toBits]
      simp [List.take_append, List.drop_append, integerBits_length,
        decodeInteger_integerBits, Nat.mod_eq_of_lt (show value < 256 by omega), bound1,
        scalar, bounded]
  · split <;> rename_i bound2
    · refine ⟨_, rfl, ?_, ?_⟩
      · simp [integerBits_length]
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        generalize ha : 192 + value / 64 = a
        generalize hb : 128 + value % 64 = b
        have aBound : a < 256 := by omega
        have bBound : b < 256 := by omega
        have notAscii : ¬a < 128 := by omega
        have leader : 194 ≤ a ∧ a ≤ 223 := by omega
        simp only [matchUtf8, ofBits, pack_toBits]
        simp [List.take_append, List.drop_append, integerBits_length,
          decodeInteger_integerBits, takeByte, dropByte, Nat.mod_eq_of_lt aBound,
          Nat.mod_eq_of_lt bBound,
          notAscii, leader, List.range_succ]
        omega
    · split <;> rename_i bound3
      · refine ⟨_, rfl, ?_, ?_⟩
        · simp [integerBits_length]
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          generalize ha : 224 + value / 4096 = a
          generalize hb : 128 + value / 64 % 64 = b
          generalize hc : 128 + value % 64 = c
          have aBound : a < 256 := by omega
          have bBound : b < 256 := by omega
          have cBound : c < 256 := by omega
          have notAscii : ¬a < 128 := by omega
          have notTwo : ¬(194 ≤ a ∧ a ≤ 223) := by omega
          have leader : 224 ≤ a ∧ a ≤ 239 := by omega
          simp only [matchUtf8, ofBits, pack_toBits]
          simp [List.take_append, List.drop_append, integerBits_length,
            decodeInteger_integerBits, takeByte, dropByte, Nat.mod_eq_of_lt aBound,
            Nat.mod_eq_of_lt bBound, Nat.mod_eq_of_lt cBound,
            notAscii, notTwo, leader, List.range_succ]
          omega
      · refine ⟨_, rfl, ?_, ?_⟩
        · simp [integerBits_length]
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          generalize ha : 240 + value / 262144 = a
          generalize hb : 128 + value / 4096 % 64 = b
          generalize hc : 128 + value / 64 % 64 = c
          generalize hd : 128 + value % 64 = d
          have aBound : a < 256 := by omega
          have bBound : b < 256 := by omega
          have cBound : c < 256 := by omega
          have dBound : d < 256 := by omega
          have notAscii : ¬a < 128 := by omega
          have notTwo : ¬(194 ≤ a ∧ a ≤ 223) := by omega
          have notThree : ¬(224 ≤ a ∧ a ≤ 239) := by omega
          have leader : 240 ≤ a ∧ a ≤ 244 := by omega
          simp only [matchUtf8, ofBits, pack_toBits]
          simp [List.take_append, List.drop_append, integerBits_length,
            decodeInteger_integerBits, takeByte, dropByte, Nat.mod_eq_of_lt aBound,
            Nat.mod_eq_of_lt bBound, Nat.mod_eq_of_lt cBound, Nat.mod_eq_of_lt dBound,
            notAscii, notTwo, notThree, leader, List.range_succ]
          omega

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

/-- Extract a sized bitstring prefix, leaving the remaining bits for later fields. -/
@[expose] public def matchBinary (input size : Term) (unit : Nat) : Option (Term × Term) :=
  match input, size with
  | .bitstring bytes last _, .integer size =>
    let bits := toBits bytes last
    let width := size.toNat * unit
    if 0 ≤ size ∧ 1 ≤ unit ∧ unit ≤ 256 ∧ width ≤ bits.length then
      some (ofBits (bits.take width), ofBits (bits.drop width))
    else none
  | _, _ => none

/-- A pattern without a trailing capture must consume the whole bitstring. -/
@[expose] public def matchEnd (input : Term) : Bool :=
  match input with
  | .bitstring bytes last _ => bitSize bytes last == 0
  | _ => Bool.false

/-- Extract a field from a bit view without expanding packed storage. -/
public theorem matchInteger_take (bits : List Bool) (width : Nat) (enough : width ≤ bits.length) :
    matchInteger (ofBits bits) (.integer width) 1 Bool.false Bool.false =
      some (.integer (decodeInteger (bits.take width) Bool.false), ofBits (bits.drop width)) := by
  simp [matchInteger, ofBits, pack_toBits, enough]

public theorem matchTail_bits (bits : List Bool) :
    matchTail (ofBits bits) (.atom "all") 1 = Bool.true := by
  simp [matchTail, ofBits, pack_bitSize, Nat.mod_one]

public theorem matchEnd_bits (bits : List Bool) :
    matchEnd (ofBits bits) = (bits.length == 0) := by
  simp [matchEnd, ofBits, pack_bitSize]

/-! ## Bytes

Byte-aligned binaries are matched one byte at a time by parsers. -/

private theorem decode_byte_bits_fin : ∀ n : Fin 256,
    decodeInteger ((List.range 8).map fun i => (UInt8.ofNat n.val).toBitVec.getMsbD i) Bool.false = n.val := by
  decide +kernel

private theorem decode_byte_bits (b : UInt8) :
    decodeInteger ((List.range 8).map fun i => b.toBitVec.getMsbD i) Bool.false = b.toNat := by
  simpa using decode_byte_bits_fin ⟨b.toNat, b.toNat_lt⟩

private theorem size_list (bs : List UInt8) : (ByteArray.mk bs.toArray).size = bs.length := by
  simp [ByteArray.size]

private theorem toBits_cons_take (b : UInt8) (bs : List UInt8) :
    (toBits ⟨(b :: bs).toArray⟩ 0).take 8 = (List.range 8).map fun i => b.toBitVec.getMsbD i := by
  apply List.ext_getElem
  · simp [toBits_length_aligned, size_list]; omega
  · intro i h₁ h₂
    simp at h₂
    have hi : i / 8 = 0 := by omega
    have hm : i % 8 = i := by omega
    simp only [List.getElem_take, toBits, List.getElem_map, List.getElem_range, hi, hm]
    have hj : 0 < (ByteArray.mk (b :: bs).toArray).size := by simp [size_list]
    simp [getElem!_pos (ByteArray.mk (b :: bs).toArray) 0 hj, ByteArray.getElem_eq_getElem_data]

private theorem toBits_cons_drop (b : UInt8) (bs : List UInt8) :
    (toBits ⟨(b :: bs).toArray⟩ 0).drop 8 = toBits ⟨bs.toArray⟩ 0 := by
  apply List.ext_getElem
  · simp [toBits_length_aligned, size_list]; omega
  · intro i h₁ h₂
    have hl := toBits_length_aligned (ByteArray.mk bs.toArray)
    simp only [size_list] at hl
    have hq : (8 + i) / 8 = i / 8 + 1 := by omega
    have hr : (8 + i) % 8 = i % 8 := by omega
    simp only [List.getElem_drop, toBits, List.getElem_map, List.getElem_range, hq, hr]
    have h1 : i / 8 + 1 < (ByteArray.mk (b :: bs).toArray).size := by simp [size_list]; omega
    have h2 : i / 8 < (ByteArray.mk bs.toArray).size := by simp [size_list]; omega
    simp [getElem!_pos (ByteArray.mk (b :: bs).toArray) (i / 8 + 1) h1,
      getElem!_pos (ByteArray.mk bs.toArray) (i / 8) h2, ByteArray.getElem_eq_getElem_data]

/-- Matching an unsigned byte at the front of a binary returns it and the remaining bytes. -/
public theorem matchInteger_byte (b : UInt8) (bs : List UInt8) (valid : Valid ⟨(b :: bs).toArray⟩ 0) :
    matchInteger (.bitstring ⟨(b :: bs).toArray⟩ 0 valid) (.integer 8) 1 Bool.false Bool.false =
      some (.integer b.toNat, .bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) := by
  have whole : Term.bitstring ⟨(b :: bs).toArray⟩ 0 valid = ofBits (toBits ⟨(b :: bs).toArray⟩ 0) :=
    (ofBits_toBits_aligned _).symm
  have rest : Term.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _) = ofBits (toBits ⟨bs.toArray⟩ 0) :=
    (ofBits_toBits_aligned _).symm
  have length : ((toBits ⟨(b :: bs).toArray⟩ 0).take 8).length = 8 := by
    rw [toBits_cons_take]; simp
  rw [whole, rest, ← List.take_append_drop 8 (toBits ⟨(b :: bs).toArray⟩ 0)]
  have := matchInteger_prefix ((toBits ⟨(b :: bs).toArray⟩ 0).take 8) ((toBits ⟨(b :: bs).toArray⟩ 0).drop 8)
  rw [length] at this
  norm_cast at this
  rw [this, toBits_cons_take, toBits_cons_drop, decode_byte_bits]

private theorem toBits_cons (b : UInt8) (bs : List UInt8) :
    toBits ⟨(b :: bs).toArray⟩ 0 =
      ((List.range 8).map fun i => b.toBitVec.getMsbD i) ++ toBits ⟨bs.toArray⟩ 0 := by
  conv => lhs; rw [← List.take_append_drop 8 (toBits _ 0)]
  rw [toBits_cons_take, toBits_cons_drop]

private theorem toBits_append (head rest : List UInt8) :
    toBits ⟨(head ++ rest).toArray⟩ 0 =
      head.flatMap (fun b => (List.range 8).map fun i => b.toBitVec.getMsbD i) ++
        toBits ⟨rest.toArray⟩ 0 := by
  induction head with
  | nil => simp
  | cons b bs ih => rw [List.cons_append, toBits_cons, ih]; simp

private theorem foldl_bits (bits : List Bool) (acc : Nat) :
    bits.foldl (fun value bit => value * 2 + if bit then 1 else 0) acc =
      acc * 2 ^ bits.length + bits.foldl (fun value bit => value * 2 + if bit then 1 else 0) 0 := by
  induction bits generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 2 + _)]
    cases b <;> simp [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

private theorem decode_bytes (head : List UInt8) (acc : Nat) :
    (head.flatMap fun b => (List.range 8).map fun i => b.toBitVec.getMsbD i).foldl
        (fun value bit => value * 2 + if bit then 1 else 0) acc =
      head.foldl (fun value b => value * 256 + b.toNat) acc := by
  induction head generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    have byte := decode_byte_bits b
    simp only [decodeInteger, Bool.false_eq_true, ↓reduceIte] at byte
    rw [List.flatMap_cons, List.foldl_append,
      foldl_bits ((List.range 8).map fun i => b.toBitVec.getMsbD i) acc, byte, ih]
    simp

/-- Matching whole bytes at the front of a binary reads them as a big-endian integer. -/
public theorem matchInteger_bytes (head rest : List UInt8) (valid : Valid ⟨(head ++ rest).toArray⟩ 0)
    (width : Int) (exact : head.length * 8 = width) :
    matchInteger (.bitstring ⟨(head ++ rest).toArray⟩ 0 valid) (.integer width) 1
        Bool.false Bool.false =
      some (.integer ((head.foldl (fun value b => value * 256 + b.toNat) 0 : Nat) : Int),
        .bitstring ⟨rest.toArray⟩ 0 (valid_aligned _)) := by
  have whole : Term.bitstring ⟨(head ++ rest).toArray⟩ 0 valid =
      ofBits (toBits ⟨(head ++ rest).toArray⟩ 0) := (ofBits_toBits_aligned _).symm
  have tail : Term.bitstring ⟨rest.toArray⟩ 0 (valid_aligned _) = ofBits (toBits ⟨rest.toArray⟩ 0) :=
    (ofBits_toBits_aligned _).symm
  rw [whole, tail, toBits_append]
  have prefix_ := matchInteger_prefix
    (head.flatMap fun b => (List.range 8).map fun i => b.toBitVec.getMsbD i) (toBits ⟨rest.toArray⟩ 0)
  have length : ((head.flatMap fun b => (List.range 8).map fun i => b.toBitVec.getMsbD i).length : Int) =
      width := by
    have bits : ∀ bytes : List UInt8,
        (bytes.flatMap fun b => (List.range 8).map fun i => b.toBitVec.getMsbD i).length =
          bytes.length * 8 := by
      intro bytes
      induction bytes with
      | nil => rfl
      | cons b bs ih => simp [List.flatMap_cons, ih]; omega
    rw [← exact, bits]
    omega
  rw [length] at prefix_
  rw [prefix_, decodeInteger]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [decode_bytes]

/-- An empty binary ends a pattern. -/
public theorem matchEnd_byte_nil :
    matchEnd (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) = Bool.true := rfl

/-- A binary with a byte left does not end a pattern. -/
public theorem matchEnd_byte (b : UInt8) (bs : List UInt8) (valid) :
    matchEnd (.bitstring ⟨(b :: bs).toArray⟩ 0 valid) = Bool.false := by
  simp [matchEnd, bitSize, ByteArray.size]

/-- Matching a byte at the front of an empty binary fails. -/
public theorem matchInteger_byte_nil :
    matchInteger (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) (.integer 8) 1
      Bool.false Bool.false = none := by
  have : (toBits ⟨([] : List UInt8).toArray⟩ 0).length = 0 := by
    rw [toBits_length_aligned]; rfl
  simp [matchInteger, this]

/-! ## Consumed bits

Every successful extraction removes its width from the measure of the input.
These facts let recursion over the remaining bits prove termination. -/

private theorem toBits_length (bytes : ByteArray) (last : Fin 8) :
    (toBits bytes last).length = bitSize bytes last := by
  simp [toBits]

private theorem matchInteger_sizeOf {input size value rest : Term} {unit : Nat} {signed little : Bool}
    (matched : matchInteger input size unit signed little = some (value, rest)) :
    ∃ width : Int, size = .integer width ∧ 0 ≤ width ∧ 1 ≤ unit ∧
      sizeOf rest + width.toNat * unit = sizeOf input := by
  unfold matchInteger at matched
  split at matched
  · rename_i bytes last _ width
    dsimp only at matched
    split at matched <;> try contradiction
    rename_i bounds
    split at matched <;> try contradiction
    cases matched
    refine ⟨width, rfl, bounds.1, bounds.2.1, ?_⟩
    simp only [ofBits_sizeOf, bitstring_sizeOf, List.length_drop, toBits_length] at *
    omega
  · contradiction

private theorem matchBinary_sizeOf {input size value rest : Term} {unit : Nat}
    (matched : matchBinary input size unit = some (value, rest)) :
    ∃ width : Int, size = .integer width ∧ 0 ≤ width ∧ 1 ≤ unit ∧
      sizeOf rest + width.toNat * unit = sizeOf input := by
  unfold matchBinary at matched
  split at matched
  · rename_i bytes last _ width
    dsimp only at matched
    split at matched <;> try contradiction
    rename_i bounds
    cases matched
    refine ⟨width, rfl, bounds.1, bounds.2.1, ?_⟩
    simp only [ofBits_sizeOf, bitstring_sizeOf, List.length_drop, toBits_length] at *
    omega
  · contradiction

public theorem matchInteger_sizeOf_integer {input value rest : Term} {width : Int} {unit : Nat}
    {signed little : Bool}
    (matched : matchInteger input (.integer width) unit signed little = some (value, rest)) :
    sizeOf rest + width.toNat * unit = sizeOf input := by
  obtain ⟨_, same, -, -, length⟩ := matchInteger_sizeOf matched
  cases same
  exact length

public theorem matchBinary_sizeOf_integer {input value rest : Term} {width : Int} {unit : Nat}
    (matched : matchBinary input (.integer width) unit = some (value, rest)) :
    sizeOf rest + width.toNat * unit = sizeOf input := by
  obtain ⟨_, same, -, -, length⟩ := matchBinary_sizeOf matched
  cases same
  exact length

public theorem matchInteger_sizeOf_le {input size value rest : Term} {unit : Nat}
    {signed little : Bool} (matched : matchInteger input size unit signed little = some (value, rest)) :
    sizeOf rest ≤ sizeOf input := by
  obtain ⟨_, -, -, -, length⟩ := matchInteger_sizeOf matched
  omega

public theorem matchBinary_sizeOf_le {input size value rest : Term} {unit : Nat}
    (matched : matchBinary input size unit = some (value, rest)) :
    sizeOf rest ≤ sizeOf input := by
  obtain ⟨_, -, -, -, length⟩ := matchBinary_sizeOf matched
  omega

/-- Whether a segment size is zero. Comprehensions raise on zero-width generator
segments, which would otherwise repeat forever. -/
@[expose] public def zeroWidth : Term → Bool
  | .integer width => width == 0
  | _ => Bool.false

public theorem matchInteger_sizeOf_nonzero {input size value rest : Term} {unit : Nat}
    {signed little : Bool} (nonzero : ¬zeroWidth size = Bool.true)
    (matched : matchInteger input size unit signed little = some (value, rest)) :
    sizeOf rest < sizeOf input := by
  obtain ⟨width, rfl, positive, unit, length⟩ := matchInteger_sizeOf matched
  simp only [zeroWidth, beq_iff_eq] at nonzero
  have : 1 ≤ width.toNat := by omega
  have := Nat.mul_le_mul this unit
  omega

public theorem matchBinary_sizeOf_nonzero {input size value rest : Term} {unit : Nat}
    (nonzero : ¬zeroWidth size = Bool.true) (matched : matchBinary input size unit = some (value, rest)) :
    sizeOf rest < sizeOf input := by
  obtain ⟨width, rfl, positive, unit, length⟩ := matchBinary_sizeOf matched
  simp only [zeroWidth, beq_iff_eq] at nonzero
  have : 1 ≤ width.toNat := by omega
  have := Nat.mul_le_mul this unit
  omega

public theorem matchFloat_sizeOf {input value rest : Term} {width : Nat} {little : Bool}
    (matched : matchFloat input width little = some (value, rest)) :
    sizeOf rest + 64 = sizeOf input := by
  unfold matchFloat at matched
  split at matched <;> try contradiction
  cases extracted : matchInteger input (.integer 64) 1 Bool.false little with
  | none => simp [extracted] at matched
  | some pair =>
    obtain ⟨integer, suffix⟩ := pair
    have length := matchInteger_sizeOf_integer extracted
    cases integer <;> simp [extracted] at matched
    obtain ⟨_, _, rfl⟩ := matched
    simpa using length

public theorem matchUtf8_sizeOf {input value rest : Term}
    (matched : matchUtf8 input = some (value, rest)) :
    sizeOf rest + 8 ≤ sizeOf input := by
  unfold matchUtf8 at matched
  split at matched
  · rename_i bytes last _
    dsimp only at matched
    simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at matched
    obtain ⟨valid, -, rfl⟩ := matched
    simp only [ofBits_sizeOf, bitstring_sizeOf, List.length_drop, ← toBits_length]
    have := valid.1
    have := valid.2.1
    omega
  · contradiction

public theorem matchUtf16_sizeOf {input value rest : Term} {little : Bool}
    (matched : matchUtf16 input little = some (value, rest)) :
    sizeOf rest + 16 ≤ sizeOf input := by
  unfold matchUtf16 at matched
  split at matched
  · rename_i bytes last _
    dsimp only at matched
    simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at matched
    obtain ⟨valid, -, rfl⟩ := matched
    have enough := valid.1
    simp only [ofBits_sizeOf, bitstring_sizeOf, List.length_drop, ← toBits_length]
    split <;> split at enough <;> omega
  · contradiction

public theorem matchUtf32_sizeOf {input value rest : Term} {little : Bool}
    (matched : matchUtf32 input little = some (value, rest)) :
    sizeOf rest + 32 = sizeOf input := by
  unfold matchUtf32 at matched
  split at matched
  · rename_i bytes last _
    dsimp only at matched
    split at matched <;> try contradiction
    cases matched
    simp only [ofBits_sizeOf, bitstring_sizeOf, List.length_drop, toBits_length] at *
    omega
  · contradiction

/-! ## Extraction -/

section Extraction

variable {β : Sort u}

/-- Continue with a value and the remaining bits extracted from a bitstring, or
fall through. The extraction is an ordinary argument, so simp can rewrite it
before selecting a branch. -/
@[expose] public def extract (lookup : Option (Term × Term))
    (found : Term → Term → β) (missing : Unit → β) : β :=
  match lookup with
  | some (value, rest) => found value rest
  | none => missing ()

@[simp] public theorem extract_some (value rest : Term)
    (found : Term → Term → β) (missing : Unit → β) :
    extract (some (value, rest)) found missing = found value rest := rfl

@[simp] public theorem extract_none
    (found : Term → Term → β) (missing : Unit → β) :
    extract none found missing = missing () := rfl

/-- Like a `match`, simp rewrites the extraction before its continuations. They
hold every later clause of a pattern match, which simp would otherwise
simplify before selecting a branch. -/
@[congr] public theorem extract_congr {lookup lookup' : Option (Term × Term)}
    (same : lookup = lookup') (found : Term → Term → β) (missing : Unit → β) :
    extract lookup found missing = extract lookup' found missing := by
  rw [same]

/-- An extraction whose continuation also receives its equation. -/
@[expose] public def extractWith (lookup : Option (Term × Term))
    (found : (value rest : Term) → lookup = some (value, rest) → β)
    (missing : Unit → β) : β :=
  match (generalizing := false) equation : lookup with
  | some (value, rest) => found value rest equation
  | none => missing ()

-- Termination proofs over the remaining bits need the equation of each extraction.
@[wf_preprocess] public theorem extract_wf (lookup : Option (Term × Term))
    (found : Term → Term → β) (missing : Unit → β) :
    extract lookup found missing =
      extractWith lookup (fun value rest _ => found value rest) missing := by
  cases lookup with
  | none => rfl
  | some pair => cases pair; rfl

/-- Extraction is monotone in its continuations, for `partial_fixpoint` proofs. -/
public theorem extract_mono [Lean.Order.PartialOrder β] (lookup : Option (Term × Term))
    {found found' : Term → Term → β} {missing missing' : Unit → β}
    (foundBelow : ∀ value rest, Lean.Order.PartialOrder.rel (found value rest) (found' value rest))
    (missingBelow : ∀ token, Lean.Order.PartialOrder.rel (missing token) (missing' token)) :
    Lean.Order.PartialOrder.rel (extract lookup found missing) (extract lookup found' missing') := by
  cases lookup with
  | none => exact missingBelow ()
  | some pair => cases pair; exact foundBelow _ _

/-- `partial_fixpoint` proves monotonicity through extractions. -/
@[partial_fixpoint_monotone] public theorem monotone_extract [Lean.Order.PartialOrder γ]
    [Lean.Order.PartialOrder β] (lookup : Option (Term × Term))
    (found : γ → Term → Term → β) (missing : γ → Unit → β)
    (foundMono : Lean.Order.monotone found) (missingMono : Lean.Order.monotone missing) :
    Lean.Order.monotone fun x => extract lookup (found x) (missing x) :=
  fun x y below => extract_mono lookup (foundMono x y below) (missingMono x y below)

end Extraction

public theorem _root_.Lynx.Result.IsPure.extract (lookup : Option (Term × Term))
    (found : Term → Term → Result α) (missing : Unit → Result α)
    (foundPure : ∀ value rest, lookup = some (value, rest) → (found value rest).IsPure)
    (missingPure : lookup = none → ∀ token, (missing token).IsPure) :
    (extract lookup found missing).IsPure := by
  cases lookup with
  | none => exact missingPure rfl ()
  | some pair => cases pair; exact foundPure _ _ rfl

/-! ## Termination

Recursion over the bits left by an extraction, such as bitstring generators,
decreases `sizeOf` by the consumed bits. Bitstring extractions continue through
`extract`, whose well-founded preprocessing passes the extraction's
equation to its continuation. Lean's default `decreasing_tactic` tries
`decreasing_trivial`, which this extends. -/

section Termination
open Lean Meta Elab Tactic

/-- Facts about the measure left by a successful extraction. -/
private meta def extractionFacts : Array Name := #[
  ``matchInteger_sizeOf_integer,
  ``matchInteger_sizeOf_le,
  ``matchBinary_sizeOf_integer,
  ``matchBinary_sizeOf_le,
  ``matchFloat_sizeOf,
  ``matchUtf8_sizeOf,
  ``matchUtf16_sizeOf,
  ``matchUtf32_sizeOf]

/-- Facts about extractions whose variable size was checked to be nonzero. -/
private meta def nonzeroFacts : Array Name := #[
  ``matchInteger_sizeOf_nonzero,
  ``matchBinary_sizeOf_nonzero]

/-- Record the measure left by every extraction equation in context. Local
definitions are unfolded in the goal and the new facts, so `omega` relates
the extracted bits to the recursive arguments. -/
elab "lynx_extraction_facts" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let mut goal ← goal.change (← zetaReduce (← instantiateMVars (← goal.getType)))
    let declarations := (← getLCtx).foldl (init := #[]) fun acc declaration =>
      if declaration.isImplementationDetail then acc else acc.push declaration
    let assert (goal : MVarId) (proof : Expr) : MetaM MVarId := do
      let fact ← zetaReduce (← instantiateMVars (← inferType proof))
      let (_, next) ← (← goal.assert `consumed fact proof).intro1P
      return next
    for declaration in declarations do
      unless (← instantiateMVars declaration.type).isAppOfArity ``Eq 3 do continue
      for lemma in extractionFacts do
        try goal ← assert goal (← mkAppM lemma #[declaration.toExpr]) catch _ => pure ()
      for check in declarations do
        unless (← instantiateMVars check.type).isAppOfArity ``Not 1 do continue
        for lemma in nonzeroFacts do
          try goal ← assert goal (← mkAppM lemma #[check.toExpr, declaration.toExpr])
          catch _ => pure ()
    return [goal]

macro_rules | `(tactic| decreasing_trivial) => `(tactic| (lynx_extraction_facts; omega))

end Termination

end Lynx.Term.Bitstring
