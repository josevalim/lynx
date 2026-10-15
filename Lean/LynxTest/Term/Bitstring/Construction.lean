module

import Lynx
public meta import LynxTest.ProofAudit

namespace LynxTest.Term.Bitstring.Construction

open Lynx

private def bits (term : Term) : List Bool :=
  match term with
  | .bitstring bytes last _ => Term.Bitstring.toBits bytes last
  | _ => []

private def size (term : Term) : Nat :=
  match term with
  | .bitstring bytes last _ => Term.Bitstring.bitSize bytes last
  | _ => 0

theorem ofBits_preserves_bits (input : List Bool) : bits (Term.Bitstring.ofBits input) = input :=
  Term.Bitstring.ofBits_toBits input

theorem ofBits_preserves_size (input : List Bool) : size (Term.Bitstring.ofBits input) = input.length :=
  Term.Bitstring.ofBits_bitSize input

theorem integer_segment_size (value : Int) (width unit : Nat) (little : Bool)
    (positive : 1 ≤ unit) (bounded : unit ≤ 256) :
    ∃ result, Term.Bitstring.integerSegment (.integer value) (.integer width) unit little = .ok result ∧
      size result = width * unit := by
  refine ⟨Term.Bitstring.ofBits (Term.Bitstring.integerBits value (width * unit) little), ?_, ?_⟩
  · simp [Term.Bitstring.integerSegment, positive, bounded]
  · change size (Term.Bitstring.ofBits _) = _
    rw [ofBits_preserves_size]
    simp [Term.Bitstring.integerBits]

theorem concatenation_preserves_bits (left right : List Bool) :
    Term.Bitstring.append (Term.Bitstring.ofBits left) (Term.Bitstring.ofBits right) =
      .ok (Term.Bitstring.ofBits (left ++ right)) := by
  have l := Term.Bitstring.ofBits_toBits left
  have r := Term.Bitstring.ofBits_toBits right
  cases hl : Term.Bitstring.ofBits left <;> try { simp [Term.Bitstring.ofBits] at hl }
  cases hr : Term.Bitstring.ofBits right <;> try { simp [Term.Bitstring.ofBits] at hr }
  simp only [hl] at l
  simp only [hr] at r
  simp [Term.Bitstring.append, l, r]

theorem integer_segment_preserves_bits (value : Int) (width unit : Nat) (little : Bool)
    (positive : 1 ≤ unit) (bounded : unit ≤ 256) :
    ∃ result, Term.Bitstring.integerSegment (.integer value) (.integer width) unit little = .ok result ∧
      bits result = Term.Bitstring.integerBits value (width * unit) little := by
  refine ⟨Term.Bitstring.ofBits (Term.Bitstring.integerBits value (width * unit) little), ?_, ?_⟩
  · simp [Term.Bitstring.integerSegment, positive, bounded]
  · exact ofBits_preserves_bits _

theorem concatenation_empty (input : List Bool) :
    Term.Bitstring.append (Term.Bitstring.ofBits []) (Term.Bitstring.ofBits input) =
      .ok (Term.Bitstring.ofBits input) ∧
    Term.Bitstring.append (Term.Bitstring.ofBits input) (Term.Bitstring.ofBits []) =
      .ok (Term.Bitstring.ofBits input) := by
  simp [concatenation_preserves_bits]

theorem concatenation_associative (left middle right : List Bool) :
    ((Term.Bitstring.append (Term.Bitstring.ofBits left) (Term.Bitstring.ofBits middle)).bind
      (fun joined => Term.Bitstring.append joined (Term.Bitstring.ofBits right))) =
    ((Term.Bitstring.append (Term.Bitstring.ofBits middle) (Term.Bitstring.ofBits right)).bind
      (fun joined => Term.Bitstring.append (Term.Bitstring.ofBits left) joined)) := by
  simp [concatenation_preserves_bits, Result.bind, List.append_assoc]

-- Checked against OTP 29's integer construction semantics, including partial bytes.
theorem big_and_little_partial_bytes :
    Term.Bitstring.integerSegment (.integer 0x123) (.integer 12) 1 false =
      .ok (.bitstring ⟨#[0x12, 0x30]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer 0x123) (.integer 12) 1 true =
      .ok (.bitstring ⟨#[0x23, 0x10]⟩ 4 (by decide)) := by
  repeat first | apply And.intro | rfl

theorem byte_aligned_endianness :
    Term.Bitstring.integerSegment (.integer 0x123456) (.integer 24) 1 false =
      .ok (.bitstring ⟨#[0x12, 0x34, 0x56]⟩ 0 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer 0x123456) (.integer 24) 1 true =
      .ok (.bitstring ⟨#[0x56, 0x34, 0x12]⟩ 0 (by decide)) := by
  repeat first | apply And.intro | rfl

theorem subbyte_endianness :
    Term.Bitstring.integerSegment (.integer 0x15) (.integer 5) 1 false =
      .ok (.bitstring ⟨#[0xa8]⟩ 5 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer 0x15) (.integer 5) 1 true =
      .ok (.bitstring ⟨#[0xa8]⟩ 5 (by decide)) := by
  repeat first | apply And.intro | rfl

set_option maxRecDepth 2048 in
theorem maximum_unit :
    Term.Bitstring.integerSegment (.integer 1) (.integer 1) 256 false =
      .ok (.bitstring ⟨((List.replicate 31 (0 : UInt8)) ++ [1]).toArray⟩ 0 (by decide)) := by
  rfl

theorem negative_values_and_truncation :
    Term.Bitstring.integerSegment (.integer (-2)) (.integer 12) 1 false =
      .ok (.bitstring ⟨#[0xff, 0xe0]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer (-2)) (.integer 12) 1 true =
      .ok (.bitstring ⟨#[0xfe, 0xf0]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer 0x12345) (.integer 12) 1 true =
      .ok (.bitstring ⟨#[0x45, 0x30]⟩ 4 (by decide)) := by
  repeat first | apply And.intro | rfl

-- Construction retains the low bits even outside signed and unsigned ranges.
private def encodesBytes (value : Int) (width unit : Nat) (big little : List UInt8) : Prop :=
  Term.Bitstring.integerSegment (.integer value) (.integer width) unit false =
    .ok (.bitstring ⟨big.toArray⟩ 0 (by intro _; rfl)) ∧
  Term.Bitstring.integerSegment (.integer value) (.integer width) unit true =
    .ok (.bitstring ⟨little.toArray⟩ 0 (by intro _; rfl))

theorem unsigned_byte_boundaries :
    encodesBytes 0 8 1 [0] [0] ∧
    encodesBytes 255 8 1 [255] [255] ∧
    encodesBytes 256 8 1 [0] [0] ∧
    encodesBytes 257 8 1 [1] [1] ∧
    encodesBytes (-1) 8 1 [255] [255] ∧
    encodesBytes (-256) 8 1 [0] [0] ∧
    encodesBytes (-257) 8 1 [255] [255] := by
  repeat first | apply And.intro | rfl

theorem signed_byte_boundaries :
    encodesBytes 127 8 1 [127] [127] ∧
    encodesBytes 128 8 1 [128] [128] ∧
    encodesBytes 129 8 1 [129] [129] ∧
    encodesBytes (-127) 8 1 [129] [129] ∧
    encodesBytes (-128) 8 1 [128] [128] ∧
    encodesBytes (-129) 8 1 [127] [127] := by
  repeat first | apply And.intro | rfl

theorem multibyte_overflow_and_underflow :
    encodesBytes 65535 16 1 [255, 255] [255, 255] ∧
    encodesBytes 65536 16 1 [0, 0] [0, 0] ∧
    encodesBytes 65537 16 1 [0, 1] [1, 0] ∧
    encodesBytes (-32768) 16 1 [128, 0] [0, 128] ∧
    encodesBytes (-32769) 16 1 [127, 255] [255, 127] ∧
    encodesBytes (-65536) 16 1 [0, 0] [0, 0] ∧
    encodesBytes (-65537) 16 1 [255, 255] [255, 255] := by
  repeat first | apply And.intro | rfl

theorem large_integer_truncation :
    encodesBytes 0x10000000000000123 16 1 [0x01, 0x23] [0x23, 0x01] ∧
    encodesBytes (-0x10000000000000123) 16 1 [0xfe, 0xdd] [0xdd, 0xfe] := by
  repeat first | apply And.intro | rfl

theorem scaled_unit_truncation :
    encodesBytes 0x12345 2 8 [0x23, 0x45] [0x45, 0x23] ∧
    encodesBytes (-0x12345) 2 8 [0xdc, 0xbb] [0xbb, 0xdc] := by
  repeat first | apply And.intro | rfl

theorem partial_byte_overflow_and_underflow :
    Term.Bitstring.integerSegment (.integer 4096) (.integer 12) 1 false =
      .ok (.bitstring ⟨#[0, 0]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer 4096) (.integer 12) 1 true =
      .ok (.bitstring ⟨#[0, 0]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer 4097) (.integer 12) 1 false =
      .ok (.bitstring ⟨#[0, 0x10]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer 4097) (.integer 12) 1 true =
      .ok (.bitstring ⟨#[1, 0]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer (-2049)) (.integer 12) 1 false =
      .ok (.bitstring ⟨#[0x7f, 0xf0]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer (-2049)) (.integer 12) 1 true =
      .ok (.bitstring ⟨#[0xff, 0x70]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer (-4097)) (.integer 12) 1 false =
      .ok (.bitstring ⟨#[0xff, 0xf0]⟩ 4 (by decide)) ∧
    Term.Bitstring.integerSegment (.integer (-4097)) (.integer 12) 1 true =
      .ok (.bitstring ⟨#[0xff, 0xf0]⟩ 4 (by decide)) := by
  repeat first | apply And.intro | rfl

theorem zero_width (value : Int) (unit : Nat) (little : Bool)
    (positive : 1 ≤ unit) (bounded : unit ≤ 256) :
    Term.Bitstring.integerSegment (.integer value) (.integer 0) unit little =
      .ok (.bitstring ⟨#[]⟩ 0 (by decide)) := by
  simp [Term.Bitstring.integerSegment, Term.Bitstring.integerBits, Term.Bitstring.ofBits, Term.Bitstring.pack, positive, bounded]

theorem negative_size (value : Term) (width : Int) (unit : Nat) (little : Bool)
    (negative : width < 0) :
    Term.Bitstring.integerSegment value (.integer width) unit little = .error (.error (.atom "badarg")) := by
  have invalid : ¬0 ≤ width := by omega
  cases value <;> simp [Term.Bitstring.integerSegment, invalid]

theorem invalid_operands :
    Term.Bitstring.integerSegment (.atom "bad") (.integer 0) 1 false = .error (.error (.atom "badarg")) ∧
    Term.Bitstring.integerSegment (.integer 1) (.integer (-1)) 1 false = .error (.error (.atom "badarg")) ∧
    Term.Bitstring.integerSegment (.integer 1) (.atom "bad") 1 false = .error (.error (.atom "badarg")) ∧
    Term.Bitstring.integerSegment (.integer 1) (.integer 8) 0 false = .error (.error (.atom "badarg")) ∧
    Term.Bitstring.integerSegment (.integer 1) (.integer 8) 257 false = .error (.error (.atom "badarg")) := by
  repeat first | apply And.intro | rfl

theorem units_and_cross_byte_concatenation :
    Term.Bitstring.integerSegment (.integer 0x123) (.integer 4) 3 false =
      .ok (.bitstring ⟨#[0x12, 0x30]⟩ 4 (by decide)) ∧
    Term.Bitstring.append (.bitstring ⟨#[0xa0]⟩ 3 (by decide))
      (.bitstring ⟨#[0x12, 0x30]⟩ 4 (by decide)) =
        .ok (.bitstring ⟨#[0xa2, 0x46]⟩ 7 (by decide)) := by
  repeat first | apply And.intro | rfl

-- Expected bytes checked against OTP 29. Signed zero and subnormals are encodings,
-- so these comparisons deliberately avoid numeric float equality.
private def floatBytes (value : Term.FiniteFloat) (big little : List UInt8) : Prop :=
  Term.Bitstring.floatSegment (.float value) 64 false =
    .ok (.bitstring ⟨big.toArray⟩ 0 (by intro _; rfl)) ∧
  Term.Bitstring.floatSegment (.float value) 64 true =
    .ok (.bitstring ⟨little.toArray⟩ 0 (by intro _; rfl))

set_option maxRecDepth 2048 in
theorem float64_signed_zeros :
    floatBytes ⟨false, 0, 0⟩ [0, 0, 0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 0] ∧
    floatBytes ⟨true, 0, 0⟩ [128, 0, 0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 128] := by
  repeat first | apply And.intro | rfl

set_option maxRecDepth 2048 in
theorem float64_normal_values :
    floatBytes ⟨false, 1023, 0⟩ [0x3f, 0xf0, 0, 0, 0, 0, 0, 0]
      [0, 0, 0, 0, 0, 0, 0xf0, 0x3f] ∧
    floatBytes ⟨true, 1023, 2 ^ 51⟩ [0xbf, 0xf8, 0, 0, 0, 0, 0, 0]
      [0, 0, 0, 0, 0, 0, 0xf8, 0xbf] := by
  repeat first | apply And.intro | rfl

set_option maxRecDepth 2048 in
theorem float64_extremes :
    floatBytes ⟨false, 0, 1⟩ [0, 0, 0, 0, 0, 0, 0, 1] [1, 0, 0, 0, 0, 0, 0, 0] ∧
    floatBytes ⟨false, 1, 0⟩ [0, 0x10, 0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0x10, 0] ∧
    floatBytes ⟨false, 2046, 2 ^ 52 - 1⟩
      [0x7f, 0xef, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
      [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xef, 0x7f] := by
  repeat first | apply And.intro | rfl

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 4096 in
theorem float64_integer_conversion :
    Term.Bitstring.floatSegment (.integer 1) 64 false =
      .ok (.bitstring ⟨#[0x3f, 0xf0, 0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) ∧
    Term.Bitstring.floatSegment (.integer (-1)) 64 true =
      .ok (.bitstring ⟨#[0, 0, 0, 0, 0, 0, 0xf0, 0xbf]⟩ 0 (by decide)) ∧
    Term.Bitstring.floatSegment (.integer (2 ^ 53 + 1)) 64 false =
      .ok (.bitstring ⟨#[0x43, 0x40, 0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) ∧
    Term.Bitstring.floatSegment (.integer (2 ^ 53 + 3)) 64 false =
      .ok (.bitstring ⟨#[0x43, 0x40, 0, 0, 0, 0, 0, 2]⟩ 0 (by decide)) ∧
    Term.Bitstring.floatSegment (.integer (-(2 ^ 53 + 1))) 64 false =
      .ok (.bitstring ⟨#[0xc3, 0x40, 0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) ∧
    Term.Bitstring.floatSegment (.integer (2 ^ 1024)) 64 false =
      .error (.error (.atom "badarg")) := by
  repeat first | apply And.intro | rfl

theorem float64_size (value : Term.FiniteFloat) (little : Bool) :
    ∃ result, Term.Bitstring.floatSegment (.float value) 64 little = .ok result ∧
      size result = 64 := by
  let encoded : Nat := (if value.negative then 2 ^ 63 else 0) +
    value.exponent.val * 2 ^ 52 + value.fraction.val
  refine ⟨Term.Bitstring.ofBits (Term.Bitstring.integerBits (Int.ofNat encoded) 64 little), ?_, ?_⟩
  · rfl
  · rw [ofBits_preserves_size]
    simp [Term.Bitstring.integerBits]

set_option maxRecDepth 2048 in
theorem float64_unaligned_concatenation :
    ((Term.Bitstring.floatSegment (.float ⟨false, 1023, 0⟩) 64 true).bind fun encoded =>
      (Term.Bitstring.append (.bitstring ⟨#[0x20]⟩ 3 (by decide)) encoded).bind fun joined =>
        Term.Bitstring.append joined (.bitstring ⟨#[0xf8]⟩ 5 (by decide))) =
      .ok (.bitstring ⟨#[32, 0, 0, 0, 0, 0, 30, 7, 255]⟩ 0 (by decide)) := by
  rfl

theorem unimplemented_float_widths (value : Term) (little : Bool) :
    Term.Bitstring.floatSegment value 16 little = .error (.error (.atom "badarg")) ∧
    Term.Bitstring.floatSegment value 32 little = .error (.error (.atom "badarg")) := by
  constructor <;> rfl

end LynxTest.Term.Bitstring.Construction

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Bitstring.Construction
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Bitstring.Construction
