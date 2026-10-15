module

import Lynx
public meta import LynxTest.ProofAudit

namespace LynxTest.Term.Bitstring.Matching

open Lynx

private def bits (term : Term) : List Bool :=
  match term with
  | .bitstring bytes last _ => Term.Bitstring.toBits bytes last
  | _ => []

private def empty : Term := .bitstring ⟨#[]⟩ 0 (by decide)

-- Extraction preserves the remainder for every value, width, unit, and endian.
theorem integer_consumes_exact_width (input : List Bool) (width unit : Nat)
    (signed little : Bool) (positive : 1 ≤ unit) (bounded : unit ≤ 256)
    (enough : width * unit ≤ input.length) :
    ∃ value rest, Term.Bitstring.matchInteger (Term.Bitstring.ofBits input)
      (.integer width) unit signed little = some (.integer value, rest) ∧
      bits rest = input.drop (width * unit) := by
  simp [Term.Bitstring.matchInteger, Term.Bitstring.ofBits, Term.Bitstring.pack_toBits,
    positive, bounded, enough, bits]
  refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
  simpa using Term.Bitstring.pack_toBits (input.drop (width * unit))

theorem short_integer_input (input : List Bool) (width unit : Nat) (signed little : Bool)
    (short : input.length < width * unit) :
    Term.Bitstring.matchInteger (Term.Bitstring.ofBits input)
      (.integer width) unit signed little = none := by
  simp [Term.Bitstring.matchInteger, Term.Bitstring.ofBits,
    Term.Bitstring.pack_toBits, Nat.not_le_of_gt short]

theorem integer_zero_width (input : List Bool) (signed little : Bool) :
    Term.Bitstring.matchInteger (Term.Bitstring.ofBits input) (.integer 0) 1 signed little =
      some (.integer 0, Term.Bitstring.ofBits input) := by
  simp [Term.Bitstring.matchInteger, Term.Bitstring.ofBits, Term.Bitstring.pack_toBits,
    Term.Bitstring.decodeInteger]

theorem integer_signed_boundaries :
    Term.Bitstring.matchInteger (.bitstring ⟨#[0x7f]⟩ 0 (by decide)) (.integer 8) 1 true false =
      some (.integer 127, empty) ∧
    Term.Bitstring.matchInteger (.bitstring ⟨#[0x80]⟩ 0 (by decide)) (.integer 8) 1 true false =
      some (.integer (-128), empty) ∧
    Term.Bitstring.matchInteger (.bitstring ⟨#[0xff]⟩ 0 (by decide)) (.integer 8) 1 true false =
      some (.integer (-1), empty) ∧
    Term.Bitstring.matchInteger (.bitstring ⟨#[0xff]⟩ 0 (by decide)) (.integer 8) 1 false false =
      some (.integer 255, empty) := by
  repeat first | apply And.intro | rfl

theorem integer_partial_little_endian :
    Term.Bitstring.matchInteger (.bitstring ⟨#[0x23, 0x10]⟩ 4 (by decide)) (.integer 12) 1 false true =
      some (.integer 0x123, empty) ∧
    Term.Bitstring.matchInteger (.bitstring ⟨#[0xfe, 0xf0]⟩ 4 (by decide)) (.integer 12) 1 true true =
      some (.integer (-2), empty) ∧
    Term.Bitstring.matchInteger (.bitstring ⟨#[0xff, 0x70]⟩ 4 (by decide)) (.integer 12) 1 true true =
      some (.integer 2047, empty) ∧
    Term.Bitstring.matchInteger (.bitstring ⟨#[0x12, 0x3a]⟩ 0 (by decide)) (.integer 4) 3 false false =
      some (.integer 0x123, .bitstring ⟨#[0xa0]⟩ 4 (by decide)) := by
  repeat first | apply And.intro | rfl

theorem integer_pattern_failures :
    Term.Bitstring.matchInteger (.atom "bad") (.integer 0) 1 false false = none ∧
    Term.Bitstring.matchInteger empty (.atom "bad") 1 false false = none ∧
    Term.Bitstring.matchInteger empty (.integer (-1)) 1 false false = none ∧
    Term.Bitstring.matchInteger empty (.integer 1) 1 false false = none ∧
    Term.Bitstring.matchInteger empty (.integer 0) 0 false false = none ∧
    Term.Bitstring.matchInteger empty (.integer 0) 257 false false = none := by
  repeat first | apply And.intro | rfl

/-- Successful float extraction always returns a finite float term. -/
theorem float_extraction_returns_float (input : Term) (width : Nat) (little : Bool)
    (value rest : Term) (returned : Term.Bitstring.matchFloat input width little = some (value, rest)) :
    ∃ float : Term.FiniteFloat, value = .float float := by
  simp only [Term.Bitstring.matchFloat] at returned
  split at returned
  · contradiction
  · cases read : Term.Bitstring.matchInteger input (.integer 64) 1 Bool.false little with
    | none => simp [read] at returned
    | some pair =>
      rcases pair with ⟨head, tail⟩
      cases head <;> simp [read, Bind.bind, Option.bind] at returned
      obtain ⟨⟨_, equality⟩, _⟩ := returned
      exact ⟨_, equality.symm⟩


set_option maxRecDepth 2048 in
theorem float64_signed_zero_and_subnormal :
    Term.Bitstring.matchFloat (.bitstring ⟨#[0x80, 0, 0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) 64 false =
      some (.float ⟨true, 0, 0⟩, empty) ∧
    Term.Bitstring.matchFloat (.bitstring ⟨#[0, 0, 0, 0, 0, 0, 0, 0x80]⟩ 0 (by decide)) 64 true =
      some (.float ⟨true, 0, 0⟩, empty) ∧
    Term.Bitstring.matchFloat (.bitstring ⟨#[0, 0, 0, 0, 0, 0, 0, 1]⟩ 0 (by decide)) 64 false =
      some (.float ⟨false, 0, 1⟩, empty) := by
  repeat first | apply And.intro | rfl

set_option maxRecDepth 2048 in
theorem float64_normal_and_extreme :
    Term.Bitstring.matchFloat (.bitstring ⟨#[0x3f, 0xf0, 0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) 64 false =
      some (.float ⟨false, 1023, 0⟩, empty) ∧
    Term.Bitstring.matchFloat (.bitstring ⟨#[0, 0, 0, 0, 0, 0, 0xf8, 0xbf]⟩ 0 (by decide)) 64 true =
      some (.float ⟨true, 1023, 2 ^ 51⟩, empty) ∧
    Term.Bitstring.matchFloat (.bitstring ⟨#[0x7f, 0xef, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]⟩
      0 (by decide)) 64 false = some (.float ⟨false, 2046, 2 ^ 52 - 1⟩, empty) := by
  repeat first | apply And.intro | rfl

set_option maxRecDepth 2048 in
theorem float64_rejects_nonfinite_and_short_inputs :
    Term.Bitstring.matchFloat (.bitstring ⟨#[0x7f, 0xf0, 0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) 64 false = none ∧
    Term.Bitstring.matchFloat (.bitstring ⟨#[0x7f, 0xf8, 0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) 64 false = none ∧
    Term.Bitstring.matchFloat (.bitstring ⟨#[0x3f, 0xf0, 0, 0, 0, 0, 0]⟩ 0 (by decide)) 64 false = none := by
  repeat first | apply And.intro | rfl

theorem tail_alignment :
    Term.Bitstring.matchTail (.bitstring ⟨#[0xab]⟩ 0 (by decide)) (.atom "all") 8 = true ∧
    Term.Bitstring.matchTail (.bitstring ⟨#[0xa0]⟩ 3 (by decide)) (.atom "all") 8 = false ∧
    Term.Bitstring.matchTail (.bitstring ⟨#[0xa0]⟩ 3 (by decide)) (.atom "all") 1 = true ∧
    Term.Bitstring.matchTail empty (.atom "all") 8 = true ∧
    Term.Bitstring.matchTail (.atom "bad") (.atom "all") 1 = false := by
  repeat first | apply And.intro | rfl

theorem fixed_tail_sizes :
    Term.Bitstring.matchTail (.bitstring ⟨#[0xab]⟩ 0 (by decide)) (.integer 1) 8 = true ∧
    Term.Bitstring.matchTail (.bitstring ⟨#[0xab]⟩ 0 (by decide)) (.integer 2) 8 = false ∧
    Term.Bitstring.matchTail (.bitstring ⟨#[0xab]⟩ 0 (by decide)) (.integer 0) 8 = false ∧
    Term.Bitstring.matchTail empty (.integer 0) 8 = true ∧
    Term.Bitstring.matchTail empty (.integer (-1)) 8 = false ∧
    Term.Bitstring.matchTail (.bitstring ⟨#[0xa0]⟩ 3 (by decide)) (.integer 3) 1 = true := by
  repeat first | apply And.intro | rfl

theorem finish_requires_no_remaining_bits :
    Term.Bitstring.matchEnd empty = true ∧
    Term.Bitstring.matchEnd (.bitstring ⟨#[0]⟩ 1 (by decide)) = false ∧
    Term.Bitstring.matchEnd (.atom "bad") = false := by
  repeat first | apply And.intro | rfl

theorem size_from_previous_segment :
    ((Term.Bitstring.matchInteger (.bitstring ⟨#[12, 254, 250]⟩ 7 (by decide))
        (.integer 8) 1 false false).bind fun (width, remaining) =>
      (Term.Bitstring.matchInteger remaining width 1 true true).bind fun (value, tail) =>
        if Term.Bitstring.matchTail tail (.atom "all") 1 then some (width, value, tail) else none) =
      some (.integer 12, .integer (-2), .bitstring ⟨#[0xa0]⟩ 3 (by decide)) := by
  rfl

theorem consecutive_integer_segments :
    ((Term.Bitstring.matchInteger (.bitstring ⟨#[0xff, 0x80, 0x0f, 0xff]⟩ 0 (by decide))
        (.integer 8) 1 false false).bind fun (first, remaining) =>
      (Term.Bitstring.matchInteger remaining (.integer 12) 1 true false).bind fun (second, remaining) =>
        (Term.Bitstring.matchInteger remaining (.integer 12) 1 true true).bind fun (third, remaining) =>
          if Term.Bitstring.matchEnd remaining then some (first, second, third) else none) =
      some (.integer 255, .integer (-2048), .integer (-1)) := by
  rfl

theorem unaligned_binary_capture :
    ((Term.Bitstring.matchInteger (.bitstring ⟨#[0xb5, 0x60]⟩ 3 (by decide))
        (.integer 3) 1 false false).bind fun (tag, remaining) =>
      if Term.Bitstring.matchTail remaining (.atom "all") 8 then some (tag, remaining) else none) =
      some (.integer 5, .bitstring ⟨#[0xab]⟩ 0 (by decide)) := by
  rfl

theorem unaligned_capture_requires_binary_length :
    ((Term.Bitstring.matchInteger (.bitstring ⟨#[0xb0]⟩ 4 (by decide))
        (.integer 3) 1 false false).bind fun (_, remaining) =>
      if Term.Bitstring.matchTail remaining (.atom "all") 8 then some remaining else none) = none ∧
    ((Term.Bitstring.matchInteger (.bitstring ⟨#[0xb0]⟩ 4 (by decide))
        (.integer 3) 1 false false).bind fun (tag, remaining) =>
      if Term.Bitstring.matchTail remaining (.atom "all") 1 then some (tag, remaining) else none) =
      some (.integer 5, .bitstring ⟨#[0x80]⟩ 1 (by decide)) := by
  constructor <;> rfl

private def literalPrefixTail (input : Term) (unit : Nat) : Option Term :=
  match Term.Bitstring.matchInteger input (.integer 3) 1 false false with
  | some (.integer 1, remaining) =>
    if Term.Bitstring.matchTail remaining (.atom "all") unit then some remaining else none
  | _ => none

theorem literal_prefix_tail :
    literalPrefixTail (.bitstring ⟨#[0x35, 0x60]⟩ 3 (by decide)) 8 =
      some (.bitstring ⟨#[0xab]⟩ 0 (by decide)) ∧
    literalPrefixTail (.bitstring ⟨#[0x35, 0x60]⟩ 3 (by decide)) 1 =
      some (.bitstring ⟨#[0xab]⟩ 0 (by decide)) ∧
    literalPrefixTail (.bitstring ⟨#[0x30]⟩ 4 (by decide)) 1 =
      some (.bitstring ⟨#[0x80]⟩ 1 (by decide)) ∧
    literalPrefixTail (.bitstring ⟨#[0x30]⟩ 4 (by decide)) 8 = none ∧
    literalPrefixTail (.bitstring ⟨#[0x20]⟩ 3 (by decide)) 1 = some empty ∧
    literalPrefixTail (.bitstring ⟨#[0x20]⟩ 3 (by decide)) 8 = some empty ∧
    literalPrefixTail (.bitstring ⟨#[0x55, 0x60]⟩ 3 (by decide)) 1 = none ∧
    literalPrefixTail (.bitstring ⟨#[0]⟩ 2 (by decide)) 1 = none := by
  repeat first | apply And.intro | rfl

private def matchesFullLiteral (input : Term) : Bool :=
  match input with
  | .bitstring ⟨⟨[97, 98, 99]⟩⟩ 0 _ => true
  | _ => false

theorem full_literal_pattern_requires_exact_bytes_and_length :
    matchesFullLiteral (.bitstring ⟨#[97, 98, 99]⟩ 0 (by decide)) = true ∧
    matchesFullLiteral (.bitstring ⟨#[97, 98]⟩ 0 (by decide)) = false ∧
    matchesFullLiteral (.bitstring ⟨#[97, 98, 99, 100]⟩ 0 (by decide)) = false ∧
    matchesFullLiteral (.bitstring ⟨#[97, 98, 100]⟩ 0 (by decide)) = false ∧
    matchesFullLiteral (.bitstring ⟨#[97, 98, 98]⟩ 7 (by decide)) = false ∧
    matchesFullLiteral (.atom "abc") = false := by
  repeat first | apply And.intro | rfl

private def matchesPartialLiteral (input : Term) : Bool :=
  match input with
  | .bitstring ⟨⟨[160]⟩⟩ ⟨3, _⟩ _ => true
  | _ => false

theorem partial_literal_pattern :
    matchesPartialLiteral (Term.Bitstring.ofBits [true, false, true]) = true ∧
    matchesPartialLiteral (.bitstring ⟨#[0xa0]⟩ 3 (by decide)) = true ∧
    matchesPartialLiteral (.bitstring ⟨#[0x80]⟩ 3 (by decide)) = false ∧
    matchesPartialLiteral (.bitstring ⟨#[0xa0]⟩ 4 (by decide)) = false ∧
    matchesPartialLiteral (.bitstring ⟨#[0xa0]⟩ 0 (by decide)) = false ∧
    matchesPartialLiteral (.bitstring ⟨#[0xa0, 0]⟩ 3 (by decide)) = false ∧
    matchesPartialLiteral empty = false := by
  repeat first | apply And.intro | rfl

end LynxTest.Term.Bitstring.Matching

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Bitstring.Matching
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Bitstring.Matching
