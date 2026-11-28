-- The automaton both sides of json run to validate multibyte UTF-8 sequences.
module

public import Bytes

public section

namespace JsonProof
open Lynx

/-- The class of each byte in `json`'s UTF-8 automaton. -/
@[expose] def utf8Types : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
   9, 9, 9, 9, 9, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
   7, 7, 7, 7, 7, 7, 8, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 10, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 11, 6, 6, 6, 5, 8, 8,
   8, 8, 8, 8, 8, 8, 8, 8, 8]

/-- The state after the first byte of a sequence, for bytes from 128. -/
@[expose] def utf8Starts : List Nat :=
  [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
   12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
   12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 24, 24, 24,
   24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
   24, 24, 24, 24, 48, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 60, 36, 36, 72, 84, 84,
   84, 96, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]

/-- The transitions of the automaton, indexed by the state plus the class of a byte, from one. -/
@[expose] def utf8Steps : List Nat :=
  [12, 24, 36, 60, 96, 84, 12, 12, 12, 48, 72, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
   12, 0, 12, 12, 12, 12, 12, 0, 12, 0, 12, 12, 12, 24, 12, 12, 12, 12, 12, 24, 12, 24, 12, 12,
   12, 12, 12, 12, 12, 12, 12, 24, 12, 12, 12, 12, 12, 24, 12, 12, 12, 12, 12, 12, 12, 24, 12,
   12, 12, 12, 12, 12, 12, 12, 12, 36, 12, 36, 12, 12, 12, 36, 12, 12, 12, 12, 12, 36, 12, 36,
   12, 12, 12, 36, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]

@[expose] def utf8Start (b : UInt8) : Nat := utf8Starts.getD (b.toNat - 128) 0

@[expose] def utf8Next (state : Nat) (c : UInt8) : Nat :=
  utf8Steps.getD (state + utf8Types.getD c.toNat 0 - 1) 0

private theorem type_cont : ∀ n, n < 256 → 0x80 ≤ n → n ≤ 0xBF →
    utf8Types.getD n 0 = 1 ∨ utf8Types.getD n 0 = 9 ∨ utf8Types.getD n 0 = 7 := by
  decide +kernel

private theorem type_high : ∀ n, n < 256 → 0xA0 ≤ n → n ≤ 0xBF → utf8Types.getD n 0 = 7 := by
  decide +kernel

private theorem type_low : ∀ n, n < 256 → 0x80 ≤ n → n ≤ 0x9F →
    utf8Types.getD n 0 = 1 ∨ utf8Types.getD n 0 = 9 := by
  decide +kernel

private theorem type_upper : ∀ n, n < 256 → 0x90 ≤ n → n ≤ 0xBF →
    utf8Types.getD n 0 = 9 ∨ utf8Types.getD n 0 = 7 := by
  decide +kernel

private theorem type_lowest : ∀ n, n < 256 → 0x80 ≤ n → n ≤ 0x8F → utf8Types.getD n 0 = 1 := by
  decide +kernel

private theorem start_two : ∀ n, n < 256 → 0xC2 ≤ n → n ≤ 0xDF → utf8Starts.getD (n - 128) 0 = 24 := by
  decide +kernel

private theorem start_three : ∀ n, n < 256 → ((0xE1 ≤ n ∧ n ≤ 0xEC) ∨ (0xEE ≤ n ∧ n ≤ 0xEF)) →
    utf8Starts.getD (n - 128) 0 = 36 := by
  decide +kernel

private theorem start_four : ∀ n, n < 256 → 0xF1 ≤ n → n ≤ 0xF3 → utf8Starts.getD (n - 128) 0 = 84 := by
  decide +kernel

/-- The automaton accepts a two-byte sequence after its second byte. -/
theorem utf8_two (b c : UInt8) (lead : lead2 b c) : utf8Start b = 24 ∧ utf8Next 24 c = 0 := by
  obtain ⟨low, high, contLow, contHigh⟩ := lead
  refine ⟨start_two _ b.toNat_lt low high, ?_⟩
  unfold utf8Next
  rcases type_cont _ c.toNat_lt contLow contHigh with h | h | h <;> rw [h] <;> rfl

/-- The automaton is in state 24 after the second byte of a three-byte sequence. -/
theorem utf8_three (b c d : UInt8) (lead : lead3 b c d) :
    utf8Start b ≠ 0 ∧ utf8Start b ≠ 12 ∧ utf8Next (utf8Start b) c = 24 ∧ utf8Next 24 d = 0 := by
  obtain ⟨first, dLow, dHigh⟩ := lead
  have last : utf8Next 24 d = 0 := by
    unfold utf8Next
    rcases type_cont _ d.toNat_lt dLow dHigh with h | h | h <;> rw [h] <;> rfl
  unfold utf8Start utf8Next
  rcases first with ⟨e0, cLow, cHigh⟩ | ⟨bLow, bHigh, cLow, cHigh⟩ | ⟨ed, cLow, cHigh⟩ |
      ⟨bLow, bHigh, cLow, cHigh⟩
  · rw [e0, type_high _ c.toNat_lt cLow cHigh]
    exact ⟨by decide, by decide, rfl, last⟩
  · rw [start_three _ b.toNat_lt (Or.inl ⟨bLow, bHigh⟩)]
    rcases type_cont _ c.toNat_lt cLow cHigh with h | h | h <;> rw [h] <;>
      exact ⟨by decide, by decide, rfl, last⟩
  · rw [ed]
    rcases type_low _ c.toNat_lt cLow cHigh with h | h <;> rw [h] <;>
      exact ⟨by decide, by decide, rfl, last⟩
  · rw [start_three _ b.toNat_lt (Or.inr ⟨bLow, bHigh⟩)]
    rcases type_cont _ c.toNat_lt cLow cHigh with h | h | h <;> rw [h] <;>
      exact ⟨by decide, by decide, rfl, last⟩

/-- The automaton is in states 36 and 24 after the second and third bytes of a four-byte
sequence. -/
theorem utf8_four (b c d e : UInt8) (lead : lead4 b c d e) :
    utf8Start b ≠ 0 ∧ utf8Start b ≠ 12 ∧ utf8Next (utf8Start b) c = 36 ∧ utf8Next 36 d = 24 ∧
      utf8Next 24 e = 0 := by
  obtain ⟨first, ⟨dLow, dHigh⟩, eLow, eHigh⟩ := lead
  have third : utf8Next 36 d = 24 := by
    unfold utf8Next
    rcases type_cont _ d.toNat_lt dLow dHigh with h | h | h <;> rw [h] <;> rfl
  have last : utf8Next 24 e = 0 := by
    unfold utf8Next
    rcases type_cont _ e.toNat_lt eLow eHigh with h | h | h <;> rw [h] <;> rfl
  unfold utf8Start utf8Next
  rcases first with ⟨f0, cLow, cHigh⟩ | ⟨bLow, bHigh, cLow, cHigh⟩ | ⟨f4, cLow, cHigh⟩
  · rw [f0]
    rcases type_upper _ c.toNat_lt cLow cHigh with h | h <;> rw [h] <;>
      exact ⟨by decide, by decide, rfl, third, last⟩
  · rw [start_four _ b.toNat_lt bLow bHigh]
    rcases type_cont _ c.toNat_lt cLow cHigh with h | h | h <;> rw [h] <;>
      exact ⟨by decide, by decide, rfl, third, last⟩
  · rw [f4, type_lowest _ c.toNat_lt cLow cHigh]
    exact ⟨by decide, by decide, rfl, third, last⟩

/-- Every state the automaton starts in is a row of its transitions. -/
theorem utf8Start_le (b : UInt8) : utf8Start b ≤ 96 := by
  have all : ∀ n, n < 256 → utf8Starts.getD (n - 128) 0 ≤ 96 := by decide +kernel
  exact all b.toNat b.toNat_lt

/-- Every byte class indexes into a row of the transitions. -/
theorem utf8Type_le (c : UInt8) : utf8Types.getD c.toNat 0 ≤ 11 := by
  have all : ∀ n, n < 256 → utf8Types.getD n 0 ≤ 11 := by decide +kernel
  exact all c.toNat c.toNat_lt

end JsonProof
