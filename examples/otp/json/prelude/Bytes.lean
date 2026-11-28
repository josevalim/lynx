-- Facts about the byte guards of json's string encoder and decoder, which
-- need no translated definitions.
module

public import Decoding

public section

namespace JsonProof
open Lynx

/-- The big-endian value of bytes, as `matchInteger_bytes` reads them. -/
@[expose] def bytesValue (l : List UInt8) : Nat := l.foldl (fun value b => value * 256 + b.toNat) 0

theorem bytesValue_snoc (l : List UInt8) (b : UInt8) :
    bytesValue (l ++ [b]) = bytesValue l * 256 + b.toNat := by
  simp [bytesValue, List.foldl_append]

/-- Erlang's `band/2` on integers. -/
@[expose] def iband : Int → Int → Int
  | .ofNat x, .ofNat y => .ofNat (x &&& y)
  | .ofNat x, .negSucc y => .ofNat (x ^^^ (x &&& y))
  | .negSucc x, .ofNat y => .ofNat (y ^^^ (y &&& x))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)

/-- Erlang's `bxor/2` on integers. -/
@[expose] def ixor : Int → Int → Int
  | .ofNat x, .ofNat y => .ofNat (x ^^^ y)
  | .ofNat x, .negSucc y => .negSucc (x ^^^ y)
  | .negSucc x, .ofNat y => .negSucc (x ^^^ y)
  | .negSucc x, .negSucc y => .ofNat (x ^^^ y)

private theorem split256 (z : Nat) : z = z / 256 * 256 + z % 256 := by omega

theorem and_byte (x a y c : Nat) (ha : a < 256) (hc : c < 256) :
    (x * 256 + a) &&& (y * 256 + c) = (x &&& y) * 256 + (a &&& c) := by
  rw [split256 ((x * 256 + a) &&& (y * 256 + c))]
  have div := Nat.and_div_two_pow (a := x * 256 + a) (b := y * 256 + c) (n := 8)
  have mod := Nat.and_mod_two_pow (a := x * 256 + a) (b := y * 256 + c) (n := 8)
  simp only [show (2 : Nat) ^ 8 = 256 from rfl] at div mod
  rw [div, mod, show (x * 256 + a) / 256 = x by omega, show (y * 256 + c) / 256 = y by omega,
    show (x * 256 + a) % 256 = a by omega, show (y * 256 + c) % 256 = c by omega]

theorem xor_byte (x a y c : Nat) (ha : a < 256) (hc : c < 256) :
    (x * 256 + a) ^^^ (y * 256 + c) = (x ^^^ y) * 256 + (a ^^^ c) := by
  rw [split256 ((x * 256 + a) ^^^ (y * 256 + c))]
  have div := Nat.xor_div_two_pow (a := x * 256 + a) (b := y * 256 + c) (n := 8)
  have mod := Nat.xor_mod_two_pow (a := x * 256 + a) (b := y * 256 + c) (n := 8)
  simp only [show (2 : Nat) ^ 8 = 256 from rfl] at div mod
  rw [div, mod, show (x * 256 + a) / 256 = x by omega, show (y * 256 + c) / 256 = y by omega,
    show (x * 256 + a) % 256 = a by omega, show (y * 256 + c) % 256 = c by omega]

private theorem high_byte : ∀ r, r < 256 → 128 ^^^ (128 &&& (255 - r)) = r &&& 128 := by
  decide +kernel

theorem iband_byte (q : Int) (r m : Nat) (hr : r < 256) :
    iband (q * 256 + r) ((m * 256 + 128 : Nat) : Int) =
      iband q m * 256 + ((r &&& 128 : Nat) : Int) := by
  cases q with
  | ofNat a =>
    have : (Int.ofNat a * 256 + r : Int) = Int.ofNat (a * 256 + r) := by simp
    rw [this]
    simp only [iband, Int.ofNat_eq_natCast]
    rw [and_byte a r m 128 hr (by decide)]
    simp
  | negSucc a =>
    have : (Int.negSucc a * 256 + r : Int) = Int.negSucc (a * 256 + (255 - r)) := by
      simp [Int.negSucc_eq]; omega
    rw [this]
    simp only [iband, Int.ofNat_eq_natCast]
    rw [and_byte m 128 a (255 - r) (by decide) (by omega),
      xor_byte m 128 (m &&& a) (128 &&& (255 - r)) (by decide)
        (Nat.lt_of_le_of_lt Nat.and_le_left (by decide)),
      high_byte r hr]
    simp

theorem plain_iff (b : UInt8) :
    plain b = true ↔ (b.toNat &&& 128 = 0 ∧ (b.toNat + 96) &&& 128 = 128 ∧
      b.toNat ^^^ 34 ≠ 0 ∧ b.toNat ^^^ 92 ≠ 0) := by
  have all : ∀ n, n < 256 → ((32 ≤ n && n < 128 && n != 34 && n != 92) = true ↔
      (n &&& 128 = 0 ∧ (n + 96) &&& 128 = 128 ∧ n ^^^ 34 ≠ 0 ∧ n ^^^ 92 ≠ 0)) := by
    decide +kernel
  exact all b.toNat b.toNat_lt

/-- Subtracting one from each byte borrows from a zero byte into its high bit. -/
theorem iband_sub_byte (x r m e : Nat) (he : e < 256)
    (zero : iband (((x * 256 + e : Nat) : Int) - ((r * 256 + 1 : Nat) : Int))
      ((m * 256 + 128 : Nat) : Int) = 0) :
    e ≠ 0 ∧ iband ((x : Int) - r) m = 0 := by
  by_cases e0 : e = 0
  · subst e0
    rw [show (((x * 256 + 0 : Nat) : Int) - ((r * 256 + 1 : Nat) : Int)) =
        ((x : Int) - r - 1) * 256 + ((255 : Nat) : Int) by omega,
      iband_byte _ _ _ (by decide)] at zero
    have : ((255 &&& 128 : Nat) : Int) = 128 := by decide
    omega
  · rw [show (((x * 256 + e : Nat) : Int) - ((r * 256 + 1 : Nat) : Int)) =
        ((x : Int) - r) * 256 + ((e - 1 : Nat) : Int) by omega,
      iband_byte _ _ _ (by omega)] at zero
    have := Nat.and_le_right (n := e - 1) (m := 128)
    exact ⟨e0, by omega⟩

/-- One byte of the SWAR test: the low byte needs no escaping and the test
holds for the bytes above it. -/
theorem swar_byte (v b r128 r96 r34 r92 r1 : Nat) (hb : b < 256)
    (h1 : (v * 256 + b) &&& (r128 * 256 + 128) = 0)
    (h2 : (v * 256 + b + (r96 * 256 + 96)) &&& (r128 * 256 + 128) = r128 * 256 + 128)
    (h3 : iband ((((v * 256 + b) ^^^ (r34 * 256 + 34) : Nat) : Int) - ((r1 * 256 + 1 : Nat) : Int))
      ((r128 * 256 + 128 : Nat) : Int) = 0)
    (h4 : iband ((((v * 256 + b) ^^^ (r92 * 256 + 92) : Nat) : Int) - ((r1 * 256 + 1 : Nat) : Int))
      ((r128 * 256 + 128 : Nat) : Int) = 0) :
    (b &&& 128 = 0 ∧ (b + 96) &&& 128 = 128 ∧ b ^^^ 34 ≠ 0 ∧ b ^^^ 92 ≠ 0) ∧
    v &&& r128 = 0 ∧ (v + r96) &&& r128 = r128 ∧
    iband (((v ^^^ r34 : Nat) : Int) - r1) r128 = 0 ∧
    iband (((v ^^^ r92 : Nat) : Int) - r1) r128 = 0 := by
  rw [and_byte _ _ _ _ hb (by decide)] at h1
  have and128 (n : Nat) : n &&& 128 ≤ 128 := Nat.and_le_right
  have low1 : b &&& 128 = 0 := by have := and128 b; omega
  have b128 : b < 128 := by
    have : ∀ x, x < 256 → x &&& 128 = 0 → x < 128 := by decide +kernel
    exact this b hb low1
  rw [show v * 256 + b + (r96 * 256 + 96) = (v + r96) * 256 + (b + 96) by clear h1 h2 h3 h4; omega,
    and_byte (v + r96) (b + 96) r128 128 (by omega) (by decide)] at h2
  have low2 : (b + 96) &&& 128 = 128 := by have := and128 (b + 96); omega
  rw [xor_byte _ _ _ _ hb (by decide)] at h3 h4
  obtain ⟨ne34, high3⟩ := iband_sub_byte _ _ _ _ (Nat.xor_lt_two_pow (n := 8) hb (by decide)) h3
  obtain ⟨ne92, high4⟩ := iband_sub_byte _ _ _ _ (Nat.xor_lt_two_pow (n := 8) hb (by decide)) h4
  exact ⟨⟨low1, low2, ne34, ne92⟩, by omega, by omega, high3, high4⟩

/-- The SWAR test of `json` passes only on bytes that need no escaping. -/
theorem swar_sound (l : List UInt8) :
    bytesValue l &&& bytesValue (List.replicate l.length 128) = 0 →
    (bytesValue l + bytesValue (List.replicate l.length 96)) &&&
        bytesValue (List.replicate l.length 128) = bytesValue (List.replicate l.length 128) →
    iband (((bytesValue l ^^^ bytesValue (List.replicate l.length 34) : Nat) : Int) -
        bytesValue (List.replicate l.length 1)) (bytesValue (List.replicate l.length 128)) = 0 →
    iband (((bytesValue l ^^^ bytesValue (List.replicate l.length 92) : Nat) : Int) -
        bytesValue (List.replicate l.length 1)) (bytesValue (List.replicate l.length 128)) = 0 →
    ∀ b ∈ l, plain b := by
  obtain ⟨r, rfl⟩ : ∃ r, l = r.reverse := ⟨l.reverse, by simp⟩
  induction r with
  | nil => simp
  | cons b r ih =>
    intro h1 h2 h3 h4
    rw [List.reverse_cons] at h1 h2 h3 h4 ⊢
    generalize r.reverse = l at ih h1 h2 h3 h4 ⊢
    simp only [List.length_append, List.length_singleton, List.replicate_succ',
      bytesValue_snoc] at h1 h2 h3 h4
    simp only [show (128 : UInt8).toNat = 128 from rfl, show (96 : UInt8).toNat = 96 from rfl,
      show (34 : UInt8).toNat = 34 from rfl, show (92 : UInt8).toNat = 92 from rfl,
      show (1 : UInt8).toNat = 1 from rfl] at h1 h2 h3 h4
    obtain ⟨low, high1, high2, high3, high4⟩ := swar_byte _ _ _ _ _ _ _ b.toNat_lt h1 h2 h3 h4
    intro x mem
    rcases List.mem_append.mp mem with mem | mem
    · exact ih high1 high2 high3 high4 x mem
    · simp only [List.mem_singleton] at mem
      subst mem
      exact (plain_iff x).mpr low

theorem isMember_naturals (n : Nat) (l : List Nat) :
    Term.isMember (.integer n) (l.map fun k : Nat => .integer k) =
      if n ∈ l then .atom "true" else .atom "false" := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, Term.isMember_cons, Term.compareExact_integers, ih, List.mem_cons]
    by_cases h : n = x
    · simp [h]
    · have : (n : Int) ≠ x := by omega
      simp [h, this]

/-- `json`'s guard for bytes that strings carry without escaping. -/
theorem isMember_plain (b : UInt8) :
    Term.isMember (.integer b.toNat)
      [.integer 32, .integer 33, .integer 35, .integer 36, .integer 37, .integer 38,
      .integer 39, .integer 40, .integer 41, .integer 42, .integer 43, .integer 44,
      .integer 45, .integer 46, .integer 47, .integer 48, .integer 49, .integer 50,
      .integer 51, .integer 52, .integer 53, .integer 54, .integer 55, .integer 56,
      .integer 57, .integer 58, .integer 59, .integer 60, .integer 61, .integer 62,
      .integer 63, .integer 64, .integer 65, .integer 66, .integer 67, .integer 68,
      .integer 69, .integer 70, .integer 71, .integer 72, .integer 73, .integer 74,
      .integer 75, .integer 76, .integer 77, .integer 78, .integer 79, .integer 80,
      .integer 81, .integer 82, .integer 83, .integer 84, .integer 85, .integer 86,
      .integer 87, .integer 88, .integer 89, .integer 90, .integer 91, .integer 93,
      .integer 94, .integer 95, .integer 96, .integer 97, .integer 98, .integer 99,
      .integer 100, .integer 101, .integer 102, .integer 103, .integer 104,
      .integer 105, .integer 106, .integer 107, .integer 108, .integer 109,
      .integer 110, .integer 111, .integer 112, .integer 113, .integer 114,
      .integer 115, .integer 116, .integer 117, .integer 118, .integer 119,
      .integer 120, .integer 121, .integer 122, .integer 123, .integer 124,
      .integer 125, .integer 126, .integer 127] =
      if plain b then .atom "true" else .atom "false" := by
  change Term.isMember _
      (((List.range' 32 96).filter fun k => k != 34 && k != 92).map fun k : Nat => .integer k) = _
  rw [isMember_naturals]
  have iff : b.toNat ∈ (List.range' 32 96).filter (fun k => k != 34 && k != 92) ↔ plain b := by
    simp only [List.mem_filter, List.mem_range'_1, plain, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    omega
  simp only [iff]

/-- `json`'s guard for bytes that strings escape. -/
theorem isMember_escape (b : UInt8) :
    Term.isMember (.integer b.toNat)
      [.integer 0, .integer 1, .integer 2, .integer 3, .integer 4, .integer 5,
      .integer 6, .integer 7, .integer 8, .integer 9, .integer 10, .integer 11,
      .integer 12, .integer 13, .integer 14, .integer 15, .integer 16, .integer 17,
      .integer 18, .integer 19, .integer 20, .integer 21, .integer 22, .integer 23,
      .integer 24, .integer 25, .integer 26, .integer 27, .integer 28, .integer 29,
      .integer 30, .integer 31, .integer 34, .integer 92] =
      if b.toNat < 32 ∨ b.toNat = 34 ∨ b.toNat = 92 then .atom "true" else .atom "false" := by
  change Term.isMember _ ((List.range 32 ++ [34, 92]).map fun k : Nat => .integer k) = _
  rw [isMember_naturals]
  simp only [List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]

/-- The SWAR test on a seven-byte word, with the constants of `json`. -/
theorem swar_plain (w : List UInt8) (seven : w.length = 7)
    (h1 : iband (bytesValue w) 36170086419038336 = 0)
    (h2 : iband (bytesValue w + 27127564814278752) 36170086419038336 = 36170086419038336)
    (h3 : iband (ixor (bytesValue w) 9607679205057058 - 282578800148737) 36170086419038336 = 0)
    (h4 : iband (ixor (bytesValue w) 25997249613683804 - 282578800148737) 36170086419038336 = 0) :
    ∀ b ∈ w, plain b := by
  have m : bytesValue (List.replicate 7 128) = 36170086419038336 := by decide
  have k96 : bytesValue (List.replicate 7 96) = 27127564814278752 := by decide
  have k34 : bytesValue (List.replicate 7 34) = 9607679205057058 := by decide
  have k92 : bytesValue (List.replicate 7 92) = 25997249613683804 := by decide
  have k1 : bytesValue (List.replicate 7 1) = 282578800148737 := by decide
  apply swar_sound w <;> rw [seven, m]
  · have : iband (bytesValue w : Int) 36170086419038336 =
        ((bytesValue w &&& 36170086419038336 : Nat) : Int) := rfl
    omega
  · rw [k96]
    have : iband ((bytesValue w : Int) + 27127564814278752) 36170086419038336 =
        (((bytesValue w + 27127564814278752) &&& 36170086419038336 : Nat) : Int) := rfl
    omega
  · rw [k34, k1]
    exact h3
  · rw [k92, k1]
    exact h4

end JsonProof
