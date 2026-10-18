# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/json.exs
# Verify that OTP's json module decodes what it encodes.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1).
ExUnit.start()

defmodule JsonProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  # Checking the translated json module alone takes about 20 seconds.
  @moduletag timeout: to_timeout(minute: 5)

  def roundtrip(data), do: :json.decode(:erlang.iolist_to_binary(:json.encode(data))) === data

  # The data covered so far: integers, booleans, null, ASCII strings, and
  # lists of them, nested at most 64 deep.
  # The encoder makes one dynamic call per nesting level, and laws run with a
  # call depth of 100.
  def supported?(data), do: supported?(data, 64)

  def supported?(data, _depth) when is_integer(data) or data in [true, false, :null],
    do: true

  def supported?(data, _depth) when is_binary(data), do: ascii?(data)
  def supported?(data, depth) when is_list(data) and depth > 0, do: values?(data, depth - 1)
  def supported?(_data, _depth), do: false

  def values?([], _depth), do: true
  def values?([x | xs], depth), do: supported?(x, depth) and values?(xs, depth)
  def values?(_data, _depth), do: false

  def ascii?(<<byte, rest::binary>>) when byte < 128, do: ascii?(rest)
  def ascii?(<<>>), do: true
  def ascii?(_data), do: false

  # The decoder is a state machine of 32 mutually recursive functions over the
  # input, whose definition needs more than Lean's default heartbeats.
  laws "json round trip", options: [maxHeartbeats: 0] do
    # Error reports format positions with functions outside the model.
    cutoff &:json.invalid_byte/2
    cutoff &:json.unexpected_sequence/2
    cutoff &:json.unexpected_utf8/2

    prelude ~LEAN"""
    namespace JsonProof
    open Lynx

    /-- The options record `json:decode/1` passes to the decoder. -/
    abbrev options : Term := .tuple #[.atom "decode", .atom "undefined", .atom "undefined",
      .atom "undefined", .atom "undefined", .atom "undefined", .atom "undefined", .function 1 1
          #[],
      .function 2 1 #[], .atom "undefined", .atom "null"]

    /-- Bytes that strings carry without escaping. -/
    @[expose] def plain (b : UInt8) : Bool :=
      32 ≤ b.toNat && b.toNat < 128 && b.toNat != 34 && b.toNat != 92

    /-- An uppercase hexadecimal digit. -/
    @[expose] def hexDigit (d : Nat) : UInt8 := if d < 10 then (48 + d).toUInt8 else (55 + d).toUInt8

    /-- The escape sequence the encoder writes for a byte that needs escaping. -/
    @[expose] def escapeBytes (b : UInt8) : List UInt8 :=
      match b.toNat with
      | 8 => [92, 98]
      | 9 => [92, 116]
      | 10 => [92, 110]
      | 12 => [92, 102]
      | 13 => [92, 114]
      | 34 => [92, 34]
      | 92 => [92, 92]
      | n => [92, 117, 48, 48, hexDigit (n / 16), hexDigit (n % 16)]

    /-- The text the encoder writes for the bytes of a string. -/
    @[expose] def escapeText (s : List UInt8) : List UInt8 :=
      s.flatMap fun b => if plain b then [b] else escapeBytes b

    /-- The byte that a letter after a backslash stands for. -/
    @[expose] def unescapeChar (c : UInt8) : Option UInt8 :=
      match c.toNat with
      | 98 => some 8
      | 116 => some 9
      | 110 => some 10
      | 102 => some 12
      | 114 => some 13
      | 34 => some 34
      | 92 => some 92
      | 47 => some 47
      | _ => none

    /-- JSON values made of integers, booleans, null, ASCII strings, and lists. -/
    inductive Json where
      | int : Int → Json
      | bool : Bool → Json
      | null : Json
      | str (s : List UInt8) (ascii : ∀ b ∈ s, b.toNat < 128)
      | arr : List Json → Json

    /-- The decimal text `integer_to_binary/1` writes for an integer. -/
    @[expose] def textOf (x : Int) : List UInt8 := (toString x).toUTF8.data.toList

    /-- The binary of bytes. -/
    abbrev bin (s : List UInt8) : Term := .bitstring ⟨s.toArray⟩ 0 (Term.Bitstring.valid_aligned _)

    mutual
    /-- The Erlang term of a value. -/
    @[expose] def Json.term : Json → Term
      | .int n => .integer n
      | .bool b => .atom (if b then "true" else "false")
      | .null => .atom "null"
      | .str s _ => bin s
      | .arr l => Json.terms l
    /-- The Erlang list of values. -/
    @[expose] def Json.terms : List Json → Term
      | [] => .nil
      | x :: xs => .cons x.term (Json.terms xs)
    end

    mutual
    /-- The text the encoder writes for a value. -/
    @[expose] def Json.text : Json → List UInt8
      | .int n => textOf n
      | .bool true => [116, 114, 117, 101]
      | .bool false => [102, 97, 108, 115, 101]
      | .null => [110, 117, 108, 108]
      | .str s _ => 34 :: (escapeText s ++ [34])
      | .arr [] => [91, 93]
      | .arr (x :: xs) => 91 :: (x.text ++ Json.tailText xs)
    /-- The text after a list's first element: a comma before each element, then `]`. -/
    @[expose] def Json.tailText : List Json → List UInt8
      | [] => [93]
      | y :: ys => 44 :: (y.text ++ Json.tailText ys)
    end

    mutual
    /-- How deeply lists nest in a value. -/
    @[expose] def Json.depth : Json → Nat
      | .int _ | .bool _ | .null | .str _ _ => 0
      | .arr l => Json.depths l + 1
    /-- The deepest nesting among values. -/
    @[expose] def Json.depths : List Json → Nat
      | [] => 0
      | x :: xs => max x.depth (Json.depths xs)
    end

    end JsonProof
    """

    # Facts about the byte guards of json's string encoder and decoder, which
    # need no translated definitions.
    prelude ~LEAN"""
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
        simp only [List.map_cons, Term.isMember_cons, Term.exactCompare_integers, ih, List.mem_cons]
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
    """

    # The encoder writes integers with integer_to_binary/1, booleans and null
    # as literals, strings between quotes, and lists as their elements between
    # brackets, separated by commas. Strings copy runs of bytes that need no
    # escaping and escape quotes, backslashes, and control characters. The
    # decoder dispatches on each byte, reads integers back with
    # binary_to_integer/1, the integer decoder in its default options, matches
    # the remaining letters of a literal at once, takes the runs of a string
    # with binary_part/3 and appends each unescaped byte, and pushes values
    # onto an array frame, opening a new frame for each nested list. Both sides
    # scan strings seven bytes at a time while a SWAR test finds no byte to
    # escape, and one byte at a time otherwise.
    law json_roundtrip(data),
      requires: supported?(data),
      expects: roundtrip(data),
      proof: ~LEAN"""
      open Lynx Lynx.Term.Bitstring Erlang.json JsonProof in
      exact (by
        -- Matching whole bytes leaves whole bytes.
        have tail8 : ∀ bs : List UInt8, matchTail (bin bs) (.atom "all") 8 = true := by
          intro bs
          simp only [matchTail, bitSize]
          split
          · split <;> simp
          · omega

        -- The SWAR word needs seven bytes.
        have short56 : ∀ bs : List UInt8, bs.length < 7 →
            matchInteger (bin bs) (.integer 56) 1 false false = none := by
          intro bs short
          simp [matchInteger, toBits_length_aligned, ByteArray.size]
          omega

        have band_iband : ∀ x y : Int,
            Erlang.erlang.«band/2» (.integer x) (.integer y) = .ok (.integer (iband x y)) := by
          intro x y
          cases x <;> cases y <;> rfl

        have bxor_ixor : ∀ x y : Int,
            Erlang.erlang.«bxor/2» (.integer x) (.integer y) = .ok (.integer (ixor x y)) := by
          intro x y
          cases x <;> cases y <;> rfl

        -- A computation that returns a known value passes it on.
        have bind_of_ok : ∀ {α : Type} {M : Except Exception α} (x : α)
            {K : α → Except Exception Term}, M = .ok x → (M >>= K) = K x := by
          intro α M x K returned
          subst returned
          rfl

        -- The encoder copies bytes that need no escaping.
        have escape_plain_byte : ∀ (b : UInt8) (bs : List UInt8) (acc orig skip : Term)
            (len : Int), plain b →
            «escape_binary/5» (bin (b :: bs)) acc orig skip (.integer len) =
              «escape_binary/5» (bin bs) acc orig skip (.integer (len + 1)) := by
          intro b bs acc orig skip len ok
          conv => lhs; unfold «escape_binary/5»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, isMember_plain, ok]
          simp

        -- A byte that needs escaping ends the current run and writes its escape sequence.
        have escape_byte : ∀ (b : UInt8) (bs : List UInt8) (acc orig : Term) (skip len : Int),
            (b.toNat < 32 ∨ b.toNat = 34 ∨ b.toNat = 92) →
            «escape_binary/5» (bin (b :: bs)) acc orig (.integer skip) (.integer len) =
              (do
                let next ← if len = 0 then .ok (.cons acc (bin (escapeBytes b))) else do
                  let part ← Erlang.erlang.«binary_part/3» orig (.integer skip) (.integer len)
                  .ok (.cons acc (.cons part (bin (escapeBytes b))))
                «escape_binary_ascii/5» (bin bs) next orig (.integer (skip + len + 1))
                  (.integer 0)) := by
          intro b bs acc orig skip len escape
          have notPlain : plain b = false := by simp [plain]; omega
          conv => lhs; unfold «escape_binary/5»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, isMember_plain, notPlain, isMember_escape, escape]
          simp
          rw [bind_of_ok (bin (escapeBytes b))]
          · by_cases zero : len = 0 <;> simp [zero]
          split
          all_goals first
            | (rename_i same
               have value := Int.ofNat.inj (Term.integer.inj same)
               simp [escapeBytes, value, hexDigit])
            | (exfalso
               simp only [Term.integer.injEq, imp_false] at *
               omega)

        -- At the end, a string without escapes is the original binary between quotes.
        -- Otherwise the escaped text so far is followed by the current run.
        have escape_end : ∀ (acc orig : Term) (skip len : Int),
            «escape_binary/5» (bin []) acc orig (.integer skip) (.integer len) =
              if skip = 0 then .ok (Term.list [.integer 34, orig, .integer 34])
              else if len = 0 then .ok (Term.list [acc, .integer 34])
              else (do
                let part ← Erlang.erlang.«binary_part/3» orig (.integer skip) (.integer len)
                .ok (Term.list [acc, part, .integer 34])) := by
          intro acc orig skip len
          unfold «escape_binary/5»
          by_cases s0 : skip = 0 <;> by_cases l0 : len = 0 <;> simp [matchInteger_byte_nil, s0, l0]

        -- The SWAR fast path skips a word of seven bytes only when they need no escaping.
        have escape_ascii_word : ∀ (w rest : List UInt8) (acc orig skip : Term) (len : Int),
            w.length = 7 →
            («escape_binary_ascii/5» (bin (w ++ rest)) acc orig skip (.integer len) =
                «escape_binary_ascii/5» (bin rest) acc orig skip (.integer (len + 7)) ∧
              ∀ b ∈ w, plain b) ∨
            «escape_binary_ascii/5» (bin (w ++ rest)) acc orig skip (.integer len) =
              «escape_binary/5» (bin (w ++ rest)) acc orig skip (.integer len) := by
          intro w rest acc orig skip len seven
          rw [«escape_binary_ascii/5».eq_def (bin (w ++ rest)),
            matchInteger_bytes _ _ _ 56 (by omega)]
          simp only [extract_some, tail8, band_iband, bxor_ixor, Erlang.erlang.«+/2_integers»,
            Erlang.erlang.«-/2_integers», Erlang.erlang.«=:=/2», Term.exactCompare_integers,
            Int.compare_eq_eq, Lynx.Except.ok_bind, Lynx.Except.andAlso_eq]
          rw [show List.foldl (fun value b => value * 256 + b.toNat) 0 w = bytesValue w from rfl]
          by_cases c1 : iband (bytesValue w) 36170086419038336 = 0
          · by_cases c2 : iband (bytesValue w + 27127564814278752) 36170086419038336 =
                36170086419038336
            · by_cases c3 : iband (ixor (bytesValue w) 9607679205057058 - 282578800148737)
                  36170086419038336 = 0
              · by_cases c4 : iband (ixor (bytesValue w) 25997249613683804 - 282578800148737)
                    36170086419038336 = 0
                · exact Or.inl ⟨by simp [c1, c2, c3, c4], swar_plain w seven c1 c2 c3 c4⟩
                · exact Or.inr (by simp [c1, c2, c3, c4])
              · exact Or.inr (by simp [c1, c2, c3])
            · exact Or.inr (by simp [c1, c2])
          · exact Or.inr (by simp [c1])

        have escape_ascii_short : ∀ (l : List UInt8) (acc orig skip : Term) (len : Int),
            l.length < 7 →
            «escape_binary_ascii/5» (bin l) acc orig skip (.integer len) =
              «escape_binary/5» (bin l) acc orig skip (.integer len) := by
          intro l acc orig skip len short
          rw [«escape_binary_ascii/5».eq_def, short56 _ short]
          rfl

        have binary_part_middle : ∀ (pre mid post : List UInt8),
            Erlang.erlang.«binary_part/3» (.bitstring ⟨(pre ++ mid ++ post).toArray⟩ 0
                (valid_aligned _))
                (.integer pre.length) (.integer mid.length) =
              .ok (.bitstring ⟨mid.toArray⟩ 0 (valid_aligned _)) := by
          intro pre mid post
          have size : (ByteArray.mk (pre ++ mid ++ post).toArray).size = pre.length + mid.length
              + post.length := by
            simp [ByteArray.size]; omega
          have nonneg : ¬ ((mid.length : Int) < 0) := by omega
          simp only [Erlang.erlang.«binary_part/3», nonneg, if_false, size]
          have bounds : (0 : Int) ≤ pre.length ∧ (pre.length : Int) ≤ pre.length + mid.length ∧
              (pre.length + mid.length : Int) ≤ ((pre.length + mid.length + post.length : Nat) :
                  Int) := by omega
          simp only [bounds, and_self, if_true]
          congr 2
          apply ByteArray.ext
          rw [ByteArray.data_extract]
          have : ((pre.length : Int) + mid.length).toNat - pre.length = mid.length := by omega
          simp [this]

        have escapeText_append : ∀ a b : List UInt8,
            escapeText (a ++ b) = escapeText a ++ escapeText b := by
          intro a b
          simp [escapeText]

        have escapeText_plain : ∀ p : List UInt8, (∀ b ∈ p, plain b) → escapeText p = p := by
          intro p all
          induction p with
          | nil => rfl
          | cons b p ih =>
            simp only [escapeText, List.flatMap_cons, all b (by simp), if_true]
            exact congrArg (b :: ·) (ih (fun x mem => all x (by simp [mem])))

        have escapeText_escape : ∀ b : UInt8, plain b = false → escapeText [b] = escapeBytes b := by
          intro b escaped
          simp [escapeText, escaped]

        -- Flattening the encoder's iodata.
        have flat_bin : ∀ x : List UInt8, Erlang.erlang.«iolist_to_binary/1» (bin x) = .ok (bin x) :=
          fun x => Erlang.erlang.iolist_to_binary_binary _

        have flat_join : ∀ (l r : Term) (x y : List UInt8),
            Erlang.erlang.«iolist_to_binary/1» l = .ok (bin x) →
            Erlang.erlang.«iolist_to_binary/1» r = .ok (bin y) →
            Erlang.erlang.«iolist_to_binary/1» (.cons l r) = .ok (bin (x ++ y)) := by
          intro l r x y left right
          rw [Erlang.erlang.iolist_to_binary_join _ _ _ _ left right]
          congr 2

        have flat_quote : ∀ (r : Term) (y : List UInt8),
            Erlang.erlang.«iolist_to_binary/1» r = .ok (bin y) →
            Erlang.erlang.«iolist_to_binary/1» (.cons (.integer 34) r) = .ok (bin (34 :: y)) := by
          intro r y rest
          rw [Erlang.erlang.iolist_to_binary_byte_cons 34 _ _ (by decide) (by decide) rest]
          congr 2

        have flat_close : Erlang.erlang.«iolist_to_binary/1» (.cons (.integer 34) .nil) =
            .ok (bin [34]) := flat_quote _ [] Erlang.erlang.iolist_to_binary_nil

        -- The encoder has written `done`, holds a run of bytes that need no escaping
        -- since then, and has `rest` left. Its iodata flattens to the string's text.
        have encode_string : ∀ (n : Nat) (rest done run : List UInt8) (acc : Term),
            rest.length ≤ n → (∀ b ∈ rest, b.toNat < 128) → (∀ b ∈ run, plain b) →
            Erlang.erlang.«iolist_to_binary/1» acc = .ok (bin (34 :: escapeText done)) →
            (∃ io, «escape_binary/5» (bin rest) acc (bin (done ++ (run ++ rest)))
                (.integer done.length) (.integer run.length) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io =
                .ok (bin (34 :: (escapeText (done ++ (run ++ rest)) ++ [34])))) ∧
            (∃ io, «escape_binary_ascii/5» (bin rest) acc (bin (done ++ (run ++ rest)))
                (.integer done.length) (.integer run.length) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io =
                .ok (bin (34 :: (escapeText (done ++ (run ++ rest)) ++ [34])))) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro rest done run acc size ascii runPlain flat
            have main : ∃ io, «escape_binary/5» (bin rest) acc (bin (done ++ (run ++ rest)))
                (.integer done.length) (.integer run.length) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io =
                .ok (bin (34 :: (escapeText (done ++ (run ++ rest)) ++ [34]))) := by
              cases rest with
              | nil =>
                rw [escape_end]
                simp only [List.append_nil] at flat ⊢
                by_cases d0 : done = []
                · subst d0
                  refine ⟨Term.list [.integer 34, bin run, .integer 34], by simp, ?_⟩
                  have joined := flat_quote _ _ (flat_join _ _ _ _ (flat_bin run) flat_close)
                  simpa [Term.list_cons, Term.list_nil, escapeText_plain run runPlain] using joined
                by_cases r0 : run = []
                · subst r0
                  refine ⟨Term.list [acc, .integer 34], by simp [d0], ?_⟩
                  have joined := flat_join _ _ _ _ flat flat_close
                  simpa [Term.list_cons, Term.list_nil] using joined
                · have part := binary_part_middle done run []
                  simp only [List.append_nil, List.append_assoc] at part
                  refine ⟨Term.list [acc, bin run, .integer 34], by simp [d0, r0, part], ?_⟩
                  have joined := flat_join _ _ _ _ flat
                    (flat_join _ _ _ _ (flat_bin run) flat_close)
                  simpa [Term.list_cons, Term.list_nil, escapeText_append,
                    escapeText_plain run runPlain] using joined
              | cons b rest =>
                have restAscii : ∀ x ∈ rest, x.toNat < 128 := fun x mem => ascii x (by simp [mem])
                have smaller : rest.length < n := by simp at size; omega
                by_cases bPlain : plain b
                · rw [escape_plain_byte _ _ _ _ _ _ bPlain]
                  have next := (ih rest.length smaller rest done (run ++ [b]) acc (Nat.le_refl _)
                    restAscii (fun x mem => by
                      rcases List.mem_append.mp mem with mem | mem
                      · exact runPlain x mem
                      · simp at mem; subst mem; exact bPlain) flat).1
                  simp only [List.append_assoc, List.singleton_append, List.length_append,
                    List.length_singleton] at next
                  push_cast at next
                  exact next
                · have escaped : b.toNat < 32 ∨ b.toNat = 34 ∨ b.toNat = 92 := by
                    have := ascii b (by simp)
                    simp [plain] at bPlain
                    omega
                  have bEscape : plain b = false := by simpa using bPlain
                  rw [escape_byte _ _ _ _ _ _ escaped]
                  by_cases r0 : run = []
                  · subst r0
                    have next := (ih rest.length smaller rest (done ++ [b]) []
                      (.cons acc (bin (escapeBytes b))) (Nat.le_refl _) restAscii (by simp)
                      (by
                        rw [escapeText_append, escapeText_escape b bEscape]
                        exact flat_join _ _ _ _ flat (flat_bin (escapeBytes b)))).2
                    simp only [List.append_assoc, List.singleton_append, List.nil_append,
                      List.length_append, List.length_singleton, List.length_nil] at next ⊢
                    push_cast at next
                    simpa using next
                  · have len : (run.length : Int) ≠ 0 := by simp [r0]
                    have part := binary_part_middle done run (b :: rest)
                    simp only [List.append_assoc] at part
                    have next := (ih rest.length smaller rest (done ++ run ++ [b]) []
                      (.cons acc (.cons (bin run) (bin (escapeBytes b)))) (Nat.le_refl _) restAscii
                      (by simp)
                      (by
                        rw [escapeText_append, escapeText_append, escapeText_escape b bEscape,
                          escapeText_plain run runPlain]
                        simpa using flat_join _ _ _ _ flat
                          (flat_join _ _ _ _ (flat_bin run) (flat_bin (escapeBytes b))))).2
                    simp only [List.append_assoc, List.singleton_append, List.nil_append,
                      List.length_append, List.length_singleton, List.length_nil] at next
                    push_cast at next
                    simp only [len, if_false, part, Lynx.Except.ok_bind]
                    simpa [Int.add_assoc] using next
            refine ⟨main, ?_⟩
            by_cases short : rest.length < 7
            · rw [escape_ascii_short _ _ _ _ _ short]
              exact main
            have seven : (rest.take 7).length = 7 := by rw [List.length_take]; omega
            rcases escape_ascii_word (rest.take 7) (rest.drop 7) acc (bin (done ++ (run ++ rest)))
                (.integer done.length) run.length seven with ⟨step, word⟩ | fallback
            · rw [List.take_append_drop] at step
              rw [step]
              have next := (ih (rest.length - 7) (by omega) (rest.drop 7) done (run ++ rest.take 7)
                acc (by simp) (fun x mem => ascii x (List.mem_of_mem_drop mem))
                (fun x mem => by
                  rcases List.mem_append.mp mem with mem | mem
                  · exact runPlain x mem
                  · exact word x mem) flat).2
              rw [List.length_append, seven] at next
              simp only [List.append_assoc, List.take_append_drop] at next
              push_cast at next
              exact next
            · rw [List.take_append_drop] at fallback
              rw [fallback]
              exact main

        -- A quote starts a string.
        have value_quote : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (bin (34 :: bs)) orig skip acc stack dec =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 1))
                «string_ascii/7» (bin bs) orig next acc stack dec (.integer 0)) := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- The decoder takes bytes that need no escaping as they are.
        have string_plain_byte : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack dec : Term)
            (len : Int), plain b →
            «string/7» (bin (b :: bs)) orig skip acc stack dec (.integer len) =
              «string/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro b bs orig skip acc stack dec len ok
          conv => lhs; unfold «string/7»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, ok]
          simp [matchTail, Nat.mod_one]

        have string_plain : ∀ (p r : List UInt8) (orig skip acc stack dec : Term) (len : Int),
            (∀ b ∈ p, plain b) →
            «string/7» (bin (p ++ r)) orig skip acc stack dec (.integer len) =
              «string/7» (bin r) orig skip acc stack dec (.integer (len + p.length)) := by
          intro p r orig skip acc stack dec len all
          induction p generalizing len with
          | nil => simp
          | cons b p ih =>
            rw [List.cons_append, string_plain_byte _ _ _ _ _ _ _ _ (all b (by simp)),
              ih _ (fun x mem => all x (by simp [mem]))]
            congr 2
            simp
            omega

        -- A closing quote ends the string with the bytes since its start.
        have string_close : ∀ (rest : List UInt8) (orig skip acc stack : Term) (len : Int),
            «string/7» (bin (34 :: rest)) orig skip acc stack options (.integer len) =
              (do
                let value ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip (.integer len))
                let after ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                let next ← Result.ofExcept (Erlang.erlang.«+/2» after (.integer 1))
                «continue/7» (bin rest) orig next acc stack options value) := by
          intro rest orig skip acc stack len
          conv => lhs; unfold «string/7»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, show plain 34 = false from rfl]
          simp [matchTail, Nat.mod_one]

        have string_ascii_word : ∀ (w rest : List UInt8) (orig skip acc stack dec : Term)
            (len : Int), w.length = 7 →
            («string_ascii/7» (bin (w ++ rest)) orig skip acc stack dec (.integer len) =
                «string_ascii/7» (bin rest) orig skip acc stack dec (.integer (len + 7)) ∧
              ∀ b ∈ w, plain b) ∨
            «string_ascii/7» (bin (w ++ rest)) orig skip acc stack dec (.integer len) =
              «string/7» (bin (w ++ rest)) orig skip acc stack dec (.integer len) := by
          intro w rest orig skip acc stack dec len seven
          rw [«string_ascii/7».eq_def (bin (w ++ rest)),
            matchInteger_bytes _ _ _ 56 (by omega)]
          simp only [extract_some, tail8, band_iband, bxor_ixor, Erlang.erlang.«+/2_integers»,
            Erlang.erlang.«-/2_integers», Erlang.erlang.«=:=/2», Term.exactCompare_integers,
            Int.compare_eq_eq, Result.ofExcept_ok, Result.ok_bind, Result.andAlso_eq]
          rw [show List.foldl (fun value b => value * 256 + b.toNat) 0 w = bytesValue w from rfl]
          by_cases c1 : iband (bytesValue w) 36170086419038336 = 0
          · by_cases c2 : iband (bytesValue w + 27127564814278752) 36170086419038336 =
                36170086419038336
            · by_cases c3 : iband (ixor (bytesValue w) 9607679205057058 - 282578800148737)
                  36170086419038336 = 0
              · by_cases c4 : iband (ixor (bytesValue w) 25997249613683804 - 282578800148737)
                    36170086419038336 = 0
                · exact Or.inl ⟨by simp [c1, c2, c3, c4], swar_plain w seven c1 c2 c3 c4⟩
                · exact Or.inr (by simp [c1, c2, c3, c4])
              · exact Or.inr (by simp [c1, c2, c3])
            · exact Or.inr (by simp [c1, c2])
          · exact Or.inr (by simp [c1])

        have string_ascii_short : ∀ (l : List UInt8) (orig skip acc stack dec : Term) (len : Int),
            l.length < 7 →
            «string_ascii/7» (bin l) orig skip acc stack dec (.integer len) =
              «string/7» (bin l) orig skip acc stack dec (.integer len) := by
          intro l orig skip acc stack dec len short
          rw [«string_ascii/7».eq_def, short56 _ short]
          rfl

        -- Bytes that need no escaping, up to one that does, extend the string.
        have string_ascii : ∀ (n : Nat) (p r : List UInt8) (orig skip acc stack dec : Term)
            (len : Int), p.length ≤ n → (∀ b ∈ p, plain b) →
            (∀ c rs, r = c :: rs → plain c = false) →
            «string_ascii/7» (bin (p ++ r)) orig skip acc stack dec (.integer len) =
              «string/7» (bin r) orig skip acc stack dec (.integer (len + p.length)) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro p r orig skip acc stack dec len size all stop
            by_cases short : (p ++ r).length < 7
            · rw [string_ascii_short _ _ _ _ _ _ _ short]
              exact string_plain p r orig skip acc stack dec len all
            have whole := List.take_append_drop 7 (p ++ r)
            rw [← whole]
            rcases string_ascii_word (List.take 7 (p ++ r)) (List.drop 7 (p ++ r)) orig skip acc
                stack dec len (by rw [List.length_take]; omega) with ⟨step, word⟩ | fallback
            · by_cases long : 7 ≤ p.length
              · rw [step, List.drop_append_of_le_length long,
                  ih (p.length - 7) (by omega) (List.drop 7 p) r orig skip acc stack dec (len + 7)
                    (by simp) (fun b mem => all b (List.mem_of_mem_drop mem)) stop]
                congr 2
                simp
                omega
              · obtain ⟨c, rs, rfl⟩ : ∃ c rs, r = c :: rs := by
                  cases r with
                  | nil => simp at short; omega
                  | cons c rs => exact ⟨c, rs, rfl⟩
                have mem : c ∈ List.take 7 (p ++ c :: rs) := by
                  rw [List.take_append, List.take_of_length_le (by omega),
                    show 7 - p.length = (6 - p.length) + 1 by omega]
                  simp
                simp [word c mem] at stop
            · rw [fallback, whole]
              exact string_plain p r orig skip acc stack dec len all

        -- A backslash ends the run, which starts the decoded bytes.
        have string_escape : ∀ (rest p : List UInt8) (orig acc stack dec : Term) (skip len : Int),
            Erlang.erlang.«binary_part/3» orig (.integer skip) (.integer len) = .ok (bin p) →
            «string/7» (bin (92 :: rest)) orig (.integer skip) acc stack dec (.integer len) =
              «unescape/9» (bin rest) orig (.integer skip) acc stack dec (.integer (skip - 1))
                (.integer len) (bin p) := by
          intro rest p orig acc stack dec skip len part
          conv => lhs; unfold «string/7»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, show plain 92 = false from rfl]
          simp [matchTail, Nat.mod_one, part, binarySegment_aligned, append_bytes, Except.bind]

        have string9_plain_byte : ∀ (b : UInt8) (bs : List UInt8)
            (orig skip acc stack dec start sacc : Term) (len : Int), plain b →
            «string/9» (bin (b :: bs)) orig skip acc stack dec start (.integer len) sacc =
              «string/9» (bin bs) orig skip acc stack dec start (.integer (len + 1)) sacc := by
          intro b bs orig skip acc stack dec start sacc len ok
          conv => lhs; unfold «string/9»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, ok]
          simp [matchTail, Nat.mod_one]

        have string9_plain : ∀ (p r : List UInt8) (orig skip acc stack dec start sacc : Term)
            (len : Int), (∀ b ∈ p, plain b) →
            «string/9» (bin (p ++ r)) orig skip acc stack dec start (.integer len) sacc =
              «string/9» (bin r) orig skip acc stack dec start (.integer (len + p.length)) sacc := by
          intro p r orig skip acc stack dec start sacc len all
          induction p generalizing len with
          | nil => simp
          | cons b p ih =>
            rw [List.cons_append, string9_plain_byte _ _ _ _ _ _ _ _ _ _ (all b (by simp)),
              ih _ (fun x mem => all x (by simp [mem]))]
            congr 2
            simp
            omega

        have string9_escape : ∀ (rest p sacc : List UInt8) (orig acc stack dec start : Term)
            (skip len : Int),
            Erlang.erlang.«binary_part/3» orig (.integer skip) (.integer len) = .ok (bin p) →
            «string/9» (bin (92 :: rest)) orig (.integer skip) acc stack dec start (.integer len)
                (bin sacc) =
              «unescape/9» (bin rest) orig (.integer skip) acc stack dec start (.integer len)
                (bin (sacc ++ p)) := by
          intro rest p sacc orig acc stack dec start skip len part
          conv => lhs; unfold «string/9»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, show plain 92 = false from rfl]
          simp [matchTail, Nat.mod_one, part, binarySegment_aligned, append_bytes, Except.bind]

        have string9_close : ∀ (rest p sacc : List UInt8) (orig acc stack start : Term)
            (skip len : Int),
            Erlang.erlang.«binary_part/3» orig (.integer skip) (.integer len) = .ok (bin p) →
            «string/9» (bin (34 :: rest)) orig (.integer skip) acc stack options start (.integer len)
                (bin sacc) =
              «continue/7» (bin rest) orig (.integer (skip + len + 1)) acc stack options
                (bin (sacc ++ p)) := by
          intro rest p sacc orig acc stack start skip len part
          conv => lhs; unfold «string/9»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, show plain 34 = false from rfl]
          simp [matchTail, Nat.mod_one, part, binarySegment_aligned, append_bytes, Except.bind]

        have string_ascii9_word : ∀ (w rest : List UInt8) (orig skip acc stack dec start sacc : Term)
            (len : Int), w.length = 7 →
            («string_ascii/9» (bin (w ++ rest)) orig skip acc stack dec start (.integer len) sacc =
                «string_ascii/9» (bin rest) orig skip acc stack dec start (.integer (len + 7)) sacc ∧
              ∀ b ∈ w, plain b) ∨
            «string_ascii/9» (bin (w ++ rest)) orig skip acc stack dec start (.integer len) sacc =
              «string/9» (bin (w ++ rest)) orig skip acc stack dec start (.integer len) sacc := by
          intro w rest orig skip acc stack dec start sacc len seven
          rw [«string_ascii/9».eq_def (bin (w ++ rest)),
            matchInteger_bytes _ _ _ 56 (by omega)]
          simp only [extract_some, tail8, band_iband, bxor_ixor, Erlang.erlang.«+/2_integers»,
            Erlang.erlang.«-/2_integers», Erlang.erlang.«=:=/2», Term.exactCompare_integers,
            Int.compare_eq_eq, Result.ofExcept_ok, Result.ok_bind, Result.andAlso_eq]
          rw [show List.foldl (fun value b => value * 256 + b.toNat) 0 w = bytesValue w from rfl]
          by_cases c1 : iband (bytesValue w) 36170086419038336 = 0
          · by_cases c2 : iband (bytesValue w + 27127564814278752) 36170086419038336 =
                36170086419038336
            · by_cases c3 : iband (ixor (bytesValue w) 9607679205057058 - 282578800148737)
                  36170086419038336 = 0
              · by_cases c4 : iband (ixor (bytesValue w) 25997249613683804 - 282578800148737)
                    36170086419038336 = 0
                · exact Or.inl ⟨by simp [c1, c2, c3, c4], swar_plain w seven c1 c2 c3 c4⟩
                · exact Or.inr (by simp [c1, c2, c3, c4])
              · exact Or.inr (by simp [c1, c2, c3])
            · exact Or.inr (by simp [c1, c2])
          · exact Or.inr (by simp [c1])

        have string_ascii9_short : ∀ (l : List UInt8) (orig skip acc stack dec start sacc : Term)
            (len : Int), l.length < 7 →
            «string_ascii/9» (bin l) orig skip acc stack dec start (.integer len) sacc =
              «string/9» (bin l) orig skip acc stack dec start (.integer len) sacc := by
          intro l orig skip acc stack dec start sacc len short
          rw [«string_ascii/9».eq_def, short56 _ short]
          rfl

        have string_ascii9 : ∀ (n : Nat) (p r : List UInt8)
            (orig skip acc stack dec start sacc : Term) (len : Int), p.length ≤ n →
            (∀ b ∈ p, plain b) → (∀ c rs, r = c :: rs → plain c = false) →
            «string_ascii/9» (bin (p ++ r)) orig skip acc stack dec start (.integer len) sacc =
              «string/9» (bin r) orig skip acc stack dec start (.integer (len + p.length)) sacc := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro p r orig skip acc stack dec start sacc len size all stop
            by_cases short : (p ++ r).length < 7
            · rw [string_ascii9_short _ _ _ _ _ _ _ _ _ short]
              exact string9_plain p r orig skip acc stack dec start sacc len all
            have whole := List.take_append_drop 7 (p ++ r)
            rw [← whole]
            rcases string_ascii9_word (List.take 7 (p ++ r)) (List.drop 7 (p ++ r)) orig skip acc
                stack dec start sacc len (by rw [List.length_take]; omega)
              with ⟨step, word⟩ | fallback
            · by_cases long : 7 ≤ p.length
              · rw [step, List.drop_append_of_le_length long,
                  ih (p.length - 7) (by omega) (List.drop 7 p) r orig skip acc stack dec start sacc
                    (len + 7) (by simp) (fun b mem => all b (List.mem_of_mem_drop mem)) stop]
                congr 2
                simp
                omega
              · obtain ⟨c, rs, rfl⟩ : ∃ c rs, r = c :: rs := by
                  cases r with
                  | nil => simp at short; omega
                  | cons c rs => exact ⟨c, rs, rfl⟩
                have mem : c ∈ List.take 7 (p ++ c :: rs) := by
                  rw [List.take_append, List.take_of_length_le (by omega),
                    show 7 - p.length = (6 - p.length) + 1 by omega]
                  simp
                simp [word c mem] at stop
            · rw [fallback, whole]
              exact string9_plain p r orig skip acc stack dec start sacc len all

        -- A letter after a backslash stands for one byte.
        have unescape_char : ∀ (c v : UInt8) (rest sacc : List UInt8)
            (orig acc stack dec start : Term) (skip len : Int), unescapeChar c = some v →
            «unescape/9» (bin (c :: rest)) orig (.integer skip) acc stack dec start (.integer len)
                (bin sacc) =
              «string_ascii/9» (bin rest) orig (.integer (skip + len + 2)) acc stack dec start
                (.integer 0) (bin (sacc ++ [v])) := by
          intro c v rest sacc orig acc stack dec start skip len char
          conv => lhs; unfold «unescape/9»
          rw [matchInteger_byte]
          simp [matchTail, Nat.mod_one]
          split
          all_goals first
            | (rename_i same
               have value := Int.ofNat.inj (Term.integer.inj same)
               simp [unescapeChar, value] at char
               have segment := integerSegment_byte v
               subst char
               simp at segment
               simp [binarySegment_aligned, segment, append_bytes, Except.bind])
            | (exfalso
               simp only [Term.integer.injEq, imp_false] at *
               unfold unescapeChar at char
               split at char <;> first | omega | simp at char)

        have unescape_unicode : ∀ (rest : List UInt8) (orig skip acc stack dec start len sacc : Term),
            «unescape/9» (bin (117 :: rest)) orig skip acc stack dec start len sacc =
              «unescapeu/9» (bin rest) orig skip acc stack dec start len sacc := by
          intro rest orig skip acc stack dec start len sacc
          conv => lhs; unfold «unescape/9»
          rw [matchInteger_byte]
          simp [matchTail, Nat.mod_one]

        -- The decoder reads hexadecimal digits from a table.
        have hex_lookup : ∀ d, d < 16 →
            Erlang.erlang.«element/2» (.integer (((hexDigit d).toNat : Int) - 48 + 1))
              lynx_literal_p3xycmru = .ok (.integer d) := by
          intro d bound
          match d, bound with
          | 0, _ => rfl
          | 1, _ => rfl
          | 2, _ => rfl
          | 3, _ => rfl
          | 4, _ => rfl
          | 5, _ => rfl
          | 6, _ => rfl
          | 7, _ => rfl
          | 8, _ => rfl
          | 9, _ => rfl
          | 10, _ => rfl
          | 11, _ => rfl
          | 12, _ => rfl
          | 13, _ => rfl
          | 14, _ => rfl
          | 15, _ => rfl
          | _ + 16, bound => exact absurd bound (by omega)

        -- A control character is escaped as four hexadecimal digits.
        have unescapeu_control : ∀ (e : UInt8) (rest sacc : List UInt8)
            (orig acc stack dec start : Term) (skip len : Int), e.toNat < 32 →
            «unescapeu/9» (bin (48 :: 48 :: hexDigit (e.toNat / 16) :: hexDigit (e.toNat % 16) ::
                rest)) orig (.integer skip) acc stack dec start (.integer len) (bin sacc) =
              «string_ascii/9» (bin rest) orig (.integer (skip + len + 6)) acc stack dec start
                (.integer 0) (bin (sacc ++ [e])) := by
          intro e rest sacc orig acc stack dec start skip len control
          have high := hex_lookup (e.toNat / 16) (by omega)
          have low := hex_lookup (e.toNat % 16) (by omega)
          have zero : Erlang.erlang.«element/2» (.integer 1) lynx_literal_p3xycmru =
              .ok (.integer 0) := rfl
          conv => lhs; unfold «unescapeu/9»
          simp only [matchInteger_byte, extract_some]
          simp [matchTail, Nat.mod_one, high, low, zero]
          have code : (e.toNat : Int) % 16 + 16 * ((e.toNat : Int) / 16) = e.toNat := by omega
          have surrogate : ¬ (55296 ≤ (e.toNat : Int)) := by omega
          have below : (e.toNat : Int) ≤ 56319 := by omega
          simp [code, surrogate, below, Erlang.erlang.«and/2», utf8Segment_ascii e (by omega),
            binarySegment_aligned, append_bytes, Except.bind]

        -- A backslash and the bytes after it stand for one byte that needs escaping.
        have unescape_escape : ∀ e : UInt8, e.toNat < 128 → plain e = false →
            ∃ t, escapeBytes e = 92 :: t ∧ ∀ (rest sacc : List UInt8)
              (orig acc stack dec start : Term) (skip len : Int),
              «unescape/9» (bin (t ++ rest)) orig (.integer skip) acc stack dec start (.integer len)
                  (bin sacc) =
                «string_ascii/9» (bin rest) orig (.integer (skip + len + (escapeBytes e).length))
                  acc stack dec start (.integer 0) (bin (sacc ++ [e])) := by
          intro e ascii escaped
          have control : e.toNat < 32 ∨ e.toNat = 34 ∨ e.toNat = 92 := by
            simp [plain] at escaped
            omega
          unfold escapeBytes
          split
          all_goals first
            | (rename_i same
               refine ⟨_, rfl, fun rest sacc orig acc stack dec start skip len => ?_⟩
               rw [List.cons_append, List.nil_append, unescape_char _ e _ _ _ _ _ _ _ _ _ (by
                 simp [unescapeChar]
                 apply UInt8.toNat_inj.mp
                 simp [same])]
               rfl)
            | (refine ⟨_, rfl, fun rest sacc orig acc stack dec start skip len => ?_⟩
               rw [List.cons_append, unescape_unicode]
               simpa using unescapeu_control e rest sacc orig acc stack dec start skip len (by
                 simp only [imp_false] at *
                 omega))

        -- A string's bytes are a run of bytes that need no escaping, then either nothing
        -- or a byte that does.
        have split_plain : ∀ s : List UInt8, ∃ p r, s = p ++ r ∧ (∀ b ∈ p, plain b) ∧
            (r = [] ∨ ∃ e r2, r = e :: r2 ∧ plain e = false) := by
          intro s
          induction s with
          | nil => exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
          | cons b s ih =>
            by_cases bPlain : plain b
            · obtain ⟨p, r, rfl, all, stop⟩ := ih
              refine ⟨b :: p, r, rfl, fun x mem => ?_, stop⟩
              rcases List.mem_cons.mp mem with rfl | mem
              · exact bPlain
              · exact all x mem
            · exact ⟨[], b :: s, rfl, by simp, Or.inr ⟨b, s, rfl, by simpa using bPlain⟩⟩

        -- After an escape, the decoder has decoded `done` and has the escaped text of
        -- `rest` left, up to the closing quote.
        have decode_rest : ∀ (n : Nat) (rest done pre post : List UInt8) (acc stack start : Term),
            rest.length ≤ n → (∀ b ∈ rest, b.toNat < 128) →
            «string_ascii/9» (bin (escapeText rest ++ 34 :: post))
                (bin (pre ++ 34 :: (escapeText (done ++ rest) ++ 34 :: post)))
                (.integer (pre.length + 1 + (escapeText done).length)) acc stack options start
                (.integer 0) (bin done) =
              «continue/7» (bin post) (bin (pre ++ 34 :: (escapeText (done ++ rest) ++ 34 :: post)))
                (.integer (pre.length + 1 + (escapeText (done ++ rest)).length + 1)) acc stack
                options (bin (done ++ rest)) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro rest done pre post acc stack start size ascii
            obtain ⟨p, r, rfl, pPlain, stop⟩ := split_plain rest
            have part := binary_part_middle (pre ++ 34 :: escapeText done) p
              (escapeText r ++ 34 :: post)
            simp only [escapeText_append, escapeText_plain p pPlain, List.append_assoc,
              List.cons_append, List.length_append, List.length_cons] at part ⊢
            push_cast at part ⊢
            rw [show (pre.length : Int) + ((escapeText done).length + 1) =
              pre.length + 1 + (escapeText done).length by omega] at part
            rcases stop with rfl | ⟨e, r, rfl, escaped⟩
            · simp only [show escapeText [] = [] from rfl, List.nil_append] at part ⊢
              rw [string_ascii9 p.length p (34 :: post) _ _ _ _ _ _ _ 0 (Nat.le_refl _) pPlain
                (fun c rs same => by cases same; rfl), Int.zero_add,
                string9_close _ _ _ _ _ _ _ _ _ part]
              simp only [List.append_nil, List.length_nil]
              congr 2
              push_cast
              omega
            · have eAscii := ascii e (by simp)
              obtain ⟨t, et, unescaped⟩ := unescape_escape e eAscii escaped
              have escapedHead : escapeText (e :: r) = escapeBytes e ++ escapeText r := by
                rw [show e :: r = [e] ++ r from rfl, escapeText_append, escapeText_escape e escaped]
              rw [escapedHead, et] at part ⊢
              simp only [List.cons_append, List.append_assoc] at part ⊢
              rw [string_ascii9 p.length p _ _ _ _ _ _ _ _ 0 (Nat.le_refl _) pPlain
                (fun c rs same => by cases same; rfl), Int.zero_add,
                string9_escape _ _ _ _ _ _ _ _ _ _ part]
              rw [unescaped]
              have next := ih r.length (by simp at size; omega) r (done ++ p ++ [e]) pre post acc
                stack start (Nat.le_refl _) (fun x mem => ascii x (by simp [mem]))
              simp only [escapeText_append, escapeText_plain p pPlain, escapeText_escape e escaped,
                escapedHead, et, List.append_assoc, List.cons_append, List.singleton_append,
                List.nil_append, List.length_append, List.length_cons] at next ⊢
              push_cast at next ⊢
              rw [show (pre.length : Int) + 1 + (escapeText done).length + p.length +
                  (t.length + 1) = pre.length + 1 + ((escapeText done).length +
                    (p.length + (t.length + 1))) by omega, next]

        -- The requirement accepts binaries of ASCII bytes.
        have ascii_bytes : ∀ s : List UInt8,
            «ascii?/1» (bin s) = .ok Term.true → ∀ b ∈ s, b.toNat < 128 := by
          intro s
          induction s with
          | nil => simp
          | cons b s ih =>
            intro returned
            unfold «ascii?/1» at returned
            rw [matchInteger_byte] at returned
            simp [tail8, matchEnd_byte] at returned
            by_cases high : (b.toNat : Int) < 128 <;> simp [high] at returned
            intro x mem
            rcases List.mem_cons.mp mem with rfl | mem
            · omega
            · exact ih returned x mem

        -- A leading digit other than zero starts a number of length one.
        have value_digit : ∀ (orig skip acc stack dec : Term) (b : UInt8) (bs : List UInt8),
            49 ≤ b.toNat → b.toNat ≤ 57 →
            «value/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                dec =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer 1) := by
          intro orig skip acc stack dec b bs low high
          unfold «value/6»
          have h32 : (b.toNat : Int) ≠ 32 := by omega
          have h9 : (b.toNat : Int) ≠ 9 := by omega
          have h13 : (b.toNat : Int) ≠ 13 := by omega
          have h10 : (b.toNat : Int) ≠ 10 := by omega
          have h48 : (b.toNat : Int) ≠ 48 := by omega
          have digit : (b.toNat : Int) = 49 ∨ (b.toNat : Int) = 50 ∨ (b.toNat : Int) = 51 ∨
              (b.toNat : Int) = 52 ∨ (b.toNat : Int) = 53 ∨ (b.toNat : Int) = 54 ∨
              (b.toNat : Int) = 55 ∨ (b.toNat : Int) = 56 ∨ (b.toNat : Int) = 57 := by omega
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»,
            h32, h9, h13, h10, h48]
          rcases digit with h | h | h | h | h | h | h | h | h <;> simp [h]

        -- A minus sign is followed by a number.
        have value_minus : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((45 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc
              stack dec =
              «number_minus/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                  dec := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- A leading zero starts a number that only continues with a fraction or exponent.
        have value_zero : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((48 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc
              stack dec =
              «number_zero/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                  dec
                (.integer 1) := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have number_minus_digit : ∀ (orig skip acc stack dec : Term) (b : UInt8) (bs : List
            UInt8),
            49 ≤ b.toNat → b.toNat ≤ 57 →
            «number_minus/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack
              dec =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer 2) := by
          intro orig skip acc stack dec b bs low high
          have h48 : (b.toNat : Int) ≠ 48 := by omega
          have digit : (b.toNat : Int) = 49 ∨ (b.toNat : Int) = 50 ∨ (b.toNat : Int) = 51 ∨
              (b.toNat : Int) = 52 ∨ (b.toNat : Int) = 53 ∨ (b.toNat : Int) = 54 ∨
              (b.toNat : Int) = 55 ∨ (b.toNat : Int) = 56 ∨ (b.toNat : Int) = 57 := by omega
          unfold «number_minus/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, h48]
          rcases digit with h | h | h | h | h | h | h | h | h <;> simp [h]

        -- Each digit extends the number by one byte.
        have number_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                dec
              (.integer len) =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          have ge : (compare (b.toNat : Int) 48).isGE = true := by
            simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
          have le : (compare (b.toNat : Int) 57).isLE = true := by
            simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have number_digits : ∀ (orig skip acc stack dec : Term) (digits rest : List UInt8),
            (∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) → ∀ len : Int,
            «number/7» (.bitstring ⟨(digits ++ rest).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack
              dec (.integer len) =
              «number/7» (.bitstring ⟨rest.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer (len + digits.length)) := by
          intro orig skip acc stack dec digits rest all len
          induction digits generalizing len with
          | nil => simp
          | cons d ds ih =>
            have bound := all d (by simp)
            simp only [List.cons_append]
            rw [number_digit orig skip acc stack dec len d (ds ++ rest) bound.1 bound.2,
              ih (fun x mem => all x (by simp [mem])) (len + 1)]
            have : len + 1 + (ds.length : Int) = len + ((d :: ds).length : Int) := by simp; omega
            rw [this]

        -- At the end of the input, the integer decoder reads the number's text.
        have number_end : ∀ (orig skip acc stack : Term) (len : Int),
            «number/7» (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) orig skip acc
              stack options
              (.integer len) =
              (do
                let token ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip (.integer len))
                let value ← Term.apply (.function 2 1 #[]) #[token]
                Result.ofExcept («unexpected/8» orig skip acc stack options
                  (.integer len) (.integer 0) (.tuple #[.atom "number", value]))) := by
          intro orig skip acc stack len
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte_nil, extract_none, matchEnd_byte_nil]
          simp

        have number_zero_end : ∀ (orig skip acc stack : Term) (len : Int),
            «number_zero/7» (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) orig skip
              acc stack options
              (.integer len) =
              (do
                let value ← Term.apply (.function 2 1 #[]) #[.bitstring ⟨#[48]⟩ 0 (valid_aligned
                    _)]
                Result.ofExcept («unexpected/8» orig skip acc stack options
                  (.integer len) (.integer 0) (.tuple #[.atom "number", value]))) := by
          intro orig skip acc stack len
          conv => lhs; unfold «number_zero/7»
          simp only [matchInteger_byte_nil, extract_none, matchEnd_byte_nil]
          simp

        -- A number spanning the whole input is the complete result.
        have unexpected_whole : ∀ (bytes : ByteArray) (acc stack dec data : Term),
            «unexpected/8» (.bitstring bytes 0 (valid_aligned _)) (.integer 0) acc stack dec
              (.integer bytes.size) (.integer 0) data =
              .ok (.tuple #[.atom "continue",
                .tuple #[.bitstring bytes 0 (valid_aligned _), acc, stack, dec, data]]) := by
          intro bytes acc stack dec data
          unfold «unexpected/8»
          have rest : matchBinary (.bitstring bytes 0 (valid_aligned _)) (.integer 0) 8 =
              some (ofBits [], .bitstring bytes 0 (valid_aligned _)) := by
            simp [matchBinary, ofBits_toBits_aligned]
          have whole : matchTail (.bitstring bytes 0 (valid_aligned _)) (.atom "all") 8 = true :=
              by
            simp only [matchTail, bitSize]
            split
            · split <;> simp
            · omega
          simp [Erlang.erlang.«byte_size/1», Erlang.erlang.«=</2», rest, whole]

        have decode_integer : ∀ (n : Int) (depth : Nat) (text : Term),
            Erlang.erlang.«integer_to_binary/1» (.integer n) = .ok text →
            Result.resolve Erlang.program.fun_table depth («decode/1» text) = .ok (.integer n) :=
                by
          intro n depth text encoded
          have parsed := Erlang.erlang.binary_to_integer_integer_to_binary n
          rw [encoded] at parsed
          simp only [Except.ok_bind] at parsed
          obtain ⟨first, rest, decimal, digits, zero⟩ := Erlang.erlang.integer_to_binary_decimal n
          rw [encoded] at decimal
          cases decimal
          have size (l : List UInt8) : (ByteArray.mk l.toArray).size = l.length := by
            simp [ByteArray.size]
          have firstLow := (digits first (by simp)).1
          have firstHigh := (digits first (by simp)).2
          have restDigits : ∀ d ∈ rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57 :=
            fun d mem => digits d (by simp [mem])
          by_cases negative : n < 0
          · have firstPositive : 49 ≤ first.toNat := by
              have := digits first (by simp)
              by_cases eq : first.toNat = 48
              · have := (zero eq).1; omega
              · omega
            simp only [negative, if_true, List.cons_append, List.nil_append] at parsed ⊢
            unfold «decode/1»
            simp only []
            rw [value_minus, number_minus_digit _ _ _ _ _ first rest firstPositive firstHigh]
            have loop := number_digits
              (.bitstring ⟨((45 : UInt8) :: first :: rest).toArray⟩ 0 (valid_aligned _))
              (.integer 0) (.atom "ok") .nil
              options rest [] restDigits 2
            simp only [List.append_nil] at loop
            rw [loop, number_end]
            have len : (2 + (rest.length : Int)) =
                ((ByteArray.mk ((45 : UInt8) :: first :: rest).toArray).size : Int) := by
              rw [size]; simp; omega
            rw [len]
            simp [Erlang.erlang.binary_part_whole, «$lynx_fun_2/1», parsed, unexpected_whole]
          · simp only [negative, if_false, List.nil_append] at parsed ⊢
            unfold «decode/1»
            simp only []
            by_cases leading : first.toNat = 48
            · obtain ⟨_, restNil⟩ := zero leading
              subst restNil
              have first48 : first = 48 := UInt8.toNat_inj.mp (by simpa using leading)
              subst first48
              rw [value_zero, number_zero_end]
              have len : (1 : Int) = ((ByteArray.mk ([(48 : UInt8)]).toArray).size : Int) := by
                rw [size]; simp
              rw [len]
              simp [«$lynx_fun_2/1», parsed, unexpected_whole]
            · rw [value_digit _ _ _ _ _ first rest (by omega) firstHigh]
              have loop := number_digits (.bitstring ⟨(first :: rest).toArray⟩ 0 (valid_aligned
                  _))
                (.integer 0) (.atom "ok") .nil
                options rest [] restDigits 1
              simp only [List.append_nil] at loop
              rw [loop, number_end]
              have len : (1 + (rest.length : Int)) =
                  ((ByteArray.mk (first :: rest).toArray).size : Int) := by
                rw [size]; simp; omega
              rw [len]
              simp [Erlang.erlang.binary_part_whole, «$lynx_fun_2/1», parsed, unexpected_whole]

        -- The encoder dispatches through the program table to integer_to_binary/1.
        have roundtrip_integer : ∀ n : Int,
            Result.resolve Erlang.program.fun_table 100 («roundtrip/1» (.integer n)) =
              .ok Term.true := by
          intro n
          simp only [«roundtrip/1», «encode/1», «encode/2», Erlang.erlang.«is_function/2»]
          simp
          unfold «do_encode/2»
          simp only []
          obtain ⟨first, rest, text, -, -⟩ := Erlang.erlang.integer_to_binary_decimal n
          simp [text, Result.resolve_bind, Erlang.erlang.iolist_to_binary_binary,
            decode_integer n 100 _ text, Erlang.erlang.«=:=/2»]

        have continue_array : ∀ (bs : List UInt8) (orig skip acc rest value : Term),
            «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc (.cons
                (.atom "array") rest) options value =
              «array_push/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc (.cons
                  (.atom "array") rest) options value := by
          intro bs orig skip acc rest value
          conv => lhs; unfold «continue/7»
          simp [matchTail, Nat.mod_one]

        have continue_top : ∀ (bs : List UInt8) (orig skip acc value : Term),
            «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc .nil options
                value =
              Result.ofExcept («terminate/5» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc
                value) :=
                  by
          intro bs orig skip acc value
          conv => lhs; unfold «continue/7»
          simp [matchTail, Nat.mod_one]

        have terminate_end : ∀ (orig skip acc value : Term),
            «terminate/5» (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) orig skip
                acc value =
              .ok (.tuple #[value, acc, .bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned
                  _)]) := by
          intro orig skip acc value
          unfold «terminate/5»
          simp [matchInteger_byte_nil, matchEnd_byte_nil]

        have array_push_comma : ∀ (bs : List UInt8) (orig skip acc stack value : Term),
            «array_push/7» (.bitstring ⟨((44 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig
                skip acc stack options value =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 1))
                «value/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig next (.cons value
                    acc) stack options) := by
          intro bs orig skip acc stack value
          conv => lhs; unfold «array_push/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have array_push_close : ∀ (bs : List UInt8) (orig skip acc old stack value : Term),
            «array_push/7» (.bitstring ⟨((93 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig
                skip acc
                (.cons (.atom "array") (.cons old stack)) options value =
              (do
                let list ← Result.ofExcept (Erlang.lists.«reverse/1» (.cons value acc))
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 1))
                «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig next old stack
                    options list) := by
          intro bs orig skip acc old stack value
          conv => lhs; unfold «array_push/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have value_open : ∀ (bs : List UInt8) (orig skip acc stack : Term),
            «value/6» (.bitstring ⟨((91 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc stack options =
              «array_start/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                  options (.integer 1) := by
          intro bs orig skip acc stack
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- An array whose first element starts with a minus sign, a digit, a bracket, a
        -- letter, or a quote.
        have array_start_value : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack : Term)
            (len : Int) (start : b.toNat = 45 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨
            b.toNat = 91 ∨ b.toNat = 116 ∨ b.toNat = 102 ∨ b.toNat = 110 ∨ b.toNat = 34),
            «array_start/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack options (.integer len) =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                «value/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig next .nil
                  (.cons (.atom "array") (.cons acc stack)) options) := by
          intro b bs orig skip acc stack len start
          have h32 : (b.toNat : Int) ≠ 32 := by omega
          have h9 : (b.toNat : Int) ≠ 9 := by omega
          have h13 : (b.toNat : Int) ≠ 13 := by omega
          have h10 : (b.toNat : Int) ≠ 10 := by omega
          have h93 : (b.toNat : Int) ≠ 93 := by omega
          conv => lhs; unfold «array_start/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», h32, h9,
            h13, h10, h93]

        have array_start_close : ∀ (bs : List UInt8) (orig skip acc stack : Term) (len : Int),
            «array_start/7» (.bitstring ⟨((93 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig
                skip acc stack options
                (.integer len) =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                let after ← Result.ofExcept (Erlang.erlang.«+/2» next (.integer 1))
                «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig after acc stack
                    options .nil) := by
          intro bs orig skip acc stack len
          conv => lhs; unfold «array_start/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- A number stops at a separator, reading its text with the integer decoder.
        have number_stop : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack : Term) (len :
            Int) (separator : b.toNat = 44 ∨ b.toNat = 93),
            «number/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                options (.integer len) =
              (do
                let token ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip (.integer len))
                let value ← Term.apply (.function 2 1 #[]) #[token]
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                «continue/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig next acc
                    stack options value) := by
          intro b bs orig skip acc stack len separator
          have h46 : (b.toNat : Int) ≠ 46 := by omega
          have h69 : (b.toNat : Int) ≠ 69 := by omega
          have h101 : (b.toNat : Int) ≠ 101 := by omega
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          rcases separator with h | h
          · have ge : ¬ (compare (b.toNat : Int) 48).isGE = true := by
              simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
            simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
              Erlang.erlang.«=:=/2»,
              Erlang.erlang.«or/2», ge, h46, h69, h101]
          · have ge : (compare (b.toNat : Int) 48).isGE = true := by
              simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
            have le : ¬ (compare (b.toNat : Int) 57).isLE = true := by
              simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega
            simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
              Erlang.erlang.«=:=/2»,
              Erlang.erlang.«or/2», ge, le, h46, h69, h101]

        have number_zero_stop : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack : Term) (len
            : Int) (separator : b.toNat = 44 ∨ b.toNat = 93),
            «number_zero/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack options (.integer len) =
              (do
                let value ← Term.apply (.function 2 1 #[]) #[.bitstring ⟨#[48]⟩ 0 (valid_aligned
                    _)]
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                «continue/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig next acc
                    stack options value) := by
          intro b bs orig skip acc stack len separator
          have h46 : (b.toNat : Int) ≠ 46 := by omega
          have h69 : (b.toNat : Int) ≠ 69 := by omega
          have h101 : (b.toNat : Int) ≠ 101 := by omega
          conv => lhs; unfold «number_zero/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», h46, h69,
            h101]

        have decode_element : ∀ (x : Int) (pre post : List UInt8) (b : UInt8) (separator :
            b.toNat = 44 ∨ b.toNat = 93) (acc stack : Term) (depth : Nat) (first : UInt8) (rest :
            List UInt8) (encoded : Erlang.erlang.«integer_to_binary/1» (.integer x) = .ok
            (.bitstring ⟨((if x < 0 then [45] else []) ++ first :: rest).toArray⟩ 0
            (valid_aligned _))) (digits : ∀ d ∈ first :: rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57) (zero
            : first.toNat = 48 → x = 0 ∧ rest = []),
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(((if x < 0 then [45] else []) ++ first :: rest) ++ b ::
                    post).toArray⟩ 0
                    (valid_aligned _))
                  (.bitstring ⟨(pre ++ ((if x < 0 then [45] else []) ++ first :: rest) ++ b ::
                      post).toArray⟩ 0
                    (valid_aligned _))
                  (.integer pre.length) acc stack options) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨(b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ ((if x < 0 then [45] else []) ++ first :: rest) ++ b ::
                      post).toArray⟩ 0
                    (valid_aligned _))
                  (.integer (pre.length + ((if x < 0 then [45] else []) ++ first ::
                      rest).length)) acc stack options
                  (.integer x)) := by
          intro x pre post b separator acc stack depth first rest encoded digits zero
          have parsed := Erlang.erlang.binary_to_integer_integer_to_binary x
          rw [encoded] at parsed
          simp only [Except.ok_bind] at parsed
          have firstLow := (digits first (by simp)).1
          have firstHigh := (digits first (by simp)).2
          have restDigits : ∀ d ∈ rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57 := fun d mem => digits d (by
              simp [mem])
          by_cases negative : x < 0
          · have firstPositive : 49 ≤ first.toNat := by
              by_cases eq : first.toNat = 48
              · have := (zero eq).1; omega
              · omega
            simp only [negative, if_true, List.cons_append, List.nil_append] at parsed ⊢
            rw [value_minus,
              number_minus_digit _ _ _ _ _ first (rest ++ b :: post) firstPositive firstHigh,
              number_digits _ _ _ _ _ rest (b :: post) restDigits 2, number_stop b post _ _ _ _ _
                  separator]
            have part := binary_part_middle pre ((45 : UInt8) :: first :: rest) (b :: post)
            simp only [List.length_cons] at part ⊢
            have len : (2 + (rest.length : Int)) = ((rest.length + 1 + 1 : Nat) : Int) := by omega
            rw [len, part]
            simp [«$lynx_fun_2/1», parsed]
          · simp only [negative, if_false, List.nil_append] at parsed ⊢
            by_cases leading : first.toNat = 48
            · obtain ⟨_, restNil⟩ := zero leading
              subst restNil
              have first48 : first = 48 := UInt8.toNat_inj.mp (by simpa using leading)
              subst first48
              simp only [List.cons_append, List.nil_append]
              rw [value_zero, number_zero_stop b post _ _ _ _ _ separator]
              simp [«$lynx_fun_2/1», parsed]
            · simp only [List.cons_append]
              rw [value_digit _ _ _ _ _ first (rest ++ b :: post) (by omega) firstHigh,
                number_digits _ _ _ _ _ rest (b :: post) restDigits 1, number_stop b post _ _ _ _
                    _ separator]
              have part := binary_part_middle pre (first :: rest) (b :: post)
              simp only [List.length_cons] at part ⊢
              have len : (1 + (rest.length : Int)) = ((rest.length + 1 : Nat) : Int) := by omega
              rw [len, part]
              simp [«$lynx_fun_2/1», parsed]

        have textOf_decimal : ∀ (x : Int),
            ∃ (first : UInt8) (rest : List UInt8),
              textOf x = (if x < 0 then [45] else []) ++ first :: rest ∧
              Erlang.erlang.«integer_to_binary/1» (.integer x) =
                .ok (.bitstring ⟨((if x < 0 then [45] else []) ++ first :: rest).toArray⟩ 0
                    (valid_aligned _)) ∧
              (∀ d ∈ first :: rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧ (first.toNat = 48 → x = 0 ∧
                  rest = []) := by
          intro x
          obtain ⟨first, rest, encoded, digits, zero⟩ := Erlang.erlang.integer_to_binary_decimal x
          refine ⟨first, rest, ?_, encoded, digits, zero⟩
          simp only [Erlang.erlang.«integer_to_binary/1», Except.ok.injEq,
            Term.bitstring.injEq] at encoded
          rw [textOf, encoded.1]

        -- A number embedded in the input, followed by a separator, continues with its value.
        have element : ∀ (x : Int) (pre post : List UInt8) (b : UInt8) (separator : b.toNat = 44
            ∨ b.toNat = 93) (acc stack : Term) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(textOf x ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ textOf x ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.integer pre.length) acc stack options) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨(b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ textOf x ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.integer (pre.length + (textOf x).length)) acc stack options (.integer x)) :=
                      by
          intro x pre post b separator acc stack depth
          obtain ⟨first, rest, text, encoded, digits, zero⟩ := textOf_decimal x
          rw [text]
          exact decode_element x pre post b separator acc stack depth first rest encoded digits zero

        have encode_integer : ∀ (x : Int) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth («do_encode/2» (.integer x) (.function
                0 2 #[])) =
              .ok (.bitstring ⟨(textOf x).toArray⟩ 0 (valid_aligned _)) := by
          intro x depth
          obtain ⟨first, rest, text, encoded, -, -⟩ := textOf_decimal x
          unfold «do_encode/2»
          simp only []
          rw [encoded, Result.resolve_of_isPure _ _ _ (by simp), text, Result.ofExcept_ok]

        -- Keywords dispatch on their first letter and match their other letters at once.
        have value_true : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((116 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc stack dec =
              «true/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have value_false : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((102 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc stack dec =
              «false/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have value_null : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((110 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc stack dec =
              «null/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have true_rest : ∀ (orig skip acc stack dec : Term) (post : List UInt8),
            «true/6» (.bitstring ⟨([114, 117, 101] ++ post).toArray⟩ 0 (valid_aligned _)) orig
                skip acc stack dec =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 4))
                «continue/7» (.bitstring ⟨post.toArray⟩ 0 (valid_aligned _)) orig next acc stack
                  dec (.atom "true")) := by
          intro orig skip acc stack dec post
          unfold «true/6»
          simp only [matchInteger_bytes [114, 117, 101] post _ 24 (by decide), extract_some]
          simp [matchTail, Nat.mod_one]

        have false_rest : ∀ (orig skip acc stack dec : Term) (post : List UInt8),
            «false/6» (.bitstring ⟨([97, 108, 115, 101] ++ post).toArray⟩ 0 (valid_aligned _))
                orig skip acc stack dec =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 5))
                «continue/7» (.bitstring ⟨post.toArray⟩ 0 (valid_aligned _)) orig next acc stack
                  dec (.atom "false")) := by
          intro orig skip acc stack dec post
          unfold «false/6»
          simp only [matchInteger_bytes [97, 108, 115, 101] post _ 32 (by decide), extract_some]
          simp [matchTail, Nat.mod_one]

        have null_rest : ∀ (orig skip acc stack : Term) (post : List UInt8),
            «null/6» (.bitstring ⟨([117, 108, 108] ++ post).toArray⟩ 0 (valid_aligned _)) orig
                skip acc stack options =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 4))
                «continue/7» (.bitstring ⟨post.toArray⟩ 0 (valid_aligned _)) orig next acc stack
                  options (.atom "null")) := by
          intro orig skip acc stack post
          unfold «null/6»
          simp only [matchInteger_bytes [117, 108, 108] post _ 24 (by decide), extract_some]
          simp [matchTail, Nat.mod_one]

        have reverse2 : ∀ (l tail : List Term),
            Erlang.lists.«reverse/2» (Term.list l) (Term.list tail) =
              .ok (Term.list (l.reverse ++ tail)) := by
          intro l tail
          induction l generalizing tail with
          | nil => simp [Erlang.lists.«reverse/2»]
          | cons x xs ih =>
            simp only [Term.list_cons, Erlang.lists.«reverse/2»]
            rw [show Term.cons x (Term.list tail) = Term.list (x :: tail) from rfl, ih]
            simp

        have reverse1 : ∀ (l : List Term),
            Erlang.lists.«reverse/1» (Term.list l) = .ok (Term.list l.reverse) := by
          intro l
          match l with
          | [] => simp [Erlang.lists.«reverse/1»]
          | [a] => simp [Erlang.lists.«reverse/1»]
          | [a, b] => simp [Erlang.lists.«reverse/1»]
          | a :: b :: c :: rest =>
            unfold Erlang.lists.«reverse/1»
            have reversed := reverse2 (c :: rest) [b, a]
            simp only [Term.list_cons, Term.list_nil] at reversed ⊢
            rw [reversed]
            simp

        have terms_list : ∀ l : List Json, Json.terms l = Term.list (l.map Json.term) := by
          intro l
          induction l with
          | nil => rfl
          | cons x xs ih => simp [Json.terms, ih]

        have depth_le : ∀ (l : List Json) (x : Json), x ∈ l → x.depth ≤ Json.depths l := by
          intro l x mem
          induction l with
          | nil => cases mem
          | cons y ys ih =>
            simp only [Json.depths]
            rcases List.mem_cons.mp mem with rfl | mem
            · exact Nat.le_max_left _ _
            · exact Nat.le_trans (ih mem) (Nat.le_max_right _ _)

        -- Values start with a minus sign, a digit, an opening bracket, a letter, or a quote.
        have first_byte : ∀ v : Json, ∃ b bs, v.text = b :: bs ∧
            (b.toNat = 45 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ b.toNat = 91 ∨ b.toNat = 116 ∨
              b.toNat = 102 ∨ b.toNat = 110 ∨ b.toNat = 34) := by
          intro v
          cases v with
          | int x =>
            obtain ⟨first, rest, text, -, digits, -⟩ := textOf_decimal x
            by_cases negative : x < 0
            · exact ⟨45, first :: rest, by simp [Json.text, text, negative], Or.inl rfl⟩
            · exact ⟨first, rest, by simp [Json.text, text, negative],
                Or.inr (Or.inl (digits first (by simp)))⟩
          | bool b => cases b <;> exact ⟨_, _, rfl, by decide⟩
          | null => exact ⟨_, _, rfl, by decide⟩
          | str s _ => exact ⟨34, _, rfl, by decide⟩
          | arr l => cases l <;> exact ⟨91, _, rfl, by decide⟩

        -- The elements after the first start with a comma or the closing bracket.
        have tail_start : ∀ xs : List Json, ∃ b post, Json.tailText xs = b :: post ∧
            (b.toNat = 44 ∨ b.toNat = 93) := by
          intro xs
          cases xs
          · exact ⟨93, [], rfl, Or.inr rfl⟩
          · exact ⟨44, _, rfl, Or.inl rfl⟩

        -- Decoding a value's text continues with its term after the text. Numbers
        -- need a separator after them, while other values end with their text.
        let Decodes : Json → Prop := fun v => ∀ (pre rest : List UInt8) (acc stack : Term)
            (depth : Nat),
            ((∃ b post, rest = b :: post ∧ (b.toNat = 44 ∨ b.toNat = 93)) ∨ ∀ n, v ≠ .int n) →
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(v.text ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ v.text ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.integer pre.length) acc stack options) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨rest.toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ v.text ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.integer (pre.length + v.text.length)) acc stack options v.term)

        -- An array frame pushes each element and closes with the reversed list.
        have loop : ∀ xs : List Json, (∀ y ∈ xs, Decodes y) →
            ∀ (done : List Term) (value : Term) (pre rest : List UInt8) (old stack : Term)
              (depth : Nat),
            Result.resolve Erlang.program.fun_table depth
                («array_push/7» (.bitstring ⟨(Json.tailText xs ++ rest).toArray⟩ 0
                    (valid_aligned _))
                  (.bitstring ⟨(pre ++ Json.tailText xs ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.integer pre.length) (Term.list done.reverse)
                  (.cons (.atom "array") (.cons old stack)) options value) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨rest.toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ Json.tailText xs ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.integer (pre.length + (Json.tailText xs).length)) old stack options
                  (Term.list (done ++ value :: xs.map Json.term))) := by
          intro xs
          induction xs with
          | nil =>
            intro _ done value pre rest old stack depth
            rw [show Json.tailText [] = [93] from rfl]
            simp only [List.cons_append, List.nil_append]
            rw [array_push_close,
              show Term.cons value (Term.list done.reverse) =
                Term.list (value :: done.reverse) from rfl, reverse1]
            simp [Result.resolve_bind]
          | cons y ys ih =>
            intro all done value pre rest old stack depth
            obtain ⟨b, post, tail, separator⟩ := tail_start ys
            have first := all y (by simp) (pre ++ [44]) (Json.tailText ys ++ rest)
              (.cons value (Term.list done.reverse)) (.cons (.atom "array") (.cons old stack))
              depth (Or.inl ⟨b, post ++ rest, by simp [tail], separator⟩)
            have next := ih (fun z mem => all z (by simp [mem])) (done ++ [value]) y.term
              (pre ++ 44 :: y.text) rest old stack depth
            have skip : (((pre ++ [44]).length : Nat) : Int) = pre.length + 1 := by simp
            have skip' : (((pre ++ 44 :: y.text).length : Nat) : Int) =
                pre.length + 1 + y.text.length := by simp; omega
            rw [skip] at first
            rw [skip'] at next
            simp only [List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append, List.reverse_append, List.reverse_singleton] at first next
            rw [show Json.tailText (y :: ys) = 44 :: (y.text ++ Json.tailText ys) from rfl]
            simp only [List.cons_append, List.append_assoc]
            rw [array_push_comma]
            simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers»,
              Result.ofExcept_ok, Result.ok_bind,
              Result.resolve_of_isPure _ _ (Result.ok _) (by simp),
              Result.resolve_of_isPure _ _ (Result.ofExcept _) (by simp)]
            rw [first, continue_array]
            rw [next]
            have length : (pre.length : Int) + 1 + y.text.length + (Json.tailText ys).length =
                pre.length + (44 :: (y.text ++ Json.tailText ys)).length := by simp; omega
            simp [length]

        have decodes : ∀ v : Json, Decodes v := by
          intro v
          induction v using Json.rec (motive_2 := fun l => ∀ x ∈ l, Decodes x) with
          | int x =>
            intro pre rest acc stack depth separated
            rcases separated with ⟨b, post, rfl, separator⟩ | number
            · exact element x pre post b separator acc stack depth
            · exact absurd rfl (number x)
          | bool b =>
            intro pre rest acc stack depth _
            cases b
            · rw [show Json.text (.bool false) = [102, 97, 108, 115, 101] from rfl]
              simp only [List.cons_append, List.nil_append]
              rw [value_false, show (97 :: 108 :: 115 :: 101 :: rest : List UInt8) =
                [97, 108, 115, 101] ++ rest from rfl, false_rest]
              simp [Result.resolve_bind, Json.term, Int.add_assoc]
            · rw [show Json.text (.bool true) = [116, 114, 117, 101] from rfl]
              simp only [List.cons_append, List.nil_append]
              rw [value_true, show (114 :: 117 :: 101 :: rest : List UInt8) =
                [114, 117, 101] ++ rest from rfl, true_rest]
              simp [Result.resolve_bind, Json.term, Int.add_assoc]
          | null =>
            intro pre rest acc stack depth _
            rw [show Json.text .null = [110, 117, 108, 108] from rfl]
            simp only [List.cons_append, List.nil_append]
            rw [value_null, show (117 :: 108 :: 108 :: rest : List UInt8) =
              [117, 108, 108] ++ rest from rfl, null_rest]
            simp [Result.resolve_bind, Json.term, Int.add_assoc]
          | str s ascii =>
            intro pre rest acc stack depth _
            rw [show Json.text (.str s ascii) = 34 :: (escapeText s ++ [34]) from rfl]
            simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
            rw [value_quote]
            simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
              Result.ok_bind]
            obtain ⟨p, r, rfl, pPlain, stop⟩ := split_plain s
            have part := binary_part_middle (pre ++ [34]) p (escapeText r ++ 34 :: rest)
            simp only [escapeText_append, escapeText_plain p pPlain, List.append_assoc,
              List.cons_append, List.singleton_append, List.nil_append, List.length_append,
              List.length_cons, List.length_nil] at part ⊢
            push_cast at part ⊢
            rcases stop with rfl | ⟨e, r, rfl, escaped⟩
            · simp only [show escapeText [] = [] from rfl, List.nil_append] at part ⊢
              rw [string_ascii p.length p (34 :: rest) _ _ _ _ _ 0 (Nat.le_refl _) pPlain
                (fun c rs same => by cases same; rfl), string_close]
              simp only [Int.zero_add, part, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
                Result.ok_bind, List.append_nil]
              rw [show (pre.length : Int) + 1 + p.length + 1 = pre.length + (p.length + 1 + 1) by
                omega]
              rfl
            · have eAscii := ascii e (by simp)
              obtain ⟨t, et, unescaped⟩ := unescape_escape e eAscii escaped
              have escapedHead : escapeText (e :: r) = escapeBytes e ++ escapeText r := by
                rw [show e :: r = [e] ++ r from rfl, escapeText_append, escapeText_escape e escaped]
              rw [escapedHead, et] at part
              simp only [escapedHead, et] at ⊢
              simp only [List.cons_append, List.append_assoc] at part ⊢
              rw [string_ascii p.length p _ _ _ _ _ _ 0 (Nat.le_refl _) pPlain
                (fun c rs same => by cases same; rfl), Int.zero_add,
                string_escape _ _ _ _ _ _ _ _ part, unescaped]
              have next := decode_rest r.length r (p ++ [e]) pre rest acc stack
                (.integer (pre.length + 1 - 1)) (Nat.le_refl _) (fun x mem => ascii x (by simp [mem]))
              simp only [escapeText_append, escapeText_plain p pPlain, escapeText_escape e escaped,
                escapedHead, et, List.append_assoc, List.cons_append, List.singleton_append,
                List.nil_append, List.length_append, List.length_cons] at next ⊢
              push_cast at next ⊢
              rw [show (pre.length : Int) + 1 + p.length + (t.length + 1) =
                pre.length + 1 + (p.length + (t.length + 1)) by omega, next,
                show (pre.length : Int) + 1 + (p.length + (t.length + (escapeText r).length + 1)) + 1 =
                  pre.length + (p.length + (t.length + (escapeText r).length + 1 + 1) + 1) by omega]
              rfl
          | arr l ih =>
            intro pre rest acc stack depth _
            cases l with
            | nil =>
              rw [show Json.text (.arr []) = [91, 93] from rfl]
              simp only [List.cons_append, List.nil_append]
              rw [value_open, array_start_close]
              simp [Result.resolve_bind, Json.term, Json.terms, Int.add_assoc]
            | cons x xs =>
              obtain ⟨b, bs, head, start⟩ := first_byte x
              obtain ⟨c, post, tail, separator⟩ := tail_start xs
              have opened := array_start_value b (bs ++ (Json.tailText xs ++ rest))
                (.bitstring ⟨(pre ++ 91 :: (x.text ++ (Json.tailText xs ++ rest))).toArray⟩ 0
                  (valid_aligned _))
                (.integer pre.length) acc stack 1 start
              rw [show b :: (bs ++ (Json.tailText xs ++ rest)) =
                x.text ++ (Json.tailText xs ++ rest) by rw [head]; rfl] at opened
              have first := ih x (by simp) (pre ++ [91]) (Json.tailText xs ++ rest) .nil
                (.cons (.atom "array") (.cons acc stack)) depth
                (Or.inl ⟨c, post ++ rest, by simp [tail], separator⟩)
              have next := loop xs (fun y mem => ih y (by simp [mem])) [] x.term
                (pre ++ 91 :: x.text) rest acc stack depth
              have skip : (((pre ++ [91]).length : Nat) : Int) = pre.length + 1 := by simp
              have skip' : (((pre ++ 91 :: x.text).length : Nat) : Int) =
                  pre.length + 1 + x.text.length := by simp; omega
              rw [skip] at first
              rw [skip'] at next
              simp only [List.append_assoc, List.cons_append, List.singleton_append,
                List.nil_append, List.reverse_nil] at first next
              rw [show Json.text (.arr (x :: xs)) = 91 :: (x.text ++ Json.tailText xs) from rfl]
              simp only [List.cons_append, List.append_assoc]
              rw [value_open, opened]
              simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers»,
                Result.ofExcept_ok, Result.ok_bind,
                Result.resolve_of_isPure _ _ (Result.ok _) (by simp),
                Result.resolve_of_isPure _ _ (Result.ofExcept _) (by simp)]
              rw [first, continue_array]
              rw [next]
              have length : (pre.length : Int) + 1 + x.text.length + (Json.tailText xs).length =
                  pre.length + (91 :: (x.text ++ Json.tailText xs)).length := by simp; omega
              simp [length, Json.term, Json.terms, terms_list]
          | nil y mem => cases mem
          | cons x xs hx hxs y mem =>
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hx
            · exact hxs y mem

        have decode_value : ∀ (v : Json) (depth : Nat), (∀ n, v ≠ .int n) →
            Result.resolve Erlang.program.fun_table depth
                («decode/1» (.bitstring ⟨v.text.toArray⟩ 0 (valid_aligned _))) = .ok v.term := by
          intro v depth number
          have whole := decodes v [] [] (.atom "ok") .nil depth (Or.inr number)
          simp only [List.nil_append, List.append_nil, List.length_nil, Int.zero_add] at whole
          rw [show ((0 : Nat) : Int) = 0 from rfl] at whole
          unfold «decode/1»
          simp only []
          simp only [Result.resolve_bind]
          rw [whole, continue_top, terminate_end]
          simp

        -- Encoding a value makes one dynamic call per nesting level.
        have flat_byte : ∀ (k : UInt8) (r : Term) (y : List UInt8),
            Erlang.erlang.«iolist_to_binary/1» r = .ok (bin y) →
            Erlang.erlang.«iolist_to_binary/1» (.cons (.integer k.toNat) r) = .ok (bin (k :: y)) := by
          intro k r y rest
          have := k.toNat_lt
          rw [Erlang.erlang.iolist_to_binary_byte_cons _ _ _ (by omega) (by omega) rest]
          congr 2
          rw [show UInt8.ofNat (k.toNat : Int).toNat = k by simp]
          rfl

        -- Encoding a value makes one dynamic call per nesting level, and builds iodata
        -- that flattens to its text.
        have list_loop_values : ∀ (xs : List Json) (k : Nat),
            (∀ y ∈ xs, ∀ depth, y.depth < depth → ∃ io,
              Result.resolve Erlang.program.fun_table depth
                («do_encode/2» y.term (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin y.text)) →
            (∀ y ∈ xs, y.depth < k) →
            ∃ io, Result.resolve Erlang.program.fun_table (k + 1)
                («list_loop/2» (Json.terms xs) (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin (Json.tailText xs)) := by
          intro xs k encodes bound
          induction xs with
          | nil => exact ⟨.cons (.integer 93) .nil, by simp [Json.terms, «list_loop/2»],
              flat_byte 93 _ _ Erlang.erlang.iolist_to_binary_nil⟩
          | cons y ys ih =>
            obtain ⟨yio, yres, yflat⟩ := encodes y (by simp) k (bound y (by simp))
            obtain ⟨lio, lres, lflat⟩ := ih (fun z mem => encodes z (by simp [mem]))
              (fun z mem => bound z (by simp [mem]))
            refine ⟨.cons (.integer 44) (.cons yio lio), ?_, flat_byte 44 _ _
              (flat_join _ _ _ _ yflat lflat)⟩
            simp only [Json.terms, «list_loop/2»]
            simp [Result.resolve_bind, yres, lres]

        have encode_value : ∀ (v : Json) (depth : Nat), v.depth < depth → ∃ io,
            Result.resolve Erlang.program.fun_table depth
                («do_encode/2» v.term (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin v.text) := by
          intro v
          induction v using Json.rec (motive_2 := fun l => ∀ x ∈ l, ∀ depth, x.depth < depth →
              ∃ io, Result.resolve Erlang.program.fun_table depth
                («do_encode/2» x.term (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin x.text)) with
          | int x => intro depth _; exact ⟨_, encode_integer x depth, flat_bin _⟩
          | bool b =>
            intro depth _
            cases b
            · exact ⟨bin [102, 97, 108, 115, 101], by unfold «do_encode/2»; simp [Json.term],
                flat_bin _⟩
            · exact ⟨bin [116, 114, 117, 101], by unfold «do_encode/2»; simp [Json.term],
                flat_bin _⟩
          | null =>
            intro depth _
            exact ⟨bin [110, 117, 108, 108], by unfold «do_encode/2»; simp [Json.term],
              flat_bin _⟩
          | str s ascii =>
            intro depth _
            obtain ⟨io, encoded, flat⟩ := (encode_string s.length s [] [] (Term.list [.integer 34])
              (Nat.le_refl _) ascii (by simp) flat_close).2
            simp only [List.nil_append, List.length_nil] at encoded flat
            refine ⟨io, ?_, flat⟩
            unfold «do_encode/2»
            simp [Json.term]
            exact encoded
          | arr l ih =>
            intro depth bound
            simp only [Json.depth] at bound
            obtain ⟨k, rfl⟩ : ∃ k, depth = k + 1 := ⟨depth - 1, by omega⟩
            cases l with
            | nil =>
              refine ⟨bin [91, 93], ?_, flat_bin _⟩
              unfold «do_encode/2»
              simp [Json.term, Json.terms, «do_encode_list/2», Erlang.erlang.«is_list/1»]
            | cons x xs =>
              have elements : ∀ y ∈ x :: xs, y.depth < k := fun y mem => by
                have := depth_le _ y mem
                omega
              obtain ⟨xio, xres, xflat⟩ := ih x (by simp) k (elements x (by simp))
              obtain ⟨lio, lres, lflat⟩ := list_loop_values xs k (fun y mem => ih y (by simp [mem]))
                (fun y mem => elements y (by simp [mem]))
              refine ⟨.cons (.integer 91) (.cons xio lio), ?_, flat_byte 91 _ _
                (flat_join _ _ _ _ xflat lflat)⟩
              unfold «do_encode/2»
              simp [Json.term, Json.terms, Erlang.erlang.«is_list/1», «do_encode_list/2»,
                Erlang.erlang.«is_function/2»]
              rw [xres, Result.ok_bind, Result.resolve_bind, lres, Result.ok_bind,
                Result.resolve_of_isPure _ _ _ (by simp)]
          | nil y mem => cases mem
          | cons x xs hx hxs y mem depth bound =>
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hx depth bound
            · exact hxs y mem depth bound

        have roundtrip_value : ∀ v : Json, (∀ n, v ≠ .int n) → v.depth < 99 →
            Result.resolve Erlang.program.fun_table 100 («roundtrip/1» v.term) = .ok Term.true := by
          intro v number bound
          simp only [«roundtrip/1», «encode/1», «encode/2», Erlang.erlang.«is_function/2»]
          simp
          obtain ⟨io, encoded, flat⟩ := encode_value v 99 bound
          rw [encoded, Result.ok_bind]
          simp only [Result.resolve_bind,
            Result.resolve_of_isPure _ _ (Result.ok _) (by simp),
            Result.resolve_of_isPure _ _ (Result.ofExcept _) (by simp),
            Result.ofExcept_ok, Result.ok_bind]
          rw [flat, Result.ofExcept_ok, Result.ok_bind,
            decode_value v _ number, Result.ok_bind]
          simp [Erlang.erlang.«=:=/2», Result.ofExcept_ok]

        -- The requirement describes values nested at most as deep as its budget.
        have extract : ∀ (s : Nat) (t : Term), sizeOf t < s →
            (∀ n : Int, «supported?/2» t (.integer n) = .ok Term.true →
              ∃ v : Json, t = v.term ∧ (v.depth : Int) ≤ max n 0) ∧
            (∀ n : Int, «values?/2» t (.integer n) = .ok Term.true →
              ∃ l : List Json, t = Json.terms l ∧ (Json.depths l : Int) ≤ max n 0) := by
          intro s
          induction s with
          | zero => intro t size; omega
          | succ s ih =>
            intro t size
            have values : ∀ n : Int, «values?/2» t (.integer n) = .ok Term.true →
                ∃ l : List Json, t = Json.terms l ∧ (Json.depths l : Int) ≤ max n 0 := by
              intro n returned
              rw [«values?/2».eq_def] at returned
              cases t with
              | nil => exact ⟨[], rfl, by simp [Json.depths] <;> omega⟩
              | cons x xs =>
                simp only [Term.cons.sizeOf_spec] at size
                cases first : «supported?/2» x (.integer n) <;>
                  simp [first, Bind.bind, Except.bind] at returned
                split at returned
                · simp at returned
                · obtain ⟨v, rfl, vDepth⟩ := (ih x (by omega)).1 n first
                  obtain ⟨l, rfl, lDepth⟩ := (ih xs (by omega)).2 n returned
                  exact ⟨v :: l, rfl, by simp [Json.depths]; omega⟩
                · simp at returned
              | _ => simp at returned
            refine ⟨fun n returned => ?_, values⟩
            rw [«supported?/2».eq_def] at returned
            cases t with
            | integer x => exact ⟨.int x, rfl, by simp [Json.depth] <;> omega⟩
            | atom name =>
              by_cases yes : name = "true"
              · subst yes; exact ⟨.bool true, rfl, by simp [Json.depth] <;> omega⟩
              by_cases no : name = "false"
              · subst no; exact ⟨.bool false, rfl, by simp [Json.depth] <;> omega⟩
              by_cases null : name = "null"
              · subst null; exact ⟨.null, rfl, by simp [Json.depth] <;> omega⟩
              simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_list/1», yes, no, null]
                at returned
            | bitstring bytes last valid =>
              by_cases aligned : last = 0
              · subst aligned
                rcases bytes with ⟨data⟩
                have same : Term.bitstring ⟨data⟩ 0 valid = bin data.toList := by simp
                simp only [same] at returned ⊢
                simp [Erlang.erlang.«is_integer/1»] at returned
                exact ⟨.str data.toList (ascii_bytes _ returned), rfl, by simp [Json.depth]; omega⟩
              · obtain ⟨_ | k, bound⟩ := last
                · exact absurd rfl aligned
                · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_list/1»] at returned
            | nil | cons _ _ =>
              by_cases positive : 0 < n
              · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_list/1»,
                  Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, positive]
                  at returned
                obtain ⟨l, same, lDepth⟩ := values (n - 1) returned
                exact ⟨.arr l, same, by simp [Json.depth]; omega⟩
              · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_list/1»,
                  Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, positive]
                  at returned
            | _ => simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_list/1»] at returned

        apply Lynx.run_of_resolve rfl
        simp only [«json_roundtrip:requires/1», «supported?/1»] at requires
        obtain ⟨v, rfl, bound⟩ := (extract _ data (Nat.lt_succ_self _)).1 64 requires
        cases v with
        | int n => simpa [«json_roundtrip:ensures/1», Json.term] using roundtrip_integer n
        | _ =>
          simpa [«json_roundtrip:ensures/1»] using roundtrip_value _ (by simp) (by omega))
      """
  end
end
