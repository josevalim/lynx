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

  # The data covered so far: integers, booleans, null, strings of printable
  # ASCII that need no escaping, and lists of them, nested at most 64 deep.
  # The encoder makes one dynamic call per nesting level, and laws run with a
  # call depth of 100.
  def supported?(data), do: supported?(data, 64)

  def supported?(data, _depth) when is_integer(data) or data in [true, false, :null],
    do: true

  def supported?(data, _depth) when is_binary(data), do: plain?(data)
  def supported?(data, depth) when is_list(data) and depth > 0, do: values?(data, depth - 1)
  def supported?(_data, _depth), do: false

  def values?([], _depth), do: true
  def values?([x | xs], depth), do: supported?(x, depth) and values?(xs, depth)
  def values?(_data, _depth), do: false

  def plain?(<<byte, rest::binary>>)
      when byte >= 32 and byte < 128 and byte != ?" and byte != ?\\,
      do: plain?(rest)

  def plain?(<<>>), do: true
  def plain?(_data), do: false

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

    /-- JSON values made of integers, booleans, null, strings, and lists. -/
    inductive Json where
      | int : Int → Json
      | bool : Bool → Json
      | null : Json
      | str (s : List UInt8) (ok : ∀ b ∈ s, plain b)
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
      | .str s _ => 34 :: (s ++ [34])
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

    mutual
    /-- The iodata `do_encode/2` builds for a value. -/
    @[expose] def Json.iodata : Json → Term
      | .int n => .bitstring ⟨(textOf n).toArray⟩ 0 (Term.Bitstring.valid_aligned _)
      | .bool true => .bitstring ⟨#[116, 114, 117, 101]⟩ 0 (Term.Bitstring.valid_aligned _)
      | .bool false => .bitstring ⟨#[102, 97, 108, 115, 101]⟩ 0 (Term.Bitstring.valid_aligned _)
      | .null => .bitstring ⟨#[110, 117, 108, 108]⟩ 0 (Term.Bitstring.valid_aligned _)
      | .str s _ => Term.list [.integer 34, bin s, .integer 34]
      | .arr [] => .bitstring ⟨#[91, 93]⟩ 0 (Term.Bitstring.valid_aligned _)
      | .arr (x :: xs) => .cons (.integer 91) (.cons x.iodata (Json.loopIodata xs))
    /-- The iodata `list_loop/2` builds for the elements after the first. -/
    @[expose] def Json.loopIodata : List Json → Term
      | [] => .cons (.integer 93) .nil
      | y :: ys => .cons (.integer 44) (.cons y.iodata (Json.loopIodata ys))
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
    # brackets, separated by commas. The decoder dispatches on each byte, reads
    # integers back with binary_to_integer/1, the integer decoder in its default
    # options, matches the remaining letters of a literal at once, takes a
    # string's bytes up to its closing quote, and pushes values onto an array
    # frame, opening a new frame for each nested list. Both sides scan strings
    # seven bytes at a time while a SWAR test finds no byte to escape, and one
    # byte at a time otherwise.
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

        have escape_plain : ∀ (p r : List UInt8) (acc orig skip : Term) (len : Int),
            (∀ b ∈ p, plain b) →
            «escape_binary/5» (bin (p ++ r)) acc orig skip (.integer len) =
              «escape_binary/5» (bin r) acc orig skip (.integer (len + p.length)) := by
          intro p r acc orig skip len all
          induction p generalizing len with
          | nil => simp
          | cons b p ih =>
            rw [List.cons_append, escape_plain_byte _ _ _ _ _ _ (all b (by simp)),
              ih _ (fun x mem => all x (by simp [mem]))]
            congr 2
            simp
            omega

        -- A string without escapes is the original binary between quotes.
        have escape_end : ∀ (acc orig len : Term),
            «escape_binary/5» (bin []) acc orig (.integer 0) len =
              .ok (Term.list [.integer 34, orig, .integer 34]) := by
          intro acc orig len
          unfold «escape_binary/5»
          simp [matchInteger_byte_nil]

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

        -- Bytes that need no escaping, up to one that does, extend the current run.
        have escape_ascii : ∀ (n : Nat) (p r : List UInt8) (acc orig skip : Term) (len : Int),
            p.length ≤ n → (∀ b ∈ p, plain b) →
            (∀ c rs, r = c :: rs → plain c = false) →
            «escape_binary_ascii/5» (bin (p ++ r)) acc orig skip (.integer len) =
              «escape_binary/5» (bin r) acc orig skip (.integer (len + p.length)) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro p r acc orig skip len size all stop
            by_cases short : (p ++ r).length < 7
            · rw [escape_ascii_short _ _ _ _ _ short]
              exact escape_plain p r acc orig skip len all
            have whole := List.take_append_drop 7 (p ++ r)
            rw [← whole]
            rcases escape_ascii_word (List.take 7 (p ++ r)) (List.drop 7 (p ++ r)) acc orig skip len
                (by rw [List.length_take]; omega) with ⟨step, word⟩ | fallback
            · by_cases long : 7 ≤ p.length
              · rw [step, List.drop_append_of_le_length long,
                  ih (p.length - 7) (by omega) (List.drop 7 p) r acc orig skip (len + 7)
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
              exact escape_plain p r acc orig skip len all

        -- Strings that need no escaping are encoded between quotes.
        have encode_plain : ∀ (s : List UInt8) (depth : Nat), (∀ b ∈ s, plain b) →
            Result.resolve Erlang.program.fun_table depth
                («do_encode/2» (bin s) (.function 0 2 #[])) =
              .ok (Term.list [.integer 34, bin s, .integer 34]) := by
          intro s depth all
          unfold «do_encode/2»
          have run := escape_ascii s.length s [] (Term.list [.integer 34]) (bin s) (.integer 0) 0
            (Nat.le_refl _) all (by simp)
          simp only [List.append_nil] at run
          simp [run, escape_end]

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

        -- The requirement accepts binaries whose bytes need no escaping.
        have plain_bytes : ∀ s : List UInt8,
            «plain?/1» (bin s) = .ok Term.true → ∀ b ∈ s, plain b := by
          intro s
          induction s with
          | nil => simp
          | cons b s ih =>
            intro returned
            unfold «plain?/1» at returned
            rw [matchInteger_byte] at returned
            simp [tail8, matchEnd_byte, Erlang.erlang.«/=/2»] at returned
            by_cases low : (32 : Int) ≤ b.toNat <;> by_cases high : (b.toNat : Int) < 128 <;>
              by_cases quote : (b.toNat : Int) = 34 <;> by_cases slash : (b.toNat : Int) = 92 <;>
              simp [low, high, quote, slash] at returned
            intro x mem
            rcases List.mem_cons.mp mem with rfl | mem
            · simp [plain]
              omega
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
          | str s ok =>
            intro pre rest acc stack depth _
            rw [show Json.text (.str s ok) = 34 :: (s ++ [34]) from rfl]
            simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
            rw [value_quote]
            simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
              Result.ok_bind]
            rw [string_ascii s.length s (34 :: rest) _ _ _ _ _ 0 (Nat.le_refl _) ok
              (fun c rs same => by cases same; rfl), string_close]
            have part := binary_part_middle (pre ++ [34]) s (34 :: rest)
            simp only [List.append_assoc, List.singleton_append, List.cons_append,
              List.nil_append, List.length_append, List.length_singleton] at part
            have skip : (((pre.length + 1 : Nat)) : Int) = pre.length + 1 := by simp
            rw [skip] at part
            simp only [Int.zero_add, part, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
              Result.ok_bind]
            have length : (pre.length : Int) + 1 + s.length + 1 =
                pre.length + (34 :: (s ++ [34])).length := by simp; omega
            rw [length]
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
        have list_loop_values : ∀ (xs : List Json) (k : Nat),
            (∀ y ∈ xs, ∀ depth, y.depth < depth →
              Result.resolve Erlang.program.fun_table depth
                («do_encode/2» y.term (.function 0 2 #[])) = .ok y.iodata) →
            (∀ y ∈ xs, y.depth < k) →
            Result.resolve Erlang.program.fun_table (k + 1)
                («list_loop/2» (Json.terms xs) (.function 0 2 #[])) = .ok (Json.loopIodata xs) := by
          intro xs k encodes bound
          induction xs with
          | nil => simp [Json.terms, Json.loopIodata, «list_loop/2»]
          | cons y ys ih =>
            simp only [Json.terms, «list_loop/2»]
            simp [Result.resolve_bind, encodes y (by simp) k (bound y (by simp)),
              ih (fun z mem => encodes z (by simp [mem])) (fun z mem => bound z (by simp [mem])),
              Json.loopIodata]

        have encode_value : ∀ (v : Json) (depth : Nat), v.depth < depth →
            Result.resolve Erlang.program.fun_table depth
                («do_encode/2» v.term (.function 0 2 #[])) = .ok v.iodata := by
          intro v
          induction v using Json.rec (motive_2 := fun l => ∀ x ∈ l, ∀ depth, x.depth < depth →
              Result.resolve Erlang.program.fun_table depth
                («do_encode/2» x.term (.function 0 2 #[])) = .ok x.iodata) with
          | int x => intro depth _; exact encode_integer x depth
          | bool b =>
            intro depth _
            unfold «do_encode/2»
            cases b <;> simp [Json.term, Json.iodata]
          | null =>
            intro depth _
            unfold «do_encode/2»
            simp [Json.term, Json.iodata]
          | str s ok => intro depth _; exact encode_plain s depth ok
          | arr l ih =>
            intro depth bound
            simp only [Json.depth] at bound
            obtain ⟨k, rfl⟩ : ∃ k, depth = k + 1 := ⟨depth - 1, by omega⟩
            cases l with
            | nil =>
              unfold «do_encode/2»
              simp [Json.term, Json.terms, «do_encode_list/2», Json.iodata,
                Erlang.erlang.«is_list/1»]
            | cons x xs =>
              have elements : ∀ y ∈ x :: xs, y.depth < k := fun y mem => by
                have := depth_le _ y mem
                omega
              unfold «do_encode/2»
              simp [Json.term, Json.terms, Erlang.erlang.«is_list/1», «do_encode_list/2»,
                Erlang.erlang.«is_function/2»]
              rw [ih x (by simp) k (elements x (by simp)), Result.ok_bind, Result.resolve_bind,
                list_loop_values xs k (fun y mem => ih y (by simp [mem]))
                  (fun y mem => elements y (by simp [mem])), Result.ok_bind,
                Result.resolve_of_isPure _ _ _ (by simp)]
              rfl
          | nil y mem => cases mem
          | cons x xs hx hxs y mem depth bound =>
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hx depth bound
            · exact hxs y mem depth bound

        have flatten_loop : ∀ xs : List Json,
            (∀ y ∈ xs, Erlang.erlang.«iolist_to_binary/1» y.iodata =
              .ok (.bitstring ⟨y.text.toArray⟩ 0 (valid_aligned _))) →
            Erlang.erlang.«iolist_to_binary/1» (Json.loopIodata xs) =
              .ok (.bitstring ⟨(Json.tailText xs).toArray⟩ 0 (valid_aligned _)) := by
          intro xs flat
          induction xs with
          | nil =>
            simp only [Json.loopIodata, Json.tailText]
            rw [Erlang.erlang.iolist_to_binary_byte_cons 93 .nil ⟨#[]⟩ (by decide) (by decide)
              Erlang.erlang.iolist_to_binary_nil]
            rfl
          | cons y ys ih =>
            simp only [Json.loopIodata, Json.tailText]
            have inner := Erlang.erlang.iolist_to_binary_join _ _ _ _ (flat y (by simp))
              (ih (fun z mem => flat z (by simp [mem])))
            rw [Erlang.erlang.iolist_to_binary_byte_cons 44 _ _ (by decide) (by decide) inner]
            congr 2

        have flatten : ∀ v : Json, Erlang.erlang.«iolist_to_binary/1» v.iodata =
            .ok (.bitstring ⟨v.text.toArray⟩ 0 (valid_aligned _)) := by
          intro v
          induction v using Json.rec (motive_2 := fun l => ∀ x ∈ l,
              Erlang.erlang.«iolist_to_binary/1» x.iodata =
                .ok (.bitstring ⟨x.text.toArray⟩ 0 (valid_aligned _))) with
          | int x => exact Erlang.erlang.iolist_to_binary_binary ⟨(textOf x).toArray⟩
          | bool b =>
            cases b
            · exact Erlang.erlang.iolist_to_binary_binary ⟨#[102, 97, 108, 115, 101]⟩
            · exact Erlang.erlang.iolist_to_binary_binary ⟨#[116, 114, 117, 101]⟩
          | null => exact Erlang.erlang.iolist_to_binary_binary ⟨#[110, 117, 108, 108]⟩
          | str s _ =>
            simp only [Json.iodata, Json.text, Term.list_cons, Term.list_nil]
            have close := Erlang.erlang.iolist_to_binary_byte_cons 34 .nil ⟨#[]⟩ (by decide)
              (by decide) Erlang.erlang.iolist_to_binary_nil
            have inner := Erlang.erlang.iolist_to_binary_join _ _ _ _
              (Erlang.erlang.iolist_to_binary_binary ⟨s.toArray⟩) close
            rw [Erlang.erlang.iolist_to_binary_byte_cons 34 _ _ (by decide) (by decide) inner]
            congr 2
          | arr l ih =>
            cases l with
            | nil => exact Erlang.erlang.iolist_to_binary_binary ⟨#[91, 93]⟩
            | cons x xs =>
              simp only [Json.iodata, Json.text]
              have inner := Erlang.erlang.iolist_to_binary_join _ _ _ _ (ih x (by simp))
                (flatten_loop xs (fun y mem => ih y (by simp [mem])))
              rw [Erlang.erlang.iolist_to_binary_byte_cons 91 _ _ (by decide) (by decide) inner]
              congr 2
          | nil y mem => cases mem
          | cons x xs hx hxs y mem =>
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hx
            · exact hxs y mem

        have roundtrip_value : ∀ v : Json, (∀ n, v ≠ .int n) → v.depth < 99 →
            Result.resolve Erlang.program.fun_table 100 («roundtrip/1» v.term) = .ok Term.true := by
          intro v number bound
          simp only [«roundtrip/1», «encode/1», «encode/2», Erlang.erlang.«is_function/2»]
          simp
          rw [encode_value v 99 bound, Result.ok_bind]
          simp only [Result.resolve_bind,
            Result.resolve_of_isPure _ _ (Result.ok _) (by simp),
            Result.resolve_of_isPure _ _ (Result.ofExcept _) (by simp),
            Result.ofExcept_ok, Result.ok_bind]
          rw [flatten, Result.ofExcept_ok, Result.ok_bind,
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
                exact ⟨.str data.toList (plain_bytes _ returned), rfl, by simp [Json.depth]; omega⟩
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
