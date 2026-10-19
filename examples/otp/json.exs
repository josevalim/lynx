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

  # The data covered so far: integers, floats, booleans, null, UTF-8 strings, and
  # lists and maps with UTF-8 string keys of them, nested at most 64 deep.
  # The encoder makes one dynamic call per nesting level, and laws run with a
  # call depth of 100.
  def supported?(data), do: supported?(data, 64)

  def supported?(data, _depth)
      when is_integer(data) or is_float(data) or data in [true, false, :null],
      do: true

  def supported?(data, _depth) when is_binary(data), do: utf8?(data)
  def supported?(data, depth) when is_list(data) and depth > 0, do: values?(data, depth - 1)

  def supported?(data, depth) when is_map(data) and depth > 0,
    do: fields?(:maps.to_list(data), depth - 1)

  def supported?(_data, _depth), do: false

  def values?([], _depth), do: true
  def values?([x | xs], depth), do: supported?(x, depth) and values?(xs, depth)
  def values?(_data, _depth), do: false

  def fields?([], _depth), do: true

  def fields?([{key, value} | rest], depth),
    do: is_binary(key) and utf8?(key) and supported?(value, depth) and fields?(rest, depth)

  def fields?(_data, _depth), do: false

  def utf8?(<<_::utf8, rest::binary>>), do: utf8?(rest)
  def utf8?(<<>>), do: true
  def utf8?(_data), do: false

  # The decoder is a state machine of 32 mutually recursive functions over the
  # input, whose definition needs more than Lean's default heartbeats.
  laws "json round trip", options: [maxHeartbeats: 0] do
    # Error reports format positions with functions outside the model.
    cutoff &:json.invalid_byte/2
    cutoff &:json.unexpected_sequence/2
    cutoff &:json.unexpected_utf8/2

    # The requirement recurses into the bindings maps:to_list/1 returns, which are not
    # structurally smaller, so it is a fixed point.
    termination_suffix &JsonProofsTest.supported?/2, ~LEAN"partial_fixpoint"
    termination_suffix &JsonProofsTest.values?/2, ~LEAN"partial_fixpoint"
    termination_suffix &JsonProofsTest.fields?/2, ~LEAN"partial_fixpoint"

    prelude ~LEAN"""
    module

    public import Lynx
    public import Lynx.Modules.Erlang.erlang

    public section

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

    /-- Bytes that strings escape. Other bytes, including those of multibyte UTF-8
    sequences, are copied. -/
    @[expose] def escaped (b : UInt8) : Bool := b.toNat < 32 || b.toNat == 34 || b.toNat == 92

    /-- The text the encoder writes for the bytes of a string. -/
    @[expose] def escapeText (s : List UInt8) : List UInt8 :=
      s.flatMap fun b => if escaped b then escapeBytes b else [b]

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

    /-- A continuation byte of a UTF-8 sequence. -/
    @[expose] def cont (c : UInt8) : Prop := 0x80 ≤ c.toNat ∧ c.toNat ≤ 0xBF

    /-- The well-formed UTF-8 sequences of two, three, and four bytes (Unicode Table 3-7). -/
    @[expose] def lead2 (b c : UInt8) : Prop := 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF ∧ cont c

    @[expose] def lead3 (b c d : UInt8) : Prop :=
      ((b.toNat = 0xE0 ∧ 0xA0 ≤ c.toNat ∧ c.toNat ≤ 0xBF) ∨
        (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC ∧ cont c) ∨
        (b.toNat = 0xED ∧ 0x80 ≤ c.toNat ∧ c.toNat ≤ 0x9F) ∨
        (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF ∧ cont c)) ∧ cont d

    @[expose] def lead4 (b c d e : UInt8) : Prop :=
      ((b.toNat = 0xF0 ∧ 0x90 ≤ c.toNat ∧ c.toNat ≤ 0xBF) ∨
        (0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 ∧ cont c) ∨
        (b.toNat = 0xF4 ∧ 0x80 ≤ c.toNat ∧ c.toNat ≤ 0x8F)) ∧ cont d ∧ cont e

    /-- Well-formed UTF-8. -/
    inductive Utf8 : List UInt8 → Prop
      | nil : Utf8 []
      | one {b rest} : b.toNat < 0x80 → Utf8 rest → Utf8 (b :: rest)
      | two {b c rest} : lead2 b c → Utf8 rest → Utf8 (b :: c :: rest)
      | three {b c d rest} : lead3 b c d → Utf8 rest → Utf8 (b :: c :: d :: rest)
      | four {b c d e rest} : lead4 b c d e → Utf8 rest → Utf8 (b :: c :: d :: e :: rest)

    /-- The keys of objects, as well-formed UTF-8. -/
    abbrev Key := { k : List UInt8 // Utf8 k }

    /-- JSON values made of integers, booleans, null, UTF-8 strings, lists, and objects. -/
    inductive Json where
      | int : Int → Json
      | float : Term.FiniteFloat → Json
      | bool : Bool → Json
      | null : Json
      | str (s : List UInt8) (valid : Utf8 s)
      | arr : List Json → Json
      | obj : List (Key × Json) → Json

    /-- The decimal text `integer_to_binary/1` writes for an integer. -/
    @[expose] def textOf (x : Int) : List UInt8 := (toString x).toUTF8.data.toList

    /-- The text `float_to_binary(Float, [short])` writes for a float. -/
    @[expose] def floatText (f : Term.FiniteFloat) : List UInt8 :=
      match Erlang.erlang.«float_to_binary/2» (.float f) (.cons (.atom "short") .nil) with
      | .ok (.bitstring bytes _ _) => bytes.data.toList
      | _ => []

    /-- The binary of bytes. -/
    abbrev bin (s : List UInt8) : Term := .bitstring ⟨s.toArray⟩ 0 (Term.Bitstring.valid_aligned _)

    mutual
    /-- The Erlang term of a value. -/
    @[expose] def Json.term : Json → Term
      | .int n => .integer n
      | .float f => .float f
      | .bool b => .atom (if b then "true" else "false")
      | .null => .atom "null"
      | .str s _ => bin s
      | .arr l => Json.terms l
      | .obj fields => .map (Json.fieldTerms fields)
    /-- The Erlang list of values. -/
    @[expose] def Json.terms : List Json → Term
      | [] => .nil
      | x :: xs => .cons x.term (Json.terms xs)
    /-- The bindings of an object, in order. -/
    @[expose] def Json.fieldTerms : List (Key × Json) → List (Term × Term)
      | [] => []
      | (k, v) :: fields => (bin k.1, v.term) :: Json.fieldTerms fields
    end

    mutual
    /-- The text the encoder writes for a value. -/
    @[expose] def Json.text : Json → List UInt8
      | .int n => textOf n
      | .float f => floatText f
      | .bool true => [116, 114, 117, 101]
      | .bool false => [102, 97, 108, 115, 101]
      | .null => [110, 117, 108, 108]
      | .str s _ => 34 :: (escapeText s ++ [34])
      | .arr [] => [91, 93]
      | .arr (x :: xs) => 91 :: (x.text ++ Json.tailText xs)
      | .obj [] => [123, 125]
      | .obj ((k, v) :: fields) =>
        123 :: 34 :: (escapeText k.1 ++ 34 :: 58 :: (v.text ++ Json.fieldsText fields))
    /-- The text after a list's first element: a comma before each element, then `]`. -/
    @[expose] def Json.tailText : List Json → List UInt8
      | [] => [93]
      | y :: ys => 44 :: (y.text ++ Json.tailText ys)
    /-- The text after an object's first field: a comma before each field, then `}`. -/
    @[expose] def Json.fieldsText : List (Key × Json) → List UInt8
      | [] => [125]
      | (k, v) :: fields =>
        44 :: 34 :: (escapeText k.1 ++ 34 :: 58 :: (v.text ++ Json.fieldsText fields))
    end

    mutual
    /-- How deeply lists nest in a value. -/
    @[expose] def Json.depth : Json → Nat
      | .int _ | .float _ | .bool _ | .null | .str _ _ => 0
      | .arr l => Json.depths l + 1
      | .obj fields => Json.fieldDepths fields + 1
    /-- The deepest nesting among values. -/
    @[expose] def Json.depths : List Json → Nat
      | [] => 0
      | x :: xs => max x.depth (Json.depths xs)
    /-- The deepest nesting among the values of fields. -/
    @[expose] def Json.fieldDepths : List (Key × Json) → Nat
      | [] => 0
      | (_, v) :: fields => max v.depth (Json.fieldDepths fields)
    end

    mutual
    /-- A term the encoder handles as a value: maps by their visible bindings. -/
    inductive Represents : Term → Json → Prop
      | int (n : Int) : Represents (.integer n) (.int n)
      | float (f : Term.FiniteFloat) : Represents (.float f) (.float f)
      | bool (b : Bool) : Represents (.atom (if b then "true" else "false")) (.bool b)
      | null : Represents (.atom "null") .null
      | str (s : List UInt8) (valid : Utf8 s) : Represents (bin s) (.str s valid)
      | arr {ts : Term} {l : List Json} : RepresentsList ts l → Represents ts (.arr l)
      | obj {entries : List (Term × Term)} {fields : List (Key × Json)} :
          RepresentsFields (Term.mapEntries entries) fields → Represents (.map entries) (.obj fields)
    /-- An Erlang list of values. -/
    inductive RepresentsList : Term → List Json → Prop
      | nil : RepresentsList .nil []
      | cons {t ts : Term} {v : Json} {vs : List Json} : Represents t v → RepresentsList ts vs →
          RepresentsList (.cons t ts) (v :: vs)
    /-- The bindings of a map, as fields in the same order. -/
    inductive RepresentsFields : List (Term × Term) → List (Key × Json) → Prop
      | nil : RepresentsFields [] []
      | cons {t : Term} {es : List (Term × Term)} {k : Key} {v : Json} {fields : List (Key × Json)} :
          Represents t v → RepresentsFields es fields →
            RepresentsFields ((bin k.1, t) :: es) ((k, v) :: fields)
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

    # The automaton both sides of json run to validate multibyte UTF-8 sequences.
    prelude ~LEAN"""
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
    """

    # The encoder writes integers with integer_to_binary/1, floats with
    # float_to_binary/2 and its shortest notation, booleans and null as
    # literals, strings between quotes, lists as their elements between
    # brackets, and maps as their bindings between braces, each key a string
    # followed by a colon, all separated by commas. Strings copy runs of bytes
    # that need no escaping and escape quotes, backslashes, and control
    # characters. Both sides check multibyte UTF-8 sequences with an automaton
    # and copy them. The decoder dispatches on each byte, reads integers back
    # with binary_to_integer/1, the integer decoder in its default options,
    # reads the fraction and exponent of a float and passes its text to
    # binary_to_float/1 inside a try, matches the remaining letters of a
    # literal at once, takes the runs of a
    # string with binary_part/3 and appends each unescaped byte, pushes values
    # onto an array frame and key-value pairs onto an object frame, opening a
    # new frame for each nested list or map, and builds maps with
    # maps:from_list/1. Both sides scan strings seven bytes at a time while a
    # SWAR test finds no byte to escape, and one byte at a time otherwise.
    #
    # Maps may hold shadowed bindings, so the requirement relates data to the
    # model through the visible bindings, and the decoded map equals the data
    # under =:= rather than as the same term.
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

        have tail1 : ∀ bs : List UInt8, matchTail (bin bs) (.atom "all") 1 = true := by
          intro bs
          simp [matchTail, Nat.mod_one]

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

        have escapeText_verbatim : ∀ p : List UInt8, (∀ b ∈ p, escaped b = false) →
            escapeText p = p := by
          intro p all
          induction p with
          | nil => rfl
          | cons b p ih =>
            simp only [escapeText, List.flatMap_cons, all b (by simp)]
            exact congrArg (b :: ·) (ih (fun x mem => all x (by simp [mem])))

        have escapeText_escape : ∀ b : UInt8, escaped b = true → escapeText [b] = escapeBytes b := by
          intro b escape
          simp [escapeText, escape]

        have plain_verbatim : ∀ b : UInt8, plain b = true → escaped b = false := by
          intro b ok
          simp only [plain, escaped] at ok ⊢
          simp at ok ⊢
          omega

        have high_verbatim : ∀ b : UInt8, 128 ≤ b.toNat → escaped b = false := by
          intro b high
          simp [escaped]
          omega

        -- Bytes below 128 that need no escaping are plain.
        have ascii_plain : ∀ b : UInt8, b.toNat < 128 → escaped b = false → plain b = true := by
          intro b ascii verbatim
          simp [plain, escaped] at verbatim ⊢
          omega

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

        -- The automaton's tables are tuples of integers.
        have element_table : ∀ (table : List Nat) (i : Nat), i < table.length →
            Erlang.erlang.«element/2» (.integer ((i : Int) + 1))
                (.tuple ((table.map fun n : Nat => Term.integer n).toArray)) =
              .ok (.integer (table.getD i 0)) := by
          intro table i bound
          have positive : (1 : Int) ≤ i + 1 := by omega
          simp [Erlang.erlang.«element/2», bound, positive]

        have start_lookup : ∀ b : UInt8, 128 ≤ b.toNat →
            Erlang.erlang.«element/2» (.integer (b.toNat - 127)) lynx_literal_lkkqxxpb =
              .ok (.integer (utf8Start b)) := by
          intro b high
          rw [show (b.toNat : Int) - 127 = ((b.toNat - 128 : Nat) : Int) + 1 by omega,
            show lynx_literal_lkkqxxpb =
              .tuple ((utf8Starts.map fun n : Nat => Term.integer n).toArray) from rfl,
            element_table _ _ (by rw [show utf8Starts.length = 128 by decide +kernel]; have := b.toNat_lt; omega)]
          rfl

        have type_lookup : ∀ c : UInt8,
            Erlang.erlang.«element/2» (.integer (c.toNat + 1)) lynx_literal_6xqzwswn =
              .ok (.integer (utf8Types.getD c.toNat 0)) := by
          intro c
          rw [show lynx_literal_6xqzwswn =
              .tuple ((utf8Types.map fun n : Nat => Term.integer n).toArray) by
                set_option maxRecDepth 4000 in rfl,
            element_table _ _ (by rw [show utf8Types.length = 256 by decide +kernel]; exact c.toNat_lt)]

        have next_lookup : ∀ (state : Nat) (c : UInt8), 1 ≤ state → state ≤ 96 →
            Erlang.erlang.«element/2» (.integer (state + utf8Types.getD c.toNat 0))
                lynx_literal_ew33mbbz = .ok (.integer (utf8Next state c)) := by
          intro state c low high
          have bounded := utf8Type_le c
          rw [show ((state : Int) + (utf8Types.getD c.toNat 0 : Nat)) =
              ((state + utf8Types.getD c.toNat 0 - 1 : Nat) : Int) + 1 by omega,
            show lynx_literal_ew33mbbz =
              .tuple ((utf8Steps.map fun n : Nat => Term.integer n).toArray) from rfl,
            element_table _ _ (by rw [show utf8Steps.length = 107 by decide +kernel]; omega)]
          rfl

        -- The encoder validates a multibyte sequence with the automaton and adds it to the run.
        have escape_utf8_start : ∀ (b : UInt8) (bs : List UInt8) (acc orig skip len : Term),
            128 ≤ b.toNat → utf8Start b ≠ 12 →
            «escape_binary/5» (bin (b :: bs)) acc orig skip len =
              «escape_binary_utf8/6» (bin bs) acc orig skip len (.integer (utf8Start b)) := by
          intro b bs acc orig skip len high valid
          have notPlain : plain b = false := by simp [plain]; omega
          have state : ((utf8Start b : Nat) : Int) ≠ 12 := by omega
          conv => lhs; unfold «escape_binary/5»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, isMember_plain, notPlain, isMember_escape]
          simp [show ¬ (b.toNat < 32 ∨ b.toNat = 34 ∨ b.toNat = 92) by omega, start_lookup b high,
            state]

        have escape_utf8_accept : ∀ (c : UInt8) (bs : List UInt8) (acc orig skip : Term) (len : Int)
            (state : Nat), 1 ≤ state → state ≤ 96 → utf8Next state c = 0 →
            «escape_binary_utf8/6» (bin (c :: bs)) acc orig skip (.integer len) (.integer state) =
              «escape_binary_ascii/5» (bin bs) acc orig skip (.integer (len + 2)) := by
          intro c bs acc orig skip len state low high accept
          conv => lhs; unfold «escape_binary_utf8/6»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind,
            type_lookup, next_lookup state c low high, accept]
          simp

        have escape_utf8_more : ∀ (c : UInt8) (bs : List UInt8) (acc orig skip : Term) (len : Int)
            (state : Nat), 1 ≤ state → state ≤ 96 → utf8Next state c ≠ 0 →
            utf8Next state c ≠ 12 →
            «escape_binary_utf8/6» (bin (c :: bs)) acc orig skip (.integer len) (.integer state) =
              «escape_binary_utf8/6» (bin bs) acc orig skip (.integer (len + 1))
                (.integer (utf8Next state c)) := by
          intro c bs acc orig skip len state low high more valid
          conv => lhs; unfold «escape_binary_utf8/6»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind,
            type_lookup, next_lookup state c low high]
          split <;> first | rfl | (rename_i same; simp at same; omega)

        -- The multibyte sequences of well-formed UTF-8.
        let Multibyte : List UInt8 → Prop := fun u =>
          (∃ b c, u = [b, c] ∧ lead2 b c) ∨ (∃ b c d, u = [b, c, d] ∧ lead3 b c d) ∨
            (∃ b c d e, u = [b, c, d, e] ∧ lead4 b c d e)

        -- A well-formed string starts with a byte below 128 or a multibyte sequence, whose
        -- bytes the encoder copies.
        have utf8_cases : ∀ rest : List UInt8, Utf8 rest → rest = [] ∨
            (∃ b rest', rest = b :: rest' ∧ b.toNat < 128 ∧ Utf8 rest') ∨
            (∃ u rest', rest = u ++ rest' ∧ Multibyte u ∧ (∀ b ∈ u, escaped b = false) ∧
              Utf8 rest') := by
          intro rest valid
          cases valid with
          | nil => exact Or.inl rfl
          | @one b rest ascii valid' => exact Or.inr (Or.inl ⟨b, rest, rfl, ascii, valid'⟩)
          | @two b c rest lead valid' =>
            refine Or.inr (Or.inr ⟨[b, c], rest, rfl, Or.inl ⟨b, c, rfl, lead⟩, ?_, valid'⟩)
            intro x mem
            apply high_verbatim
            simp at mem
            unfold lead2 cont at lead
            rcases mem with rfl | rfl <;> omega
          | @three b c d rest lead valid' =>
            refine Or.inr (Or.inr ⟨[b, c, d], rest, rfl, Or.inr (Or.inl ⟨b, c, d, rfl, lead⟩), ?_,
              valid'⟩)
            intro x mem
            apply high_verbatim
            simp at mem
            unfold lead3 cont at lead
            rcases mem with rfl | rfl | rfl <;> omega
          | @four b c d e rest lead valid' =>
            refine Or.inr (Or.inr ⟨[b, c, d, e], rest, rfl,
              Or.inr (Or.inr ⟨b, c, d, e, rfl, lead⟩), ?_, valid'⟩)
            intro x mem
            apply high_verbatim
            simp at mem
            unfold lead4 cont at lead
            rcases mem with rfl | rfl | rfl | rfl <;> omega

        have escape_utf8 : ∀ (u bs : List UInt8) (acc orig skip : Term) (len : Int), Multibyte u →
            «escape_binary/5» (bin (u ++ bs)) acc orig skip (.integer len) =
              «escape_binary_ascii/5» (bin bs) acc orig skip (.integer (len + u.length)) := by
          intro u bs acc orig skip len unit
          rcases unit with ⟨b, c, rfl, lead⟩ | ⟨b, c, d, rfl, lead⟩ | ⟨b, c, d, e, rfl, lead⟩
          · obtain ⟨start, accept⟩ := utf8_two b c lead
            have high : 128 ≤ b.toNat := by have := lead.1; omega
            simp only [List.cons_append, List.nil_append]
            rw [escape_utf8_start _ _ _ _ _ _ high (by omega), start,
              escape_utf8_accept _ _ _ _ _ _ _ (by decide) (by decide) accept]
            rfl
          · obtain ⟨start, invalid, second, accept⟩ := utf8_three b c d lead
            have high : 128 ≤ b.toNat := by
              rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
            simp only [List.cons_append, List.nil_append]
            rw [escape_utf8_start _ _ _ _ _ _ high invalid,
              escape_utf8_more _ _ _ _ _ _ _ (by omega) (utf8Start_le b) (by omega) (by omega),
              second, escape_utf8_accept _ _ _ _ _ _ _ (by decide) (by decide) accept]
            congr 2
            simp
            omega
          · obtain ⟨start, invalid, second, third, accept⟩ := utf8_four b c d e lead
            have high : 128 ≤ b.toNat := by
              rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
            simp only [List.cons_append, List.nil_append]
            rw [escape_utf8_start _ _ _ _ _ _ high invalid,
              escape_utf8_more _ _ _ _ _ _ _ (by omega) (utf8Start_le b) (by omega) (by omega),
              second, escape_utf8_more _ _ _ _ _ _ _ (by decide) (by decide) (by omega) (by omega),
              third, escape_utf8_accept _ _ _ _ _ _ _ (by decide) (by decide) accept]
            congr 2
            simp
            omega

        -- Bytes below 128 are complete UTF-8 sequences on their own.
        have utf8_drop : ∀ p r : List UInt8, (∀ b ∈ p, b.toNat < 128) → Utf8 (p ++ r) → Utf8 r := by
          intro p r ascii valid
          induction p with
          | nil => simpa using valid
          | cons b p ih =>
            have low := ascii b (by simp)
            refine ih (fun x mem => ascii x (by simp [mem])) ?_
            rw [List.cons_append] at valid
            generalize p ++ r = rest at valid ⊢
            cases valid with
            | one _ rest => exact rest
            | two lead _ => have := lead.1; omega
            | three lead _ =>
              rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
            | four lead _ => rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

        -- The encoder has written `done`, holds a run of bytes that it copies since then,
        -- and has `rest` left. Its iodata flattens to the string's text.
        have encode_string : ∀ (n : Nat) (rest done run : List UInt8) (acc : Term),
            rest.length ≤ n → Utf8 rest → (∀ b ∈ run, escaped b = false) →
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
            intro rest done run acc size valid verbatim flat
            -- Continuing in the SWAR loop with a longer run.
            have extend : ∀ u rest', rest = u ++ rest' → 0 < u.length → Utf8 rest' →
                (∀ b ∈ u, escaped b = false) →
                ∃ io, «escape_binary_ascii/5» (bin rest') acc (bin (done ++ (run ++ rest)))
                    (.integer done.length) (.integer (run.length + u.length)) = .ok io ∧
                  Erlang.erlang.«iolist_to_binary/1» io =
                    .ok (bin (34 :: (escapeText (done ++ (run ++ rest)) ++ [34]))) := by
              intro u rest' same nonempty valid' copied
              subst same
              have next := (ih rest'.length (by simp at size; omega) rest' done (run ++ u) acc
                (Nat.le_refl _) valid' (fun x mem => by
                  rcases List.mem_append.mp mem with mem | mem
                  · exact verbatim x mem
                  · exact copied x mem) flat).2
              simp only [List.append_assoc, List.length_append] at next ⊢
              push_cast at next
              exact next
            have main : ∃ io, «escape_binary/5» (bin rest) acc (bin (done ++ (run ++ rest)))
                (.integer done.length) (.integer run.length) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io =
                .ok (bin (34 :: (escapeText (done ++ (run ++ rest)) ++ [34]))) := by
              rcases utf8_cases rest valid with rfl | ⟨b, rest, rfl, ascii, valid'⟩ |
                  ⟨u, rest, rfl, unit, copied, valid'⟩
              · rw [escape_end]
                simp only [List.append_nil] at flat ⊢
                by_cases d0 : done = []
                · subst d0
                  refine ⟨Term.list [.integer 34, bin run, .integer 34], by simp, ?_⟩
                  have joined := flat_quote _ _ (flat_join _ _ _ _ (flat_bin run) flat_close)
                  simpa [Term.list_cons, Term.list_nil, escapeText_verbatim run verbatim] using joined
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
                    escapeText_verbatim run verbatim] using joined
              · have smaller : rest.length < n := by simp at size; omega
                by_cases bPlain : plain b
                · rw [escape_plain_byte _ _ _ _ _ _ bPlain]
                  have next := (ih rest.length smaller rest done (run ++ [b]) acc (Nat.le_refl _)
                    valid' (fun x mem => by
                      rcases List.mem_append.mp mem with mem | mem
                      · exact verbatim x mem
                      · simp at mem; rw [mem]; exact plain_verbatim b bPlain) flat).1
                  simp only [List.append_assoc, List.singleton_append, List.length_append,
                    List.length_singleton] at next
                  push_cast at next
                  exact next
                · have escape : escaped b = true := by
                    cases copied : escaped b
                    · exact absurd (ascii_plain b ascii copied) bPlain
                    · rfl
                  have control : b.toNat < 32 ∨ b.toNat = 34 ∨ b.toNat = 92 := by
                    simp [escaped] at escape
                    omega
                  rw [escape_byte _ _ _ _ _ _ control]
                  by_cases r0 : run = []
                  · subst r0
                    have next := (ih rest.length smaller rest (done ++ [b]) []
                      (.cons acc (bin (escapeBytes b))) (Nat.le_refl _) valid' (by simp)
                      (by
                        rw [escapeText_append, escapeText_escape b escape]
                        exact flat_join _ _ _ _ flat (flat_bin (escapeBytes b)))).2
                    simp only [List.append_assoc, List.singleton_append, List.nil_append,
                      List.length_append, List.length_singleton, List.length_nil] at next ⊢
                    push_cast at next
                    simpa using next
                  · have len : (run.length : Int) ≠ 0 := by simp [r0]
                    have part := binary_part_middle done run (b :: rest)
                    simp only [List.append_assoc] at part
                    have next := (ih rest.length smaller rest (done ++ run ++ [b]) []
                      (.cons acc (.cons (bin run) (bin (escapeBytes b)))) (Nat.le_refl _) valid'
                      (by simp)
                      (by
                        rw [escapeText_append, escapeText_append, escapeText_escape b escape,
                          escapeText_verbatim run verbatim]
                        simpa using flat_join _ _ _ _ flat
                          (flat_join _ _ _ _ (flat_bin run) (flat_bin (escapeBytes b))))).2
                    simp only [List.append_assoc, List.singleton_append, List.nil_append,
                      List.length_append, List.length_singleton, List.length_nil] at next
                    push_cast at next
                    simp only [len, if_false, part, Lynx.Except.ok_bind]
                    simpa [Int.add_assoc] using next
              · rw [escape_utf8 _ _ _ _ _ _ unit]
                exact extend u rest rfl (by
                  rcases unit with ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ <;>
                    simp) valid' copied
            refine ⟨main, ?_⟩
            by_cases short : rest.length < 7
            · rw [escape_ascii_short _ _ _ _ _ short]
              exact main
            have seven : (rest.take 7).length = 7 := by rw [List.length_take]; omega
            rcases escape_ascii_word (rest.take 7) (rest.drop 7) acc (bin (done ++ (run ++ rest)))
                (.integer done.length) run.length seven with ⟨step, word⟩ | fallback
            · rw [List.take_append_drop] at step
              rw [step]
              have ascii : ∀ b ∈ rest.take 7, b.toNat < 128 := fun b mem => by
                have := word b mem
                simp [plain] at this
                omega
              have next := extend (rest.take 7) (rest.drop 7) (List.take_append_drop _ _).symm
                (by omega) (utf8_drop _ _ ascii (by rw [List.take_append_drop]; exact valid))
                (fun b mem => plain_verbatim b (word b mem))
              rw [seven] at next
              exact next
            · rw [List.take_append_drop] at fallback
              rw [fallback]
              exact main

        -- Each section clears the facts that later sections do not use, since tactics slow
        -- down with the size of the local context.
        clear escape_utf8 escape_utf8_more escape_utf8_accept escape_utf8_start element_table
          flat_quote high_verbatim escape_ascii_short escape_ascii_word escape_end escape_byte
          escape_plain_byte bind_of_ok

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
        have unescape_escape : ∀ e : UInt8, escaped e = true →
            ∃ t, escapeBytes e = 92 :: t ∧ ∀ (rest sacc : List UInt8)
              (orig acc stack dec start : Term) (skip len next : Int),
              next = skip + len + (escapeBytes e).length →
              «unescape/9» (bin (t ++ rest)) orig (.integer skip) acc stack dec start (.integer len)
                  (bin sacc) =
                «string_ascii/9» (bin rest) orig (.integer next) acc stack dec start (.integer 0)
                  (bin (sacc ++ [e])) := by
          intro e escape
          have control : e.toNat < 32 ∨ e.toNat = 34 ∨ e.toNat = 92 := by
            simp [escaped] at escape
            omega
          unfold escapeBytes
          split
          all_goals first
            | (rename_i same
               refine ⟨_, rfl, fun rest sacc orig acc stack dec start skip len next after => ?_⟩
               subst after
               rw [List.cons_append, List.nil_append, unescape_char _ e _ _ _ _ _ _ _ _ _ (by
                 simp [unescapeChar]
                 apply UInt8.toNat_inj.mp
                 simp [same])]
               rfl)
            | (refine ⟨_, rfl, fun rest sacc orig acc stack dec start skip len next after => ?_⟩
               subst after
               rw [List.cons_append, unescape_unicode]
               simpa using unescapeu_control e rest sacc orig acc stack dec start skip len (by
                 simp only [imp_false] at *
                 omega))

        have escapeBytes_head : ∀ b : UInt8, ∃ t, escapeBytes b = 92 :: t := by
          intro b
          unfold escapeBytes
          split <;> exact ⟨_, rfl⟩

        -- A plain prefix of a string's text is a prefix of its bytes.
        have plain_text : ∀ (w rest post Y : List UInt8), (∀ b ∈ w, plain b) →
            escapeText rest ++ 34 :: post = w ++ Y →
            ∃ rest2, rest = w ++ rest2 ∧ Y = escapeText rest2 ++ 34 :: post := by
          intro w
          induction w with
          | nil => intro rest post Y _ same; exact ⟨rest, rfl, by simpa using same.symm⟩
          | cons a w ih =>
            intro rest post Y all same
            have aPlain := all a (by simp)
            cases rest with
            | nil =>
              simp [escapeText] at same
              rw [← same.1] at aPlain
              exact absurd aPlain (by decide)
            | cons b rest =>
              by_cases escape : escaped b
              · obtain ⟨t, et⟩ := escapeBytes_head b
                simp [escapeText, escape, et] at same
                rw [← same.1] at aPlain
                exact absurd aPlain (by decide)
              · simp only [escapeText, List.flatMap_cons, escape] at same
                simp only [Bool.false_eq_true, if_false, List.cons_append, List.singleton_append,
                  List.cons.injEq] at same
                obtain ⟨rfl, same⟩ := same
                obtain ⟨rest2, rfl, rfl⟩ := ih rest post Y (fun x mem => all x (by simp [mem]))
                  (by simpa [escapeText] using same)
                exact ⟨rest2, rfl, rfl⟩

        -- The decoder validates a multibyte sequence with the automaton and adds it to the run.
        have string_utf8_start : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack dec len : Term),
            128 ≤ b.toNat → utf8Start b ≠ 12 →
            «string/7» (bin (b :: bs)) orig skip acc stack dec len =
              «string_utf8/8» (bin bs) orig skip acc stack dec len (.integer (utf8Start b)) := by
          intro b bs orig skip acc stack dec len high valid
          have notPlain : plain b = false := by simp [plain]; omega
          have state : ((utf8Start b : Nat) : Int) ≠ 12 := by omega
          conv => lhs; unfold «string/7»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, notPlain, isMember_escape]
          simp [tail1, tail8, show (b.toNat : Int) ≠ 92 by omega,
            show (b.toNat : Int) ≠ 34 by omega,
            show ¬ (b.toNat < 32 ∨ b.toNat = 34 ∨ b.toNat = 92) by omega, start_lookup b high, state]

        have string_utf8_accept : ∀ (c : UInt8) (bs : List UInt8) (orig skip acc stack dec : Term)
            (len : Int) (state : Nat), 1 ≤ state → state ≤ 96 → utf8Next state c = 0 →
            «string_utf8/8» (bin (c :: bs)) orig skip acc stack dec (.integer len) (.integer state) =
              «string_ascii/7» (bin bs) orig skip acc stack dec (.integer (len + 2)) := by
          intro c bs orig skip acc stack dec len state low high accept
          conv => lhs; unfold «string_utf8/8»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
            Result.ok_bind, type_lookup, next_lookup state c low high, accept]
          simp

        have string_utf8_more : ∀ (c : UInt8) (bs : List UInt8) (orig skip acc stack dec : Term)
            (len : Int) (state : Nat), 1 ≤ state → state ≤ 96 → utf8Next state c ≠ 0 →
            utf8Next state c ≠ 12 →
            «string_utf8/8» (bin (c :: bs)) orig skip acc stack dec (.integer len) (.integer state) =
              «string_utf8/8» (bin bs) orig skip acc stack dec (.integer (len + 1))
                (.integer (utf8Next state c)) := by
          intro c bs orig skip acc stack dec len state low high more valid
          conv => lhs; unfold «string_utf8/8»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
            Result.ok_bind, type_lookup, next_lookup state c low high]
          split <;> first | rfl | (rename_i same; simp at same; omega)

        have string9_utf8_start : ∀ (b : UInt8) (bs : List UInt8)
            (orig skip acc stack dec start len sacc : Term), 128 ≤ b.toNat → utf8Start b ≠ 12 →
            «string/9» (bin (b :: bs)) orig skip acc stack dec start len sacc =
              «string_utf8/10» (bin bs) orig skip acc stack dec start len sacc
                (.integer (utf8Start b)) := by
          intro b bs orig skip acc stack dec start len sacc high valid
          have notPlain : plain b = false := by simp [plain]; omega
          have state : ((utf8Start b : Nat) : Int) ≠ 12 := by omega
          conv => lhs; unfold «string/9»
          rw [matchInteger_byte]
          simp only [extract_some, isMember_plain, notPlain, isMember_escape]
          simp [tail1, tail8, show (b.toNat : Int) ≠ 92 by omega,
            show (b.toNat : Int) ≠ 34 by omega,
            show ¬ (b.toNat < 32 ∨ b.toNat = 34 ∨ b.toNat = 92) by omega, start_lookup b high, state]

        have string10_accept : ∀ (c : UInt8) (bs : List UInt8)
            (orig skip acc stack dec start sacc : Term) (len : Int) (state : Nat), 1 ≤ state →
            state ≤ 96 → utf8Next state c = 0 →
            «string_utf8/10» (bin (c :: bs)) orig skip acc stack dec start (.integer len) sacc
                (.integer state) =
              «string_ascii/9» (bin bs) orig skip acc stack dec start (.integer (len + 2)) sacc := by
          intro c bs orig skip acc stack dec start sacc len state low high accept
          conv => lhs; unfold «string_utf8/10»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
            Result.ok_bind, type_lookup, next_lookup state c low high, accept]
          simp

        have string10_more : ∀ (c : UInt8) (bs : List UInt8)
            (orig skip acc stack dec start sacc : Term) (len : Int) (state : Nat), 1 ≤ state →
            state ≤ 96 → utf8Next state c ≠ 0 → utf8Next state c ≠ 12 →
            «string_utf8/10» (bin (c :: bs)) orig skip acc stack dec start (.integer len) sacc
                (.integer state) =
              «string_utf8/10» (bin bs) orig skip acc stack dec start (.integer (len + 1)) sacc
                (.integer (utf8Next state c)) := by
          intro c bs orig skip acc stack dec start sacc len state low high more valid
          conv => lhs; unfold «string_utf8/10»
          rw [matchInteger_byte]
          simp only [extract_some, tail8, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
            Result.ok_bind, type_lookup, next_lookup state c low high]
          split <;> first | rfl | (rename_i same; simp at same; omega)

        have string_utf8 : ∀ (u bs : List UInt8) (orig skip acc stack dec : Term) (len : Int),
            Multibyte u →
            «string/7» (bin (u ++ bs)) orig skip acc stack dec (.integer len) =
              «string_ascii/7» (bin bs) orig skip acc stack dec (.integer (len + u.length)) := by
          intro u bs orig skip acc stack dec len unit
          rcases unit with ⟨b, c, rfl, lead⟩ | ⟨b, c, d, rfl, lead⟩ | ⟨b, c, d, e, rfl, lead⟩
          · obtain ⟨start, accept⟩ := utf8_two b c lead
            have high : 128 ≤ b.toNat := by have := lead.1; omega
            simp only [List.cons_append, List.nil_append]
            rw [string_utf8_start _ _ _ _ _ _ _ _ high (by omega), start,
              string_utf8_accept _ _ _ _ _ _ _ _ _ (by decide) (by decide) accept]
            rfl
          · obtain ⟨start, invalid, second, accept⟩ := utf8_three b c d lead
            have high : 128 ≤ b.toNat := by
              rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
            simp only [List.cons_append, List.nil_append]
            rw [string_utf8_start _ _ _ _ _ _ _ _ high invalid,
              string_utf8_more _ _ _ _ _ _ _ _ _ (by omega) (utf8Start_le b) (by omega) (by omega),
              second, string_utf8_accept _ _ _ _ _ _ _ _ _ (by decide) (by decide) accept]
            congr 2
            simp
            omega
          · obtain ⟨start, invalid, second, third, accept⟩ := utf8_four b c d e lead
            have high : 128 ≤ b.toNat := by
              rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
            simp only [List.cons_append, List.nil_append]
            rw [string_utf8_start _ _ _ _ _ _ _ _ high invalid,
              string_utf8_more _ _ _ _ _ _ _ _ _ (by omega) (utf8Start_le b) (by omega) (by omega),
              second,
              string_utf8_more _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by omega) (by omega),
              third, string_utf8_accept _ _ _ _ _ _ _ _ _ (by decide) (by decide) accept]
            congr 2
            simp
            omega

        have string9_utf8 : ∀ (u bs : List UInt8) (orig skip acc stack dec start sacc : Term)
            (len : Int), Multibyte u →
            «string/9» (bin (u ++ bs)) orig skip acc stack dec start (.integer len) sacc =
              «string_ascii/9» (bin bs) orig skip acc stack dec start (.integer (len + u.length))
                sacc := by
          intro u bs orig skip acc stack dec start sacc len unit
          rcases unit with ⟨b, c, rfl, lead⟩ | ⟨b, c, d, rfl, lead⟩ | ⟨b, c, d, e, rfl, lead⟩
          · obtain ⟨start', accept⟩ := utf8_two b c lead
            have high : 128 ≤ b.toNat := by have := lead.1; omega
            simp only [List.cons_append, List.nil_append]
            rw [string9_utf8_start _ _ _ _ _ _ _ _ _ _ high (by omega), start',
              string10_accept _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) accept]
            rfl
          · obtain ⟨start', invalid, second, accept⟩ := utf8_three b c d lead
            have high : 128 ≤ b.toNat := by
              rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
            simp only [List.cons_append, List.nil_append]
            rw [string9_utf8_start _ _ _ _ _ _ _ _ _ _ high invalid,
              string10_more _ _ _ _ _ _ _ _ _ _ _ (by omega) (utf8Start_le b) (by omega)
                (by omega),
              second, string10_accept _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) accept]
            congr 2
            simp
            omega
          · obtain ⟨start', invalid, second, third, accept⟩ := utf8_four b c d e lead
            have high : 128 ≤ b.toNat := by
              rcases lead.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
            simp only [List.cons_append, List.nil_append]
            rw [string9_utf8_start _ _ _ _ _ _ _ _ _ _ high invalid,
              string10_more _ _ _ _ _ _ _ _ _ _ _ (by omega) (utf8Start_le b) (by omega)
                (by omega),
              second,
              string10_more _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by omega) (by omega),
              third, string10_accept _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) accept]
            congr 2
            simp
            omega

        clear string10_more string10_accept string9_utf8_start string_utf8_more string_utf8_accept
          string_utf8_start escapeBytes_head unescapeu_control hex_lookup unescape_unicode
          unescape_char next_lookup type_lookup start_lookup bxor_ixor band_iband short56 tail1

        -- After an escape, the decoder has decoded `done`, holds a run of copied bytes since
        -- then, and has the text of `rest` left up to the closing quote.
        have decode9 : ∀ (n : Nat) (rest done run pre post : List UInt8) (acc stack start : Term)
            (skip len stop : Int), rest.length ≤ n → Utf8 rest → (∀ b ∈ run, escaped b = false) →
            skip = pre.length + 1 + (escapeText done).length → len = run.length →
            stop = skip + len + (escapeText rest).length + 1 →
            («string/9» (bin (escapeText rest ++ 34 :: post))
                (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                (.integer skip) acc stack options start (.integer len) (bin done) =
              «continue/7» (bin post)
                (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                (.integer stop) acc stack options (bin (done ++ (run ++ rest)))) ∧
            («string_ascii/9» (bin (escapeText rest ++ 34 :: post))
                (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                (.integer skip) acc stack options start (.integer len) (bin done) =
              «continue/7» (bin post)
                (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                (.integer stop) acc stack options (bin (done ++ (run ++ rest)))) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro rest done run pre post acc stack start skip len stop size valid verbatim
              skipped running stopped
            -- After adding copied bytes to the run, the SWAR loop resumes.
            have extend : ∀ u rest', rest = u ++ rest' → 0 < u.length → Utf8 rest' →
                (∀ b ∈ u, escaped b = false) →
                «string_ascii/9» (bin (escapeText rest' ++ 34 :: post))
                    (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                    (.integer skip) acc stack options start (.integer (len + u.length)) (bin done) =
                  «continue/7» (bin post)
                    (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                    (.integer stop) acc stack options (bin (done ++ (run ++ rest))) := by
              intro u rest' same nonempty valid' copied
              subst same
              have next := (ih rest'.length (by simp at size; omega) rest' done (run ++ u) pre post
                acc stack start skip (len + u.length) stop (Nat.le_refl _) valid'
                (fun x mem => by
                  rcases List.mem_append.mp mem with mem | mem
                  · exact verbatim x mem
                  · exact copied x mem)
                skipped (by simp; omega)
                (by simp [escapeText_append, escapeText_verbatim u copied] at stopped; omega)).2
              simp only [escapeText_append, escapeText_verbatim u copied, List.append_assoc] at next ⊢
              exact next
            have main : «string/9» (bin (escapeText rest ++ 34 :: post))
                (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                (.integer skip) acc stack options start (.integer len) (bin done) =
              «continue/7» (bin post)
                (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                (.integer stop) acc stack options (bin (done ++ (run ++ rest))) := by
              rcases utf8_cases rest valid with rfl | ⟨b, rest', rfl, ascii, valid'⟩ |
                  ⟨u, rest', rfl, unit, copied, valid'⟩
              · have part := binary_part_middle (pre ++ 34 :: escapeText done) run (34 :: post)
                simp only [List.append_assoc, List.cons_append, List.length_append,
                  List.length_cons] at part
                simp only [show escapeText [] = [] from rfl, List.nil_append, List.append_nil,
                  List.length_nil] at stopped ⊢
                rw [show skip = ((pre.length + ((escapeText done).length + 1) : Nat) : Int) by
                    push_cast; omega, running, string9_close _ _ _ _ _ _ _ _ _ part]
                congr 2
                push_cast
                omega
              · have smaller : rest'.length < n := by simp at size; omega
                by_cases bPlain : plain b
                · have text : escapeText (b :: rest') = b :: escapeText rest' := by
                    simp [escapeText, plain_verbatim b bPlain]
                  simp only [text, List.cons_append] at stopped ⊢
                  rw [running, string9_plain_byte _ _ _ _ _ _ _ _ _ _ bPlain]
                  have next := (ih rest'.length smaller rest' done (run ++ [b]) pre post acc stack
                    start skip (run.length + 1) stop (Nat.le_refl _) valid'
                    (fun x mem => by
                      rcases List.mem_append.mp mem with mem | mem
                      · exact verbatim x mem
                      · simp at mem; rw [mem]; exact plain_verbatim b bPlain)
                    skipped (by simp) (by simp at stopped; omega)).1
                  simp only [List.append_assoc, List.singleton_append] at next
                  exact next
                · have escape : escaped b = true := by
                    cases copied : escaped b
                    · exact absurd (ascii_plain b ascii copied) bPlain
                    · rfl
                  obtain ⟨t, et, unescaped⟩ := unescape_escape b escape
                  have text : escapeText (b :: rest') = 92 :: (t ++ escapeText rest') := by
                    rw [show b :: rest' = [b] ++ rest' from rfl, escapeText_append,
                      escapeText_escape b escape, et]
                    rfl
                  have part := binary_part_middle (pre ++ 34 :: escapeText done) run
                    (92 :: (t ++ (escapeText rest' ++ 34 :: post)))
                  simp only [List.append_assoc, List.cons_append, List.length_append,
                    List.length_cons] at part
                  simp only [text, List.cons_append, List.append_assoc, List.length_cons,
                    List.length_append] at stopped ⊢
                  rw [show skip = ((pre.length + ((escapeText done).length + 1) : Nat) : Int) by
                      push_cast; omega, running, string9_escape _ _ _ _ _ _ _ _ _ _ part,
                    unescaped _ _ _ _ _ _ _ _ _
                      (pre.length + 1 + (escapeText (done ++ run ++ [b])).length)
                      (by simp [escapeText_append, escapeText_verbatim run verbatim,
                        escapeText_escape b escape]; omega)]
                  have next := (ih rest'.length smaller rest' (done ++ run ++ [b]) [] pre post acc
                    stack start _ 0 stop (Nat.le_refl _) valid' (by simp) rfl rfl
                    (by
                      simp [escapeText_append, escapeText_verbatim run verbatim,
                        escapeText_escape b escape, et]
                      omega)).2
                  simp only [escapeText_append, escapeText_verbatim run verbatim,
                    escapeText_escape b escape, et, List.append_assoc, List.cons_append,
                    List.singleton_append, List.nil_append] at next ⊢
                  exact next
              · have text : escapeText (u ++ rest') = u ++ escapeText rest' := by
                  rw [escapeText_append, escapeText_verbatim u copied]
                rw [text, List.append_assoc, running, string9_utf8 _ _ _ _ _ _ _ _ _ _ unit]
                rw [← running]
                have extended := extend u rest' rfl (by
                  rcases unit with ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ <;>
                    simp) valid' copied
                simp only [text, List.append_assoc] at extended
                exact extended
            refine ⟨main, ?_⟩
            by_cases short : (escapeText rest ++ 34 :: post).length < 7
            · rw [string_ascii9_short _ _ _ _ _ _ _ _ _ short]
              exact main
            have seven : ((escapeText rest ++ 34 :: post).take 7).length = 7 := by
              rw [List.length_take]; omega
            rcases string_ascii9_word ((escapeText rest ++ 34 :: post).take 7)
                ((escapeText rest ++ 34 :: post).drop 7)
                (bin (pre ++ 34 :: (escapeText done ++ (run ++ (escapeText rest ++ 34 :: post)))))
                (.integer skip) acc stack options start (bin done) len seven
              with ⟨step, word⟩ | fallback
            · rw [List.take_append_drop] at step
              rw [step]
              obtain ⟨rest2, same, after⟩ := plain_text _ rest post _ word
                (List.take_append_drop 7 _).symm
              have ascii : ∀ b ∈ (escapeText rest ++ 34 :: post).take 7, b.toNat < 128 :=
                fun b mem => by
                  have := word b mem
                  simp [plain] at this
                  omega
              rw [after]
              have extended := extend _ rest2 same (by omega)
                (utf8_drop _ _ ascii (same ▸ valid)) (fun b mem => plain_verbatim b (word b mem))
              rw [seven] at extended
              exact extended
            · rw [List.take_append_drop] at fallback
              rw [fallback]
              exact main

        -- Before an escape, the decoder holds a run of copied bytes since the opening quote.
        have decode7 : ∀ (n : Nat) (rest run pre post : List UInt8) (acc stack : Term)
            (skip len stop : Int), rest.length ≤ n → Utf8 rest → (∀ b ∈ run, escaped b = false) →
            skip = pre.length + 1 → len = run.length →
            stop = skip + len + (escapeText rest).length + 1 →
            («string/7» (bin (escapeText rest ++ 34 :: post))
                (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                (.integer skip) acc stack options (.integer len) =
              «continue/7» (bin post) (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                (.integer stop) acc stack options (bin (run ++ rest))) ∧
            («string_ascii/7» (bin (escapeText rest ++ 34 :: post))
                (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                (.integer skip) acc stack options (.integer len) =
              «continue/7» (bin post) (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                (.integer stop) acc stack options (bin (run ++ rest))) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro rest run pre post acc stack skip len stop size valid verbatim skipped running
              stopped
            have extend : ∀ u rest', rest = u ++ rest' → 0 < u.length → Utf8 rest' →
                (∀ b ∈ u, escaped b = false) →
                «string_ascii/7» (bin (escapeText rest' ++ 34 :: post))
                    (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                    (.integer skip) acc stack options (.integer (len + u.length)) =
                  «continue/7» (bin post) (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                    (.integer stop) acc stack options (bin (run ++ rest)) := by
              intro u rest' same nonempty valid' copied
              subst same
              have next := (ih rest'.length (by simp at size; omega) rest' (run ++ u) pre post
                acc stack skip (len + u.length) stop (Nat.le_refl _) valid'
                (fun x mem => by
                  rcases List.mem_append.mp mem with mem | mem
                  · exact verbatim x mem
                  · exact copied x mem)
                skipped (by simp; omega)
                (by simp [escapeText_append, escapeText_verbatim u copied] at stopped; omega)).2
              simp only [escapeText_append, escapeText_verbatim u copied, List.append_assoc] at next ⊢
              exact next
            have main : «string/7» (bin (escapeText rest ++ 34 :: post))
                (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                (.integer skip) acc stack options (.integer len) =
              «continue/7» (bin post) (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                (.integer stop) acc stack options (bin (run ++ rest)) := by
              rcases utf8_cases rest valid with rfl | ⟨b, rest', rfl, ascii, valid'⟩ |
                  ⟨u, rest', rfl, unit, copied, valid'⟩
              · have part := binary_part_middle (pre ++ [34]) run (34 :: post)
                simp only [List.append_assoc, List.cons_append, List.singleton_append,
                  List.nil_append, List.length_append, List.length_cons, List.length_nil] at part
                simp only [show escapeText [] = [] from rfl, List.nil_append, List.append_nil,
                  List.length_nil] at stopped ⊢
                rw [show skip = ((pre.length + (0 + 1) : Nat) : Int) by push_cast; omega, running,
                  string_close _ _ _ _ _ _ ]
                simp only [part, Erlang.erlang.«+/2_integers», Result.ofExcept_ok, Result.ok_bind]
                congr 2
                push_cast
                omega
              · have smaller : rest'.length < n := by simp at size; omega
                by_cases bPlain : plain b
                · have text : escapeText (b :: rest') = b :: escapeText rest' := by
                    simp [escapeText, plain_verbatim b bPlain]
                  simp only [text, List.cons_append] at stopped ⊢
                  rw [running, string_plain_byte _ _ _ _ _ _ _ _ bPlain]
                  have next := (ih rest'.length smaller rest' (run ++ [b]) pre post acc stack
                    skip (run.length + 1) stop (Nat.le_refl _) valid'
                    (fun x mem => by
                      rcases List.mem_append.mp mem with mem | mem
                      · exact verbatim x mem
                      · simp at mem; rw [mem]; exact plain_verbatim b bPlain)
                    skipped (by simp) (by simp at stopped; omega)).1
                  simp only [List.append_assoc, List.singleton_append] at next
                  exact next
                · have escape : escaped b = true := by
                    cases copied : escaped b
                    · exact absurd (ascii_plain b ascii copied) bPlain
                    · rfl
                  obtain ⟨t, et, unescaped⟩ := unescape_escape b escape
                  have text : escapeText (b :: rest') = 92 :: (t ++ escapeText rest') := by
                    rw [show b :: rest' = [b] ++ rest' from rfl, escapeText_append,
                      escapeText_escape b escape, et]
                    rfl
                  have part := binary_part_middle (pre ++ [34]) run
                    (92 :: (t ++ (escapeText rest' ++ 34 :: post)))
                  simp only [List.append_assoc, List.cons_append, List.singleton_append,
                    List.nil_append, List.length_append, List.length_cons, List.length_nil] at part
                  simp only [text, List.cons_append, List.append_assoc, List.length_cons,
                    List.length_append] at stopped ⊢
                  rw [show skip = ((pre.length + (0 + 1) : Nat) : Int) by push_cast; omega, running,
                    string_escape _ _ _ _ _ _ _ _ part,
                    unescaped _ _ _ _ _ _ _ _ _ (pre.length + 1 + (escapeText ([] ++ run ++ [b])).length)
                      (by simp [escapeText_append, escapeText_verbatim run verbatim,
                        escapeText_escape b escape]; omega)]
                  have next := (decode9 rest'.length rest' (run ++ [b]) [] pre post acc stack
                    (.integer (((pre.length + (0 + 1) : Nat) : Int) - 1)) _ 0 stop (Nat.le_refl _)
                    valid' (by simp) rfl rfl
                    (by
                      simp [escapeText_append, escapeText_verbatim run verbatim,
                        escapeText_escape b escape, et]
                      omega)).2
                  simp only [escapeText_append, escapeText_verbatim run verbatim,
                    escapeText_escape b escape, et, List.append_assoc, List.cons_append,
                    List.singleton_append, List.nil_append] at next ⊢
                  exact next
              · have text : escapeText (u ++ rest') = u ++ escapeText rest' := by
                  rw [escapeText_append, escapeText_verbatim u copied]
                rw [text, List.append_assoc, running, string_utf8 _ _ _ _ _ _ _ _ unit]
                rw [← running]
                have extended := extend u rest' rfl (by
                  rcases unit with ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ <;>
                    simp) valid' copied
                simp only [text, List.append_assoc] at extended
                exact extended
            refine ⟨main, ?_⟩
            by_cases short : (escapeText rest ++ 34 :: post).length < 7
            · rw [string_ascii_short _ _ _ _ _ _ _ short]
              exact main
            have seven : ((escapeText rest ++ 34 :: post).take 7).length = 7 := by
              rw [List.length_take]; omega
            rcases string_ascii_word ((escapeText rest ++ 34 :: post).take 7)
                ((escapeText rest ++ 34 :: post).drop 7)
                (bin (pre ++ 34 :: (run ++ (escapeText rest ++ 34 :: post))))
                (.integer skip) acc stack options len seven
              with ⟨step, word⟩ | fallback
            · rw [List.take_append_drop] at step
              rw [step]
              obtain ⟨rest2, same, after⟩ := plain_text _ rest post _ word
                (List.take_append_drop 7 _).symm
              have ascii : ∀ b ∈ (escapeText rest ++ 34 :: post).take 7, b.toNat < 128 :=
                fun b mem => by
                  have := word b mem
                  simp [plain] at this
                  omega
              rw [after]
              have extended := extend _ rest2 same (by omega)
                (utf8_drop _ _ ascii (same ▸ valid)) (fun b mem => plain_verbatim b (word b mem))
              rw [seven] at extended
              exact extended
            · rw [List.take_append_drop] at fallback
              rw [fallback]
              exact main

        -- The requirement accepts well-formed UTF-8.
        have utf8_bytes : ∀ (n : Nat) (s : List UInt8), s.length ≤ n →
            «utf8?/1» (bin s) = .ok Term.true → Utf8 s := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            intro s size returned
            unfold «utf8?/1» at returned
            rcases matched : matchUtf8 (bin s) with _ | ⟨value, remaining⟩
            · rw [matched] at returned
              rcases s with _ | ⟨b, s⟩
              · exact Utf8.nil
              · simp [matchEnd_byte] at returned
            · obtain ⟨head, tail, rfl, rfl, rows⟩ := matchUtf8_bytes matched
              rw [matched] at returned
              simp only [extract_some, tail8] at returned
              have smaller : tail.length < n := by
                rcases rows with ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ |
                  ⟨_, _, _, _, rfl, _⟩ <;> simp at size <;> omega
              have valid := ih tail.length smaller tail (Nat.le_refl _) returned
              rcases rows with ⟨b, rfl, low⟩ | ⟨b, c, rfl, lead⟩ | ⟨b, c, d, rfl, lead⟩ |
                ⟨b, c, d, e, rfl, lead⟩
              · exact Utf8.one low valid
              · exact Utf8.two (by unfold lead2 cont; omega) valid
              · exact Utf8.three (by unfold lead3 cont; omega) valid
              · exact Utf8.four (by unfold lead4 cont; omega) valid

        clear decode9 string9_utf8 string_utf8 plain_text unescape_escape string_ascii9_short
          string_ascii9_word string9_close string9_escape string9_plain_byte string_escape
          string_ascii_short string_ascii_word string_close string_plain_byte utf8_drop utf8_cases
          ascii_plain plain_verbatim escapeText_escape escapeText_verbatim escapeText_append tail8

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
        -- letter, a quote, or a brace.
        have array_start_value : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack : Term)
            (len : Int) (start : b.toNat = 45 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨
            b.toNat = 91 ∨ b.toNat = 116 ∨ b.toNat = 102 ∨ b.toNat = 110 ∨ b.toNat = 34 ∨
            b.toNat = 123),
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
            Int) (separator : b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125),
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
          by_cases comma : b.toNat = 44
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
            : Int) (separator : b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125),
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
            b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125) (acc stack : Term) (depth : Nat) (first : UInt8) (rest :
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
            ∨ b.toNat = 93 ∨ b.toNat = 125) (acc stack : Term) (depth : Nat),
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

        -- json decodes floats with binary_to_float/1 inside a try.
        have try_float : ∀ {α : Type} (depth : Nat) (token : Term) (next : Term → Result α)
            (handler : Exception → Result α),
            Result.resolve Erlang.program.fun_table depth
                (Result.tryWith (Term.apply (.function 1 1 #[]) #[token]) next handler) =
              Result.resolve Erlang.program.fun_table depth
                (Result.tryWith (Result.ofExcept (Erlang.erlang.«binary_to_float/1» token)) next
                  handler) :=
          fun depth token next handler =>
            Result.resolve_tryWith_apply_pure Erlang.program.fun_table depth 1 1 #[] #[token] _ next
              handler (by rfl) (by rfl)

        have float_decode_end : ∀ (orig skip acc stack : Term) (len : Int) (token : Term)
            (f : Term.FiniteFloat) (depth : Nat),
            Erlang.erlang.«binary_to_float/1» token = .ok (.float f) →
            Result.resolve Erlang.program.fun_table depth
                («float_decode/8» (bin []) orig skip acc stack options (.integer len) token) =
              Result.ofExcept («unexpected/8» orig skip acc stack options (.integer len)
                (.integer 0) (.tuple #[.atom "number", .float f])) := by
          intro orig skip acc stack len token f depth parsed
          unfold «float_decode/8»
          simp only [matchEnd_byte_nil]
          simp only [show ∀ (g : Term → Result Term) (x : Term), (pure x >>= g) = g x from
            fun _ _ => rfl]
          rw [try_float, parsed]
          simp
        have tail1 : ∀ bs : List UInt8, matchTail (bin bs) (.atom "all") 1 = true := by
          intro bs
          simp [matchTail, Nat.mod_one]

        -- Before a separator, the float decoder continues with the value.
        have float_decode_rest : ∀ (b : UInt8) (post : List UInt8) (orig skip acc stack : Term)
            (len : Int) (token : Term) (f : Term.FiniteFloat) (depth : Nat),
            Erlang.erlang.«binary_to_float/1» token = .ok (.float f) →
            Result.resolve Erlang.program.fun_table depth
                («float_decode/8» (bin (b :: post)) orig skip acc stack options (.integer len) token) =
              Result.resolve Erlang.program.fun_table depth
                (do
                  let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                  «continue/7» (bin (b :: post)) orig next acc stack options (.float f)) := by
          intro b post orig skip acc stack len token f depth parsed
          have whole : matchTail (bin (b :: post)) (.atom "all") 1 = true := by
            simp [matchTail, Nat.mod_one]
          unfold «float_decode/8»
          simp only [matchEnd_byte, whole]
          simp only [show ∀ (g : Term → Result Term) (x : Term), (pure x >>= g) = g x from
            fun _ _ => rfl]
          rw [try_float, parsed]
          simp

        -- A minus sign followed by zero continues as a leading zero.
        have number_minus_zero : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «number_minus/6» (bin ((48 : UInt8) :: bs)) orig skip acc stack dec =
              «number_zero/7» (bin bs) orig skip acc stack dec (.integer 2) := by
          intro orig skip acc stack dec bs
          unfold «number_minus/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one]

        -- A point after the whole part starts the fraction.
        have number_point : ∀ (orig skip acc stack dec : Term) (len : Int) (bs : List UInt8),
            «number/7» (bin ((46 : UInt8) :: bs)) orig skip acc stack dec (.integer len) =
              «number_frac/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len bs
          have below : (compare (46 : Int) 48).isGE = false := by decide
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», below]

        have number_zero_point : ∀ (orig skip acc stack dec : Term) (len : Int) (bs : List UInt8),
            «number_zero/7» (bin ((46 : UInt8) :: bs)) orig skip acc stack dec (.integer len) =
              «number_frac/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len bs
          conv => lhs; unfold «number_zero/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one]

        -- Digits of the fraction and the exponent extend the number by one byte each.
        have digit_guard : ∀ (b : UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            (compare (b.toNat : Int) 48).isGE = true ∧ (compare (b.toNat : Int) 57).isLE = true := by
          intro b low high
          constructor
          · simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
          · simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega

        have frac_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number_frac/7» (bin (b :: bs)) orig skip acc stack dec (.integer len) =
              «number_frac_cont/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          obtain ⟨ge, le⟩ := digit_guard b low high
          conv => lhs; unfold «number_frac/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have frac_cont_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number_frac_cont/7» (bin (b :: bs)) orig skip acc stack dec (.integer len) =
              «number_frac_cont/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          obtain ⟨ge, le⟩ := digit_guard b low high
          conv => lhs; unfold «number_frac_cont/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have exp_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number_exp/7» (bin (b :: bs)) orig skip acc stack dec (.integer len) =
              «number_exp_cont/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          obtain ⟨ge, le⟩ := digit_guard b low high
          conv => lhs; unfold «number_exp/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have exp_sign_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number_exp_sign/7» (bin (b :: bs)) orig skip acc stack dec (.integer len) =
              «number_exp_cont/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          obtain ⟨ge, le⟩ := digit_guard b low high
          conv => lhs; unfold «number_exp_sign/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have exp_cont_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number_exp_cont/7» (bin (b :: bs)) orig skip acc stack dec (.integer len) =
              «number_exp_cont/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          obtain ⟨ge, le⟩ := digit_guard b low high
          conv => lhs; unfold «number_exp_cont/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        -- An `e` after the fraction starts the exponent, which may have a minus sign.
        have frac_cont_exp : ∀ (orig skip acc stack dec : Term) (len : Int) (bs : List UInt8),
            «number_frac_cont/7» (bin ((101 : UInt8) :: bs)) orig skip acc stack dec (.integer len) =
              «number_exp/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len bs
          have ge : (compare (101 : Int) 48).isGE = true := by decide
          have above : (compare (101 : Int) 57).isLE = false := by decide
          conv => lhs; unfold «number_frac_cont/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
            Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», ge, above]

        have exp_minus : ∀ (orig skip acc stack dec : Term) (len : Int) (bs : List UInt8),
            «number_exp/7» (bin ((45 : UInt8) :: bs)) orig skip acc stack dec (.integer len) =
              «number_exp_sign/7» (bin bs) orig skip acc stack dec (.integer (len + 1)) := by
          intro orig skip acc stack dec len bs
          have below : (compare (45 : Int) 48).isGE = false := by decide
          conv => lhs; unfold «number_exp/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
            Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», below]

        -- A number ends at the end of the input or before a separator.
        have frac_cont_done : ∀ (orig skip acc stack : Term) (len : Int) (rest : List UInt8),
            (rest = [] ∨ ∃ b post, rest = b :: post ∧
              (b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125)) →
            «number_frac_cont/7» (bin rest) orig skip acc stack options (.integer len) =
              (do
                let token ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip (.integer len))
                «float_decode/8» (bin rest) orig skip acc stack options (.integer len) token) := by
          intro orig skip acc stack len rest stops
          rcases stops with rfl | ⟨b, post, rfl, separator⟩
          · conv => lhs; unfold «number_frac_cont/7»
            simp only [matchInteger_byte_nil, extract_none]
          · have h69 : (b.toNat : Int) ≠ 69 := by omega
            have h101 : (b.toNat : Int) ≠ 101 := by omega
            conv => lhs; unfold «number_frac_cont/7»
            simp only [matchInteger_byte, extract_some]
            by_cases comma : b.toNat = 44
            · have ge : ¬ (compare (b.toNat : Int) 48).isGE = true := by
                simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
              simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
                Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», ge, h69, h101]
            · have ge : (compare (b.toNat : Int) 48).isGE = true := by
                simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
              have le : ¬ (compare (b.toNat : Int) 57).isLE = true := by
                simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega
              simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
                Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», ge, le, h69, h101]

        have exp_cont_done : ∀ (orig skip acc stack : Term) (len : Int) (rest : List UInt8),
            (rest = [] ∨ ∃ b post, rest = b :: post ∧
              (b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125)) →
            «number_exp_cont/7» (bin rest) orig skip acc stack options (.integer len) =
              (do
                let token ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip (.integer len))
                «float_decode/8» (bin rest) orig skip acc stack options (.integer len) token) := by
          intro orig skip acc stack len rest stops
          rcases stops with rfl | ⟨b, post, rfl, separator⟩
          · conv => lhs; unfold «number_exp_cont/7»
            simp only [matchInteger_byte_nil, extract_none]
          · conv => lhs; unfold «number_exp_cont/7»
            simp only [matchInteger_byte, extract_some]
            by_cases comma : b.toNat = 44
            · have ge : ¬ (compare (b.toNat : Int) 48).isGE = true := by
                simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
              simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge]
            · have ge : (compare (b.toNat : Int) 48).isGE = true := by
                simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
              have le : ¬ (compare (b.toNat : Int) 57).isLE = true := by
                simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega
              simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have frac_cont_digits : ∀ (orig skip acc stack dec : Term) (digits rest : List UInt8),
            (∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) → ∀ len : Int,
            «number_frac_cont/7» (bin (digits ++ rest)) orig skip acc stack dec (.integer len) =
              «number_frac_cont/7» (bin rest) orig skip acc stack dec
                (.integer (len + digits.length)) := by
          intro orig skip acc stack dec digits rest all len
          induction digits generalizing len with
          | nil => simp
          | cons d ds ih =>
            have bound := all d (by simp)
            simp only [List.cons_append]
            rw [frac_cont_digit orig skip acc stack dec len d (ds ++ rest) bound.1 bound.2,
              ih (fun x mem => all x (by simp [mem])) (len + 1)]
            have : len + 1 + (ds.length : Int) = len + ((d :: ds).length : Int) := by simp; omega
            rw [this]

        have exp_cont_digits : ∀ (orig skip acc stack dec : Term) (digits rest : List UInt8),
            (∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) → ∀ len : Int,
            «number_exp_cont/7» (bin (digits ++ rest)) orig skip acc stack dec (.integer len) =
              «number_exp_cont/7» (bin rest) orig skip acc stack dec
                (.integer (len + digits.length)) := by
          intro orig skip acc stack dec digits rest all len
          induction digits generalizing len with
          | nil => simp
          | cons d ds ih =>
            have bound := all d (by simp)
            simp only [List.cons_append]
            rw [exp_cont_digit orig skip acc stack dec len d (ds ++ rest) bound.1 bound.2,
              ih (fun x mem => all x (by simp [mem])) (len + 1)]
            have : len + 1 + (ds.length : Int) = len + ((d :: ds).length : Int) := by simp; omega
            rw [this]

        -- The fraction and the optional exponent end with the float decoder on the token.
        have after_point : ∀ (fraction exponent rest : List UInt8) (orig skip acc stack : Term)
            (len : Int), fraction ≠ [] → (∀ d ∈ fraction, 48 ≤ d.toNat ∧ d.toNat ≤ 57) →
            (exponent = [] ∨ ∃ esign digits, exponent = 101 :: (esign ++ digits) ∧
              (esign = [] ∨ esign = [45]) ∧ digits ≠ [] ∧
              ∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) →
            (rest = [] ∨ ∃ b post, rest = b :: post ∧
              (b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125)) →
            «number_frac/7» (bin (fraction ++ exponent ++ rest)) orig skip acc stack options
                (.integer len) =
              (do
                let token ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip
                  (.integer (len + (fraction ++ exponent).length)))
                «float_decode/8» (bin rest) orig skip acc stack options
                  (.integer (len + (fraction ++ exponent).length)) token) := by
          intro fraction exponent rest orig skip acc stack len fne fd ex stops
          have done : ∀ a b : Int, a = b →
              (do
                let token ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip (.integer a))
                «float_decode/8» (bin rest) orig skip acc stack options (.integer a) token) =
              (do
                let token ← Result.ofExcept (Erlang.erlang.«binary_part/3» orig skip (.integer b))
                «float_decode/8» (bin rest) orig skip acc stack options (.integer b) token) := by
            intro a b h; rw [h]
          obtain ⟨f, fs, rfl⟩ := List.exists_cons_of_ne_nil fne
          have fb := fd f (by simp)
          simp only [List.cons_append, List.append_assoc]
          rw [frac_digit _ _ _ _ _ _ f _ fb.1 fb.2,
            frac_cont_digits _ _ _ _ _ fs _ (fun x mem => fd x (by simp [mem])) (len + 1)]
          rcases ex with rfl | ⟨esign, digits, rfl, sign, dne, dd⟩
          · rw [List.nil_append, frac_cont_done _ _ _ _ _ _ stops]
            exact done _ _ (by simp; omega)
          · obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil dne
            have db := dd d (by simp)
            rw [List.cons_append, frac_cont_exp]
            rcases sign with rfl | rfl
            · simp only [List.nil_append, List.cons_append]
              rw [exp_digit _ _ _ _ _ _ d _ db.1 db.2,
                exp_cont_digits _ _ _ _ _ ds _ (fun x mem => dd x (by simp [mem])),
                exp_cont_done _ _ _ _ _ _ stops]
              exact done _ _ (by simp; omega)
            · simp only [List.singleton_append, List.cons_append, List.nil_append]
              rw [exp_minus, exp_sign_digit _ _ _ _ _ _ d _ db.1 db.2,
                exp_cont_digits _ _ _ _ _ ds _ (fun x mem => dd x (by simp [mem])),
                exp_cont_done _ _ _ _ _ _ stops]
              exact done _ _ (by simp; omega)

        -- An optional minus sign and the whole part lead to the point.
        have before_point : ∀ (sign whole tail : List UInt8) (orig skip acc stack : Term),
            (sign = [] ∨ sign = [45]) → whole ≠ [] →
            (∀ d ∈ whole, 48 ≤ d.toNat ∧ d.toNat ≤ 57) → (∀ r, whole = 48 :: r → r = []) →
            «value/6» (bin (sign ++ whole ++ 46 :: tail)) orig skip acc stack options =
              «number_frac/7» (bin tail) orig skip acc stack options
                (.integer ((sign ++ whole).length + 1)) := by
          intro sign whole tail orig skip acc stack sign_ wne wd leading
          have frac : ∀ a b : Int, a = b →
              «number_frac/7» (bin tail) orig skip acc stack options (.integer a) =
                «number_frac/7» (bin tail) orig skip acc stack options (.integer b) := by
            intro a b h; rw [h]
          obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil wne
          have wb := wd w (by simp)
          have wsd : ∀ d ∈ ws, 48 ≤ d.toNat ∧ d.toNat ≤ 57 := fun d mem => wd d (by simp [mem])
          by_cases zero : w = 48
          · subst zero
            have := leading ws rfl
            subst this
            rcases sign_ with rfl | rfl
            · simp only [List.nil_append, List.cons_append]
              rw [value_zero, number_zero_point]
              exact frac _ _ (by simp)
            · simp only [List.singleton_append, List.cons_append, List.nil_append]
              rw [value_minus, number_minus_zero, number_zero_point]
              exact frac _ _ (by simp)
          · have positive : 49 ≤ w.toNat := by
              have : w.toNat ≠ 48 := fun h => zero (UInt8.toNat_inj.mp (by simpa using h))
              omega
            rcases sign_ with rfl | rfl
            · simp only [List.nil_append, List.cons_append]
              rw [value_digit _ _ _ _ _ w _ positive wb.2, number_digits _ _ _ _ _ ws _ wsd,
                number_point]
              exact frac _ _ (by simp; omega)
            · simp only [List.singleton_append, List.cons_append, List.nil_append]
              rw [value_minus, number_minus_digit _ _ _ _ _ w _ positive wb.2,
                number_digits _ _ _ _ _ ws _ wsd, number_point]
              exact frac _ _ (by simp; omega)

        -- The text of a float, with the shape of float_to_binary/2's output.
        have float_text : ∀ f : Term.FiniteFloat, ∃ sign whole fraction exponent,
            floatText f = sign ++ whole ++ 46 :: (fraction ++ exponent) ∧
            Erlang.erlang.«float_to_binary/2» (.float f) (.cons (.atom "short") .nil) =
              .ok (bin (floatText f)) ∧
            Erlang.erlang.«binary_to_float/1» (bin (floatText f)) = .ok (.float f) ∧
            (sign = [] ∨ sign = [45]) ∧ whole ≠ [] ∧ (∀ d ∈ whole, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
            (∀ r, whole = 48 :: r → r = []) ∧ fraction ≠ [] ∧
            (∀ d ∈ fraction, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
            (exponent = [] ∨ ∃ esign digits, exponent = 101 :: (esign ++ digits) ∧
              (esign = [] ∨ esign = [45]) ∧ digits ≠ [] ∧
              ∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) := by
          intro f
          obtain ⟨sign, whole, fraction, exponent, encoded, s1, s2, s3, s4, s5, s6, s7⟩ :=
            Erlang.erlang.float_to_binary_decimal f
          have text : floatText f = sign ++ whole ++ 46 :: (fraction ++ exponent) := by
            rw [floatText, encoded]
          have parsed := Erlang.erlang.binary_to_float_float_to_binary f
          rw [encoded] at parsed
          simp only [Except.ok_bind] at parsed
          exact ⟨sign, whole, fraction, exponent, text, by rw [text]; exact encoded,
            by rw [text]; exact parsed, s1, s2, s3, s4, s5, s6, s7⟩

        have decode_float : ∀ (f : Term.FiniteFloat) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth («decode/1» (bin (floatText f))) =
              .ok (.float f) := by
          intro f depth
          obtain ⟨sign, whole, fraction, exponent, text, -, parsed, s1, s2, s3, s4, s5, s6, s7⟩ :=
            float_text f
          rw [text] at parsed ⊢
          have before := before_point sign whole (fraction ++ exponent)
            (bin (sign ++ whole ++ 46 :: (fraction ++ exponent))) (.integer 0) (.atom "ok") .nil
            s1 s2 s3 s4
          have after := after_point fraction exponent []
            (bin (sign ++ whole ++ 46 :: (fraction ++ exponent))) (.integer 0) (.atom "ok") .nil
            ((sign ++ whole).length + 1) s5 s6 s7 (Or.inl rfl)
          rw [List.append_nil] at after
          have len : ((sign ++ whole).length + 1 : Int) + ((fraction ++ exponent).length : Int) =
              ((ByteArray.mk (sign ++ whole ++ 46 :: (fraction ++ exponent)).toArray).size : Int) := by
            simp [ByteArray.size]; omega
          unfold «decode/1»
          simp only []
          rw [before, after, len]
          simp only [Erlang.erlang.binary_part_whole, Result.ofExcept_ok, Result.ok_bind,
            Result.resolve_bind]
          rw [float_decode_end _ _ _ _ _ _ f depth parsed, unexpected_whole]
          simp

        have roundtrip_float : ∀ f : Term.FiniteFloat,
            Result.resolve Erlang.program.fun_table 100 («roundtrip/1» (.float f)) =
              .ok Term.true := by
          intro f
          obtain ⟨-, -, -, -, -, encoded, -⟩ := float_text f
          simp only [«roundtrip/1», «encode/1», «encode/2», Erlang.erlang.«is_function/2»]
          simp
          unfold «do_encode/2»
          simp only [Term.list]
          simp [encoded, Result.resolve_bind, Erlang.erlang.iolist_to_binary_binary,
            decode_float f 100, Erlang.erlang.«=:=/2»]

        -- A float embedded in the input, followed by a separator, continues with its value.
        have float_element : ∀ (f : Term.FiniteFloat) (pre post : List UInt8) (b : UInt8)
            (separator : b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125) (acc stack : Term)
            (depth : Nat),
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(floatText f ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ floatText f ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.integer pre.length) acc stack options) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨(b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ floatText f ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.integer (pre.length + (floatText f).length)) acc stack options (.float f)) := by
          intro f pre post b separator acc stack depth
          obtain ⟨sign, whole, fraction, exponent, text, -, parsed, s1, s2, s3, s4, s5, s6, s7⟩ :=
            float_text f
          have part := binary_part_middle pre (floatText f) (b :: post)
          rw [text] at parsed part ⊢
          have before := before_point sign whole (fraction ++ exponent ++ b :: post)
            (bin (pre ++ (sign ++ whole ++ 46 :: (fraction ++ exponent)) ++ b :: post))
            (.integer pre.length) acc stack s1 s2 s3 s4
          have after := after_point fraction exponent (b :: post)
            (bin (pre ++ (sign ++ whole ++ 46 :: (fraction ++ exponent)) ++ b :: post))
            (.integer pre.length) acc stack ((sign ++ whole).length + 1) s5 s6 s7
            (Or.inr ⟨b, post, rfl, separator⟩)
          have len : ((sign ++ whole).length + 1 : Int) + ((fraction ++ exponent).length : Int) =
              ((sign ++ whole ++ 46 :: (fraction ++ exponent)).length : Int) := by
            simp; omega
          rw [len] at after
          rw [show sign ++ whole ++ 46 :: (fraction ++ exponent) ++ b :: post =
            sign ++ whole ++ 46 :: (fraction ++ exponent ++ b :: post) by simp, before, after]
          simp only [Result.resolve_bind, part, Result.ofExcept_ok, Result.ok_bind]
          rw [float_decode_rest _ _ _ _ _ _ _ _ f depth parsed]
          simp [Result.resolve_bind]

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

        have field_depth_le : ∀ (l : List (Key × Json)) (f : Key × Json), f ∈ l →
            f.2.depth ≤ Json.fieldDepths l := by
          intro l f mem
          induction l with
          | nil => cases mem
          | cons g gs ih =>
            obtain ⟨key, v⟩ := g
            simp only [Json.fieldDepths]
            rcases List.mem_cons.mp mem with rfl | mem
            · exact Nat.le_max_left _ _
            · exact Nat.le_trans (ih mem) (Nat.le_max_right _ _)

        have depth_le : ∀ (l : List Json) (x : Json), x ∈ l → x.depth ≤ Json.depths l := by
          intro l x mem
          induction l with
          | nil => cases mem
          | cons y ys ih =>
            simp only [Json.depths]
            rcases List.mem_cons.mp mem with rfl | mem
            · exact Nat.le_max_left _ _
            · exact Nat.le_trans (ih mem) (Nat.le_max_right _ _)

        clear reverse2 decode_element number_zero_stop number_stop decode_integer unexpected_whole
          number_zero_end number_end number_digits number_digit number_minus_digit value_zero
          value_minus value_digit binary_part_middle try_float float_decode_end float_decode_rest
          number_minus_zero number_point number_zero_point digit_guard frac_digit frac_cont_digit
          exp_digit exp_sign_digit exp_cont_digit frac_cont_exp exp_minus frac_cont_done
          exp_cont_done frac_cont_digits exp_cont_digits after_point before_point decode_float

        -- An opening brace starts an object.
        have value_brace : ∀ (bs : List UInt8) (orig skip acc stack : Term),
            «value/6» (bin (123 :: bs)) orig skip acc stack options =
              «object_start/7» (bin bs) orig skip acc stack options (.integer 1) := by
          intro bs orig skip acc stack
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have object_start_close : ∀ (bs : List UInt8) (orig skip acc stack : Term) (len : Int),
            «object_start/7» (bin (125 :: bs)) orig skip acc stack options (.integer len) =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                let after ← Result.ofExcept (Erlang.erlang.«+/2» next (.integer 1))
                «continue/7» (bin bs) orig after acc stack options (.map [])) := by
          intro bs orig skip acc stack len
          conv => lhs; unfold «object_start/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- An object frame decodes its first key with the outer accumulator saved.
        have object_start_quote : ∀ (bs : List UInt8) (orig skip acc stack : Term) (len : Int),
            «object_start/7» (bin (34 :: bs)) orig skip acc stack options (.integer len) =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer len))
                let after ← Result.ofExcept (Erlang.erlang.«+/2» next (.integer 1))
                «string_ascii/7» (bin bs) orig after .nil (.cons (.atom "object") (.cons acc stack))
                  options (.integer 0)) := by
          intro bs orig skip acc stack len
          conv => lhs; unfold «object_start/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- A decoded key waits for its colon, and a decoded value is pushed with its key.
        have continue_object : ∀ (bs : List UInt8) (orig skip acc rest value : Term),
            «continue/7» (bin bs) orig skip acc (.cons (.atom "object") rest) options value =
              «object_value/7» (bin bs) orig skip acc (.cons (.atom "object") rest) options
                value := by
          intro bs orig skip acc rest value
          conv => lhs; unfold «continue/7»
          simp [matchTail, Nat.mod_one]

        have object_value_colon : ∀ (bs : List UInt8) (orig skip acc stack key : Term),
            «object_value/7» (bin (58 :: bs)) orig skip acc stack options key =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 1))
                «value/6» (bin bs) orig next acc (.cons key stack) options) := by
          intro bs orig skip acc stack key
          conv => lhs; unfold «object_value/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have continue_key : ∀ (bs key : List UInt8) (orig skip acc rest value : Term),
            «continue/7» (bin bs) orig skip acc (.cons (bin key) rest) options value =
              «object_push/8» (bin bs) orig skip acc rest options value (bin key) := by
          intro bs key orig skip acc rest value
          conv => lhs; unfold «continue/7»
          simp [matchTail, Nat.mod_one]

        have object_push_comma : ∀ (bs : List UInt8) (orig skip acc stack value key : Term),
            «object_push/8» (bin (44 :: bs)) orig skip acc stack options value key =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 1))
                «object_key/6» (bin bs) orig next (.cons (.tuple #[key, value]) acc) stack
                  options) := by
          intro bs orig skip acc stack value key
          conv => lhs; unfold «object_push/8»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- The closing brace builds the map from the pushed pairs and restores the outer frame.
        have object_push_close : ∀ (bs : List UInt8) (orig skip acc frame old stack value key : Term),
            «object_push/8» (bin (125 :: bs)) orig skip acc (.cons frame (.cons old stack)) options
                value key =
              (do
                let map ← Result.ofExcept
                  (Erlang.maps.«from_list/1» (.cons (.tuple #[key, value]) acc))
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 1))
                «continue/7» (bin bs) orig next old stack options map) := by
          intro bs orig skip acc frame old stack value key
          conv => lhs; unfold «object_push/8»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have object_key_quote : ∀ (bs : List UInt8) (orig skip acc stack : Term),
            «object_key/6» (bin (34 :: bs)) orig skip acc stack options =
              (do
                let next ← Result.ofExcept (Erlang.erlang.«+/2» skip (.integer 1))
                «string_ascii/7» (bin bs) orig next acc stack options (.integer 0)) := by
          intro bs orig skip acc stack
          conv => lhs; unfold «object_key/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have from_list_pairs : ∀ pairs : List (Term × Term),
            Erlang.maps.«from_list/1» (Term.list (pairs.map fun p => .tuple #[p.1, p.2])) =
              .ok (.map pairs.reverse) := by
          intro pairs
          have collected : Term.pairList? (Term.list (pairs.map fun p => .tuple #[p.1, p.2])) =
              some pairs := by
            induction pairs with
            | nil => rfl
            | cons p ps ih =>
              rw [List.map_cons, Term.list_cons,
                show Term.pairList? (.cons (.tuple #[p.1, p.2])
                    (Term.list (ps.map fun p => .tuple #[p.1, p.2]))) =
                  (Term.pairList? (Term.list (ps.map fun p => .tuple #[p.1, p.2]))).map
                    ((p.1, p.2) :: ·) from rfl, ih]
              rfl
          simp [Erlang.maps.«from_list/1», collected]

        -- Values start with a minus sign, a digit, an opening bracket, a letter, a quote, or
        -- an opening brace.
        have first_byte : ∀ v : Json, ∃ b bs, v.text = b :: bs ∧
            (b.toNat = 45 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ b.toNat = 91 ∨ b.toNat = 116 ∨
              b.toNat = 102 ∨ b.toNat = 110 ∨ b.toNat = 34 ∨ b.toNat = 123) := by
          intro v
          cases v with
          | int x =>
            obtain ⟨first, rest, text, -, digits, -⟩ := textOf_decimal x
            by_cases negative : x < 0
            · exact ⟨45, first :: rest, by simp [Json.text, text, negative], Or.inl rfl⟩
            · exact ⟨first, rest, by simp [Json.text, text, negative],
                Or.inr (Or.inl (digits first (by simp)))⟩
          | float f =>
            obtain ⟨sign, whole, fraction, exponent, text, -, -, s1, s2, s3, -⟩ := float_text f
            obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil s2
            rcases s1 with rfl | rfl
            · exact ⟨w, ws ++ 46 :: (fraction ++ exponent), by simp [Json.text, text],
                Or.inr (Or.inl (s3 w (by simp)))⟩
            · exact ⟨45, w :: (ws ++ 46 :: (fraction ++ exponent)), by simp [Json.text, text],
                Or.inl rfl⟩
          | bool b => cases b <;> exact ⟨_, _, rfl, by decide⟩
          | null => exact ⟨_, _, rfl, by decide⟩
          | str s _ => exact ⟨34, _, rfl, by decide⟩
          | arr l => cases l <;> exact ⟨91, _, rfl, by decide⟩
          | obj fields => rcases fields with _ | ⟨⟨k, v⟩, fields⟩ <;> exact ⟨123, _, rfl, by decide⟩

        -- The elements after the first start with a comma or the closing bracket.
        have tail_start : ∀ xs : List Json, ∃ b post, Json.tailText xs = b :: post ∧
            (b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125) := by
          intro xs
          cases xs
          · exact ⟨93, [], rfl, Or.inr (Or.inl rfl)⟩
          · exact ⟨44, _, rfl, Or.inl rfl⟩

        -- Decoding a value's text continues with its term after the text. Numbers
        -- need a separator after them, while other values end with their text.
        let Decodes : Json → Prop := fun v => ∀ (pre rest : List UInt8) (acc stack : Term)
            (depth : Nat),
            ((∃ b post, rest = b :: post ∧ (b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125)) ∨
              (∀ n, v ≠ .int n) ∧ ∀ f, v ≠ .float f) →
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(v.text ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ v.text ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.integer pre.length) acc stack options) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨rest.toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ v.text ++ rest).toArray⟩ 0 (valid_aligned _))
                  (.integer (pre.length + v.text.length)) acc stack options v.term)

        -- The fields after the first start with a comma or the closing brace.
        have fields_start : ∀ fs : List (Key × Json), ∃ b post, Json.fieldsText fs = b :: post ∧
            (b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125) := by
          intro fs
          rcases fs with _ | ⟨⟨k, v⟩, fs⟩
          · exact ⟨125, [], rfl, Or.inr (Or.inr rfl)⟩
          · exact ⟨44, _, rfl, Or.inl rfl⟩

        -- A field decodes its key, a colon, and its value, then pushes the pair.
        have field_step : ∀ (k : Key) (v : Json), Decodes v → ∀ (fs : List (Key × Json))
            (pre rest : List UInt8) (acc frame : Term) (skip : Int) (depth : Nat),
            skip = pre.length + 1 →
            Result.resolve Erlang.program.fun_table depth
                («string_ascii/7» (bin (escapeText k.1 ++ 34 :: 58 ::
                    (v.text ++ (Json.fieldsText fs ++ rest))))
                  (bin (pre ++ 34 :: (escapeText k.1 ++ 34 :: 58 ::
                    (v.text ++ (Json.fieldsText fs ++ rest)))))
                  (.integer skip) acc (.cons (.atom "object") frame) options (.integer 0)) =
              Result.resolve Erlang.program.fun_table depth
                («object_push/8» (bin (Json.fieldsText fs ++ rest))
                  (bin (pre ++ 34 :: (escapeText k.1 ++ 34 :: 58 ::
                    (v.text ++ (Json.fieldsText fs ++ rest)))))
                  (.integer (pre.length + (escapeText k.1).length + 3 + v.text.length)) acc
                  (.cons (.atom "object") frame) options v.term (bin k.1)) := by
          intro k v decodes fs pre rest acc frame skip depth skipped
          have key := (decode7 k.1.length k.1 [] pre (58 :: (v.text ++ (Json.fieldsText fs ++ rest)))
            acc (.cons (.atom "object") frame) skip 0 (skip + (escapeText k.1).length + 1)
            (Nat.le_refl _) k.2 (by simp) skipped (by simp) (by simp)).2
          simp only [List.nil_append] at key
          rw [key, continue_object, object_value_colon]
          simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
            Result.ok_bind]
          obtain ⟨b, post, start, separator⟩ := fields_start fs
          have value := decodes (pre ++ 34 :: (escapeText k.1 ++ [34, 58]))
            (Json.fieldsText fs ++ rest) acc (.cons (bin k.1) (.cons (.atom "object") frame)) depth
            (Or.inl ⟨b, post ++ rest, by simp [start], separator⟩)
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
            List.length_cons, List.length_nil] at value
          push_cast at value
          rw [show skip + (escapeText k.1).length + 1 + 1 =
            (pre.length : Int) + ((escapeText k.1).length + 1 + 1 + 1) by omega, value,
            continue_key]
          congr 2

        -- An object frame pushes each field and closes with the map of its pairs.
        have object_loop : ∀ fs : List (Key × Json), (∀ f ∈ fs, Decodes f.2) →
            ∀ (done : List (Term × Term)) (key value : Term) (pre rest : List UInt8)
              (old stack : Term) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth
                («object_push/8» (bin (Json.fieldsText fs ++ rest))
                  (bin (pre ++ (Json.fieldsText fs ++ rest))) (.integer pre.length)
                  (Term.list ((done.map fun p => .tuple #[p.1, p.2]).reverse))
                  (.cons (.atom "object") (.cons old stack)) options value key) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (bin rest) (bin (pre ++ (Json.fieldsText fs ++ rest)))
                  (.integer (pre.length + (Json.fieldsText fs).length)) old stack options
                  (.map (done ++ (key, value) :: Json.fieldTerms fs))) := by
          intro fs
          induction fs with
          | nil =>
            intro _ done key value pre rest old stack depth
            rw [show Json.fieldsText [] = [125] from rfl]
            simp only [List.cons_append, List.nil_append]
            rw [object_push_close]
            have collected := from_list_pairs ((done ++ [(key, value)]).reverse)
            simp only [List.map_reverse, List.reverse_reverse, List.map_append, List.map_cons,
              List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
              List.nil_append, List.singleton_append, Term.list_cons] at collected
            simp [Result.resolve_bind, collected, Json.fieldTerms]
          | cons f fs ih =>
            intro all done key value pre rest old stack depth
            obtain ⟨k, v⟩ := f
            rw [show Json.fieldsText ((k, v) :: fs) =
              44 :: 34 :: (escapeText k.1 ++ 34 :: 58 :: (v.text ++ Json.fieldsText fs)) from rfl]
            simp only [List.cons_append, List.append_assoc]
            rw [object_push_comma]
            simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
              Result.ok_bind]
            rw [object_key_quote]
            simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
              Result.ok_bind]
            have step := field_step k v (all (k, v) (by simp)) fs (pre ++ [44]) rest
              (.cons (.tuple #[key, value]) (Term.list ((done.map fun p => .tuple #[p.1, p.2]).reverse)))
              (.cons old stack) _ depth rfl
            simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
              List.length_append, List.length_singleton] at step
            push_cast at step
            rw [step]
            have next := ih (fun g mem => all g (by simp [mem])) (done ++ [(key, value)]) (bin k.1)
              v.term (pre ++ 44 :: 34 :: (escapeText k.1 ++ 34 :: 58 :: v.text)) rest old stack
              depth
            simp only [List.append_assoc, List.cons_append, List.length_append,
              List.length_cons] at next
            push_cast at next
            rw [show (pre.length : Int) + 1 + (escapeText k.1).length + 3 + v.text.length =
                pre.length + ((escapeText k.1).length + (v.text.length + 1 + 1) + 1 + 1) by omega,
              show Term.cons (.tuple #[key, value])
                  (Term.list ((done.map fun p => .tuple #[p.1, p.2]).reverse)) =
                Term.list (((done ++ [(key, value)]).map fun p => .tuple #[p.1, p.2]).reverse) by
                rw [List.map_append, List.reverse_append]; rfl,
              next]
            simp only [Json.fieldTerms, List.append_assoc, List.singleton_append, List.length_cons,
              List.length_append]
            congr 3
            omega

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
          refine Json.rec (motive_1 := fun v => Decodes v) (motive_2 := fun l => ∀ x ∈ l, Decodes x)
            (motive_3 := fun fields => ∀ f ∈ fields, Decodes f.2) (motive_4 := fun f => Decodes f.2)
            ?decodesInt ?decodesFloat ?decodesBool ?decodesNull ?decodesStr ?decodesArr ?decodesObj ?decodesNil ?decodesCons ?decodesFieldsNil ?decodesFieldsCons ?decodesField v
          case decodesInt =>
            intro x
            intro pre rest acc stack depth separated
            rcases separated with ⟨b, post, rfl, separator⟩ | number
            · exact element x pre post b separator acc stack depth
            · exact absurd rfl (number.1 x)
          case decodesFloat =>
            intro f
            intro pre rest acc stack depth separated
            rcases separated with ⟨b, post, rfl, separator⟩ | number
            · exact float_element f pre post b separator acc stack depth
            · exact absurd rfl (number.2 f)
          case decodesBool =>
            intro b
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
          case decodesNull =>
            intro pre rest acc stack depth _
            rw [show Json.text .null = [110, 117, 108, 108] from rfl]
            simp only [List.cons_append, List.nil_append]
            rw [value_null, show (117 :: 108 :: 108 :: rest : List UInt8) =
              [117, 108, 108] ++ rest from rfl, null_rest]
            simp [Result.resolve_bind, Json.term, Int.add_assoc]
          case decodesStr =>
            intro s valid
            intro pre rest acc stack depth _
            rw [show Json.text (.str s valid) = 34 :: (escapeText s ++ [34]) from rfl]
            simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
            rw [value_quote]
            simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
              Result.ok_bind]
            have decoded := (decode7 s.length s [] pre rest acc stack (pre.length + 1) 0
              (pre.length + (34 :: (escapeText s ++ [34])).length) (Nat.le_refl _) valid (by simp)
              rfl (by simp) (by simp; omega)).2
            simp only [List.nil_append] at decoded
            rw [decoded]
            rfl
          case decodesArr =>
            intro l ih
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
          case decodesObj =>
            intro fields ih pre rest acc stack depth _
            rcases fields with _ | ⟨⟨k, v⟩, fs⟩
            · rw [show Json.text (.obj []) = [123, 125] from rfl]
              simp only [List.cons_append, List.nil_append]
              rw [value_brace, object_start_close]
              simp [Result.resolve_bind, Json.term, Json.fieldTerms, Int.add_assoc]
            · rw [show Json.text (.obj ((k, v) :: fs)) =
                123 :: 34 :: (escapeText k.1 ++ 34 :: 58 :: (v.text ++ Json.fieldsText fs)) from rfl]
              simp only [List.cons_append, List.append_assoc]
              rw [value_brace, object_start_quote]
              simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ofExcept_ok,
                Result.ok_bind]
              have step := field_step k v (ih (k, v) (by simp)) fs (pre ++ [123]) rest .nil
                (.cons acc stack) _ depth rfl
              simp only [List.append_assoc, List.singleton_append, List.cons_append,
                List.nil_append, List.length_append, List.length_singleton] at step
              push_cast at step
              rw [show (pre.length : Int) + 1 + 1 = pre.length + 1 + 1 by omega, step]
              have next := object_loop fs (fun g mem => ih g (by simp [mem])) [] (bin k.1) v.term
                (pre ++ 123 :: 34 :: (escapeText k.1 ++ 34 :: 58 :: v.text)) rest acc stack depth
              simp only [List.map_nil, List.reverse_nil, List.nil_append, List.append_assoc,
                List.cons_append, List.length_append, List.length_cons] at next
              push_cast at next
              rw [show (pre.length : Int) + 1 + (escapeText k.1).length + 3 + v.text.length =
                pre.length + ((escapeText k.1).length + (v.text.length + 1 + 1) + 1 + 1) by omega]
              rw [show (Term.list [] : Term) = .nil from rfl] at next
              rw [next]
              simp only [Json.term, Json.fieldTerms, List.length_cons, List.length_append]
              congr 3
              omega
          case decodesNil => intro y mem; cases mem
          case decodesCons =>
            intro x xs hx hxs y mem
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hx
            · exact hxs y mem
          case decodesFieldsNil => intro f mem; cases mem
          case decodesFieldsCons =>
            intro f fs hf hfs g mem
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hf
            · exact hfs g mem
          case decodesField => intro k v hv; exact hv

        have decode_value : ∀ (v : Json) (depth : Nat), (∀ n, v ≠ .int n) ∧ (∀ f, v ≠ .float f) →
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

        clear loop object_loop field_step fields_start tail_start first_byte from_list_pairs
          object_key_quote object_push_close object_push_comma continue_key object_value_colon
          continue_object object_start_quote object_start_close value_brace terms_list reverse1
          null_rest false_rest true_rest value_null value_false value_true element textOf_decimal
          float_element
          array_start_close array_start_value value_open array_push_close array_push_comma
          terminate_end continue_top continue_array decode7 value_quote

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
        let Encodes : Json → Prop := fun v => ∀ (t : Term) (depth : Nat), Represents t v →
            v.depth < depth → ∃ io, Result.resolve Erlang.program.fun_table depth
                («do_encode/2» t (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin v.text)

        have list_loop_values : ∀ (xs : List Json) (ts : Term) (k : Nat), RepresentsList ts xs →
            (∀ y ∈ xs, Encodes y) → (∀ y ∈ xs, y.depth < k) →
            ∃ io, Result.resolve Erlang.program.fun_table (k + 1)
                («list_loop/2» ts (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin (Json.tailText xs)) := by
          intro xs
          induction xs with
          | nil =>
            intro ts k represents _ _
            cases represents
            exact ⟨.cons (.integer 93) .nil, by simp [«list_loop/2»],
              flat_byte 93 _ _ Erlang.erlang.iolist_to_binary_nil⟩
          | cons y ys ih =>
            intro ts k represents encodes bound
            cases represents with
            | cons head tail =>
              obtain ⟨yio, yres, yflat⟩ := encodes y (by simp) _ k head (bound y (by simp))
              obtain ⟨lio, lres, lflat⟩ := ih _ k tail (fun z mem => encodes z (by simp [mem]))
                (fun z mem => bound z (by simp [mem]))
              refine ⟨.cons (.integer 44) (.cons yio lio), ?_, flat_byte 44 _ _
                (flat_join _ _ _ _ yflat lflat)⟩
              simp only [«list_loop/2»]
              simp [Result.resolve_bind, yres, lres]

        have encode_str : ∀ (s : List UInt8) (valid : Utf8 s) (depth : Nat), ∃ io,
            Result.resolve Erlang.program.fun_table depth
                («do_encode/2» (bin s) (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin (34 :: (escapeText s ++ [34]))) := by
          intro s valid depth
          obtain ⟨io, encoded, flat⟩ := (encode_string s.length s [] [] (Term.list [.integer 34])
            (Nat.le_refl _) valid (by simp) flat_close).2
          simp only [List.nil_append, List.length_nil] at encoded flat
          refine ⟨io, ?_, flat⟩
          unfold «do_encode/2»
          simp
          exact encoded

        -- The map generator yields each binding as a tuple with the rest of the iterator.
        have fields_loop : ∀ (fs : List (Key × Json)) (es : List (Term × Term)) (k : Nat),
            RepresentsFields es fs → (∀ f ∈ fs, Encodes f.2) → (∀ f ∈ fs, f.2.depth < k) →
            ∃ io text, Result.resolve Erlang.program.fun_table (k + 1)
                («lynx_local_10/2» (es.foldr (fun e rest => .tuple #[e.1, e.2, rest]) (.atom "none"))
                  (.function 0 2 #[])) = .ok io ∧
              Erlang.erlang.«iolist_to_binary/1» io = .ok (bin text) ∧
              text ++ [125] = Json.fieldsText fs := by
          intro fs
          induction fs with
          | nil =>
            intro es k represents _ _
            cases represents
            exact ⟨.nil, [], by simp [«lynx_local_10/2»], Erlang.erlang.iolist_to_binary_nil,
              by simp [Json.fieldsText]⟩
          | cons f fs ih =>
            intro es k represents encodes bound
            obtain ⟨key, v⟩ := f
            cases represents with
            | cons head tail =>
              obtain ⟨kio, kres, kflat⟩ := encode_str key.1 key.2 k
              obtain ⟨vio, vres, vflat⟩ := encodes (key, v) (by simp) _ k head
                (bound (key, v) (by simp))
              obtain ⟨lio, text, lres, lflat, closed⟩ := ih _ k tail
                (fun g mem => encodes g (by simp [mem])) (fun g mem => bound g (by simp [mem]))
              refine ⟨.cons (.cons (.integer 44) (.cons kio (.cons (.integer 58) vio))) lio,
                44 :: ((34 :: (escapeText key.1 ++ [34])) ++ 58 :: v.text) ++ text, ?_, ?_, ?_⟩
              · simp only [List.foldr_cons, «lynx_local_10/2», «key/2»]
                simp [Result.resolve_bind, kres, vres, lres]
              · exact flat_join _ _ _ _ (flat_byte 44 _ _ (flat_join _ _ _ _ kflat
                  (flat_byte 58 _ _ vflat))) lflat |>.trans (by simp)
              · simp [Json.fieldsText, ← closed]

        have encode_value : ∀ v : Json, Encodes v := by
          intro v
          refine Json.rec (motive_1 := fun v => Encodes v) (motive_2 := fun l => ∀ x ∈ l, Encodes x)
            (motive_3 := fun fields => ∀ f ∈ fields, Encodes f.2) (motive_4 := fun f => Encodes f.2)
            ?encodesInt ?encodesFloat ?encodesBool ?encodesNull ?encodesStr ?encodesArr ?encodesObj ?encodesNil ?encodesCons ?encodesFieldsNil ?encodesFieldsCons ?encodesField v
          case encodesInt =>
            intro x
            intro t depth represents _
            cases represents
            exact ⟨_, encode_integer x depth, flat_bin _⟩
          case encodesFloat =>
            intro f
            intro t depth represents _
            cases represents
            obtain ⟨-, -, -, -, -, encoded, -⟩ := float_text f
            refine ⟨_, ?_, flat_bin _⟩
            unfold «do_encode/2»
            simp only [Term.list]
            rw [encoded, Result.resolve_of_isPure _ _ _ (by simp), Result.ofExcept_ok]
            rfl
          case encodesBool =>
            intro b
            intro t depth represents _
            cases represents
            cases b
            · exact ⟨bin [102, 97, 108, 115, 101], by unfold «do_encode/2»; simp, flat_bin _⟩
            · exact ⟨bin [116, 114, 117, 101], by unfold «do_encode/2»; simp, flat_bin _⟩
          case encodesNull =>
            intro t depth represents _
            cases represents
            exact ⟨bin [110, 117, 108, 108], by unfold «do_encode/2»; simp, flat_bin _⟩
          case encodesStr =>
            intro s valid
            intro t depth represents _
            cases represents
            exact encode_str s valid depth
          case encodesArr =>
            intro l ih
            intro t depth represents bound
            simp only [Json.depth] at bound
            obtain ⟨k, rfl⟩ : ∃ k, depth = k + 1 := ⟨depth - 1, by omega⟩
            cases represents with
            | arr elements =>
            cases l with
            | nil =>
              cases elements
              refine ⟨bin [91, 93], ?_, flat_bin _⟩
              unfold «do_encode/2»
              simp [«do_encode_list/2», Erlang.erlang.«is_list/1»]
            | cons x xs =>
              cases elements with
              | cons head tail =>
              have below : ∀ y ∈ x :: xs, y.depth < k := fun y mem => by
                have := depth_le _ y mem
                omega
              obtain ⟨xio, xres, xflat⟩ := ih x (by simp) _ k head (below x (by simp))
              obtain ⟨lio, lres, lflat⟩ := list_loop_values xs _ k tail
                (fun y mem => ih y (by simp [mem])) (fun y mem => below y (by simp [mem]))
              refine ⟨.cons (.integer 91) (.cons xio lio), ?_, flat_byte 91 _ _
                (flat_join _ _ _ _ xflat lflat)⟩
              unfold «do_encode/2»
              simp [Erlang.erlang.«is_list/1», «do_encode_list/2», Erlang.erlang.«is_function/2»]
              rw [xres, Result.ok_bind, Result.resolve_bind, lres, Result.ok_bind,
                Result.resolve_of_isPure _ _ _ (by simp)]
          case encodesObj =>
            intro fields ih t depth represents bound
            simp only [Json.depth] at bound
            obtain ⟨k, rfl⟩ : ∃ k, depth = k + 1 := ⟨depth - 1, by omega⟩
            cases represents with
            | obj bindings =>
            unfold «do_encode/2»
            simp [Erlang.erlang.«is_list/1», «do_encode_map/2», Erlang.erlang.«is_function/2»,
              Erlang.erts_internal.«mc_iterator/1»]
            generalize Term.mapEntries _ = es at bindings ⊢
            have below : ∀ f ∈ fields, f.2.depth < k := fun f mem => by
              have := field_depth_le fields f mem
              omega
            cases fields with
            | nil =>
              cases bindings
              exact ⟨bin [123, 125], by simp [«lynx_local_10/2»], flat_bin _⟩
            | cons f fs =>
              obtain ⟨key, v⟩ := f
              cases bindings with
              | cons head tail =>
              obtain ⟨kio, kres, kflat⟩ := encode_str key.1 key.2 k
              obtain ⟨vio, vres, vflat⟩ := ih (key, v) (by simp) _ k head (below (key, v) (by simp))
              obtain ⟨lio, text, lres, lflat, closed⟩ := fields_loop fs _ k tail
                (fun g mem => ih g (by simp [mem])) (fun g mem => below g (by simp [mem]))
              refine ⟨Term.list [.integer 123, .cons kio (.cons (.integer 58) vio), lio, .integer 125],
                ?_, ?_⟩
              · simp only [List.foldr_cons, Result.ok_bind, «lynx_local_10/2», «key/2»]
                simp [Result.resolve_bind, kres, vres, lres]
              · have joined := flat_byte 123 _ _ (flat_join _ _ _ _ (flat_join _ _ _ _ kflat
                  (flat_byte 58 _ _ vflat)) (flat_join _ _ _ _ lflat (flat_byte 125 _ _
                    Erlang.erlang.iolist_to_binary_nil)))
                refine Eq.trans joined ?_
                simp [Json.text, ← closed]
          case encodesNil => intro y mem; cases mem
          case encodesCons =>
            intro x xs hx hxs y mem
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hx
            · exact hxs y mem
          case encodesFieldsNil => intro f mem; cases mem
          case encodesFieldsCons =>
            intro f fs hf hfs g mem
            rcases List.mem_cons.mp mem with rfl | mem
            · exact hf
            · exact hfs g mem
          case encodesField => intro k v hv; exact hv

        -- A value decodes to a term that is exactly equal to every term it represents.
        have represents_eq : ∀ (v : Json) (t : Term), Represents t v → Term.exactCompare v.term t = .eq := by
          intro v
          refine Json.rec (motive_1 := fun v => ∀ t, Represents t v → Term.exactCompare v.term t = .eq)
            (motive_2 := fun l => ∀ ts, RepresentsList ts l → Term.exactCompare (Json.terms l) ts = .eq)
            (motive_3 := fun fields => ∀ es, RepresentsFields es fields → ∀ q,
              Option.Rel (fun a b => Term.exactCompare a b = .eq) (Term.mapLookup (Json.fieldTerms fields) q)
                (Term.mapLookup es q))
            (motive_4 := fun f => ∀ t, Represents t f.2 → Term.exactCompare f.2.term t = .eq)
            ?equalInt ?equalFloat ?equalBool ?equalNull ?equalStr ?equalArr ?equalObj ?equalNil ?equalCons ?equalFieldsNil ?equalFieldsCons ?equalField v
          case equalInt => intro x; intro t represents; cases represents; simp [Json.term]
          case equalFloat => intro f; intro t represents; cases represents; simp [Json.term]
          case equalBool => intro b; intro t represents; cases represents; simp [Json.term]
          case equalNull => intro t represents; cases represents; simp [Json.term]
          case equalStr => intro s valid; intro t represents; cases represents; simp [Json.term]
          case equalArr => intro l ih; intro t represents; cases represents with | arr elements => exact ih _ elements
          case equalObj =>
            intro fields ih
            intro t represents
            cases represents with
            | obj bindings =>
              apply Term.map_exactCompare_eq_of_lookup
              intro q
              have related := ih _ bindings q
              rw [Term.mapLookup_mapEntries] at related
              exact related
          case equalNil => intro ts represents; cases represents; simp [Json.terms]
          case equalCons =>
            intro x xs hx hxs
            intro ts represents
            cases represents with
            | cons head tail => simp [Json.terms, Term.exactCompare_cons, hx _ head, hxs _ tail]
          case equalFieldsNil => intro es represents q; cases represents; simp [Json.fieldTerms, Term.mapLookup]
          case equalFieldsCons =>
            intro f fs hf hfs es represents q
            obtain ⟨k, v⟩ := f
            cases represents with
            | cons head tail =>
              have rest := hfs _ tail q
              simp only [Json.fieldTerms, Term.mapLookup, List.find?_cons] at rest ⊢
              by_cases same : Term.exactCompare q (bin k.1) = .eq <;> simp [same] at rest ⊢
              · exact hf _ head
              · exact rest
          case equalField => intro k v hv; exact hv

        have roundtrip_value : ∀ (v : Json) (t : Term), Represents t v →
            (∀ n, v ≠ .int n) ∧ (∀ f, v ≠ .float f) →
            v.depth < 99 →
            Result.resolve Erlang.program.fun_table 100 («roundtrip/1» t) = .ok Term.true := by
          intro v t represents number bound
          simp only [«roundtrip/1», «encode/1», «encode/2», Erlang.erlang.«is_function/2»]
          simp
          obtain ⟨io, encoded, flat⟩ := encode_value v t 99 represents bound
          rw [encoded, Result.ok_bind]
          simp only [Result.resolve_bind,
            Result.resolve_of_isPure _ _ (Result.ok _) (by simp),
            Result.resolve_of_isPure _ _ (Result.ofExcept _) (by simp),
            Result.ofExcept_ok, Result.ok_bind]
          rw [flat, Result.ofExcept_ok, Result.ok_bind,
            decode_value v _ number, Result.ok_bind]
          simp [Erlang.erlang.«=:=/2», Result.ofExcept_ok, represents_eq v t represents]

        clear represents_eq encode_value fields_loop encode_str list_loop_values flat_byte
          decode_value decodes depth_le field_depth_le encode_integer encode_string flat_close
          flat_join flat_bin float_text

        -- The requirement describes values nested at most as deep as its budget.
        have extract : ∀ (m : Nat) (t : Term), «supported?/2» t (.integer m) = .ok Term.true →
            ∃ v : Json, Represents t v ∧ v.depth ≤ m := by
          intro m
          induction m using Nat.strongRecOn with
          | ind m ih =>
            have smaller : ∀ (t : Term), 0 < m →
                «supported?/2» t (.integer ((m : Int) - 1)) = .ok Term.true →
                ∃ v : Json, Represents t v ∧ v.depth ≤ m - 1 := by
              intro t positive returned
              exact ih (m - 1) (by omega) t
                (by rw [show ((m - 1 : Nat) : Int) = (m : Int) - 1 by omega]; exact returned)
            -- The elements of a list within the budget.
            have values : ∀ (s : Nat) (t : Term), sizeOf t < s → 0 < m →
                «values?/2» t (.integer ((m : Int) - 1)) = .ok Term.true →
                ∃ l : List Json, RepresentsList t l ∧ Json.depths l ≤ m - 1 := by
              intro s
              induction s with
              | zero => intro t size; omega
              | succ s ihs =>
                intro t size positive returned
                rw [«values?/2».eq_def] at returned
                cases t with
                | nil => exact ⟨[], .nil, by simp [Json.depths]⟩
                | cons x xs =>
                  simp only [Term.cons.sizeOf_spec] at size
                  cases first : «supported?/2» x (.integer ((m : Int) - 1)) <;>
                    simp [first, Bind.bind, Except.bind] at returned
                  split at returned
                  · simp at returned
                  · obtain ⟨v, head, vDepth⟩ := smaller x positive first
                    obtain ⟨l, tail, lDepth⟩ := ihs xs (by omega) positive returned
                    exact ⟨v :: l, .cons head tail, by simp [Json.depths]; omega⟩
                  · simp at returned
                | _ => simp at returned
            -- The bindings of a map within the budget.
            have fields : ∀ es : List (Term × Term), 0 < m →
                «fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2]))
                  (.integer ((m : Int) - 1)) = .ok Term.true →
                ∃ fs, RepresentsFields es fs ∧ Json.fieldDepths fs ≤ m - 1 := by
              intro es positive
              induction es with
              | nil => intro _; exact ⟨[], .nil, by simp [Json.fieldDepths]⟩
              | cons e es ih =>
                intro returned
                obtain ⟨key, value⟩ := e
                rw [«fields?/2».eq_def] at returned
                simp only [List.map_cons, Term.list_cons] at returned
                rcases key with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨bytes, last, valid⟩
                all_goals try (simp [Erlang.erlang.«is_binary/1»] at returned; done)
                obtain ⟨_ | k, bound⟩ := last
                rotate_left
                · simp [Erlang.erlang.«is_binary/1»] at returned
                rcases bytes with ⟨data⟩
                have same : Term.bitstring ⟨data⟩ ⟨0, bound⟩ valid = bin data.toList := rfl
                simp only [same] at returned
                -- Each conjunct returns true.
                have strict : ∀ (left right : Except Exception Term),
                    (left >>= fun result => match result with
                      | .atom "false" => pure (.atom "false")
                      | .atom "true" => right
                      | other => Except.error (Exception.error
                          (.tuple #[.atom "badbool", .atom "and", other]))) = .ok Term.true →
                    left = .ok Term.true ∧ right = .ok Term.true := by
                  intro left right both
                  cases left with
                  | error e => simp at both
                  | ok result =>
                    simp only [Lynx.Except.ok_bind] at both
                    split at both
                    · simp at both
                    · exact ⟨rfl, both⟩
                    · simp at both
                simp [Erlang.erlang.«is_binary/1»] at returned
                rw [← bind_assoc] at returned
                obtain ⟨first, restValid⟩ := strict _ _ returned
                obtain ⟨keyValid, valueValid⟩ := strict _ _ first
                obtain ⟨v, head, vDepth⟩ := smaller value positive valueValid
                obtain ⟨fs, tail, fDepth⟩ := ih restValid
                rw [same]
                have keyUtf8 := utf8_bytes _ _ (Nat.le_refl _) keyValid
                exact ⟨(⟨data.toList, keyUtf8⟩, v) :: fs,
                  RepresentsFields.cons (k := ⟨data.toList, keyUtf8⟩) head tail,
                  by simp [Json.fieldDepths]; omega⟩
            intro t returned
            rw [«supported?/2».eq_def] at returned
            cases t with
            | integer x => exact ⟨.int x, .int x, by simp [Json.depth]⟩
            | float f => exact ⟨.float f, .float f, by simp [Json.depth]⟩
            | atom name =>
              by_cases yes : name = "true"
              · subst yes; exact ⟨.bool true, by simpa using Represents.bool true, by simp [Json.depth]⟩
              by_cases no : name = "false"
              · subst no; exact ⟨.bool false, by simpa using Represents.bool false, by simp [Json.depth]⟩
              by_cases null : name = "null"
              · subst null; exact ⟨.null, .null, by simp [Json.depth]⟩
              simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1», Erlang.erlang.«is_list/1», Erlang.erlang.«is_map/1»,
                yes, no, null] at returned
            | bitstring bytes last valid =>
              by_cases aligned : last = 0
              · subst aligned
                rcases bytes with ⟨data⟩
                have same : Term.bitstring ⟨data⟩ 0 valid = bin data.toList := by simp
                simp only [same] at returned ⊢
                simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1»] at returned
                exact ⟨.str data.toList (utf8_bytes _ _ (Nat.le_refl _) returned), .str _ _,
                  by simp [Json.depth]⟩
              · obtain ⟨_ | k, bound⟩ := last
                · exact absurd rfl aligned
                · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1», Erlang.erlang.«is_list/1»,
                    Erlang.erlang.«is_map/1»] at returned
            | nil | cons _ _ =>
              by_cases positive : 0 < m
              · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1», Erlang.erlang.«is_list/1»,
                  Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, positive]
                  at returned
                obtain ⟨l, elements, lDepth⟩ := values _ _ (Nat.lt_succ_self _) positive returned
                exact ⟨.arr l, .arr elements, by simp [Json.depth]; omega⟩
              · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1», Erlang.erlang.«is_list/1»,
                  Erlang.erlang.«is_map/1», Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
                  Int.compare_eq_gt, positive] at returned
            | map entries =>
              by_cases positive : 0 < m
              · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1», Erlang.erlang.«is_list/1»,
                  Erlang.erlang.«is_map/1», Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
                  Int.compare_eq_gt, positive, Erlang.maps.«to_list/1»] at returned
                obtain ⟨fs, bindings, fDepth⟩ := fields _ positive returned
                exact ⟨.obj fs, .obj bindings, by simp [Json.depth]; omega⟩
              · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1», Erlang.erlang.«is_list/1»,
                  Erlang.erlang.«is_map/1», Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
                  Int.compare_eq_gt, positive] at returned
            | _ => simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«is_float/1», Erlang.erlang.«is_list/1»,
                Erlang.erlang.«is_map/1»] at returned

        apply Lynx.run_of_resolve rfl
        simp only [«json_roundtrip:requires/1», «supported?/1»] at requires
        obtain ⟨v, represents, bound⟩ := extract 64 data requires
        cases v with
        | int n =>
          cases represents
          simpa [«json_roundtrip:ensures/1»] using roundtrip_integer n
        | float f =>
          cases represents
          simpa [«json_roundtrip:ensures/1»] using roundtrip_float f
        | _ =>
          simpa [«json_roundtrip:ensures/1»] using
            roundtrip_value _ _ represents (by simp) (by omega))
      """
  end
end
