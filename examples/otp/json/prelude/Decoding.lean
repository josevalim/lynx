module

public import Lynx
public import Lynx.Modules.Erlang.erlang

public section

namespace JsonProof
open Lynx

/-- The options record `json:decode/1` passes to the decoder. -/
abbrev options : Term := .tuple #[.atom "decode", .atom "undefined", .atom "undefined",
  .atom "undefined", .atom "undefined", .atom "undefined", .atom "undefined",
  .function true "erlang" "binary_to_float" 1 #[], .function true "erlang" "binary_to_integer" 1 #[],
  .atom "undefined", .atom "null"]

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
