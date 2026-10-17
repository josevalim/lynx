module

public import Lynx.Purity

namespace Erlang.erlang
open Lynx

-- Only list elements may be bytes. A tail is itself iodata, so an integer
-- improper tail is rejected while a binary improper tail is accepted.
private def iodataBytes : Term → Option ByteArray
  | .nil => some ⟨#[]⟩
  | .bitstring bytes last _ => if last = 0 then some bytes else none
  | .cons head tail => do
    let first ← match head with
      | .integer byte =>
        if 0 ≤ byte ∧ byte ≤ 255 then some ⟨#[UInt8.ofNat byte.toNat]⟩ else none
      | _ => iodataBytes head
    let rest ← iodataBytes tail
    pure (first ++ rest)
  | _ => none

/-- Flatten nested byte lists and byte-aligned binaries. Binary tails are valid;
integer tails and unaligned bitstrings raise badarg. -/
#lynx_pure public def «iolist_to_binary/1» (value : Term) : Result :=
  match iodataBytes value with
  | some bytes => .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes))
  | none => .error (.error (.atom "badarg"))

/-- Decimal formatting of an arbitrary Erlang integer. -/
#lynx_pure @[expose] public def «integer_to_binary/1» : Term → Result
  | .integer value => .ok (.bitstring (toString value).toUTF8 0 (Term.Bitstring.valid_aligned _))
  | _ => .error (.error (.atom "badarg"))

/-- The name of an atom as UTF-8, or as Latin-1 when every character fits a byte. -/
#lynx_pure @[expose] public def «atom_to_binary/2» : Term → Term → Result
  | .atom name, .atom "utf8" | .atom name, .atom "unicode" =>
    .ok (.bitstring name.toUTF8 0 (Term.Bitstring.valid_aligned _))
  | .atom name, .atom "latin1" =>
    if name.toList.all (·.toNat < 256) then
      let bytes := ByteArray.mk (name.toList.map (UInt8.ofNat ·.toNat)).toArray
      .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned _))
    else .error (.error (.atom "badarg"))
  | _, _ => .error (.error (.atom "badarg"))

#lynx_pure @[expose] public def «atom_to_binary/1» (atom : Term) : Result :=
  «atom_to_binary/2» atom (.atom "utf8")

private def binaryOfString (text : String) : Term :=
  .bitstring text.toUTF8 0 (Term.Bitstring.valid_aligned _)

private def isDigit (byte : UInt8) : Bool := 48 ≤ byte && byte ≤ 57

/-- The value of a nonempty run of decimal digits. -/
private def digitsValue (digits : List UInt8) : Option Nat :=
  if digits.isEmpty || !digits.all isDigit then none
  else some (digits.foldl (fun value byte => value * 10 + (byte.toNat - 48)) 0)

/-- Split an optional leading sign. -/
private def splitSign : List UInt8 → Bool × List UInt8
  | 45 :: rest => (true, rest)
  | 43 :: rest => (false, rest)
  | bytes => (false, bytes)

/-- An optionally signed decimal integer, without whitespace or underscores. -/
#lynx_pure public def «binary_to_integer/1» : Term → Result
  | .bitstring bytes 0 _ =>
    let (negative, digits) := splitSign bytes.toList
    match digitsValue digits with
    | some value => .ok (.integer (if negative then -(value : Int) else value))
    | none => .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

/-- Erlang float syntax: a signed mantissa with digits on both sides of the
point and an optional signed exponent. Returns the sign, the digits as an
integer, and the decimal exponent applied to them. -/
private def parseFloat (bytes : List UInt8) : Option (Bool × Nat × Int) := do
  let (negative, rest) := splitSign bytes
  let (whole, rest) := rest.span isDigit
  let rest ← match rest with
    | 46 :: rest => some rest
    | _ => none
  let (fraction, rest) := rest.span isDigit
  let mantissa ← digitsValue (whole ++ fraction)
  if fraction.isEmpty || whole.isEmpty then none
  let exponent : Int ← match rest with
    | [] => some 0
    | marker :: rest =>
      if marker == 101 || marker == 69 then
        let (exponentNegative, digits) := splitSign rest
        let value ← digitsValue digits
        some (if exponentNegative then -(value : Int) else value)
      else none
  pure (negative, mantissa, exponent - fraction.length)

/-- Parse an Erlang float, rounding to the nearest binary64 value. Results that
overflow binary64 raise `badarg`. -/
#lynx_pure public def «binary_to_float/1» : Term → Result
  | .bitstring bytes 0 _ =>
    match parseFloat bytes.toList with
    | some (negative, mantissa, exponent) =>
      match Term.FiniteFloat.ofScientific negative mantissa exponent with
      | some value => .ok (.float value)
      | none => .error (.error (.atom "badarg"))
    | none => .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

private def powerOfTen (exponent : Int) : Rat :=
  if exponent < 0 then 1 / ((10 : Rat) ^ exponent.natAbs) else (10 : Rat) ^ exponent.toNat

/-- The decimal exponent `e` with `10 ^ e ≤ magnitude < 10 ^ (e + 1)`, for a
positive magnitude. Binary64 magnitudes lie within `10 ^ -324` and `10 ^ 309`. -/
private def decimalExponent (magnitude : Rat) : Int := Id.run do
  let mut exponent : Int := -324
  for _ in [0:634] do
    if powerOfTen (exponent + 1) ≤ magnitude then exponent := exponent + 1
  return exponent

/-- The shortest digits `d` and exponent `k` such that `d * 10 ^ k` rounds back
to the positive value, preferring the candidate nearest to it and then an even one. -/
private def shortestDigits (value : Term.FiniteFloat) : Nat × Int := Id.run do
  let magnitude := value.magnitude
  let positive := { value with negative := false }
  let exponent := decimalExponent magnitude
  for count in [1:18] do
    let shift := exponent - count + 1
    let scaled := magnitude / powerOfTen shift
    let lower := scaled.floor.toNat
    let candidates := [lower, lower + 1].filter fun digits =>
      digits ≠ 0 && Term.FiniteFloat.ofScientific false digits shift == some positive
    let distance (digits : Nat) : Rat :=
      let difference := (digits : Rat) - scaled
      if difference < 0 then -difference else difference
    match candidates with
    | [digits] => return (digits, shift)
    | [low, high] =>
      if distance low < distance high || (distance low == distance high && low % 2 == 0) then
        return (low, shift)
      else return (high, shift)
    | _ => pure ()
  return (magnitude.floor.toNat, 0)

/-- Remove trailing zeros, raising the exponent accordingly. -/
private def stripZeros (digits : Nat) (exponent : Int) : Nat × Int := Id.run do
  let mut digits := digits
  let mut exponent := exponent
  for _ in [0:20] do
    if digits ≠ 0 && digits % 10 == 0 then
      digits := digits / 10
      exponent := exponent + 1
  return (digits, exponent)

/-- `float_to_binary(Float, [short])`: the shortest round-tripping digits in
fixed or scientific notation, whichever is shorter, preferring fixed on ties.
Magnitudes from `2 ^ 53`, where binary64 stops representing every integer,
always use scientific notation. -/
private def shortFloat (value : Term.FiniteFloat) : String :=
  let sign := if value.negative then "-" else ""
  if value.magnitude == 0 then sign ++ "0.0" else
    let (digits, shift) := shortestDigits value
    let (digits, shift) := stripZeros digits shift
    let text := toString digits
    let count := text.length
    let point : Int := count + shift
    let zeros (n : Nat) := String.ofList (List.replicate n '0')
    let fixed :=
      if point ≤ 0 then "0." ++ zeros point.natAbs ++ text
      else if point < count then
        String.ofList (text.toList.take point.toNat) ++ "." ++
          String.ofList (text.toList.drop point.toNat)
      else text ++ zeros (point.toNat - count) ++ ".0"
    let rest := String.ofList (text.toList.drop 1)
    let scientific := String.ofList (text.toList.take 1) ++ "." ++
      (if rest.isEmpty then "0" else rest) ++ "e" ++ toString (point - 1)
    let exact := value.magnitude < (2 : Rat) ^ 53
    sign ++ if exact && fixed.length ≤ scientific.length then fixed else scientific

/-- Only the `[short]` option is modeled; other options raise `badarg`. -/
#lynx_pure public def «float_to_binary/2» : Term → Term → Result
  | .float value, .cons (.atom "short") .nil => .ok (binaryOfString (shortFloat value))
  | _, _ => .error (.error (.atom "badarg"))

public theorem iolist_to_binary_nil :
    «iolist_to_binary/1» .nil = .ok (.bitstring ⟨#[]⟩ 0 (Term.Bitstring.valid_aligned _)) := by
  simp [«iolist_to_binary/1», iodataBytes]

public theorem iolist_to_binary_binary (bytes : ByteArray) :
    «iolist_to_binary/1» (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes)) =
      .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes)) := by
  simp [«iolist_to_binary/1», iodataBytes]

/-- Nesting two valid iodata values preserves their concatenated byte sequence. -/
public theorem iolist_to_binary_join (left right : Term) (a b : ByteArray)
    (leftReturned : «iolist_to_binary/1» left = .ok (.bitstring a 0 (Term.Bitstring.valid_aligned a)))
    (rightReturned : «iolist_to_binary/1» right = .ok (.bitstring b 0 (Term.Bitstring.valid_aligned b))) :
    «iolist_to_binary/1» (.cons left right) =
      .ok (.bitstring (a ++ b) 0 (Term.Bitstring.valid_aligned _)) := by
  cases hl : iodataBytes left <;> simp [«iolist_to_binary/1», hl] at leftReturned
  cases hr : iodataBytes right <;> simp [«iolist_to_binary/1», hr] at rightReturned
  subst a b
  cases left <;> simp [iodataBytes] at hl <;>
    simp [«iolist_to_binary/1», iodataBytes, hl, hr]

/-- Adding a valid byte to an iolist prepends exactly that byte. -/
public theorem iolist_to_binary_byte_cons (byte : Int) (tail : Term) (bytes : ByteArray)
    (lower : 0 ≤ byte) (upper : byte ≤ 255)
    (returned : «iolist_to_binary/1» tail = .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes))) :
    «iolist_to_binary/1» (.cons (.integer byte) tail) =
      .ok (.bitstring (ByteArray.mk #[UInt8.ofNat byte.toNat] ++ bytes) 0 (Term.Bitstring.valid_aligned _)) := by
  cases ht : iodataBytes tail <;> simp [«iolist_to_binary/1», ht] at returned
  subst bytes
  simp [«iolist_to_binary/1», iodataBytes, lower, upper, ht]

end Erlang.erlang
