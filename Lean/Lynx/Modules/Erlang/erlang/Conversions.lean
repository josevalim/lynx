module

public import Lynx.Purity

namespace Erlang.erlang

-- Other modules use these lemmas constantly, including while checking
-- well-founded recursion, so they are proved once, here.
set_option lynx.lazyPurity false
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

/-! The bytes of `ByteArray.toList`, defined by an index loop, are those of its array. -/

private theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction i, r using ByteArray.toList.loop.induct bs with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop, if_pos h, ih]
    have hi : i < bs.data.size := h
    have hd : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi
    rw [List.drop_eq_getElem_cons hd]
    simp [ByteArray.get!, getElem!_pos bs.data i hi]
  | case2 i r h =>
    rw [ByteArray.toList.loop, if_neg h]
    have : bs.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt h
    rw [List.drop_eq_nil_of_le this, List.append_nil]

private theorem toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop]; simp

/-- ASCII digits of a natural number, most significant first. -/
private def decimalBytes (m : Nat) : List UInt8 :=
  if m < 10 then [UInt8.ofNat (48 + m)] else decimalBytes (m / 10) ++ [UInt8.ofNat (48 + m % 10)]
decreasing_by omega

private theorem digitChar_bytes (d : Nat) (h : d < 10) :
    String.utf8EncodeChar d.digitChar = [UInt8.ofNat (48 + d)] := by
  have hc : d.digitChar.val.toNat = 48 + d := Nat.toNat_digitChar_of_lt_ten h
  have small : 48 + d ≤ 127 := by omega
  simp only [String.utf8EncodeChar, hc, small, if_true]

private theorem toDigits_utf8Encode (m : Nat) :
    (Nat.toDigits 10 m).utf8Encode = (decimalBytes m).toByteArray := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [Nat.toDigits_eq_if (by decide), decimalBytes]
    split
    · simp [List.utf8Encode_singleton, digitChar_bytes m ‹_›]
    · rw [List.utf8Encode_append, ih (m / 10) (by omega), List.utf8Encode_singleton,
        digitChar_bytes (m % 10) (Nat.mod_lt _ (by decide))]
      simp [List.toByteArray_append]

private theorem decimalBytes_value (m : Nat) :
    (decimalBytes m).foldl (fun value byte => value * 10 + (byte.toNat - 48)) 0 = m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [decimalBytes]
    split
    · simp [UInt8.toNat_ofNat]; omega
    · rw [List.foldl_append, ih (m / 10) (by omega)]
      simp [UInt8.toNat_ofNat]
      have := Nat.mod_lt m (show 10 > 0 by decide)
      omega

private theorem decimalBytes_digits (m : Nat) : ∀ byte ∈ decimalBytes m, isDigit byte = true := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [decimalBytes]
    split
    · simp [isDigit]; constructor <;> (apply UInt8.le_iff_toNat_le.mpr; simp [UInt8.toNat_ofNat]; omega)
    · intro byte mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with mem | rfl
      · exact ih (m / 10) (by omega) byte mem
      · have := Nat.mod_lt m (show 10 > 0 by decide)
        simp [isDigit]; constructor <;> (apply UInt8.le_iff_toNat_le.mpr; simp [UInt8.toNat_ofNat]; omega)

private theorem decimalBytes_ne_nil (m : Nat) : decimalBytes m ≠ [] := by
  rw [decimalBytes]; split <;> simp

private theorem splitSign_decimalBytes (m : Nat) : splitSign (decimalBytes m) = (false, decimalBytes m) := by
  match h : decimalBytes m with
  | [] => exact absurd h (decimalBytes_ne_nil m)
  | byte :: rest =>
    have digit := decimalBytes_digits m byte (by simp [h])
    unfold splitSign
    split
    · rename_i r eq; cases eq; simp [isDigit] at digit
    · rename_i r eq; cases eq; simp [isDigit] at digit
    · rfl

private theorem digitsValue_decimalBytes (m : Nat) : digitsValue (decimalBytes m) = some m := by
  have nonempty := decimalBytes_ne_nil m
  have digits := decimalBytes_digits m
  have empty : (decimalBytes m).isEmpty = false := by cases h : decimalBytes m <;> simp_all
  simp [digitsValue, empty, List.all_eq_true.mpr digits, decimalBytes_value]

private theorem repr_bytes (m : Nat) : (Nat.repr m).toByteArray = (decimalBytes m).toByteArray := by
  rw [Nat.repr_eq_ofList_toDigits, String.toByteArray_ofList, toDigits_utf8Encode]

/-- `binary_to_integer/1` reads back the decimal text of `integer_to_binary/1`. -/
public theorem binary_to_integer_integer_to_binary (n : Int) :
    («integer_to_binary/1» (.integer n) >>= «binary_to_integer/1») = .ok (.integer n) := by
  simp only [«integer_to_binary/1», Result.ok_bind, «binary_to_integer/1», String.toUTF8_eq_toByteArray,
    Int.toString_eq_repr, Int.repr_eq_if]
  by_cases nonneg : 0 ≤ n
  · have bytes : n.toNat.repr.toByteArray.toList = decimalBytes n.toNat := by
      rw [repr_bytes, toList_eq_data, List.toList_data_toByteArray]
    simp only [nonneg, if_true, bytes, splitSign_decimalBytes, digitsValue_decimalBytes]
    simp; omega
  · have bytes : ("-" ++ (-n).toNat.repr).toByteArray.toList = 45 :: decimalBytes (-n).toNat := by
      rw [String.toByteArray_append, repr_bytes, toList_eq_data]
      simp [ByteArray.data_append]
      rfl
    simp only [nonneg, if_false, bytes, splitSign, digitsValue_decimalBytes]
    simp; omega

private theorem decimalBytes_head (m : Nat) (positive : 0 < m) :
    ∃ first rest, decimalBytes m = first :: rest ∧ 49 ≤ first.toNat ∧ first.toNat ≤ 57 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [decimalBytes]
    split
    · exact ⟨_, _, rfl, by simp [UInt8.toNat_ofNat]; omega, by simp [UInt8.toNat_ofNat]; omega⟩
    · obtain ⟨first, rest, eq, low, high⟩ := ih (m / 10) (by omega) (by omega)
      exact ⟨first, rest ++ [UInt8.ofNat (48 + m % 10)], by simp [eq], low, high⟩

private theorem decimalBytes_zero : decimalBytes 0 = [48] := by
  rw [decimalBytes]; simp

private theorem bytes_of_toList (bytes : ByteArray) (list : List UInt8) (h : bytes.toList = list) :
    bytes = ⟨list.toArray⟩ := by
  rw [toList_eq_data] at h
  cases bytes with
  | mk data => simp only at h; rw [← h]

/-- The text of `integer_to_binary/1` is an optional minus sign followed by decimal
digits, which start with zero only for zero. -/
public theorem integer_to_binary_decimal (n : Int) :
    ∃ (first : UInt8) (rest : List UInt8),
      «integer_to_binary/1» (.integer n) =
        .ok (.bitstring ⟨((if n < 0 then [45] else []) ++ first :: rest).toArray⟩ 0
          (Term.Bitstring.valid_aligned _)) ∧
      (∀ d ∈ first :: rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
      (first.toNat = 48 → n = 0 ∧ rest = []) := by
  have bounds (byte : UInt8) (digit : isDigit byte = true) : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 := by
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at digit
    exact ⟨UInt8.le_iff_toNat_le.mp digit.1, UInt8.le_iff_toNat_le.mp digit.2⟩
  have repr (m : Nat) : m.repr.toByteArray.toList = decimalBytes m := by
    rw [repr_bytes, toList_eq_data, List.toList_data_toByteArray]
  -- A positive magnitude has a leading digit other than zero.
  have positive (m : Nat) (sign : List UInt8) (text : ByteArray) (zero : 0 < m)
      (eq : text.toList = sign ++ decimalBytes m) :
      ∃ (first : UInt8) (rest : List UInt8), text = ⟨(sign ++ first :: rest).toArray⟩ ∧
        (∀ d ∈ first :: rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧ 49 ≤ first.toNat := by
    obtain ⟨first, rest, digits, low, _⟩ := decimalBytes_head m zero
    refine ⟨first, rest, bytes_of_toList _ _ (by rw [eq, digits]), ?_, low⟩
    intro d mem
    exact bounds d (decimalBytes_digits m d (by rw [digits]; exact mem))
  have congr (a b : ByteArray) (same : a = b) (va : Term.Bitstring.Valid a 0)
      (vb : Term.Bitstring.Valid b 0) : Term.bitstring a 0 va = Term.bitstring b 0 vb := by
    subst same; rfl
  simp only [«integer_to_binary/1», String.toUTF8_eq_toByteArray, Int.toString_eq_repr,
    Int.repr_eq_if]
  by_cases nonneg : 0 ≤ n
  · simp only [nonneg, if_true, show ¬n < 0 by omega, if_false, List.nil_append]
    by_cases zero : n.toNat = 0
    · have text := bytes_of_toList n.toNat.repr.toByteArray [48] (by rw [repr, zero, decimalBytes_zero])
      exact ⟨48, [], congrArg Result.ok (congr _ _ text _ _), by simp, fun _ => ⟨by omega, rfl⟩⟩
    · obtain ⟨first, rest, text, digits, low⟩ :=
        positive n.toNat [] n.toNat.repr.toByteArray (by omega) (by rw [repr]; rfl)
      exact ⟨first, rest, congrArg Result.ok (congr _ _ text _ _), digits, fun h => by omega⟩
  · simp only [nonneg, if_false, show n < 0 by omega, if_true]
    have sign : ("-" : String).toByteArray.data.toList = [45] := by decide
    obtain ⟨first, rest, text, digits, low⟩ :=
      positive (-n).toNat [45] ("-" ++ (-n).toNat.repr).toByteArray (by omega) (by
        rw [String.toByteArray_append, toList_eq_data, ByteArray.data_append, Array.toList_append,
          sign, ← toList_eq_data, repr])
    exact ⟨first, rest, congrArg Result.ok (congr _ _ text _ _), digits, fun h => by omega⟩

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
