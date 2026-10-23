module

public import Lynx.Term

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
public def «iolist_to_binary/1» (value : Term) : Except Exception Term :=
  match iodataBytes value with
  | some bytes => .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes))
  | none => .error (.error (.atom "badarg"))

/-- Decimal formatting of an arbitrary Erlang integer. -/
@[expose] public def «integer_to_binary/1» : Term → Except Exception Term
  | .integer value => .ok (.bitstring (toString value).toUTF8 0 (Term.Bitstring.valid_aligned _))
  | _ => .error (.error (.atom "badarg"))

/-- The name of an atom as UTF-8, or as Latin-1 when every character fits a byte. -/
@[expose] public def «atom_to_binary/2» : Term → Term → Except Exception Term
  | .atom name, .atom "utf8" | .atom name, .atom "unicode" =>
    .ok (.bitstring name.toUTF8 0 (Term.Bitstring.valid_aligned _))
  | .atom name, .atom "latin1" =>
    if name.toList.all (·.toNat < 256) then
      let bytes := ByteArray.mk (name.toList.map (UInt8.ofNat ·.toNat)).toArray
      .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned _))
    else .error (.error (.atom "badarg"))
  | _, _ => .error (.error (.atom "badarg"))

@[expose] public def «atom_to_binary/1» (atom : Term) : Except Exception Term :=
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
public def «binary_to_integer/1» : Term → Except Exception Term
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
    rw [ByteArray.toList.loop, ite_eq_left h, ih]
    have hi : i < bs.data.size := h
    have hd : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi
    rw [List.drop_eq_getElem_cons hd]
    simp [ByteArray.get!, getElem!_pos bs.data i hi]
  | case2 i r h =>
    rw [ByteArray.toList.loop, ite_eq_right h]
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
  simp only [String.utf8EncodeChar, hc, small, ite_true]

private theorem toDigits_utf8Encode (m : Nat) :
    (Nat.toDigits 10 m).utf8Encode = (decimalBytes m).toByteArray := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [Nat.toDigits_eq_ite (by decide), decimalBytes]
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
  simp only [«integer_to_binary/1», Except.ok_bind, «binary_to_integer/1», String.toUTF8_eq_toByteArray,
    Int.toString_eq_repr, Int.repr_eq_ite]
  by_cases nonneg : 0 ≤ n
  · have bytes : n.toNat.repr.toByteArray.toList = decimalBytes n.toNat := by
      rw [repr_bytes, toList_eq_data, List.toList_data_toByteArray]
    simp only [nonneg, ite_true, bytes, splitSign_decimalBytes, digitsValue_decimalBytes]
    simp; omega
  · have bytes : ("-" ++ (-n).toNat.repr).toByteArray.toList = 45 :: decimalBytes (-n).toNat := by
      rw [String.toByteArray_append, repr_bytes, toList_eq_data]
      simp [ByteArray.data_append]
      rfl
    simp only [nonneg, ite_false, bytes, splitSign, digitsValue_decimalBytes]
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
    Int.repr_eq_ite]
  by_cases nonneg : 0 ≤ n
  · simp only [nonneg, ite_true, show ¬n < 0 by omega, ite_false, List.nil_append]
    by_cases zero : n.toNat = 0
    · have text := bytes_of_toList n.toNat.repr.toByteArray [48] (by rw [repr, zero, decimalBytes_zero])
      exact ⟨48, [], congrArg Except.ok (congr _ _ text _ _), by simp, fun _ => ⟨by omega, rfl⟩⟩
    · obtain ⟨first, rest, text, digits, low⟩ :=
        positive n.toNat [] n.toNat.repr.toByteArray (by omega) (by rw [repr]; rfl)
      exact ⟨first, rest, congrArg Except.ok (congr _ _ text _ _), digits, fun h => by omega⟩
  · simp only [nonneg, ite_false, show n < 0 by omega, ite_true]
    have sign : ("-" : String).toByteArray.data.toList = [45] := by decide
    obtain ⟨first, rest, text, digits, low⟩ :=
      positive (-n).toNat [45] ("-" ++ (-n).toNat.repr).toByteArray (by omega) (by
        rw [String.toByteArray_append, toList_eq_data, ByteArray.data_append, Array.toList_append,
          sign, ← toList_eq_data, repr])
    exact ⟨first, rest, congrArg Except.ok (congr _ _ text _ _), digits, fun h => by omega⟩

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
public def «binary_to_float/1» : Term → Except Exception Term
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

/-- How far digits lie from the scaled value. -/
private def distance (scaled : Rat) (digits : Nat) : Rat :=
  let difference := (digits : Rat) - scaled
  if difference < 0 then -difference else difference

/-- Whether `low` is nearer to the scaled value than `high`, or as near and even. -/
private def nearer (scaled : Rat) (low high : Nat) : Bool :=
  distance scaled low < distance scaled high ||
    (distance scaled low == distance scaled high && low % 2 == 0)

/-- The digits of `count` significant figures that round back to the positive
value, preferring the candidate nearest to it and then an even one. -/
private def candidateDigits (positive : Term.FiniteFloat) (exponent : Int) (count : Nat) :
    Option (Nat × Int) :=
  let shift := exponent - count + 1
  let scaled := positive.magnitude / powerOfTen shift
  let lower := scaled.floor.toNat
  let candidates := [lower, lower + 1].filter fun digits =>
    digits ≠ 0 && Term.FiniteFloat.ofScientific false digits shift == some positive
  match candidates with
  | [digits] => some (digits, shift)
  | [low, high] => some (if nearer scaled low high then low else high, shift)
  | _ => none

/-- The exact decimal value of a positive float: its significand times a power of
two, written with a power of ten. -/
private def exactDigits (value : Term.FiniteFloat) : Nat × Int :=
  let (significand, exponent) : Nat × Int :=
    if value.exponent.val = 0 then (value.fraction.val, -1074)
    else (2 ^ 52 + value.fraction.val, (value.exponent.val : Int) - 1075)
  if 0 ≤ exponent then (significand * 2 ^ exponent.toNat, 0)
  else (significand * 5 ^ (-exponent).toNat, exponent)

/-- The shortest digits `d` and exponent `k` such that `d * 10 ^ k` rounds back
to the positive value. Seventeen significant digits always suffice; the exact
decimal value only stands behind them. -/
private def shortestDigits (value : Term.FiniteFloat) : Nat × Int :=
  let positive := { value with negative := false }
  let exponent := decimalExponent value.magnitude
  ((List.range' 1 17).findSome? (candidateDigits positive exponent)).getD (exactDigits value)

/-- Remove up to `fuel` trailing zeros, raising the exponent accordingly. -/
private def stripZeros : Nat → Nat → Int → Nat × Int
  | 0, digits, exponent => (digits, exponent)
  | fuel + 1, digits, exponent =>
    if digits ≠ 0 && digits % 10 == 0 then stripZeros fuel (digits / 10) (exponent + 1)
    else (digits, exponent)

/-- The ASCII text of an integer. -/
private def intBytes (value : Int) : List UInt8 :=
  if value < 0 then 45 :: decimalBytes value.natAbs else decimalBytes value.toNat

/-- `float_to_binary(Float, [short])`: the shortest round-tripping digits in
fixed or scientific notation, whichever is shorter, preferring fixed on ties.
Magnitudes from `2 ^ 53`, where binary64 stops representing every integer,
always use scientific notation. -/
private def shortBytes (value : Term.FiniteFloat) : List UInt8 :=
  let sign : List UInt8 := if value.negative then [45] else []
  if value.magnitude == 0 then sign ++ [48, 46, 48] else
    let (digits, shift) := shortestDigits value
    let (digits, shift) := stripZeros 20 digits shift
    let text := decimalBytes digits
    let count := text.length
    let point : Int := count + shift
    let fixed :=
      if point ≤ 0 then 48 :: 46 :: (List.replicate point.natAbs 48 ++ text)
      else if point < count then text.take point.toNat ++ 46 :: text.drop point.toNat
      else text ++ List.replicate (point.toNat - count) 48 ++ [46, 48]
    let rest := text.drop 1
    let scientific :=
      text.take 1 ++ 46 :: ((if rest.isEmpty then [48] else rest) ++ 101 :: intBytes (point - 1))
    let exact := value.magnitude < (2 : Rat) ^ 53
    sign ++ if exact && fixed.length ≤ scientific.length then fixed else scientific

/-- Only the `[short]` option is modeled; other options raise `badarg`. -/
public def «float_to_binary/2» : Term → Term → Except Exception Term
  | .float value, .cons (.atom "short") .nil =>
    .ok (.bitstring ⟨(shortBytes value).toArray⟩ 0 (Term.Bitstring.valid_aligned _))
  | _, _ => .error (.error (.atom "badarg"))

/-! Reading back the text of `float_to_binary/2`. -/

private abbrev digitStep (value : Nat) (byte : UInt8) : Nat := value * 10 + (byte.toNat - 48)

private theorem foldl_digitStep (l : List UInt8) (start : Nat) :
    l.foldl digitStep start = start * 10 ^ l.length + l.foldl digitStep 0 := by
  induction l generalizing start with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (digitStep 0 b)]
    simp only [digitStep, Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10, Nat.add_assoc]
    simp

private theorem foldl_digitStep_append (l r : List UInt8) :
    (l ++ r).foldl digitStep 0 = l.foldl digitStep 0 * 10 ^ r.length + r.foldl digitStep 0 := by
  rw [List.foldl_append, foldl_digitStep]

private theorem foldl_digitStep_zeros (n : Nat) : (List.replicate n (48 : UInt8)).foldl digitStep 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, foldl_digitStep, ih]
    have : digitStep 0 48 = 0 := rfl
    simp [this]

private theorem decimalBytes_value' (m : Nat) : (decimalBytes m).foldl digitStep 0 = m :=
  decimalBytes_value m

private theorem isDigit_48 : isDigit 48 = true := rfl

private theorem isDigit_zeros (n : Nat) : ∀ b ∈ List.replicate n (48 : UInt8), isDigit b = true := by
  intro b mem
  rw [List.eq_of_mem_replicate mem]
  rfl

private theorem digitsValue_eq {l : List UInt8} (ne : l ≠ []) (digits : ∀ b ∈ l, isDigit b = true) :
    digitsValue l = some (l.foldl digitStep 0) := by
  have empty : l.isEmpty = false := by cases l <;> simp_all
  simp [digitsValue, empty, List.all_eq_true.mpr digits]

private theorem span_digits {l : List UInt8} (digits : ∀ b ∈ l, isDigit b = true) (rest : List UInt8)
    (stop : ∀ b r, rest = b :: r → isDigit b = false) :
    (l ++ rest).span isDigit = (l, rest) := by
  suffices loop : ∀ acc, List.span.loop isDigit (l ++ rest) acc = (acc.reverse ++ l, rest) by
    unfold List.span
    simpa using loop []
  induction l with
  | nil =>
    intro acc
    cases rest with
    | nil => simp [List.span.loop]
    | cons b r => simp [List.span.loop, stop b r rfl]
  | cons b l ih =>
    intro acc
    have hb := digits b (by simp)
    simp only [List.cons_append, List.span.loop, hb]
    rw [ih (fun x mem => digits x (by simp [mem]))]
    simp

private theorem splitSign_intBytes (k : Int) :
    splitSign (intBytes k) = (decide (k < 0), decimalBytes k.natAbs) := by
  unfold intBytes
  by_cases neg : k < 0
  · simp [neg, splitSign]
  · simp only [neg, ite_false, splitSign_decimalBytes, decide_false]
    congr 2
    omega

/-- The parts of a float's text: a signed whole part, a point, a fraction, and an
optional exponent. -/
private theorem parseFloat_parts (negative : Bool) {whole fraction tail : List UInt8} {e : Int}
    (wne : whole ≠ []) (wd : ∀ b ∈ whole, isDigit b = true) (fne : fraction ≠ [])
    (fd : ∀ b ∈ fraction, isDigit b = true)
    (tl : (tail = [] ∧ e = 0) ∨ ∃ k, tail = 101 :: intBytes k ∧ e = k) :
    parseFloat ((if negative then [45] else []) ++ (whole ++ 46 :: (fraction ++ tail))) =
      some (negative, (whole ++ fraction).foldl digitStep 0, e - fraction.length) := by
  have sign : splitSign ((if negative then [45] else []) ++ (whole ++ 46 :: (fraction ++ tail))) =
      (negative, whole ++ 46 :: (fraction ++ tail)) := by
    cases negative
    · obtain ⟨b, w, rfl⟩ := List.exists_cons_of_ne_nil wne
      have hb := wd b (by simp)
      simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
      unfold splitSign
      split
      · rename_i r eq; cases eq; simp [isDigit] at hb
      · rename_i r eq; cases eq; simp [isDigit] at hb
      · rfl
    · rfl
  have wholeSpan := span_digits wd (46 :: (fraction ++ tail)) (by intro b r h; cases h; rfl)
  have fractionSpan := span_digits fd tail (by
    intro b r h
    rcases tl with ⟨rfl, -⟩ | ⟨k, rfl, -⟩
    · cases h
    · cases h; rfl)
  have value := digitsValue_eq (l := whole ++ fraction) (by simp [wne])
    (by intro b mem; simp only [List.mem_append] at mem; rcases mem with m | m
        · exact wd b m
        · exact fd b m)
  have wEmpty : whole.isEmpty = false := by cases whole <;> simp_all
  rcases tl with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · rw [List.append_nil] at fractionSpan
    simp only [List.append_nil] at sign wholeSpan ⊢
    simp [parseFloat, sign, wholeSpan, fractionSpan, value, wEmpty, fne]
  · simp [parseFloat, sign, wholeSpan, fractionSpan, value, wEmpty, fne, splitSign_intBytes,
      digitsValue_decimalBytes]
    split <;> omega

private theorem ten_zpow_add (a b : Int) : (10 : Rat) ^ (a + b) = 10 ^ a * 10 ^ b :=
  Rat.zpow_add (by decide) a b

private theorem scale_ten (d j : Nat) (s : Int) :
    ((d * 10 ^ j : Nat) : Rat) * 10 ^ (s - j) = d * 10 ^ s := by
  have : s = (s - j) + (j : Int) := by omega
  conv => rhs; rw [this, ten_zpow_add, Rat.zpow_natCast]
  rw [Rat.natCast_mul, Rat.natCast_pow]
  grind

private theorem stripZeros_value (fuel d : Nat) (e : Int) :
    ((stripZeros fuel d e).1 : Rat) * 10 ^ (stripZeros fuel d e).2 = d * 10 ^ e ∧
      (d ≠ 0 → (stripZeros fuel d e).1 ≠ 0) := by
  induction fuel generalizing d e with
  | zero => exact ⟨rfl, id⟩
  | succ fuel ih =>
    simp only [stripZeros]
    by_cases strip : (d ≠ 0 && d % 10 == 0) = true
    · rw [ite_eq_left strip]
      simp only [Bool.and_eq_true, ne_eq, decide_eq_true_eq, beq_iff_eq] at strip
      obtain ⟨value, nonzero⟩ := ih (d / 10) (e + 1)
      refine ⟨?_, fun _ => nonzero (by omega)⟩
      rw [value]
      have := scale_ten (d / 10) 1 (e + 1)
      rw [show d / 10 * 10 ^ 1 = d by omega, show e + 1 - ((1 : Nat) : Int) = e by omega] at this
      exact this.symm
    · rw [ite_eq_right strip]
      exact ⟨rfl, id⟩

private theorem candidateDigits_spec {positive : Term.FiniteFloat} {exponent : Int} {count d : Nat}
    {s : Int} (h : candidateDigits positive exponent count = some (d, s)) :
    d ≠ 0 ∧ Term.FiniteFloat.ofScientific false d s = some positive := by
  unfold candidateDigits at h
  simp only at h
  generalize hc : List.filter _ _ = candidates at h
  have mem : ∀ x ∈ candidates, x ≠ 0 ∧ Term.FiniteFloat.ofScientific false x
      (exponent - count + 1) = some positive := by
    intro x m
    rw [← hc, List.mem_filter] at m
    simpa using m.2
  split at h
  · cases h; exact mem _ (by simp)
  · cases h
    split <;> exact mem _ (by simp)
  · cases h

private theorem exactDigits_spec (value : Term.FiniteFloat) (nonzero : value.magnitude ≠ 0) :
    (exactDigits value).1 ≠ 0 ∧
      ((exactDigits value).1 : Rat) * 10 ^ (exactDigits value).2 = value.magnitude := by
  -- The significand times a power of two, written in decimal.
  have decimal (sig : Nat) (e : Int) (pos : sig ≠ 0) :
      (if 0 ≤ e then (sig * 2 ^ e.toNat, (0 : Int)) else (sig * 5 ^ (-e).toNat, e)).1 ≠ 0 ∧
        (((if 0 ≤ e then (sig * 2 ^ e.toNat, (0 : Int)) else (sig * 5 ^ (-e).toNat, e)).1 : Nat) :
          Rat) * 10 ^ (if 0 ≤ e then (sig * 2 ^ e.toNat, (0 : Int)) else (sig * 5 ^ (-e).toNat, e)).2 =
          (sig : Rat) * 2 ^ e := by
    by_cases nonneg : 0 ≤ e
    · simp only [nonneg, ite_true]
      refine ⟨Nat.mul_ne_zero pos (by simp), ?_⟩
      rw [Rat.zpow_zero, Rat.mul_one, Rat.natCast_mul, Rat.natCast_pow,
        show e = ((e.toNat : Nat) : Int) by omega, Rat.zpow_natCast]
      simp
      rw [show (max e 0).toNat = e.toNat by omega]
    · simp only [nonneg, ite_false]
      refine ⟨Nat.mul_ne_zero pos (by simp), ?_⟩
      have k : e = -(((-e).toNat : Nat) : Int) := by omega
      generalize (-e).toNat = n at k
      subst k
      have ten : (10 : Rat) ^ n = 5 ^ n * 2 ^ n := by
        have nat : (10 : Nat) ^ n = 5 ^ n * 2 ^ n := by rw [← Nat.mul_pow]
        have := congrArg (fun x : Nat => (x : Rat)) nat
        simpa [Rat.natCast_mul, Rat.natCast_pow] using this
      have p5 : (0 : Rat) < 5 ^ n := Rat.pow_pos (by decide)
      have c5 : ((5 : Nat) : Rat) = 5 := rfl
      rw [Rat.zpow_neg, Rat.zpow_neg, Rat.zpow_natCast, Rat.zpow_natCast, Rat.natCast_mul,
        Rat.natCast_pow, c5, ten, Rat.inv_mul_rev, Rat.mul_assoc]
      congr 1
      rw [Rat.mul_comm ((2 : Rat) ^ n)⁻¹, ← Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt p5),
        Rat.one_mul]
  unfold exactDigits
  unfold Term.FiniteFloat.magnitude at nonzero ⊢
  by_cases e0 : value.exponent.val = 0
  · have f0 : value.fraction.val ≠ 0 := by
      intro f0; simp [e0, f0] at nonzero
    simp only [e0, ite_true, ite_eq_right f0]
    exact decimal _ _ f0
  · simp only [e0, ite_false]
    exact decimal _ _ (by omega)

private theorem shortestDigits_spec (value : Term.FiniteFloat) (nonzero : value.magnitude ≠ 0) :
    (shortestDigits value).1 ≠ 0 ∧
      (Term.FiniteFloat.ofScientific false (shortestDigits value).1 (shortestDigits value).2 =
          some { value with negative := false } ∨
        ((shortestDigits value).1 : Rat) * 10 ^ (shortestDigits value).2 = value.magnitude) := by
  unfold shortestDigits
  simp only
  cases found : (List.range' 1 17).findSome? (candidateDigits { value with negative := false }
      (decimalExponent value.magnitude)) with
  | some r =>
    obtain ⟨count, -, eq⟩ := List.exists_of_findSome?_eq_some found
    obtain ⟨d, s⟩ := r
    obtain ⟨nz, rounds⟩ := candidateDigits_spec eq
    exact ⟨nz, Or.inl rounds⟩
  | none =>
    obtain ⟨nz, exact⟩ := exactDigits_spec value nonzero
    exact ⟨nz, Or.inr exact⟩

/-- A float's text after its sign: a whole part, a point, a fraction, and an optional
exponent, denoting `value`. Only zero starts with the digit zero. -/
private def Parts (body : List UInt8) (value : Rat) : Prop :=
  ∃ whole fraction tail e, body = whole ++ 46 :: (fraction ++ tail) ∧
    whole ≠ [] ∧ (∀ b ∈ whole, isDigit b = true) ∧ (∀ r, whole = 48 :: r → r = []) ∧
    fraction ≠ [] ∧ (∀ b ∈ fraction, isDigit b = true) ∧
    ((tail = [] ∧ e = 0) ∨ ∃ k, tail = 101 :: intBytes k ∧ e = k) ∧
    (((whole ++ fraction).foldl digitStep 0 : Nat) : Rat) * 10 ^ (e - fraction.length) = value

private theorem decimalBytes_parts {d : Nat} (nonzero : d ≠ 0) :
    ∃ first rest, decimalBytes d = first :: rest ∧ first ≠ 48 ∧
      (∀ b ∈ decimalBytes d, isDigit b = true) ∧ (decimalBytes d).foldl digitStep 0 = d := by
  obtain ⟨first, rest, eq, low, -⟩ := decimalBytes_head d (by omega)
  refine ⟨first, rest, eq, ?_, decimalBytes_digits d, decimalBytes_value' d⟩
  intro h; subst h; simp at low

private theorem fixed_parts {d : Nat} (nonzero : d ≠ 0) (s : Int) :
    Parts (if ((decimalBytes d).length + s : Int) ≤ 0 then
        48 :: 46 :: (List.replicate ((decimalBytes d).length + s : Int).natAbs 48 ++ decimalBytes d)
      else if ((decimalBytes d).length + s : Int) < (decimalBytes d).length then
        (decimalBytes d).take ((decimalBytes d).length + s : Int).toNat ++
          46 :: (decimalBytes d).drop ((decimalBytes d).length + s : Int).toNat
      else decimalBytes d ++
        List.replicate (((decimalBytes d).length + s : Int).toNat - (decimalBytes d).length) 48 ++
          [46, 48])
      ((d : Rat) * 10 ^ s) := by
  obtain ⟨first, rest, text, first48, digits, value⟩ := decimalBytes_parts nonzero
  generalize decimalBytes d = t at text digits value
  subst text
  generalize hc : (first :: rest).length = count
  have count1 : 1 ≤ count := by rw [← hc]; simp
  split
  · rename_i nonpos
    refine ⟨[48], List.replicate ((count : Int) + s).natAbs 48 ++ first :: rest, [], 0,
      by simp, by simp, by simp [isDigit_48], fun r h => (List.cons.inj h).2.symm, by simp, ?_,
      Or.inl ⟨rfl, rfl⟩, ?_⟩
    · intro b mem
      simp only [List.mem_append] at mem
      rcases mem with m | m
      · exact isDigit_zeros _ b m
      · exact digits b m
    · have z : digitStep 0 48 = 0 := rfl
      rw [List.singleton_append, List.foldl_cons, z, foldl_digitStep, foldl_digitStep_append,
        foldl_digitStep_zeros, value, Nat.zero_mul, Nat.zero_add, Nat.zero_mul, Nat.zero_add]
      have : (0 : Int) - ((List.replicate ((count : Int) + s).natAbs (48 : UInt8) ++ first :: rest).length
          : Nat) = s := by simp [hc]; omega
      rw [this]
  · rename_i pos
    split
    · rename_i inside
      have p1 : 1 ≤ ((count : Int) + s).toNat := by omega
      refine ⟨(first :: rest).take ((count : Int) + s).toNat,
        (first :: rest).drop ((count : Int) + s).toNat, [], 0, by simp, ?_, ?_, ?_, ?_, ?_,
        Or.inl ⟨rfl, rfl⟩, ?_⟩
      · obtain ⟨k, hk⟩ : ∃ k, ((count : Int) + s).toNat = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos p1).symm⟩
        rw [hk]; simp
      · exact fun b m => digits b (List.mem_of_mem_take m)
      · obtain ⟨k, hk⟩ : ∃ k, ((count : Int) + s).toNat = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos p1).symm⟩
        rw [hk]; intro r h
        simp only [List.take_succ_cons, List.cons.injEq] at h
        exact absurd h.1 first48
      · intro h
        rw [List.drop_eq_nil_iff, hc] at h
        omega
      · exact fun b m => digits b (List.mem_of_mem_drop m)
      · rw [List.take_append_drop, value]
        have : (0 : Int) - ((first :: rest).drop ((count : Int) + s).toNat).length = s := by
          rw [List.length_drop, hc]; omega
        rw [this]
    · rename_i outside
      refine ⟨first :: rest ++ List.replicate (((count : Int) + s).toNat - count) 48, [48], [], 0,
        by simp, by simp, ?_, ?_, by simp, by simp [isDigit_48], Or.inl ⟨rfl, rfl⟩, ?_⟩
      · intro b mem
        simp only [List.mem_append] at mem
        rcases mem with m | m
        · exact digits b m
        · exact isDigit_zeros _ b m
      · intro r h
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 first48
      · rw [foldl_digitStep_append, foldl_digitStep_append, foldl_digitStep_zeros, value]
        have zero : [(48 : UInt8)].foldl digitStep 0 = 0 := rfl
        rw [zero]
        simp only [List.length_replicate, List.length_singleton, Nat.add_zero, Nat.pow_one]
        have := scale_ten d ((((count : Int) + s).toNat - count) + 1) s
        rw [show s - (((((count : Int) + s).toNat - count) + 1 : Nat) : Int) = 0 - ((1 : Nat) : Int)
          by omega, Nat.pow_succ, ← Nat.mul_assoc] at this
        exact this

private theorem scientific_parts {d : Nat} (nonzero : d ≠ 0) (s : Int) :
    Parts ((decimalBytes d).take 1 ++ 46 ::
        ((if ((decimalBytes d).drop 1).isEmpty then [48] else (decimalBytes d).drop 1) ++
          101 :: intBytes (((decimalBytes d).length + s : Int) - 1)))
      ((d : Rat) * 10 ^ s) := by
  obtain ⟨first, rest, text, first48, digits, value⟩ := decimalBytes_parts nonzero
  generalize decimalBytes d = t at text digits value
  subst text
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
  have leading : ∀ r, [first] = 48 :: r → r = [] := by
    intro r h; simp only [List.cons.injEq] at h; exact absurd h.1 first48
  have firstDigit : ∀ b ∈ [first], isDigit b = true := fun b m => digits b (by simp_all)
  cases rest with
  | nil =>
    refine ⟨[first], [48], _, _, rfl, by simp, firstDigit, leading, by simp, by simp [isDigit_48],
      Or.inr ⟨_, rfl, rfl⟩, ?_⟩
    rw [foldl_digitStep_append, show [first].foldl digitStep 0 = d from value]
    have zero : [(48 : UInt8)].foldl digitStep 0 = 0 := rfl
    rw [zero]
    have := scale_ten d 1 s
    simp only [List.length_singleton, Nat.pow_one, Nat.add_zero] at this ⊢
    have key : ∀ x : Int, x = s - ((1 : Nat) : Int) → ((d * 10 : Nat) : Rat) * 10 ^ x = d * 10 ^ s := by
      intro x hx; subst hx; exact this
    exact key _ (by omega)
  | cons r rs =>
    refine ⟨[first], r :: rs, 101 :: intBytes (((rs.length + 1 + 1 : Nat) : Int) + s - 1),
      ((rs.length + 1 + 1 : Nat) : Int) + s - 1, by simp, by simp, firstDigit, leading, by simp,
      fun b m => digits b (by simp_all), Or.inr ⟨_, rfl, rfl⟩, ?_⟩
    rw [List.singleton_append, value]
    rw [show ((rs.length + 1 + 1 : Nat) : Int) + s - 1 - ((r :: rs).length : Nat) = s by
      simp; omega]

private theorem parts_ite {c : Prop} [Decidable c] {a b : List UInt8} {value : Rat}
    (ha : Parts a value) (hb : Parts b value) : Parts (if c then a else b) value := by
  split <;> assumption

private theorem shortBytes_parts (value : Term.FiniteFloat) :
    ∃ body digits, shortBytes value = (if value.negative then [45] else []) ++ body ∧
      Parts body digits ∧ ∀ (m : Nat) (e : Int), (m : Rat) * 10 ^ e = digits →
        Term.FiniteFloat.ofScientific value.negative m e = some value := by
  by_cases zero : value.magnitude = 0
  · refine ⟨[48, 46, 48], 0, ?_, ⟨[48], [48], [], 0, rfl, by simp, by simp [isDigit_48],
      fun r h => (List.cons.inj h).2.symm, by simp, by simp [isDigit_48], Or.inl ⟨rfl, rfl⟩,
      by rw [show ([48] ++ [48] : List UInt8).foldl digitStep 0 = 0 from rfl]; simp⟩, ?_⟩
    · unfold shortBytes
      simp [zero]
    · intro m e h
      exact Term.FiniteFloat.ofScientific_magnitude value (by rw [h, zero])
  · obtain ⟨nonzero, rounds⟩ := shortestDigits_spec value zero
    generalize found : shortestDigits value = pair at nonzero rounds
    obtain ⟨d₀, s₀⟩ := pair
    simp only at nonzero rounds
    obtain ⟨stripped, strippedNonzero⟩ := stripZeros_value 20 d₀ s₀
    have strippedNonzero := strippedNonzero nonzero
    refine ⟨?body, ((stripZeros 20 d₀ s₀).1 : Rat) * 10 ^ (stripZeros 20 d₀ s₀).2, ?eq, ?parts,
      ?round⟩
    case eq =>
      unfold shortBytes
      rw [ite_eq_right (by simpa using zero), found]
    case parts =>
      exact parts_ite (fixed_parts strippedNonzero _) (scientific_parts strippedNonzero _)
    case round =>
      intro m e h
      have scaled : (m : Rat) * 10 ^ e = d₀ * 10 ^ s₀ := h.trans stripped
      rcases rounds with rounds | exact
      · have positive := (Term.FiniteFloat.ofScientific_congr scaled).trans rounds
        cases value with
        | mk negative exponent fraction =>
        cases negative
        · exact positive
        · exact Term.FiniteFloat.ofScientific_neg positive
      · exact Term.FiniteFloat.ofScientific_magnitude value (scaled.trans exact)

/-- `binary_to_float/1` reads back the text of `float_to_binary(Float, [short])`. -/
public theorem binary_to_float_float_to_binary (value : Term.FiniteFloat) :
    («float_to_binary/2» (.float value) (.cons (.atom "short") .nil) >>= «binary_to_float/1») =
      .ok (.float value) := by
  obtain ⟨body, digits, eq, ⟨whole, fraction, tail, e, parts, wne, wd, -, fne, fd, tl, scaled⟩,
    round⟩ := shortBytes_parts value
  have bytes : (ByteArray.mk (shortBytes value).toArray).toList = shortBytes value := by
    rw [toList_eq_data]
  simp only [«float_to_binary/2», Except.ok_bind, «binary_to_float/1»]
  rw [bytes, eq, parts, parseFloat_parts value.negative wne wd fne fd tl]
  simp only [round _ _ scaled]

private theorem isDigit_bounds {b : UInt8} (h : isDigit b = true) : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨UInt8.le_iff_toNat_le.mp h.1, UInt8.le_iff_toNat_le.mp h.2⟩

/-- The text of `float_to_binary(Float, [short])`: an optional minus sign, decimal
digits that start with zero only for zero, a point, decimal digits, and an optional
exponent of `e`, an optional minus sign, and decimal digits. -/
public theorem float_to_binary_decimal (value : Term.FiniteFloat) :
    ∃ (sign whole fraction exponent : List UInt8),
      «float_to_binary/2» (.float value) (.cons (.atom "short") .nil) =
        .ok (.bitstring ⟨(sign ++ whole ++ 46 :: (fraction ++ exponent)).toArray⟩ 0
          (Term.Bitstring.valid_aligned _)) ∧
      (sign = [] ∨ sign = [45]) ∧ whole ≠ [] ∧ (∀ d ∈ whole, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
      (∀ rest, whole = 48 :: rest → rest = []) ∧ fraction ≠ [] ∧
      (∀ d ∈ fraction, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
      (exponent = [] ∨ ∃ esign digits, exponent = 101 :: (esign ++ digits) ∧
        (esign = [] ∨ esign = [45]) ∧ digits ≠ [] ∧ ∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) := by
  obtain ⟨body, -, eq, ⟨whole, fraction, tail, e, parts, wne, wd, leading, fne, fd, tl, -⟩, -⟩ :=
    shortBytes_parts value
  refine ⟨if value.negative then [45] else [], whole, fraction, tail, ?_, ?_, wne,
    fun d m => isDigit_bounds (wd d m), leading, fne, fun d m => isDigit_bounds (fd d m), ?_⟩
  · simp only [«float_to_binary/2», eq, parts, List.append_assoc]
  · split <;> simp
  · rcases tl with ⟨rfl, -⟩ | ⟨k, rfl, -⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨if k < 0 then [45] else [], decimalBytes k.natAbs, ?_, by split <;> simp,
        decimalBytes_ne_nil _, fun d m => isDigit_bounds (decimalBytes_digits _ d m)⟩
      unfold intBytes
      by_cases neg : k < 0
      · simp [neg]
      · simp only [neg, ite_false, List.nil_append]
        congr 2
        omega

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
