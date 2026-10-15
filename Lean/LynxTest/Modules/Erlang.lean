module

meta import LynxTest.ProofAudit
-- Import implementation modules here to audit their private declarations as well.
import all Lynx.Modules.Erlang.erlang
import Lynx.Modules.Erlang.maps
import Lynx.Term.Bitstring.Construction
import LynxTest.Term.Compare
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.FiniteFloat
import all Lynx.Term.Compare
import all Lynx.Term.Apply
import all Lynx.Term.Runner
import all Lynx.Modules.Erlang.erlang.Guards
import all Lynx.Modules.Erlang.erlang.Process
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String
import all Init.Data.Rat.Basic

namespace LynxTest.Modules.Erlang
open Lynx
open Erlang.erlang
open LynxTest.Term.Compare (orderedTerms ordered_terms)

theorem make_tuple_replicates (n : Nat) (value : Term) (bound : n ≤ 16777215) :
    «make_tuple/2» (.integer n) value = .ok (.tuple (Array.replicate n value)) := by
  have limit : (n : Int) ≤ 16777215 := by omega
  simp [«make_tuple/2», limit]

theorem make_tuple_bad_size (n : Int) (value : Term) (invalid : n < 0 ∨ 16777215 < n) :
    «make_tuple/2» (.integer n) value = .error (.error (.atom "badarg")) := by
  have : ¬ (0 ≤ n ∧ n ≤ 16777215) := by omega
  simp [«make_tuple/2», this]

theorem setelement_read (entries : Array Term) (i : Nat) (value : Term)
    (valid : i < entries.size) :
    (do
      let updated ← «setelement/3» (.integer (i + 1)) (.tuple entries) value
      «element/2» (.integer (i + 1)) updated) = .ok value := by
  have lower : (1 : Int) ≤ i + 1 := by omega
  have upper : (i : Int) + 1 ≤ entries.size := by omega
  simp [«setelement/3», «element/2», lower, upper, valid]

theorem setelement_bad_index (entries : Array Term) (n : Int) (value : Term)
    (invalid : n < 1 ∨ entries.size < n) :
    «setelement/3» (.integer n) (.tuple entries) value = .error (.error (.atom "badarg")) := by
  have : ¬ (1 ≤ n ∧ n ≤ entries.size) := by omega
  simp [«setelement/3», this]

private def identityFun (args : Array Term) : Result :=
  match args.toList with
  | [value] => .ok value
  | _ => .error (.error (.atom "unexpected_arguments"))

private def firstFun (args : Array Term) : Result :=
  match args.toList with
  | [left, _] => .ok left
  | _ => .error (.error (.atom "unexpected_arguments"))

private def rememberSelf : Result := do
  let pid ← «self/0»
  let _ ← «put/2» (.atom "pid") pid
  .ok pid

private def rememberSelfFun (args : Array Term) : Result :=
  match args.toList with
  | [] => rememberSelf
  | _ => .error (.error (.atom "unexpected_arguments"))

private def functions : Term.FunTable := #[.effectful fun _ => identityFun, .effectful fun _ => firstFun, .effectful fun _ => rememberSelfFun]

private def floatOne : Term.FiniteFloat :=
  ⟨false, 1023, 0⟩

private def floatOneAndHalf : Term.FiniteFloat :=
  ⟨false, 1023, 2 ^ 51⟩

theorem nonfinite_float_results_rejected :
    Term.FiniteFloat.ofModel (Float.Model.ofBits 0x7ff0000000000000) = none ∧
    Term.FiniteFloat.ofModel (Float.Model.ofBits 0xfff0000000000000) = none ∧
    Term.FiniteFloat.ofModel (Float.Model.ofBits 0x7ff8000000000001) = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem addition_numeric_types :
    «+/2» (.integer 2) (.integer 3) = .ok (.integer 5) ∧
    «+/2» (.float floatOne) (.float floatOneAndHalf) =
      .ok (.float ⟨false, 1024, 2 ^ 50⟩) ∧
    «+/2» (.integer 1) (.float floatOneAndHalf) =
      .ok (.float ⟨false, 1024, 2 ^ 50⟩) ∧
    «+/2» (.float floatOneAndHalf) (.integer 1) =
      .ok (.float ⟨false, 1024, 2 ^ 50⟩) ∧
    «+/2» (.float floatOneAndHalf) (.integer (-2)) =
      .ok (.float ⟨true, 1022, 0⟩) := by
  repeat' first | apply And.intro | rfl

-- Halfway sums choose the even significand; rounding may carry into the exponent.
theorem addition_rounding :
    «+/2» (.float ⟨false, 1023, 0⟩) (.float ⟨false, 970, 0⟩) =
      .ok (.float ⟨false, 1023, 0⟩) ∧
    «+/2» (.float ⟨false, 1023, 1⟩) (.float ⟨false, 970, 0⟩) =
      .ok (.float ⟨false, 1023, 2⟩) ∧
    «+/2» (.float ⟨false, 1023, 2 ^ 52 - 1⟩) (.float ⟨false, 970, 0⟩) =
      .ok (.float ⟨false, 1024, 0⟩) ∧
    -- Integer conversion rounds before addition, rather than rounding the exact sum.
    «+/2» (.integer (2 ^ 53 + 1)) (.float floatOne) =
      .ok (.float ⟨false, 1076, 0⟩) ∧
    «+/2» (.float ⟨true, 1076, 0⟩) (.integer (2 ^ 53 + 1)) =
      .ok (.float ⟨false, 0, 0⟩) := by
  repeat' first | apply And.intro | rfl

theorem addition_subnormals_and_zero :
    «+/2» (.float ⟨false, 0, 1⟩) (.float ⟨false, 0, 1⟩) =
      .ok (.float ⟨false, 0, 2⟩) ∧
    «+/2» (.float ⟨false, 0, 2 ^ 52 - 1⟩) (.float ⟨false, 0, 1⟩) =
      .ok (.float ⟨false, 1, 0⟩) ∧
    «+/2» (.float ⟨false, 1, 0⟩) (.float ⟨true, 0, 2 ^ 52 - 1⟩) =
      .ok (.float ⟨false, 0, 1⟩) ∧
    «+/2» (.float ⟨true, 0, 0⟩) (.float ⟨true, 0, 0⟩) =
      .ok (.float ⟨true, 0, 0⟩) ∧
    «+/2» (.float ⟨true, 0, 0⟩) (.float ⟨false, 0, 0⟩) =
      .ok (.float ⟨false, 0, 0⟩) ∧
    «+/2» (.integer 0) (.float ⟨true, 0, 0⟩) =
      .ok (.float ⟨false, 0, 0⟩) := by
  repeat' first | apply And.intro | rfl

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 4096 in
theorem addition_overflow :
    «+/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.float ⟨false, 2046, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    «+/2» (.float ⟨true, 2046, 2 ^ 52 - 1⟩) (.float ⟨true, 2046, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    -- Rounding at the overflow boundary, and a sum just below it.
    «+/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.float ⟨false, 1993, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    «+/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.float ⟨false, 1992, 0⟩) =
      .ok (.float ⟨false, 2046, 2 ^ 52 - 1⟩) ∧
    -- Conversion must fail even if exact addition would cancel the large integer.
    «+/2» (.integer (2 ^ 1024)) (.float ⟨true, 2046, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    «+/2» (.float ⟨false, 2046, 0⟩) (.integer (-(2 ^ 1024))) =
      .error (.error (.atom "badarith")) := by
  repeat' first | apply And.intro | rfl

theorem addition_rejects_nonnumeric (input other : Term)
    (hi : ∀ n, input ≠ .integer n) (hf : ∀ f, input ≠ .float f) :
    «+/2» input other = .error (.error (.atom "badarith")) ∧
    «+/2» other input = .error (.error (.atom "badarith")) := by
  cases input <;> cases other <;> simp_all [«+/2»]

theorem tuple_access (first second : Term) :
    «tuple_size/1» (.tuple #[]) = .ok (.integer 0) ∧
    «tuple_size/1» (.tuple #[first, second]) = .ok (.integer 2) ∧
    «element/2» (.integer 1) (.tuple #[first, second]) = .ok first ∧
    «element/2» (.integer 2) (.tuple #[first, second]) = .ok second := by
  repeat' first | apply And.intro | rfl

theorem tuple_access_invalid_indices (value : Term) :
    «element/2» (.integer 0) (.tuple #[value]) = .error (.error (.atom "badarg")) ∧
    «element/2» (.integer (-1)) (.tuple #[value]) = .error (.error (.atom "badarg")) ∧
    «element/2» (.integer 2) (.tuple #[value]) = .error (.error (.atom "badarg")) ∧
    «element/2» (.integer 1) (.tuple #[]) = .error (.error (.atom "badarg")) ∧
    «element/2» (.float floatOne) (.tuple #[value]) = .error (.error (.atom "badarg")) := by
  repeat' first | apply And.intro | rfl

theorem tuple_access_rejects_nontuples (input index : Term)
    (valid : ∀ entries, input ≠ .tuple entries) :
    «tuple_size/1» input = .error (.error (.atom "badarg")) ∧
    «element/2» index input = .error (.error (.atom "badarg")) := by
  cases input <;> cases index <;> simp_all [«tuple_size/1», «element/2»]

theorem multiplication_numeric_types :
    «*/2» (.integer (-7)) (.integer (2 ^ 100)) = .ok (.integer (-7 * 2 ^ 100)) ∧
    «*/2» (.float floatOneAndHalf) (.float floatOneAndHalf) =
      .ok (.float ⟨false, 1024, 2 ^ 49⟩) ∧
    «*/2» (.integer 2) (.float floatOneAndHalf) = .ok (.float ⟨false, 1024, 2 ^ 51⟩) ∧
    «*/2» (.float floatOneAndHalf) (.integer (-2)) = .ok (.float ⟨true, 1024, 2 ^ 51⟩) := by
  repeat' first | apply And.intro | rfl

-- Rounding happens during integer conversion before multiplication.
theorem multiplication_rounding_and_underflow :
    «*/2» (.integer (2 ^ 53 + 1)) (.float floatOne) =
      .ok (.float ⟨false, 1076, 0⟩) ∧
    «*/2» (.float ⟨false, 0, 1⟩) (.float ⟨false, 1022, 0⟩) =
      .ok (.float ⟨false, 0, 0⟩) ∧
    «*/2» (.float ⟨true, 0, 3⟩) (.float ⟨false, 1022, 0⟩) =
      .ok (.float ⟨true, 0, 2⟩) ∧
    «*/2» (.float ⟨true, 0, 0⟩) (.float floatOne) =
      .ok (.float ⟨true, 0, 0⟩) := by
  repeat' first | apply And.intro | rfl

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 2048 in
theorem multiplication_overflow :
    «*/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.integer 2) =
      .error (.error (.atom "badarith")) ∧
    -- Conversion overflows even though multiplication by zero would be finite.
    «*/2» (.integer (2 ^ 1024)) (.float ⟨false, 0, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    «*/2» (.float ⟨false, 0, 0⟩) (.integer (2 ^ 1024)) =
      .error (.error (.atom "badarith")) := by
  repeat' first | apply And.intro | rfl

theorem multiplication_rejects_nonnumeric (input other : Term)
    (hi : ∀ n, input ≠ .integer n) (hf : ∀ f, input ≠ .float f) :
    «*/2» input other = .error (.error (.atom "badarith")) ∧
    «*/2» other input = .error (.error (.atom "badarith")) := by
  cases input <;> cases other <;> simp_all [«*/2»]

theorem remainder_signs_and_zero :
    «rem/2» (.integer 7) (.integer 3) = .ok (.integer 1) ∧
    «rem/2» (.integer (-7)) (.integer 3) = .ok (.integer (-1)) ∧
    «rem/2» (.integer 7) (.integer (-3)) = .ok (.integer 1) ∧
    «rem/2» (.integer (-7)) (.integer (-3)) = .ok (.integer (-1)) ∧
    «rem/2» (.integer 7) (.integer 0) = .error (.error (.atom "badarith")) := by
  repeat' first | apply And.intro | rfl

theorem bitwise_and_signs :
    «band/2» (.integer 10) (.integer 12) = .ok (.integer 8) ∧
    «band/2» (.integer 10) (.integer (-4)) = .ok (.integer 8) ∧
    «band/2» (.integer (-4)) (.integer 10) = .ok (.integer 8) ∧
    «band/2» (.integer (-10)) (.integer (-12)) = .ok (.integer (-12)) ∧
    «band/2» (.integer (2 ^ 100 + 3)) (.integer (-2)) = .ok (.integer (2 ^ 100 + 2)) := by
  repeat' first | apply And.intro | rfl

theorem shifts_signed_values_and_counts :
    «bsr/2» (.integer (-7)) (.integer 1) = .ok (.integer (-4)) ∧
    «bsr/2» (.integer (-7)) (.integer (-2)) = .ok (.integer (-28)) ∧
    «bsl/2» (.integer (-7)) (.integer 2) = .ok (.integer (-28)) ∧
    «bsl/2» (.integer (-7)) (.integer (-1)) = .ok (.integer (-4)) ∧
    «bsr/2» (.integer (-7)) (.integer 100) = .ok (.integer (-1)) ∧
    «bsl/2» (.integer 7) (.integer (-100)) = .ok (.integer 0) ∧
    «bsl/2» (.integer 7) (.integer 100) = .ok (.integer (7 * 2 ^ 100)) ∧
    «bsr/2» (.integer 7) (.integer 0) = .ok (.integer 7) := by
  repeat' first | apply And.intro | rfl

theorem integer_operations_reject_nonintegers (input other : Term)
    (hi : ∀ n, input ≠ .integer n) :
    «rem/2» input other = .error (.error (.atom "badarith")) ∧
    «rem/2» other input = .error (.error (.atom "badarith")) ∧
    «band/2» input other = .error (.error (.atom "badarith")) ∧
    «band/2» other input = .error (.error (.atom "badarith")) ∧
    «bsr/2» input other = .error (.error (.atom "badarith")) ∧
    «bsr/2» other input = .error (.error (.atom "badarith")) ∧
    «bsl/2» input other = .error (.error (.atom "badarith")) ∧
    «bsl/2» other input = .error (.error (.atom "badarith")) := by
  cases input <;> cases other <;> simp_all [«rem/2», «band/2», «bsr/2», «bsl/2»]

-- Word masking and signed shifts expose arithmetic equations through the public API.
theorem word_mask (n bits : Nat) :
    «band/2» (.integer n) (.integer (2 ^ bits - 1)) =
      .ok (.integer ((n : Int) % 2 ^ bits)) := by
  exact «band/2_mask» n bits (Int.natCast_nonneg n)

theorem right_shift_is_floor_division (value : Int) (bits : Nat) :
    «bsr/2» (.integer value) (.integer bits) =
      .ok (.integer (value / 2 ^ bits)) := by
  simp [«bsr/2», Int.shiftRight_eq_div_pow]

-- Elixir: <<>>, <<1::1>>, <<1::7>>, <<1>>, <<1, 1::1>>.
-- Partial bytes store their meaningful bits at the most significant end.
private def bitstrings : List Term := [
  .bitstring ⟨#[]⟩ 0, .bitstring ⟨#[128]⟩ 1,
  .bitstring ⟨#[2]⟩ 7, .bitstring ⟨#[1]⟩ 0,
  .bitstring ⟨#[1, 128]⟩ 1]

theorem bitstring_guards :
    bitstrings.map «is_binary/1» =
      [.ok Term.true, .ok Term.false, .ok Term.false, .ok Term.true, .ok Term.false] ∧
    bitstrings.map «is_bitstring/1» = List.replicate 5 (.ok Term.true) ∧
    bitstrings.map «bit_size/1» =
      [.ok (.integer 0), .ok (.integer 1), .ok (.integer 7),
       .ok (.integer 8), .ok (.integer 9)] ∧
    bitstrings.map «byte_size/1» =
      [.ok (.integer 0), .ok (.integer 1), .ok (.integer 1),
       .ok (.integer 1), .ok (.integer 2)] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem binary_guard_alignment (bytes : ByteArray) (bits : Fin 8)
    (valid : Term.Bitstring.Valid bytes bits) :
    «is_binary/1» (.bitstring bytes bits valid) =
      .ok (if bits = 0 then Term.true else Term.false) := by
  unfold «is_binary/1»
  split <;> simp_all

theorem all_partial_byte_sizes :
    ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8)).map
      (fun bits => «bit_size/1» (.bitstring ⟨#[255, 0]⟩ bits (by
        have valid : ∀ bits : Fin 8, Term.Bitstring.Valid ⟨#[255, 0]⟩ bits := by decide
        exact valid bits))) =
    [16, 9, 10, 11, 12, 13, 14, 15].map (fun n => .ok (.integer n)) := rfl

theorem non_bitstrings_rejected (input : Term)
    (h : ∀ bytes bits valid, input ≠ .bitstring bytes bits valid) :
    «is_binary/1» input = .ok Term.false ∧
    «is_bitstring/1» input = .ok Term.false ∧
    «bit_size/1» input = .error (.error (.atom "badarg")) ∧
    «byte_size/1» input = .error (.error (.atom "badarg")) := by
  cases input with
  | bitstring bytes bits valid => exact False.elim (h bytes bits valid rfl)
  | _ => simp [«is_binary/1», «is_bitstring/1», «bit_size/1», «byte_size/1»]

theorem bitstring_comparison :
    -- A proper prefix sorts first; significant bits take precedence over length.
    «</2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[128]⟩ 0) = .ok Term.true ∧
    «>/2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[127]⟩ 0) = .ok Term.true ∧
    «</2» (.cons (.integer 1) .nil) (.bitstring ⟨#[]⟩ 0) = .ok Term.true ∧
    -- Canonical partial bytes support ordinary and exact equality.
    «==/2» (.bitstring ⟨#[128]⟩ 1) (Term.Bitstring.ofBits [true]) = .ok Term.true ∧
    «=:=/2» (.bitstring ⟨#[128]⟩ 1) (Term.Bitstring.ofBits [true]) = .ok Term.true ∧
    «=:=/2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[128]⟩ 2) = .ok Term.false ∧
    «=:=/2» (.map [(.bitstring ⟨#[128]⟩ 1, .integer 42)])
      (.map [(Term.Bitstring.ofBits [true], .integer 42)]) = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem empty_bitstring_has_zero_lastBits (bits : Fin 8)
    (valid : Term.Bitstring.Valid ⟨#[]⟩ bits) :
    bits = 0 ∧
    «is_binary/1» (.bitstring ⟨#[]⟩ bits valid) = .ok Term.true ∧
    «bit_size/1» (.bitstring ⟨#[]⟩ bits valid) = .ok (.integer 0) ∧
    «byte_size/1» (.bitstring ⟨#[]⟩ bits valid) = .ok (.integer 0) := by
  have zero := valid.1 rfl
  subst bits
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem floatOne_toRat : floatOne.toRat = 1 := by
  simp [floatOne, Term.FiniteFloat.toRat, Term.FiniteFloat.magnitude]
  change (4503599627370496 : Rat) * 2 ^ (-52 : Int) = 1
  rw [show (-52 : Int) = -(52 : Int) by rfl, Rat.zpow_neg]
  change (2 : Rat) ^ (52 : Nat) * ((2 : Rat) ^ (52 : Nat))⁻¹ = 1
  exact Rat.mul_inv_cancel _ (by decide)

private def applyWith (table : Term.FunTable) (function arguments : Term) : Result :=
  Result.resolve table 1 («apply/2» function arguments)

theorem dynamic_apply_2 :
    applyWith functions (.function 0 1 #[]) (.cons (.integer 7) .nil) = .ok (.integer 7) ∧
    applyWith functions (.function 1 2 #[])
      (.cons (.atom "left") (.cons (.atom "right") .nil)) = .ok (.atom "left") ∧
    applyWith functions (.function 0 1 #[]) (.cons (.integer 7) (.atom "improper")) =
      .error (.error (.atom "badarg")) := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

/-- Native argument arrays preserve both the dispatch result and error payloads. -/
theorem dynamic_apply_array :
    Result.resolve functions 1 (Term.apply (.function 0 1 #[]) #[.integer 7]) =
      .ok (.integer 7) ∧
    Term.apply (.atom "not_a_fun") #[] =
      .error (.error (.tuple #[.atom "badfun", .atom "not_a_fun"])) ∧
    Term.apply (.function 0 0 #[]) #[.integer 7, .atom "last"] =
      .error (.error (.tuple #[.atom "badarity", .tuple #[.function 0 0 #[],
        .cons (.integer 7) (.cons (.atom "last") .nil)]])) ∧
    «apply/2» (.function 0 0 #[]) (.cons (.integer 7) (.atom "improper")) =
      .error (.error (.atom "badarg")) := by
  repeat' apply And.intro
  all_goals cbv

private def closureFunctions : Term.FunTable := #[
  .effectful fun captures args =>
    match captures.toList, args.toList with
    | [captured], [argument] => «+/2» captured argument
    | _, _ => .error (.error (.atom "badarg"))
]

theorem dynamic_apply_captures :
    applyWith closureFunctions (.function 0 1 #[.integer 10]) (.cons (.integer 7) .nil) =
      .ok (.integer 17) ∧
    applyWith closureFunctions (.function 0 1 #[.integer 20]) (.cons (.integer 7) .nil) =
      .ok (.integer 27) ∧
    applyWith closureFunctions (.function 0 1 #[]) (.cons (.integer 7) .nil) =
      .error (.error (.atom "badarg")) := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

theorem dynamic_apply_2_errors :
    applyWith functions (.atom "not_a_fun") .nil =
        .error (.error (.tuple #[.atom "badfun", .atom "not_a_fun"])) ∧
    applyWith functions (.function 9 0 #[]) .nil =
        .error (.error (.tuple #[.atom "badfun", .function 9 0 #[]])) ∧
    applyWith functions (.function 0 1 #[]) .nil =
        .error (.error (.tuple #[.atom "badarity", .tuple #[.function 0 1 #[], .nil]])) := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

theorem float_equality_guards :
    «is_float/1» (.float floatOneAndHalf) = .ok Term.true ∧
    «==/2» (.integer 1) (.float floatOne) = .ok Term.true ∧
    «/=/2» (.integer 1) (.float floatOne) = .ok Term.false ∧
    «=:=/2» (.integer 1) (.float floatOne) = .ok Term.false ∧
    «=/=/2» (.integer 1) (.float floatOne) = .ok Term.true := by
  simp [«is_float/1», «==/2», «/=/2», «=:=/2», «=/=/2»,
    floatOne_toRat]

theorem append_reduces (head tail right : Term) :
    «++/2» (.cons head tail) right =
      («++/2» tail right >>= fun rest => .ok (.cons head rest)) :=
  rfl

theorem ordered_operators :
    orderedTerms.Pairwise (fun a b =>
      «</2» a b = .ok (.atom "true") ∧
      «>/2» a b = .ok (.atom "false") ∧
      «=</2» a b = .ok (.atom "true") ∧
      «>=/2» a b = .ok (.atom "false") ∧
      «</2» b a = .ok (.atom "false") ∧
      «>/2» b a = .ok (.atom "true") ∧
      «=</2» b a = .ok (.atom "false") ∧
      «>=/2» b a = .ok (.atom "true")) := by
  apply List.Pairwise.imp (R := fun a b => Term.compare a b = .lt ∧ Term.compare b a = .gt)
    (fun {a b} h => ?_) ordered_terms
  simp [«</2», «>/2», «=</2», «>=/2», h.1, h.2]

theorem reflexive_operators (a : Term) :
    «</2» a a = .ok (.atom "false") ∧
    «>/2» a a = .ok (.atom "false") ∧
    «=</2» a a = .ok (.atom "true") ∧
    «>=/2» a a = .ok (.atom "true") := by
  simp [«</2», «>/2», «=</2», «>=/2»]

/-- Callers remain in direct style even when the helper they invoke spawns. -/
private def spawnFromHelper : Result :=
  «spawn/1» (.function 2 0 #[])

private def spawnCaller : Result := do
  let childPid ← spawnFromHelper
  let parentPid ← rememberSelf
  pure (.tuple #[childPid, parentPid])

theorem spawn_schedules_child_or_parent_first :
    let final : Environment := {
      pidCounter := 2
      currentProcess := { pdict := [(.atom "pid", .pid 1)] } }
    Lynx.run spawnCaller [.swap 2] functions 1 =
      .ok (.tuple #[.pid 2, .pid 1]) final ∧
    Lynx.run spawnCaller [.current] functions 1 =
      .ok (.tuple #[.pid 2, .pid 1]) final := by
  cbv

private def nestedSpawnFun (args : Array Term) : Result :=
  match args.toList with
  | [] => «spawn/1» (.function 2 0 #[])
  | _ => .error (.error (.atom "unexpected_arguments"))

private def nestedSpawnCaller : Result :=
  «spawn/1» (.function 3 0 #[])

private def nestedFunctions : Term.FunTable := functions.push (.effectful fun _ => nestedSpawnFun)

theorem completed_nested_processes_are_removed :
    let final : Environment := { pidCounter := 3 }
    Lynx.run nestedSpawnCaller [.swap 2, .swap 3] nestedFunctions 2 =
      .ok (.pid 2) final ∧
    Lynx.run nestedSpawnCaller [.current, .current] nestedFunctions 2 =
      .ok (.pid 2) final := by
  cbv

theorem spawn_rejects_invalid_fun :
    Lynx.run («spawn/1» (.atom "not_a_fun")) [] functions =
      .error (.error (.atom "badarg")) {} ∧
    Lynx.run («spawn/1» (.function 9 0 #[])) [] functions =
      .error (.error (.atom "badarg")) {} ∧
    Lynx.run («spawn/1» (.function 0 1 #[])) [] functions =
      .error (.error (.atom "badarg")) {} := by
  repeat' apply And.intro
  all_goals cbv

theorem tuple_equality :
    «==/2» (.tuple #[]) (.tuple #[]) = .ok Term.true ∧
    «==/2» (.tuple #[.integer 1]) (.tuple #[.integer 1, .nil]) = .ok Term.false ∧
    «==/2» (.tuple #[.integer 1, .atom "a"])
      (.tuple #[.atom "a", .integer 1]) = .ok Term.false ∧
    «==/2» (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil])
      (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil]) = .ok Term.true ∧
    «==/2» (.tuple #[]) (Term.map []) = .ok Term.false := by
  repeat' first | apply And.intro | rfl

theorem map_equality :
    «==/2» (Term.map []) (Term.map []) = .ok Term.true ∧
    «==/2» (Term.map [(.atom "a", .integer 1), (.atom "b", .integer 2)])
      (Term.map [(.atom "b", .integer 2), (.atom "a", .integer 1)]) = .ok Term.true ∧
    «==/2» (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "a", .integer 2)]) = .ok Term.false ∧
    «==/2» (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "b", .integer 1)]) = .ok Term.false ∧
    «==/2» (Term.map []) (Term.map [(.atom "a", .nil)]) = .ok Term.false ∧
    «==/2» (Term.map [(.tuple #[(Term.map [])], .tuple #[.nil])])
      (Term.map [(.tuple #[Term.map []], .tuple #[.nil])]) = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem semantic_comparison_operators :
    let a := Term.map [(.integer 1, .nil), (.integer 0, .nil)]
    let b := Term.map [(.integer 0, .nil), (.integer 1, .nil), (.integer 1, .integer 99)]
    «==/2» a b = .ok Term.true ∧
    «</2» a b = .ok Term.false ∧
    «>/2» a b = .ok Term.false ∧
    «=</2» a b = .ok Term.true ∧
    «>=/2» a b = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem process_dictionary_empty :
    Lynx.run «get/0» = .ok .nil {} ∧
    Lynx.run («get/1» (.atom "missing")) = .ok (.atom "undefined") {} ∧
    Lynx.run «get_keys/0» = .ok .nil {} ∧
    Lynx.run «erase/0» = .ok .nil {} := by
  repeat' first | apply And.intro | rfl

theorem process_dictionary_put_replace_erase :
    Lynx.run (do
      let missing ← «put/2» (.atom "key") (.integer 1)
      let previous ← «put/2» (.atom "key") (.integer 2)
      let found ← «get/1» (.atom "key")
      let erased ← «erase/1» (.atom "key")
      let absent ← «get/1» (.atom "key")
      Result.ok (Term.tuple #[missing, previous, found, erased, absent])) =
      .ok (Term.tuple #[.atom "undefined", .integer 1, .integer 2,
        .integer 2, .atom "undefined"]) {} := by
  rfl

theorem process_dictionary_numeric_types_are_distinct :
    Lynx.run (do
      let _ ← «put/2» (.integer 1) (.atom "integer")
      let _ ← «put/2» (.float floatOne) (.atom "float")
      let integer ← «get/1» (.integer 1)
      let float ← «get/1» (.float floatOne)
      Result.ok (Term.tuple #[integer, float])) =
      .ok (Term.tuple #[.atom "integer", .atom "float"])
        { currentProcess := { pdict :=
            [(.float floatOne, .atom "float"), (.integer 1, .atom "integer")] } } := by
  rfl

theorem process_dictionary_queries :
    let env : Environment := {
      currentProcess := { pdict := [(.atom "a", .integer 1), (.atom "b", .integer 1)] } }
    «get/0» env = .ok (.cons (.tuple #[.atom "a", .integer 1])
      (.cons (.tuple #[.atom "b", .integer 1]) .nil)) env ∧
    «get_keys/0» env = .ok (.cons (.atom "a") (.cons (.atom "b") .nil)) env ∧
    «get_keys/1» (.integer 1) env =
      .ok (.cons (.atom "a") (.cons (.atom "b") .nil)) env ∧
    «erase/0» env = .ok (.cons (.tuple #[.atom "a", .integer 1])
      (.cons (.tuple #[.atom "b", .integer 1]) .nil)) {} := by
  repeat' first | apply And.intro | rfl

section
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

-- Boundary results checked against the installed Erlang/OTP 28.1.1.
private def half : Term.FiniteFloat := ⟨false, 1022, 0⟩
private def minusOneHalf : Term.FiniteFloat := ⟨true, 1023, 2 ^ 51⟩

theorem «hd/1_cons» (head tail : Term) :
    «hd/1» (.cons head tail) = .ok head := by rfl

theorem «tl/1_cons» (head tail : Term) :
    «tl/1» (.cons head tail) = .ok tail := by rfl

theorem «length/1_two_elements» (first second : Term) :
    «length/1» (.cons first (.cons second .nil)) = .ok (.integer 2) := by
  simp [«length/1»]

theorem list_guards_invalid :
    «hd/1» .nil = .error (.error (.atom "badarg")) ∧
    «tl/1» .nil = .error (.error (.atom "badarg")) ∧
    «length/1» (.cons (.integer 1) (.atom "tail")) = .error (.error (.atom "badarg")) := by
  simp [«hd/1», «tl/1», «length/1»]

theorem «is_function/2_arity» (id arity : Nat) (captures : Array Term) :
    «is_function/2» (.function id arity captures) (.integer arity) = .ok Term.true := by
  simp [«is_function/2»]

theorem «is_function/2_invalid_arity» (input : Term) :
    «is_function/2» input (.integer (-1)) = .error (.error (.atom "badarg")) ∧
    «is_function/2» input (.atom "arity") = .error (.error (.atom "badarg")) := by
  simp [«is_function/2»]

theorem «is_function/2_mismatch» :
    «is_function/2» (.function 0 2 #[]) (.integer 1) = .ok Term.false ∧
    «is_function/2» (.atom "not_fun") (.integer 999) = .ok Term.false := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem «map_get/2_after_put» (entries : List (Term × Term)) (key value : Term) :
    (Erlang.maps.«put/3» key value (.map entries) >>= «map_get/2» key) = .ok value := by
  simp [Erlang.maps.«put/3», «map_get/2»]

theorem «map_size/1_shadowed_and_exact_keys» :
    «map_size/1» (.map [(.integer 1, .nil), (.integer 1, .atom "new"),
      (.float ⟨false, 1023, 0⟩, .nil)]) = .ok (.integer 2) ∧
    «map_size/1» (.map []) = .ok (.integer 0) ∧
    «is_map_key/2» (.integer 1) (.map [(.float ⟨false, 1023, 0⟩, .nil)]) = .ok Term.false ∧
    «is_map_key/2» (.integer 1) (.map [(.integer 1, .nil)]) = .ok Term.true := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem map_guards_errors (key : Term) :
    «map_get/2» key (.map []) = .error (.error (.tuple #[.atom "badkey", key])) ∧
    «map_get/2» key .nil = .error (.error (.tuple #[.atom "badmap", .nil])) ∧
    «is_map_key/2» key .nil = .error (.error (.tuple #[.atom "badmap", .nil])) ∧
    «map_size/1» .nil = .error (.error (.tuple #[.atom "badmap", .nil])) := by
  simp [«map_get/2», «is_map_key/2», «map_size/1»]

theorem numeric_rounding :
    «round/1» (.float half) = .ok (.integer 1) ∧
    «round/1» (.float { half with negative := true }) = .ok (.integer (-1)) ∧
    «round/1» (.float floatOneAndHalf) = .ok (.integer 2) ∧
    «round/1» (.float minusOneHalf) = .ok (.integer (-2)) ∧
    «floor/1» (.float minusOneHalf) = .ok (.integer (-2)) ∧
    «ceil/1» (.float minusOneHalf) = .ok (.integer (-1)) ∧
    «trunc/1» (.float minusOneHalf) = .ok (.integer (-1)) ∧
    «floor/1» (.float half) = .ok (.integer 0) ∧
    «ceil/1» (.float half) = .ok (.integer 1) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem numeric_conversion_boundaries :
    «abs/1» (.float ⟨true, 0, 0⟩) = .ok (.float ⟨false, 0, 0⟩) ∧
    «float/1» (.integer (2 ^ 53 + 1)) = .ok (.float ⟨false, 1076, 0⟩) ∧
    «float/1» (.integer (2 ^ 1024)) = .error (.error (.atom "badarg")) ∧
    «trunc/1» (.float ⟨false, 0, 1⟩) = .ok (.integer 0) ∧
    «floor/1» (.float ⟨true, 0, 1⟩) = .ok (.integer (-1)) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem numeric_guards_integer_identity (n : Int) :
    «round/1» (.integer n) = .ok (.integer n) ∧
    «floor/1» (.integer n) = .ok (.integer n) ∧
    «ceil/1» (.integer n) = .ok (.integer n) ∧
    «trunc/1» (.integer n) = .ok (.integer n) ∧
    «abs/1» (.integer n) = .ok (.integer n.natAbs) := by
  simp [«round/1», «floor/1», «ceil/1», «trunc/1», «abs/1»]

theorem numeric_guards_invalid :
    ([«round/1», «floor/1», «ceil/1», «trunc/1», «abs/1», «float/1»].map
      (fun operation => operation .nil)) =
      List.replicate 6 (.error (.error (.atom "badarg"))) := by rfl

theorem integer_range_guard (n lo hi : Int) :
    «is_integer/3» (.integer n) (.integer lo) (.integer hi) =
      .ok (if lo ≤ n ∧ n ≤ hi then Term.true else Term.false) := by rfl

theorem arithmetic_boundaries :
    «-/1» (.float ⟨false, 0, 0⟩) = .ok (.float ⟨true, 0, 0⟩) ∧
    «+/1» (.float ⟨true, 0, 0⟩) = .ok (.float ⟨true, 0, 0⟩) ∧
    «-/2» (.float floatOneAndHalf) (.integer 1) = .ok (.float half) ∧
    «-/2» (.integer 1) (.float floatOneAndHalf) = .ok (.float { half with negative := true }) ∧
    «//2» (.integer 3) (.integer 2) = .ok (.float floatOneAndHalf) ∧
    «//2» (.float floatOneAndHalf) (.integer 3) = .ok (.float half) ∧
    «//2» (.integer 3) (.float floatOneAndHalf) = .ok (.float ⟨false, 1024, 0⟩) ∧
    «//2» (.integer 1) (.float ⟨true, 0, 0⟩) = .error (.error (.atom "badarith")) ∧
    «//2» (.integer 0) (.integer 0) = .error (.error (.atom "badarith")) ∧
    «-/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.float ⟨true, 2046, 2 ^ 52 - 1⟩) =
      .error (.error (.atom "badarith")) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem «div/2_signs» :
    «div/2» (.integer 7) (.integer (-3)) = .ok (.integer (-2)) ∧
    «div/2» (.integer (-7)) (.integer 3) = .ok (.integer (-2)) ∧
    «div/2» (.integer (-7)) (.integer (-3)) = .ok (.integer 2) ∧
    «div/2» (.integer 7) (.integer 0) = .error (.error (.atom "badarith")) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem bitwise_signs :
    «bor/2» (.integer 10) (.integer 12) = .ok (.integer 14) ∧
    «bor/2» (.integer (-10)) (.integer 12) = .ok (.integer (-2)) ∧
    «bor/2» (.integer 10) (.integer (-12)) = .ok (.integer (-2)) ∧
    «bor/2» (.integer (-10)) (.integer (-12)) = .ok (.integer (-10)) ∧
    «bxor/2» (.integer 10) (.integer 12) = .ok (.integer 6) ∧
    «bxor/2» (.integer (-10)) (.integer 12) = .ok (.integer (-6)) ∧
    «bxor/2» (.integer 10) (.integer (-12)) = .ok (.integer (-2)) ∧
    «bxor/2» (.integer (-10)) (.integer (-12)) = .ok (.integer 2) ∧
    «bnot/1» (.integer (-10)) = .ok (.integer 9) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem «bnot/1_involution» (n : Int) :
    («bnot/1» (.integer n) >>= «bnot/1») = .ok (.integer n) := by
  simp [«bnot/1»]
  omega

theorem arithmetic_invalid :
    «+/1» .nil = .error (.error (.atom "badarith")) ∧
    «-/1» .nil = .error (.error (.atom "badarith")) ∧
    ([«-/2», «//2», «div/2», «bor/2», «bxor/2»].map
      (fun operation => operation (.integer 1) .nil)) =
      List.replicate 5 (.error (.error (.atom "badarith"))) ∧
    «bnot/1» (.float half) = .error (.error (.atom "badarith")) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem «xor/2_booleans» :
    «xor/2» Term.true Term.false = .ok Term.true ∧
    «xor/2» Term.false Term.true = .ok Term.true ∧
    «xor/2» Term.true Term.true = .ok Term.false ∧
    «xor/2» Term.false Term.false = .ok Term.false ∧
    «xor/2» Term.true (.integer 0) = .error (.error (.atom "badarg")) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem min_max_equal_returns_first :
    «min/2» (.integer 1) (.float ⟨false, 1023, 0⟩) = .ok (.integer 1) ∧
    «max/2» (.float ⟨false, 1023, 0⟩) (.integer 1) = .ok (.float ⟨false, 1023, 0⟩) ∧
    «min/2» (.atom "a") (.integer 1) = .ok (.integer 1) ∧
    «max/2» (.integer 1) (.atom "a") = .ok (.atom "a") := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem local_node (pid reference : Nat) (input : Term) :
    «node/1» (.pid pid) = «node/0» ∧
    «node/1» (.reference reference) = «node/0» ∧
    «node/1» .nil = .error (.error (.atom "badarg")) ∧
    «is_port/1» input = .ok Term.false := by
  simp [«node/1», «is_port/1»]

private def bytes : ByteArray := ⟨#[1, 2, 3]⟩

theorem «binary_part/3_ranges» :
    «binary_part/3» (.bitstring bytes 0) (.integer 1) (.integer 2) =
      .ok (.bitstring ⟨#[2, 3]⟩ 0) ∧
    «binary_part/2» (.bitstring bytes 0) (.tuple #[.integer 3, .integer (-2)]) =
      .ok (.bitstring ⟨#[2, 3]⟩ 0) ∧
    «binary_part/3» (.bitstring bytes 0) (.integer 3) (.integer 0) =
      .ok (.bitstring ⟨#[]⟩ 0) ∧
    «binary_part/3» (.bitstring bytes 0) (.integer 2) (.integer 2) =
      .error (.error (.atom "badarg")) ∧
    «binary_part/3» (.bitstring bytes 0) (.integer 1) (.integer (-2)) =
      .error (.error (.atom "badarg")) ∧
    «binary_part/3» (.bitstring ⟨#[1, 2, 0]⟩ 1) (.integer 0) (.integer 0) =
      .error (.error (.atom "badarg")) ∧
    «binary_part/2» (.bitstring bytes 0) (.tuple #[.integer 1]) =
      .error (.error (.atom "badarg")) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)

theorem «size/1_complete_bytes» :
    «size/1» (.bitstring ⟨#[1, 2, 0]⟩ 1) = .ok (.integer 2) ∧
    «byte_size/1» (.bitstring ⟨#[1, 2, 0]⟩ 1) = .ok (.integer 3) ∧
    «size/1» (.tuple #[.nil, .nil]) = .ok (.integer 2) ∧
    «size/1» .nil = .error (.error (.atom "badarg")) := by
  repeat' first | apply And.intro | (with_unfolding_all rfl)


end

end LynxTest.Modules.Erlang

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Erlang
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang.Guards
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang.Process
  LynxTest.ProofAudit.checkModule `Lynx.Term.FiniteFloat
