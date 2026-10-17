# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/elixir/float.exs
# Prove the installed Float module, translated from BEAM debug information.
# Checked against Elixir 1.21.0-dev (3790cd8), Erlang/OTP 29.
# Source reference: ../elixir/lib/elixir/lib/float.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule FloatProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  import Bitwise

  def ratio_is_reduced({numerator, denominator}) do
    is_integer(numerator) and is_integer(denominator) and denominator > 0 and
      Integer.gcd(numerator, denominator) === 1
  end

  # Exact integer cross multiplication against the IEEE binary64 value.
  # This avoids converting huge numerators or denominators back to floats.
  def ratio_is_exact(number, {numerator, denominator}) do
    <<sign::1, exponent::11, fraction::52>> = <<number::float>>
    significand = if exponent == 0, do: fraction, else: (1 <<< 52) + fraction
    significand = if sign == 1, do: -significand, else: significand
    shift = if exponent == 0, do: -1074, else: exponent - 1075

    scaled_ratio_matches(numerator, denominator, significand, shift)
  end

  defp scaled_ratio_matches(numerator, denominator, significand, shift) do
    if shift >= 0 do
      numerator === (significand <<< shift) * denominator
    else
      numerator <<< -shift === significand * denominator
    end
  end

  def ratio_contract(number) do
    ratio = Float.ratio(number)
    ratio_is_reduced(ratio) and ratio_is_exact(number, ratio)
  end

  def rounding_preserves_encoding(number, precision) do
    encoded = <<number::float>>

    encoded === <<Float.floor(number, precision)::float>> and
      encoded === <<Float.ceil(number, precision)::float>> and
      encoded === <<Float.round(number, precision)::float>>
  end

  # At this binary64 exponent the spacing between adjacent values is at least
  # one, so every represented value is already an integer.
  def has_integral_spacing?(number) do
    <<_sign::1, exponent::11, _fraction::52>> = <<number::float>>
    exponent >= 1075
  end

  # The private reducer loops on zero. Keep it partial; the law proves the
  # public function terminates, including both signed zeros.
  @ratio_fixpoint ~LEAN"""
  partial_fixpoint monotonicity by
    intro f g h
    repeat' first
      | exact Lean.Order.PartialOrder.rel_refl
      | exact h _ _ _
      | exact h _ _
      | apply Lynx.Result.tryWith_mono_pure
      | apply Lynx.Result.bind_mono_left
      | apply Lynx.Result.bind_mono_pure
      | apply Lynx.Result.IsPure.tryWith
      | apply Lynx.Result.IsPure.handle
      | apply Lynx.Result.IsPure.bind
      | apply Lynx.Result.IsPure.bind_explicit
      | (intro)
      | split
      | simp_all
  """

  laws "Float exact reduced ratios" do
    termination_suffix &Float.reduce_to_ratio/3, @ratio_fixpoint
    termination_suffix &Integer.gcd_positive/2, @ratio_fixpoint

    law ratio_exact_reduced_and_total(number),
      requires: is_float(number),
      expects: ratio_contract(number),
      proof: ~LEAN"""
      let ratioPair (n : Nat) (e : Int) (negative : Bool) : Lynx.Term :=
        let signed : Int := if negative then -(n : Int) else n
        let numerator := if e < 0 then signed else signed <<< e.toNat
        .tuple #[.integer numerator, .integer ((1 : Int) <<< (-e).toNat)]

      have reduction (n : Nat) (e : Int) (negative : Bool) (positive : 0 < n) :
          ∃ m k : Nat, 0 < m ∧ m % 2 = 1 ∧ n = m * 2 ^ k ∧
            Elixir.Float.«reduce_to_ratio/3» (.integer n) (.integer e)
              (.integer (if negative then 1 else 0)) = .ok (ratioPair m (e + k) negative) := by
        induction n using Nat.strongRecOn generalizing e with
        | ind n ih =>
          have bit (n k : Nat) : n &&& (2 ^ k - 1) = n % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod n k
          have band1 : n &&& 1 = n % 2 := by simpa using bit n 1
          have band16 : n &&& 65535 = n % 65536 := by simpa using bit n 16
          have band4 : n &&& 15 = n % 16 := by simpa using bit n 4
          have oddInt : (n : Int) % 2 = 1 ↔ n % 2 = 1 := by
            change Int.ofNat (n % 2) = Int.ofNat 1 ↔ _
            exact ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
          have not_neg (a : Nat) : ¬ (a : Int) < 0 := by omega
          by_cases odd : n % 2 = 1
          · refine ⟨n, 0, positive, odd, by simp, ?_⟩
            rw [Elixir.Float.«reduce_to_ratio/3».eq_def]
            have mask : n &&& 1 = 1 := by simpa using bit n 1 |>.trans odd
            cases e <;> cases negative <;>
              simp [ratioPair, not_neg, ← Int.natCast_add, Erlang.erlang.«==/2», Erlang.erlang.«-/1», Erlang.erlang.«band/2», mask, Erlang.erlang.«bsl/2»]
          · have advance (chunk : Nat) (nonzero : chunk ≠ 0) (divisible : n % 2 ^ chunk = 0)
                (recurse : Elixir.Float.«reduce_to_ratio/3» (.integer n) (.integer e)
                    (.integer (if negative then 1 else 0)) =
                  Elixir.Float.«reduce_to_ratio/3» (.integer (n / 2 ^ chunk)) (.integer (e + chunk))
                    (.integer (if negative then 1 else 0))) :
                ∃ m k : Nat, 0 < m ∧ m % 2 = 1 ∧ n = m * 2 ^ k ∧
                  Elixir.Float.«reduce_to_ratio/3» (.integer n) (.integer e)
                    (.integer (if negative then 1 else 0)) = .ok (ratioPair m (e + k) negative) := by
              have power := Nat.one_lt_two_pow nonzero
              have dvd : 2 ^ chunk ∣ n := Nat.dvd_of_mod_eq_zero divisible
              have smaller := Nat.div_lt_self positive power
              have quotientPos : 0 < n / 2 ^ chunk :=
                Nat.div_pos (Nat.le_of_dvd positive dvd) (by omega)
              obtain ⟨m, k, hm, ho, factor, returned⟩ := ih (n / 2 ^ chunk) smaller (e + chunk) quotientPos
              refine ⟨m, k + chunk, hm, ho, ?_, ?_⟩
              · calc
                  n = n / 2 ^ chunk * 2 ^ chunk := (Nat.div_mul_cancel dvd).symm
                  _ = m * 2 ^ k * 2 ^ chunk := by rw [factor]
                  _ = m * 2 ^ (k + chunk) := by rw [Nat.pow_add, Nat.mul_assoc]
              · rw [recurse]
                simpa [Int.natCast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using returned
            by_cases mask16 : n % 65536 = 0
            · apply advance 16 (by decide) (by simpa using mask16)
              rw [Elixir.Float.«reduce_to_ratio/3».eq_def]
              have b1 : n &&& 1 ≠ 1 := by simpa only [band1] using odd
              have b16 : n &&& 65535 = 0 := by simpa using bit n 16 |>.trans mask16
              simp [oddInt, odd, ← Int.natCast_add, Erlang.erlang.«==/2», Erlang.erlang.«-/1», Erlang.erlang.«band/2», Erlang.erlang.«bsr/2», b1, b16,
                Nat.shiftRight_eq_div_pow, ← Int.natCast_shiftRight]
            · by_cases mask4 : n % 16 = 0
              · apply advance 4 (by decide) (by simpa using mask4)
                rw [Elixir.Float.«reduce_to_ratio/3».eq_def]
                have b1 : n &&& 1 ≠ 1 := by simpa only [band1] using odd
                have b16 : n &&& 65535 ≠ 0 := by simpa only [band16] using mask16
                have b4 : n &&& 15 = 0 := by simpa using bit n 4 |>.trans mask4
                simp [oddInt, odd, ← Int.natCast_add, Erlang.erlang.«==/2», Erlang.erlang.«-/1», Erlang.erlang.«band/2», Erlang.erlang.«bsr/2», b1, b16, b4,
                  Nat.shiftRight_eq_div_pow, ← Int.natCast_shiftRight]
              · apply advance 1 (by decide) (by have := Nat.mod_lt n (by decide : 0 < 2); omega)
                rw [Elixir.Float.«reduce_to_ratio/3».eq_def]
                have b1 : n &&& 1 ≠ 1 := by simpa only [band1] using odd
                have b16 : n &&& 65535 ≠ 0 := by simpa only [band16] using mask16
                have b4 : n &&& 15 ≠ 0 := by simpa only [band4] using mask4
                simp [oddInt, odd, ← Int.natCast_add, Erlang.erlang.«==/2», Erlang.erlang.«-/1», Erlang.erlang.«band/2», Erlang.erlang.«bsr/2», b1, b16, b4,
                  Nat.shiftRight_eq_div_pow, ← Int.natCast_shiftRight]

      have pair_properties (m : Nat) (e : Int) (negative : Bool) (odd : m % 2 = 1) :
          ∃ numerator : Int, ∃ denominator : Nat,
            ratioPair m e negative = .tuple #[.integer numerator, .integer denominator] ∧
            0 < denominator ∧ Nat.Coprime numerator.natAbs denominator ∧
            (numerator : Rat) / (denominator : Rat) =
              (if negative then -(m : Rat) else m) * (2 : Rat) ^ e := by
        have inverseOne : (1 : Rat)⁻¹ = 1 := Rat.inv_eq_of_mul_eq_one (Rat.one_mul 1)
        have coprime : Nat.Coprime m 2 := by
          change Nat.gcd m 2 = 1
          rw [Nat.gcd_comm, Nat.gcd_rec, odd]
          simp
        have not_neg (n : Nat) : ¬ (n : Int) < 0 := by omega
        cases e with
        | ofNat k =>
          refine ⟨(if negative then -(m : Int) else m) <<< k, 1, ?_, by decide, by simp, ?_⟩
          · cases negative <;> simp [ratioPair, not_neg]
          · cases negative <;> simp [Int.shiftLeft_eq, Rat.intCast_mul, Rat.intCast_pow,
              Rat.zpow_natCast, Rat.div_def, inverseOne, Rat.intCast_neg, Rat.intCast_natCast, Rat.neg_mul]
        | negSucc k =>
          refine ⟨if negative then -(m : Int) else m, 2 ^ (k + 1), ?_, Nat.two_pow_pos _, ?_, ?_⟩
          · cases negative <;> simp [ratioPair, Int.shiftLeft_eq, ← Int.natCast_add, ← Int.natCast_pow] <;> rfl
          · cases negative <;> simpa using coprime.pow_right (k + 1)
          · have exponent : Int.negSucc k = -((k + 1 : Nat) : Int) := by omega
            rw [exponent, Rat.zpow_neg, Rat.zpow_natCast]
            cases negative <;> simp [Rat.div_def, Rat.natCast_pow, Rat.intCast_natCast]

      have reduced_properties (n : Nat) (e : Int) (negative : Bool) (positive : 0 < n) :
          ∃ numerator : Int, ∃ denominator : Nat,
            0 < denominator ∧ Nat.Coprime numerator.natAbs denominator ∧
            (numerator : Rat) / (denominator : Rat) =
              (if negative then -(n : Rat) else n) * (2 : Rat) ^ e ∧
            Elixir.Float.«reduce_to_ratio/3» (.integer n) (.integer e)
              (.integer (if negative then 1 else 0)) =
                .ok (.tuple #[.integer numerator, .integer denominator]) := by
        obtain ⟨m, k, hm, odd, factor, returned⟩ := reduction n e negative positive
        obtain ⟨num, den, pair, denPos, coprime, exact⟩ := pair_properties m (e + k) negative odd
        refine ⟨num, den, denPos, coprime, ?_, by rw [returned, pair]⟩
        have left_comm (a b c : Rat) : a * (b * c) = b * (a * c) := by
          rw [← Rat.mul_assoc, ← Rat.mul_assoc, Rat.mul_comm a b]
        rw [exact]
        cases negative <;>
          simp [factor, Rat.natCast_mul, Rat.natCast_pow, Rat.zpow_add (by decide : (2 : Rat) ≠ 0),
            Rat.zpow_natCast, Rat.mul_assoc, Rat.mul_comm, left_comm, Rat.neg_mul, Rat.mul_neg]

      have float_zero_iff (value : Lynx.Term.FiniteFloat) :
          value.toRat = 0 ↔ value.exponent.val = 0 ∧ value.fraction.val = 0 := by
        have magnitude_zero : value.magnitude = 0 ↔ value.exponent.val = 0 ∧ value.fraction.val = 0 := by
          by_cases exp0 : value.exponent.val = 0
          · by_cases frac0 : value.fraction.val = 0
            · simp [Lynx.Term.FiniteFloat.magnitude, exp0, frac0]
            · have nonzero : (value.fraction.val : Rat) * (2 : Rat) ^ (-1074 : Int) ≠ 0 :=
                Rat.ne_of_gt (Rat.mul_pos (Rat.natCast_pos.mpr (by omega)) (Rat.zpow_pos (by decide)))
              simp only [Lynx.Term.FiniteFloat.magnitude, if_pos exp0, if_neg frac0]
              exact ⟨fun h => False.elim (nonzero h), fun h => False.elim (frac0 h.2)⟩
          · have nonzero : ((2 ^ 52 + value.fraction.val : Nat) : Rat) *
                (2 : Rat) ^ ((value.exponent.val : Int) - 1075) ≠ 0 :=
              Rat.ne_of_gt (Rat.mul_pos (Rat.natCast_pos.mpr (by omega)) (Rat.zpow_pos (by decide)))
            simp only [Lynx.Term.FiniteFloat.magnitude, if_neg exp0]
            exact ⟨fun h => False.elim (nonzero h), fun h => False.elim (exp0 h.1)⟩
        unfold Lynx.Term.FiniteFloat.toRat
        cases hn : value.negative
        · simpa only [hn, Bool.false_eq_true, ↓reduceIte] using magnitude_zero
        · simp only [hn, ↓reduceIte]
          have neg_zero : -value.magnitude = 0 ↔ value.magnitude = 0 := by
            constructor
            · intro h
              have := congrArg Neg.neg h
              simpa only [Rat.neg_neg, Rat.neg_zero] using this
            · intro h; rw [h, Rat.neg_zero]
          exact neg_zero.trans magnitude_zero

      have ratio_decomposes (value : Lynx.Term.FiniteFloat) :
          Elixir.Float.«ratio/1» (.float value) =
            if value.exponent.val = 0 ∧ value.fraction.val = 0 then
              .ok (.tuple #[.integer 0, .integer 1])
            else if value.exponent.val = 0 then
              Elixir.Float.«reduce_to_ratio/3» (.integer value.fraction.val) (.integer (-1074))
                (.integer (if value.negative then 1 else 0))
            else if value.fraction.val = 0 then
              Elixir.Float.«reduce_to_ratio/3» (.integer 1) (.integer ((value.exponent.val : Int) - 1023))
                (.integer (if value.negative then 1 else 0))
            else
              Elixir.Float.«reduce_to_ratio/3» (.integer (2 ^ 52 + value.fraction.val : Nat))
                (.integer ((value.exponent.val : Int) - 1075))
                (.integer (if value.negative then 1 else 0)) := by
        obtain ⟨encoded, built, sign, exponent, fraction⟩ := Lynx.Term.Bitstring.floatSegment_fields value
        have bor : value.fraction.val ||| 4503599627370496 = 2 ^ 52 + value.fraction.val := by
          have := Nat.or_two_pow_eq_add_of_lt value.fraction.isLt
          simpa [Nat.add_comm] using this
        have zero : (⟨false, 0, 0⟩ : Lynx.Term.FiniteFloat).toRat = 0 := rfl
        have empty : Lynx.Term.Bitstring.matchEnd (Lynx.Term.Bitstring.ofBits []) = true := rfl
        by_cases exp0 : value.exponent.val = 0 <;> by_cases frac0 : value.fraction.val = 0
        · simp [Elixir.Float.«ratio/1», Erlang.erlang.«is_float/1», Erlang.erlang.«=:=/2», Erlang.erlang.«==/2», zero, float_zero_iff, exp0, frac0]
        · simp [Elixir.Float.«ratio/1», Erlang.erlang.«is_float/1», Erlang.erlang.«=:=/2», Erlang.erlang.«==/2», zero, Erlang.erlang.«/=/2»,
            float_zero_iff, exp0, frac0, built, sign, exponent, fraction, empty]
        · rw [if_neg (by simp [exp0]), if_neg exp0, if_pos frac0]
          rw [Elixir.Float.«reduce_to_ratio/3».eq_def]
          simp [Elixir.Float.«ratio/1», Erlang.erlang.«is_float/1», Erlang.erlang.«=:=/2», Erlang.erlang.«==/2», zero, Erlang.erlang.«/=/2»,
            Erlang.erlang.«band/2», Erlang.erlang.«-/1», float_zero_iff, exp0, frac0, built, sign, exponent, fraction, empty]
        · simp [Elixir.Float.«ratio/1», Erlang.erlang.«is_float/1», Erlang.erlang.«=:=/2», Erlang.erlang.«==/2», zero, Erlang.erlang.«/=/2»,
            Erlang.erlang.«bor/2», float_zero_iff, exp0, frac0, built, sign, exponent, fraction, empty, bor,
            Int.natCast_add]

      have ratio_returns (value : Lynx.Term.FiniteFloat) :
          ∃ numerator : Int, ∃ denominator : Nat,
            0 < denominator ∧ Nat.Coprime numerator.natAbs denominator ∧
            (numerator : Rat) / (denominator : Rat) = value.toRat ∧
            Elixir.Float.«ratio/1» (.float value) =
              .ok (.tuple #[.integer numerator, .integer denominator]) := by
        rw [ratio_decomposes]
        by_cases exp0 : value.exponent.val = 0 <;> by_cases frac0 : value.fraction.val = 0
        · rw [if_pos ⟨exp0, frac0⟩]
          refine ⟨0, 1, by decide, by simp, ?_, rfl⟩
          have zero := (float_zero_iff value).mpr ⟨exp0, frac0⟩
          simp [zero, Rat.div_def]
        · rw [if_neg (by simp [frac0]), if_pos exp0]
          obtain ⟨num, den, denPos, coprime, equality, returned⟩ :=
            reduced_properties value.fraction.val (-1074) value.negative (by omega)
          refine ⟨num, den, denPos, coprime, ?_, returned⟩
          rw [equality]
          cases hn : value.negative <;>
            simp [Lynx.Term.FiniteFloat.toRat, Lynx.Term.FiniteFloat.magnitude, exp0, frac0, hn,
              Rat.neg_mul]
        · rw [if_neg (by simp [exp0]), if_neg exp0, if_pos frac0]
          obtain ⟨num, den, denPos, coprime, equality, returned⟩ :=
            reduced_properties 1 ((value.exponent.val : Int) - 1023) value.negative (by decide)
          refine ⟨num, den, denPos, coprime, ?_, returned⟩
          have scale : (2 : Rat) ^ ((value.exponent.val : Int) - 1023) =
              ((2 ^ 52 : Nat) : Rat) * (2 : Rat) ^ ((value.exponent.val : Int) - 1075) := by
            have exponent : (value.exponent.val : Int) - 1023 = 52 + ((value.exponent.val : Int) - 1075) := by omega
            rw [exponent, Rat.zpow_add (by decide)]
            congr 1
          rw [equality, scale]
          cases hn : value.negative <;>
            simp [Lynx.Term.FiniteFloat.toRat, Lynx.Term.FiniteFloat.magnitude, exp0, frac0, hn,
              Rat.neg_mul]
        · rw [if_neg (by simp [exp0]), if_neg exp0, if_neg frac0]
          obtain ⟨num, den, denPos, coprime, equality, returned⟩ :=
            reduced_properties (2 ^ 52 + value.fraction.val) ((value.exponent.val : Int) - 1075)
              value.negative (by omega)
          refine ⟨num, den, denPos, coprime, ?_, returned⟩
          rw [equality]
          cases hn : value.negative <;>
            simp [Lynx.Term.FiniteFloat.toRat, Lynx.Term.FiniteFloat.magnitude, exp0, frac0, hn,
              Rat.neg_mul]

      have rational_cross (num : Int) (den : Nat) (sig shift : Int) (positive : 0 < den)
          (equality : (num : Rat) / (den : Rat) = (sig : Rat) * (2 : Rat) ^ shift) :
          (if 0 ≤ shift then num = (sig <<< shift.toNat) * (den : Int)
            else num <<< (-shift).toNat = sig * (den : Int)) := by
        have den_ne : (den : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr positive)
        have left_comm (a b c : Rat) : a * (b * c) = b * (a * c) := by
          rw [← Rat.mul_assoc, ← Rat.mul_assoc, Rat.mul_comm a b]
        cases shift with
        | ofNat k =>
          rw [if_pos (by simp [Int.ofNat_eq_natCast])]
          apply Rat.intCast_inj.mp
          have result := congrArg (fun q : Rat => q * (den : Rat)) equality
          rw [Rat.div_mul_cancel den_ne] at result
          simpa [Int.shiftLeft_eq, Rat.intCast_mul, Rat.intCast_pow, Rat.zpow_natCast,
            Rat.intCast_natCast, Rat.mul_assoc] using result
        | negSucc k =>
          rw [if_neg (by simp [Int.negSucc_eq])]
          have exponent : Int.negSucc k = -((k + 1 : Nat) : Int) := by omega
          rw [exponent, Rat.zpow_neg, Rat.zpow_natCast] at equality
          have scale_ne : (2 : Rat) ^ (k + 1) ≠ 0 := Rat.ne_of_gt (Rat.pow_pos (by decide))
          have result := congrArg (fun q : Rat => q * (den : Rat) * (2 : Rat) ^ (k + 1)) equality
          rw [Rat.div_mul_cancel den_ne] at result
          have cancel : (sig : Rat) * ((2 : Rat) ^ (k + 1))⁻¹ * (den : Rat) * (2 : Rat) ^ (k + 1) =
              (sig : Rat) * (den : Rat) := by
            calc
              _ = (sig : Rat) * (den : Rat) * (((2 : Rat) ^ (k + 1))⁻¹ * (2 : Rat) ^ (k + 1)) := by
                simp [Rat.mul_assoc, Rat.mul_comm, left_comm]
              _ = _ := by rw [Rat.inv_mul_cancel _ scale_ne, Rat.mul_one]
          rw [cancel] at result
          apply Rat.intCast_inj.mp
          simpa [Int.shiftLeft_eq, Rat.intCast_mul, Rat.intCast_pow, Rat.intCast_natCast] using result

      have gcd_model (a b : Nat) :
          Elixir.Integer.«gcd_positive/2» (.integer a) (.integer b) =
            .ok (.integer (Nat.gcd a b)) := by
        induction b using Nat.strongRecOn generalizing a with
        | ind b ih =>
          by_cases aZero : a = 0
          · subst a
            rw [Elixir.Integer.«gcd_positive/2».eq_def]
            simp
          · by_cases bZero : b = 0
            · subst b
              rw [Elixir.Integer.«gcd_positive/2».eq_def]
              simp [aZero]
            · have recurse := ih (a % b) (Nat.mod_lt a (by omega)) b
              rw [Elixir.Integer.«gcd_positive/2».eq_def]
              simp [aZero, bZero, Erlang.erlang.«rem/2», ← Int.ofNat_tmod, recurse,
                Nat.gcd_rec b a, Nat.gcd_comm]
              simpa only [Int.natCast_emod] using recurse

      have reduced_contract (num : Int) (den : Nat) (positive : 0 < den)
          (coprime : Nat.Coprime num.natAbs den) :
          Elixir.FloatProofsTest.«ratio_is_reduced/1» (.tuple #[.integer num, .integer den]) =
            .ok (.atom "true") := by
        have gcd : Elixir.Integer.«gcd/2» (.integer num) (.integer den) = .ok (.integer 1) := by
          simpa [Elixir.Integer.«gcd/2», Erlang.erlang.«is_integer/1», Erlang.erlang.«abs/1»,
            Erlang.erlang.«==/2», Erlang.erlang.«=:=/2», gcd_model, Nat.Coprime] using (congrArg (fun n : Nat => (n : Int)) coprime)
        simp [Elixir.FloatProofsTest.«ratio_is_reduced/1», Erlang.erlang.«is_integer/1»,
          Erlang.erlang.«>/2», Erlang.erlang.«=:=/2», Int.compare_eq_gt, Ordering.isGT_iff_eq_gt, gcd, positive]

      have cross_contract (num : Int) (den : Nat) (sig shift : Int) (positive : 0 < den)
          (equality : (num : Rat) / (den : Rat) = (sig : Rat) * (2 : Rat) ^ shift) :
          Elixir.FloatProofsTest.«scaled_ratio_matches/4» (.integer num) (.integer den)
            (.integer sig) (.integer shift) = .ok (.atom "true") := by
        have cross := rational_cross num den sig shift positive equality
        cases shift with
        | ofNat k =>
          have nonnegative : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg _
          simp only [if_pos nonnegative] at cross
          simp [Elixir.FloatProofsTest.«scaled_ratio_matches/4», Erlang.erlang.«bsl/2»,
            Erlang.erlang.«=:=/2», cross]
        | negSucc k =>
          have negative : ¬ (0 : Int) ≤ Int.negSucc k := by simp [Int.negSucc_eq]
          simp only [if_neg negative] at cross
          change num <<< (k + 1) = sig * (den : Int) at cross
          simp [Elixir.FloatProofsTest.«scaled_ratio_matches/4», Erlang.erlang.«bsl/2»,
            Erlang.erlang.«-/1», Erlang.erlang.«=:=/2», ← Int.natCast_add, cross]

      let floatSignificand (value : Lynx.Term.FiniteFloat) : Int :=
        let n := if value.exponent.val = 0 then value.fraction.val else 2 ^ 52 + value.fraction.val
        if value.negative then -(n : Int) else n

      let floatExponent (value : Lynx.Term.FiniteFloat) : Int :=
        if value.exponent.val = 0 then -1074 else (value.exponent.val : Int) - 1075

      have value_exact (value : Lynx.Term.FiniteFloat) :
          value.toRat = (floatSignificand value : Rat) * (2 : Rat) ^ floatExponent value := by
        cases hn : value.negative <;> by_cases exp0 : value.exponent.val = 0 <;>
          by_cases frac0 : value.fraction.val = 0 <;>
          simp only [Lynx.Term.FiniteFloat.toRat, Lynx.Term.FiniteFloat.magnitude,
            floatSignificand, floatExponent, hn, exp0, frac0, ↓reduceIte,
            Bool.false_eq_true, Rat.intCast_neg, Rat.intCast_natCast, Rat.natCast_ofNat,
            Rat.neg_mul, Rat.zero_mul, Rat.neg_zero, Nat.add_zero, Int.ofNat_eq_natCast]

      have exact_contract (value : Lynx.Term.FiniteFloat) (num : Int) (den : Nat)
          (positive : 0 < den) (equality : (num : Rat) / (den : Rat) = value.toRat) :
          Elixir.FloatProofsTest.«ratio_is_exact/2» (.float value) (.tuple #[.integer num, .integer den]) =
            .ok (.atom "true") := by
        obtain ⟨encoded, built, sign, exponent, fraction⟩ := Lynx.Term.Bitstring.floatSegment_fields value
        have cross := cross_contract num den (floatSignificand value) (floatExponent value)
          positive (equality.trans (value_exact value))
        have empty : Lynx.Term.Bitstring.matchEnd (Lynx.Term.Bitstring.ofBits []) = true := rfl
        cases hn : value.negative <;> by_cases exp0 : value.exponent = 0 <;>
          simpa [Elixir.FloatProofsTest.«ratio_is_exact/2», built, sign, exponent, fraction, empty,
            Erlang.erlang.«==/2», Erlang.erlang.«-/1», floatSignificand, floatExponent,
            hn, exp0, Int.natCast_add] using cross

      have contract_true (value : Lynx.Term.FiniteFloat) :
          Elixir.FloatProofsTest.«ratio_contract/1» (.float value) = .ok (.atom "true") := by
        obtain ⟨num, den, positive, coprime, equality, returned⟩ := ratio_returns value
        simp [Elixir.FloatProofsTest.«ratio_contract/1», returned,
          reduced_contract num den positive coprime, exact_contract value num den positive equality]

      cases number <;> simp [«ratio_exact_reduced_and_total:requires/1»,
        Erlang.erlang.«is_float/1»] at requires
      rename_i value
      simpa [«ratio_exact_reduced_and_total:ensures/1»] using contract_true value
      """
  end

  laws "Float decimal rounding" do
    # Successful-return proofs must establish these error paths are unreachable.
    cutoff &Float.invalid_precision_message/1
    cutoff &ArgumentError.exception/1

    law decimal_rounding_preserves_exact_integers(number, precision),
      requires:
        is_float(number) and is_integer(precision) and precision >= 1 and precision <= 15 and
          has_integral_spacing?(number),
      expects: rounding_preserves_encoding(number, precision),
      proof: ~LEAN"""
      have spacing (value : Lynx.Term.FiniteFloat) :
          «has_integral_spacing?/1» (.float value) = .ok (.atom "true") ↔
            1075 ≤ value.exponent.val := by
        obtain ⟨encoded, built, sign, exponent, fraction⟩ := Lynx.Term.Bitstring.floatSegment_fields value
        have empty : Lynx.Term.Bitstring.matchEnd (Lynx.Term.Bitstring.ofBits []) = true := rfl
        by_cases large : 1075 ≤ value.exponent.val
        · have bound : (1075 : Int) ≤ value.exponent.val := by omega
          simp [«has_integral_spacing?/1», built, sign, exponent, fraction, empty, bound, large]
        · have bound : ¬ (1075 : Int) ≤ value.exponent.val := by omega
          simp [«has_integral_spacing?/1», built, sign, exponent, fraction, empty, bound, large]
      have fixed (value : Lynx.Term.FiniteFloat) (p : Int)
          (lower : 1 ≤ p) (upper : p ≤ 15) (large : 1075 ≤ value.exponent.val) :
          Elixir.Float.«floor/2» (.float value) (.integer p) = .ok (.float value) ∧
          Elixir.Float.«ceil/2» (.float value) (.integer p) = .ok (.float value) ∧
          Elixir.Float.«round/2» (.float value) (.integer p) = .ok (.float value) := by
        have nonzero : value.toRat ≠ 0 := by
          intro zero
          have fields := (Lynx.Term.FiniteFloat.toRat_eq_zero value).mp zero
          omega
        have pNonzero : p ≠ 0 := by omega
        have nonnegative : 0 ≤ p := by omega
        have notTiny : ¬ (value.exponent.val : Int) ≤ 971 := by omega
        have exact : (1075 : Int) - p ≤ value.exponent.val := by omega
        obtain ⟨encoded, built, sign, exponent, fraction⟩ := Lynx.Term.Bitstring.floatSegment_fields value
        have empty : Lynx.Term.Bitstring.matchEnd (Lynx.Term.Bitstring.ofBits []) = true := rfl
        simp [Elixir.Float.«floor/2», Elixir.Float.«ceil/2», Elixir.Float.«round/2», Elixir.Float.«round/3»,
          Erlang.erlang.«is_float/1», Erlang.erlang.«is_integer/1»,
          Erlang.erlang.«=:=/2», Erlang.erlang.«==/2», nonzero, pNonzero, lower, upper, nonnegative,
          built, sign, exponent, fraction, empty, notTiny, exact]
      cases number <;> simp [«decimal_rounding_preserves_exact_integers:requires/2»,
        Erlang.erlang.«is_float/1»] at requires
      rename_i value
      cases precision <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i p
      have bounds : 1 ≤ p ∧ p ≤ 15 ∧ 1075 ≤ value.exponent.val := by
        by_cases lower : 1 ≤ p <;> by_cases upper : p ≤ 15 <;>
          simp [lower, upper, spacing] at requires <;> omega
      obtain ⟨floored, ceiled, rounded⟩ := fixed value p bounds.1 bounds.2.1 bounds.2.2
      obtain ⟨encoded, built, _⟩ := Lynx.Term.Bitstring.floatSegment_fields value
      simp [«decimal_rounding_preserves_exact_integers:ensures/2», «rounding_preserves_encoding/2»,
        floored, ceiled, rounded, built, Erlang.erlang.«=:=/2»]
      """
  end

  laws "Float finite bounds" do
    law finite_extrema_bound_every_float(number),
      requires: is_float(number),
      expects: Float.min_finite() <= number and number <= Float.max_finite(),
      proof: ~LEAN"""
      have two_zpow_mono (a b : Int) (h : a ≤ b) :
          (2 : Rat) ^ a ≤ (2 : Rat) ^ b := by
        have one_le (n : Nat) : (1 : Rat) ≤ (2 : Rat) ^ n := by
          induction n with
          | zero => simp
          | succ n ih =>
            rw [Rat.pow_succ]
            exact Rat.le_trans (by decide : (1 : Rat) ≤ 2)
              (by simpa using Rat.mul_le_mul_of_nonneg_right ih (by decide : (0 : Rat) ≤ 2))
        have exponent : b = a + ((b - a).toNat : Int) := by omega
        rw [exponent, Rat.zpow_add (by decide), Rat.zpow_natCast]
        simpa using Rat.mul_le_mul_of_nonneg_left (one_le (b - a).toNat)
          (Rat.zpow_nonneg (n := a) (by decide : (0 : Rat) ≤ 2))
      let maximum : Rat := (9007199254740991 : Rat) * (2 : Rat) ^ (971 : Int)
      have magnitude_bounds (value : Lynx.Term.FiniteFloat) :
          0 ≤ value.magnitude ∧ value.magnitude ≤ maximum := by
        have product (n : Nat) (e : Int) (hn : n ≤ 9007199254740991) (he : e ≤ 971) :
            0 ≤ (n : Rat) * (2 : Rat) ^ e ∧
            (n : Rat) * (2 : Rat) ^ e ≤ maximum := by
          have nonnegative : (0 : Rat) ≤ (2 : Rat) ^ e := Rat.zpow_nonneg (by decide)
          refine ⟨Rat.mul_nonneg Rat.natCast_nonneg nonnegative, ?_⟩
          exact Rat.le_trans
            (Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hn) nonnegative)
            (Rat.mul_le_mul_of_nonneg_left (two_zpow_mono e 971 he) (by decide))
        have frac := value.fraction.isLt
        have exp := value.exponent.isLt
        unfold Lynx.Term.FiniteFloat.magnitude
        split
        · split
          · exact ⟨Rat.le_refl, Rat.mul_nonneg (by decide) (Rat.zpow_nonneg (by decide))⟩
          · exact product value.fraction.val (-1074) (by omega) (by decide)
        · exact product (2 ^ 52 + value.fraction.val) (value.exponent.val - 1075) (by omega) (by omega)
      have bounds (value : Lynx.Term.FiniteFloat) :
          -maximum ≤ value.toRat ∧ value.toRat ≤ maximum := by
        obtain ⟨nonnegative, upper⟩ := magnitude_bounds value
        have bound : 0 ≤ maximum := Rat.le_trans nonnegative upper
        have negBound : -maximum ≤ 0 := by simpa using Rat.neg_le_neg bound
        have negMagnitude : -value.magnitude ≤ 0 := by simpa using Rat.neg_le_neg nonnegative
        unfold Lynx.Term.FiniteFloat.toRat
        cases value.negative <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact ⟨Rat.le_trans negBound nonnegative, upper⟩
        · exact ⟨Rat.neg_le_neg upper, Rat.le_trans negMagnitude bound⟩
      have order (a b : Rat) (le : a ≤ b) :
          (compareOfLessAndEq a b).isLE = true := by
        rcases Rat.le_iff_lt_or_eq.mp le with lt | eq
        · simp [compareOfLessAndEq, lt]
        · simp [compareOfLessAndEq, eq, Rat.lt_irrefl]
      cases number <;> simp [«finite_extrema_bound_every_float:requires/1»,
        Erlang.erlang.«is_float/1»] at requires
      rename_i value
      obtain ⟨lower, upper⟩ := bounds value
      have lowerOrder := order (-maximum) value.toRat lower
      have upperOrder := order value.toRat maximum upper
      change (compareOfLessAndEq
        (Lynx.Term.FiniteFloat.toRat ⟨true, 2046, 4503599627370495⟩) value.toRat).isLE = true
        at lowerOrder
      change (compareOfLessAndEq value.toRat
        (Lynx.Term.FiniteFloat.toRat ⟨false, 2046, 4503599627370495⟩)).isLE = true
        at upperOrder
      simp [«finite_extrema_bound_every_float:ensures/1», Elixir.Float.«min_finite/0»,
        Elixir.Float.«max_finite/0», Erlang.erlang.«=</2»,
        Lynx.Term.compare_floats, lowerOrder, upperOrder]
      """
  end
end
