# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/elixir/float.exs
# Prove the installed Float module, translated from BEAM debug information.
# Checked against Elixir 1.21.0-dev (3790cd8), Erlang/OTP 29.
# Source reference: ../elixir/lib/elixir/lib/float.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule FloatProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

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
