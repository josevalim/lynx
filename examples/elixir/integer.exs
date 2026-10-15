# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/elixir/integer.exs
# Prove the installed Integer module, translated from BEAM debug information.
# Checked against Elixir 1.21.0-dev (3790cd8), Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/integer.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule IntegerProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case
  require Integer

  def division_contract(dividend, divisor) do
    division_reconstructs(dividend, divisor) and
      ceil_is_dual(dividend, divisor) and
      remainder_in_bounds(Integer.mod(dividend, divisor), divisor)
  end

  def division_reconstructs(dividend, divisor),
    do:
      Integer.floor_div(dividend, divisor) * divisor + Integer.mod(dividend, divisor) === dividend

  def ceil_is_dual(dividend, divisor),
    do: Integer.ceil_div(dividend, divisor) === -Integer.floor_div(-dividend, divisor)

  def remainder_in_bounds(remainder, divisor) do
    if divisor > 0 do
      remainder >= 0 and remainder < divisor
    else
      remainder > divisor and remainder <= 0
    end
  end

  def zero_divisor_raises(dividend),
    do: mod_zero_raises(dividend) and floor_zero_raises(dividend) and ceil_zero_raises(dividend)

  def mod_zero_raises(dividend) do
    try do
      Integer.mod(dividend, 0)
      false
    catch
      :error, :badarith -> true
    end
  end

  def floor_zero_raises(dividend) do
    try do
      Integer.floor_div(dividend, 0)
      false
    catch
      :error, :badarith -> true
    end
  end

  def ceil_zero_raises(dividend) do
    try do
      Integer.ceil_div(dividend, 0)
      false
    catch
      :error, :badarith -> true
    end
  end

  # Private helpers have broader domains than the public API: popcount/2 can
  # diverge on negative inputs. Prove totality separately on each API's domain.
  @integer_fixpoint ~LEAN"""
  partial_fixpoint monotonicity by
    intro f g h
    repeat' first
      | exact Lean.Order.PartialOrder.rel_refl
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

  laws "Integer division" do
    law signed_division_contract(dividend, divisor),
      requires: is_integer(dividend) and is_integer(divisor) and divisor !== 0,
      expects: division_contract(dividend, divisor),
      proof: ~LEAN"""
      cases dividend <;> simp [«signed_division_contract:requires/2»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      cases divisor <;> simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«=/=/2»] at requires
      rename_i b
      have nonzero : b ≠ 0 := by simpa using requires
      have sign : b.sign = if b < 0 then -1 else 1 := by
        by_cases negative : b < 0
        · simp [negative, Int.sign_eq_neg_one_of_neg negative]
        · simp [negative, Int.sign_eq_one_of_pos (show 0 < b by omega)]
      have floor (a : Int) : Elixir.Integer.«floor_div/2» (.integer a) (.integer b) =
          .ok (.integer (a.fdiv b)) := by
        have divisible : b ∣ a ↔ a.tmod b = 0 := Int.dvd_iff_tmod_eq_zero
        by_cases aNeg : a < 0 <;> by_cases bNeg : b < 0 <;> by_cases zero : a.tmod b = 0 <;>
          simp [Elixir.Integer.«floor_div/2», Erlang.erlang.«xor/2»,
            Erlang.erlang.«rem/2», Erlang.erlang.«div/2», Erlang.erlang.«/=/2»,
            nonzero, aNeg, bNeg, zero, Int.fdiv_eq_tdiv, divisible,
            show (0 ≤ a) ↔ ¬ a < 0 by omega, show (0 ≤ b) ↔ ¬ b < 0 by omega,
            sign]
      have modulo : Elixir.Integer.«mod/2» (.integer a) (.integer b) =
          .ok (.integer (a.fmod b)) := by
        have divisible : b ∣ a ↔ a.tmod b = 0 := Int.dvd_iff_tmod_eq_zero
        by_cases aSign : 0 ≤ a
        · have remSign := Int.tmod_nonneg b aSign
          by_cases bSign : 0 ≤ b
          · have product : ¬ a.tmod b * b < 0 := by
              have := Int.mul_nonneg remSign bSign
              omega
            simp [Elixir.Integer.«mod/2», Erlang.erlang.«rem/2», nonzero,
              Int.fmod_eq_tmod, aSign, bSign, product]
          · have bNeg : b < 0 := by omega
            by_cases zero : a.tmod b = 0
            · simp [Elixir.Integer.«mod/2», Erlang.erlang.«rem/2», nonzero,
                Int.fmod_eq_tmod, aSign, bSign, zero, divisible]
            · have product : a.tmod b * b < 0 := Int.mul_neg_of_pos_of_neg (by omega) bNeg
              simp [Elixir.Integer.«mod/2», Erlang.erlang.«rem/2», nonzero,
                Int.fmod_eq_tmod, aSign, bSign, zero, divisible, product]
        · have remSign : a.tmod b ≤ 0 := by
            have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
            simpa using this
          by_cases bSign : 0 ≤ b
          · have bPos : 0 < b := by omega
            by_cases zero : a.tmod b = 0
            · simp [Elixir.Integer.«mod/2», Erlang.erlang.«rem/2», nonzero,
                Int.fmod_eq_tmod, aSign, bSign, zero, divisible]
            · have product : a.tmod b * b < 0 := Int.mul_neg_of_neg_of_pos (by omega) bPos
              simp [Elixir.Integer.«mod/2», Erlang.erlang.«rem/2», nonzero,
                Int.fmod_eq_tmod, aSign, bSign, zero, divisible, product,
                Int.natAbs_of_nonneg bSign]
          · have product : ¬ a.tmod b * b < 0 := by
              have := Int.mul_nonneg_of_nonpos_of_nonpos remSign (show b ≤ 0 by omega)
              omega
            simp [Elixir.Integer.«mod/2», Erlang.erlang.«rem/2», nonzero,
              Int.fmod_eq_tmod, aSign, bSign, product, Int.toNat_eq_zero.mpr (by omega : b ≤ 0)]
      have ceil : Elixir.Integer.«ceil_div/2» (.integer a) (.integer b) =
          .ok (.integer (-(-a).fdiv b)) := by
        rw [Int.neg_fdiv, Int.fdiv_eq_tdiv]
        have divisible : b ∣ a ↔ a.tmod b = 0 := Int.dvd_iff_tmod_eq_zero
        by_cases aNeg : a < 0 <;> by_cases bNeg : b < 0 <;> by_cases zero : a.tmod b = 0 <;>
          simp [Elixir.Integer.«ceil_div/2», Erlang.erlang.«xor/2», Erlang.erlang.«not/1»,
            Erlang.erlang.«rem/2», Erlang.erlang.«div/2», Erlang.erlang.«/=/2»,
            nonzero, aNeg, bNeg, zero, divisible, sign,
            show (0 ≤ a) ↔ ¬ a < 0 by omega, show (0 ≤ b) ↔ ¬ b < 0 by omega] <;> omega
      have reconstruction := Int.fdiv_mul_add_fmod a b
      by_cases positive : 0 < b
      · have lo := Int.fmod_nonneg_of_pos a positive
        have hi := Int.fmod_lt_of_pos a positive
        simp [«signed_division_contract:ensures/2», «division_contract/2», «division_reconstructs/2»,
          «ceil_is_dual/2», «remainder_in_bounds/2», Erlang.erlang.«-/1»,
          Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, floor,
          modulo, ceil, reconstruction, positive, lo, hi, Erlang.erlang.«=:=/2»]
      · have negative : b < 0 := by omega
        have lo := Int.fmod_nonneg_of_pos (-a) (show 0 < -b by omega)
        have hi := Int.fmod_lt_of_pos (-a) (show 0 < -b by omega)
        rw [Int.neg_fmod_neg] at lo hi
        simp [«signed_division_contract:ensures/2», «division_contract/2», «division_reconstructs/2»,
          «ceil_is_dual/2», «remainder_in_bounds/2», Erlang.erlang.«-/1»,
          Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, floor,
          modulo, ceil, reconstruction, positive, show b < a.fmod b by omega,
          show a.fmod b ≤ 0 by omega, Erlang.erlang.«=:=/2»]
      """

    law zero_divisor_raises_badarith(dividend),
      requires: is_integer(dividend),
      expects: zero_divisor_raises(dividend),
      proof: ~LEAN"""
      cases dividend <;> simp [«zero_divisor_raises_badarith:requires/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      by_cases negative : a < 0 <;>
        simp [«zero_divisor_raises_badarith:ensures/1», «zero_divisor_raises/1»,
          «mod_zero_raises/1», «floor_zero_raises/1», «ceil_zero_raises/1»,
          Elixir.Integer.«mod/2», Elixir.Integer.«floor_div/2», Elixir.Integer.«ceil_div/2»,
          Erlang.erlang.«rem/2», Erlang.erlang.«div/2», Erlang.erlang.«xor/2»,
          Erlang.erlang.«not/1», Lynx.Exception.classTerm, Lynx.Exception.reason, negative]
      """
  end

  def divides(divisor, integer) do
    if divisor === 0, do: integer === 0, else: rem(integer, divisor) === 0
  end

  def common_divisor_preserved(divisor, left, right, gcd) do
    if divides(divisor, left) and divides(divisor, right), do: divides(divisor, gcd), else: true
  end

  def gcd_contract(left, right, divisor) do
    gcd = Integer.gcd(left, right)

    gcd >= 0 and divides(gcd, left) and divides(gcd, right) and
      common_divisor_preserved(divisor, left, right, gcd)
  end

  def popcount_in_bounds(count, integer),
    do: is_integer(count) and count >= 0 and count <= integer and count === 0 === (integer === 0)

  laws "Integer recursion and parity" do
    termination_suffix &Integer.gcd_positive/2, @integer_fixpoint
    termination_suffix &Integer.popcount/2, @integer_fixpoint

    law gcd_characterization(left, right, divisor),
      requires: is_integer(left) and is_integer(right) and is_integer(divisor),
      expects: gcd_contract(left, right, divisor),
      proof: ~LEAN"""
      have model (a b : Nat) :
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
      have divides (d n : Int) : «divides/2» (.integer d) (.integer n) =
          .ok (if d ∣ n then Lynx.Term.true else Lynx.Term.false) := by
        by_cases zero : d = 0
        · subst d
          by_cases nZero : n = 0 <;>
            simp [«divides/2», Erlang.erlang.«=:=/2», nZero]
        · by_cases divisible : d ∣ n <;>
            simp [«divides/2», Erlang.erlang.«=:=/2», Erlang.erlang.«rem/2», zero,
              ← Int.dvd_iff_tmod_eq_zero, divisible]
      cases left <;> simp [«gcd_characterization:requires/3», Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      cases right <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i b
      cases divisor <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i d
      have returned : Elixir.Integer.«gcd/2» (.integer a) (.integer b) =
          .ok (.integer (Int.gcd a b)) := by
        simp [Elixir.Integer.«gcd/2», Erlang.erlang.«is_integer/1», Erlang.erlang.«abs/1»,
          Erlang.erlang.«=:=/2», model, Int.gcd_eq_natAbs_gcd_natAbs]
      have leftDivides := Int.gcd_dvd_left a b
      have rightDivides := Int.gcd_dvd_right a b
      by_cases da : d ∣ a <;> by_cases db : d ∣ b <;>
        simp [«gcd_characterization:ensures/3», «gcd_contract/3», returned,
          «common_divisor_preserved/4», Erlang.erlang.«=:=/2», divides, leftDivides, rightDivides, da, db,
          Int.dvd_coe_gcd]
      """

    law popcount_total_and_bounded(integer),
      requires: is_integer(integer) and integer >= 0,
      expects: popcount_in_bounds(Integer.popcount(integer), integer),
      proof: ~LEAN"""
      have count (n : Nat) (acc : Int) : ∃ bits : Nat, bits ≤ n ∧
          (bits = 0 ↔ n = 0) ∧
          Elixir.Integer.«popcount/2» (.integer n) (.integer acc) = .ok (.integer (acc + bits)) := by
        induction n using Nat.strongRecOn generalizing acc with
        | ind n ih =>
          by_cases zero : n = 0
          · subst n
            refine ⟨0, by omega, by simp, ?_⟩
            rw [Elixir.Integer.«popcount/2».eq_def]
            simp
          · have lower : n &&& (n - 1) < n := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
            obtain ⟨bits, bounded, _, returned⟩ := ih (n &&& (n - 1)) lower (acc + 1)
            refine ⟨bits + 1, by omega, by omega, ?_⟩
            rw [Elixir.Integer.«popcount/2».eq_def]
            have previous : (n : Int) - 1 = ((n - 1 : Nat) : Int) := by omega
            simp [zero, previous, Erlang.erlang.«band/2», returned, Int.add_assoc, Int.add_comm,
              Int.add_left_comm]
      cases integer <;> simp [«popcount_total_and_bounded:requires/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have nonnegative : 0 ≤ n := by
        by_cases h : 0 ≤ n <;> simp [h] at requires <;> omega
      obtain ⟨bits, bounded, zero, returned⟩ := count n.toNat 0
      have shape : (n.toNat : Int) = n := Int.toNat_of_nonneg nonnegative
      simp only [Int.zero_add, shape] at returned
      have upper : (bits : Int) ≤ n := by omega
      have bitsZero : ((bits : Int) = 0) ↔ n = 0 := by omega
      simp [«popcount_total_and_bounded:ensures/1», Elixir.Integer.«popcount/1»,
        Erlang.erlang.«is_integer/1», Erlang.erlang.«=:=/2», show ¬ n < 0 by omega,
        returned, «popcount_in_bounds/2», upper, bitsZero]
      all_goals split <;> simp_all [Erlang.erlang.«=:=/2»]
      """

    law parity_is_complementary(integer),
      requires: is_integer(integer),
      expects: Integer.is_even(integer) === not Integer.is_odd(integer),
      proof: ~LEAN"""
      cases integer <;> simp [«parity_is_complementary:requires/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      cases n with
      | ofNat n =>
        have mask : n &&& 1 = n % 2 := Nat.and_two_pow_sub_one_eq_mod n 1
        have bound : n % 2 < 2 := Nat.mod_lt n (by decide)
        have choices : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases choices with choice | choice <;>
          simp [«parity_is_complementary:ensures/1», Erlang.erlang.«is_integer/1»,
            Erlang.erlang.«band/2», mask, choice, Erlang.erlang.«==/2»,
            Erlang.erlang.«not/1», Erlang.erlang.«=:=/2»]
      | negSucc n =>
        have mask : 1 &&& n = n % 2 := by
          simpa [Nat.and_comm] using Nat.and_two_pow_sub_one_eq_mod n 1
        have bound : n % 2 < 2 := Nat.mod_lt n (by decide)
        have choices : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases choices with choice | choice <;>
          simp [«parity_is_complementary:ensures/1», Erlang.erlang.«is_integer/1»,
            Erlang.erlang.«band/2», mask, choice, Erlang.erlang.«==/2»,
            Erlang.erlang.«not/1», Erlang.erlang.«=:=/2»]
      """
  end
end
