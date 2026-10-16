# LYNX_PROFILE=1 LYNX_CACHE=0 elixir examples/deps/decimal.exs
# Prove a Hex dependency, translated from the BEAM debug information that Mix
# compiles by default. Mix.install/2 cannot run inside a Mix project, so this
# example runs with `elixir` and installs Lynx from this checkout.
# Checked against Decimal 3.2.0, Elixir 1.21.0-dev, Erlang/OTP 29.1.2.
# These proofs depend on implementation details; rerun after Decimal upgrades.
lynx = Path.expand("../..", __DIR__)

# Lynx builds its Lean library with the toolchain selected for the project
# directory. Mix.install/2 has none, so pin the checkout's toolchain.
System.put_env("ELAN_TOOLCHAIN", String.trim(File.read!(Path.join(lynx, "lean-toolchain"))))

Mix.install([
  {:lynx, path: lynx},
  {:decimal, "3.2.0"}
])

ExUnit.start()

defmodule DecimalProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def integer_order(left, right) when left < right, do: :lt
  def integer_order(left, right) when left > right, do: :gt
  def integer_order(_left, _right), do: :eq

  # compare/2 recurses only after coercing integers and strings with decimal/1.
  # The laws compare structs, so that coercion is cut off and the recursive
  # call sits behind an exhausted computation.
  @compare_fixpoint ~LEAN"""
  partial_fixpoint monotonicity by
    intro f g h
    simp only [«decimal/1», Lynx.Result.exhausted_bind]
    exact Lean.Order.PartialOrder.rel_refl
  """

  # Every input below is a finite struct, so compare/2 never coerces operands,
  # reaches NaN signals, or formats error messages. Decimals with equal
  # exponents never align coefficients or count their digits, and integer
  # decimals have a zero exponent, so to_integer/1 never strips trailing zeros.
  laws "Decimal integers and comparison" do
    cutoff &Decimal.decimal/1
    cutoff &Decimal.do_handle_error/4
    cutoff &Decimal.Error.exception/1
    cutoff &Decimal.parse/2
    cutoff &Decimal.pow10/1
    cutoff &Decimal.strip_trailing_zeros/2
    cutoff &Decimal.integer_decimal_digit_count/1
    cutoff &ArgumentError.exception/1
    cutoff &Kernel.inspect/1
    cutoff &:elixir_erl_pass.no_parens_remote/2
    termination_suffix &Decimal.compare/2, @compare_fixpoint

    law integer_round_trip(integer),
      requires: is_integer(integer),
      expects: Decimal.to_integer(Decimal.new(integer)) === integer,
      proof: ~LEAN"""
      cases integer <;> simp [«integer_round_trip:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      by_cases zero : n = 0
      · subst zero
        simp [«integer_round_trip:ensures/1», Elixir.Decimal.«new/1», Elixir.Decimal.«to_integer/1»,
          Erlang.erlang.«</2», Erlang.erlang.«abs/1», Erlang.erlang.«=:=/2», Lynx.Term.getMapKeys]
      · by_cases negative : n < 0 <;>
          simp [«integer_round_trip:ensures/1», Elixir.Decimal.«new/1», Elixir.Decimal.«to_integer/1»,
            Erlang.erlang.«</2», Int.compare_eq_lt, Erlang.erlang.«abs/1», Erlang.erlang.«=:=/2»,
            Lynx.Term.getMapKeys, zero, negative] <;> omega
      """

    law integer_compare(left, right),
      requires: is_integer(left) and is_integer(right),
      expects:
        Decimal.compare(Decimal.new(left), Decimal.new(right)) === integer_order(left, right),
      proof: ~LEAN"""
      cases left <;> cases right <;>
        simp [«integer_compare:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a b
      have created (n : Int) : Elixir.Decimal.«new/1» (.integer n) = .ok (.map [
          (.atom "coef", .integer (if n < 0 then -n else n)),
          (.atom "sign", .integer (if n < 0 then -1 else 1)),
          (.atom "exp", .integer 0), (.atom "__struct__", .atom "Elixir.Decimal")]) := by
        by_cases negative : n < 0 <;>
          simp [Elixir.Decimal.«new/1», Erlang.erlang.«</2», Int.compare_eq_lt,
            Erlang.erlang.«abs/1», Lynx.Term.getMapKeys, negative] <;> omega
      simp only [«integer_compare:ensures/2», created, Lynx.Result.ok_bind]
      rw [Elixir.Decimal.«compare/2».eq_def]
      rcases Int.lt_trichotomy a 0 with ha | ha | ha <;>
        rcases Int.lt_trichotomy b 0 with hb | hb | hb <;>
        (try have ha0 : a ≠ 0 := by omega) <;>
        (try have hb0 : b ≠ 0 := by omega) <;>
        (try have ha1 : ¬ a < 0 := by omega) <;>
        (try have hb1 : ¬ b < 0 := by omega) <;>
        (try have ha2 : ¬ 0 < a := by omega) <;>
        (try have hb2 : ¬ 0 < b := by omega) <;>
        simp [Lynx.Term.getMapKeys, «integer_order/2», Erlang.erlang.«=:=/2», Erlang.erlang.«==/2»,
          Erlang.erlang.«</2», Erlang.erlang.«>/2», Int.compare_eq_lt, Int.compare_eq_gt,
          Ordering.isLT_iff_eq_lt, Ordering.isGT_iff_eq_gt, *]
      all_goals
        by_cases lt : a < b <;> by_cases gt : b < a <;>
          first | omega | simp [lt, gt, show b = a ↔ ¬ a < b ∧ ¬ b < a by omega]
      """

    law same_exponent_compare(sign1, coef1, sign2, coef2, exp),
      requires:
        is_integer(coef1) and coef1 >= 0 and is_integer(coef2) and coef2 >= 0 and
          is_integer(exp) and sign1 in [1, -1] and sign2 in [1, -1],
      expects:
        Decimal.compare(Decimal.new(sign1, coef1, exp), Decimal.new(sign2, coef2, exp)) ===
          integer_order(sign1 * coef1, sign2 * coef2),
      proof: ~LEAN"""
      have created (s c e : Int) (sign : s = 1 ∨ s = -1) (nonneg : 0 ≤ c) :
          Elixir.Decimal.«new/3» (.integer s) (.integer c) (.integer e) = .ok (.map [
            (.atom "exp", .integer e), (.atom "coef", .integer c), (.atom "sign", .integer s),
            (.atom "__struct__", .atom "Elixir.Decimal")]) := by
        rcases sign with rfl | rfl <;>
          simp [Elixir.Decimal.«new/3», Erlang.erlang.«=:=/2», Erlang.erlang.«is_integer/1»,
            Erlang.erlang.«>=/2», Int.isGE_compare, nonneg]
      cases coef1 <;> simp [«same_exponent_compare:requires/5», Erlang.erlang.«is_integer/1»,
        Erlang.erlang.«>=/2», Int.isGE_compare] at requires
      rename_i c1
      have nonneg1 : 0 ≤ c1 := by
        by_cases nonneg : 0 ≤ c1
        · exact nonneg
        · simp [nonneg] at requires
      cases coef2 <;> simp [Erlang.erlang.«is_integer/1», Int.isGE_compare, nonneg1] at requires
      rename_i c2
      have nonneg2 : 0 ≤ c2 := by
        by_cases nonneg : 0 ≤ c2
        · exact nonneg
        · simp [nonneg] at requires
      cases exp <;> simp [Erlang.erlang.«is_integer/1», Int.isGE_compare, nonneg2] at requires
      rename_i e
      cases sign1 <;> simp [Erlang.erlang.«=:=/2»] at requires
      rename_i s1
      have sign1 : s1 = 1 ∨ s1 = -1 := by
        by_cases valid : s1 = 1 ∨ s1 = -1
        · exact valid
        · simp [show s1 ≠ 1 by omega, show s1 ≠ -1 by omega] at requires
      rcases sign1 with rfl | rfl
      all_goals
        cases sign2 <;> simp [Erlang.erlang.«=:=/2»] at requires
        rename_i s2
        have sign2 : s2 = 1 ∨ s2 = -1 := by
          by_cases valid : s2 = 1 ∨ s2 = -1
          · exact valid
          · simp [show s2 ≠ 1 by omega, show s2 ≠ -1 by omega] at requires
        rcases sign2 with rfl | rfl
      all_goals
        simp only [«same_exponent_compare:ensures/5»]
        simp [created, nonneg1, nonneg2]
        rw [Elixir.Decimal.«compare/2».eq_def]
        rcases (show c1 = 0 ∨ 0 < c1 by omega) with z1 | p1 <;>
          rcases (show c2 = 0 ∨ 0 < c2 by omega) with z2 | p2 <;>
          (try have n1 : c1 ≠ 0 := by omega) <;>
          (try have n2 : c2 ≠ 0 := by omega) <;>
          simp [Lynx.Term.getMapKeys, «integer_order/2», Erlang.erlang.«=:=/2»,
            Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», Int.compare_eq_lt,
            Int.compare_eq_gt, Ordering.isLT_iff_eq_lt, Ordering.isGT_iff_eq_gt, *]
      all_goals
        repeat' split
        all_goals first | omega | (simp_all <;> omega)
      """
  end
end
