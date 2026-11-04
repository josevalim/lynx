# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/mult_commutative.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true:
#
#   * c/recursive/MultCommutative-2.yml and
#     java/jayhorn-recursive/SatMultCommutative01.yml: m, n in 0..46340, asserting
#     not (mult(m, n) != mult(n, m) and m > 0 and n > 0). Law mult_commutative_2.
#
# The bounds avoid int32 overflow; the law holds for all integers.
ExUnit.start()

defmodule SVBench.MultCommutativeTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def mult(n, m) when m < 0, do: mult(n, -m)
  def mult(_n, 0), do: 0
  def mult(n, m), do: n + mult(n, m - 1)

  laws "MultCommutative" do
    termination_suffix &__MODULE__.mult/2, ~LEAN"partial_fixpoint"

    law mult_commutative_2(m, n),
      requires: is_integer(m) and is_integer(n),
      expects: not (mult(m, n) != mult(n, m) and m > 0 and n > 0),
      proof: ~LEAN"""
      have mult (a : Int) (k : Nat) :
          «mult/2» (.integer a) (.integer k) = .ok (.integer (a * k)) := by
        induction k with
        | zero => rw [«mult/2».eq_def]; simp [Lynx.Except.guard]
        | succ k ih =>
          rw [«mult/2».eq_def]
          simp only [Lynx.Except.guard, Erlang.erlang.«</2_integers», if_neg (show ¬ (k : Int) + 1 < 0 by omega)]
          split
          · omega
          · simp [ih, Int.mul_add, Int.add_comm]
      have total (a b : Int) : «mult/2» (.integer a) (.integer b) = .ok (.integer (a * b.natAbs)) := by
        by_cases nonneg : 0 ≤ b
        · simpa [Int.natAbs_of_nonneg nonneg] using mult a b.natAbs
        · rw [«mult/2».eq_def]
          simp [Lynx.Except.guard, show b < 0 by omega, Erlang.erlang.«-/1»]
          simpa [show (-b : Int) = (b.natAbs : Int) by omega] using mult a b.natAbs
      cases m <;> cases n <;> simp [«mult_commutative_2:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a b
      by_cases positive : 0 < a ∧ 0 < b
      · simp [«mult_commutative_2:ensures/2», total,
          Int.natAbs_of_nonneg (show 0 ≤ a by omega), Int.natAbs_of_nonneg (show 0 ≤ b by omega),
          Int.mul_comm]
      · simp [«mult_commutative_2:ensures/2», total]
        (repeat' split) <;> simp_all <;> omega
      """
  end
end
