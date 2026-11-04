# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/addition.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true:
#
#   * c/recursive/Addition01-2.yml: m, n in 0..1073741823, asserting
#     addition(m, n) == m + n. Law addition01_2, which also covers
#     java/jayhorn-recursive/Addition.yml (m, n in 0..9999) and
#     java/jayhorn-recursive/SatAddition01.yml (m, n in 0..2147483647), both
#     asserting the same.
#   * c/recursive/Addition03-1.yml: m, n any int, with long long arithmetic,
#     asserting m < 100 or n < 100 or addition(m, n) >= 200. Law addition03_1.
#
# The bounds avoid overflow. Both laws hold for all integers.
ExUnit.start()

defmodule SVBench.AdditionTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def addition(m, 0), do: m
  def addition(m, n) when n > 0, do: addition(m + 1, n - 1)
  def addition(m, n), do: addition(m - 1, n + 1)

  laws "Addition" do
    termination_suffix &__MODULE__.addition/2, ~LEAN"partial_fixpoint"

    law addition01_2(m, n),
      requires: is_integer(m) and is_integer(n),
      expects: addition(m, n) == m + n,
      proof: ~LEAN"""
      have up (k : Nat) : ∀ m : Int,
          «addition/2» (.integer m) (.integer k) = .ok (.integer (m + k)) := by
        induction k with
        | zero => intro m; rw [«addition/2».eq_def]; simp
        | succ k ih =>
          intro m
          rw [«addition/2».eq_def]
          split <;> simp_all [Lynx.Except.guard, show (0 : Int) < k + 1 by omega] <;> omega
      have down (k : Nat) : ∀ m : Int,
          «addition/2» (.integer m) (.integer (-k)) = .ok (.integer (m - k)) := by
        induction k with
        | zero => intro m; rw [«addition/2».eq_def]; simp
        | succ k ih =>
          intro m
          rw [«addition/2».eq_def]
          have step := ih (m - 1)
          split <;> simp_all [Lynx.Except.guard, show ¬ (k : Int) + 1 < 0 by omega,
            show -((k : Int) + 1) + 1 = -k by omega] <;> omega
      have total (m n : Int) : «addition/2» (.integer m) (.integer n) = .ok (.integer (m + n)) := by
        by_cases nonneg : 0 ≤ n
        · simpa [Int.toNat_of_nonneg nonneg] using up n.toNat m
        · simpa [show ((-n).toNat : Int) = -n by omega, Int.sub_eq_add_neg] using down (-n).toNat m
      cases m <;> simp [«addition01_2:requires/2», Erlang.erlang.«is_integer/1»] at requires
      cases n <;> simp [Erlang.erlang.«is_integer/1»] at requires
      simp [«addition01_2:ensures/2», total]
      """

    law addition03_1(m, n),
      requires: is_integer(m) and is_integer(n),
      expects: m < 100 or n < 100 or addition(m, n) >= 200,
      proof: ~LEAN"""
      have up (k : Nat) : ∀ m : Int,
          «addition/2» (.integer m) (.integer k) = .ok (.integer (m + k)) := by
        induction k with
        | zero => intro m; rw [«addition/2».eq_def]; simp
        | succ k ih =>
          intro m
          rw [«addition/2».eq_def]
          split <;> simp_all [Lynx.Except.guard, show (0 : Int) < k + 1 by omega] <;> omega
      have down (k : Nat) : ∀ m : Int,
          «addition/2» (.integer m) (.integer (-k)) = .ok (.integer (m - k)) := by
        induction k with
        | zero => intro m; rw [«addition/2».eq_def]; simp
        | succ k ih =>
          intro m
          rw [«addition/2».eq_def]
          have step := ih (m - 1)
          split <;> simp_all [Lynx.Except.guard, show ¬ (k : Int) + 1 < 0 by omega,
            show -((k : Int) + 1) + 1 = -k by omega] <;> omega
      have total (m n : Int) : «addition/2» (.integer m) (.integer n) = .ok (.integer (m + n)) := by
        by_cases nonneg : 0 ≤ n
        · simpa [Int.toNat_of_nonneg nonneg] using up n.toNat m
        · simpa [show ((-n).toNat : Int) = -n by omega, Int.sub_eq_add_neg] using down (-n).toNat m
      cases m <;> simp [«addition03_1:requires/2», Erlang.erlang.«is_integer/1»] at requires
      cases n <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i m n
      by_cases small : m < 100 ∨ n < 100
      · rcases small with small | small <;> simp [«addition03_1:ensures/2», small]
      · simp [«addition03_1:ensures/2», total]
        omega
      """
  end
end
