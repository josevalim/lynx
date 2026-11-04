# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/even_odd.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true:
#
#   * c/recursive/EvenOdd01-1.yml and java/jayhorn-recursive/SatEvenOdd01.yml:
#     int n with n >= 0, asserting result < 0 or isOdd(n) == n % 2. Law evenodd01_1.
#
# The law holds for all non-negative integers, as the stronger equality
# odd?(n) == rem(n, 2). Negative inputs diverge, as in C and Java.
ExUnit.start()

defmodule SVBench.EvenOddTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def odd?(0), do: 0
  def odd?(1), do: 1
  def odd?(n), do: even?(n - 1)

  def even?(0), do: 1
  def even?(1), do: 0
  def even?(n), do: odd?(n - 1)

  laws "EvenOdd" do
    termination_suffix &__MODULE__.odd?/1, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.even?/1, ~LEAN"partial_fixpoint"

    law evenodd01_1(n),
      requires: is_integer(n) and n >= 0,
      expects: odd?(n) == rem(n, 2),
      proof: ~LEAN"""
      have parity (k : Nat) :
          «odd?/1» (.integer k) = .ok (.integer (k % 2)) ∧
            «even?/1» (.integer k) = .ok (.integer (1 - k % 2)) := by
        induction k with
        | zero => constructor <;> (first | rw [«odd?/1».eq_def] | rw [«even?/1».eq_def]) <;> simp
        | succ k ih =>
          constructor
          · rw [«odd?/1».eq_def]
            split <;> simp_all <;> omega
          · rw [«even?/1».eq_def]
            split <;> simp_all <;> omega
      cases n <;> simp [«evenodd01_1:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      by_cases n0 : 0 ≤ n <;> simp [n0] at requires
      have returned := (parity n.toNat).1
      rw [Int.toNat_of_nonneg n0] at returned
      simp [«evenodd01_1:ensures/1», returned, Erlang.erlang.«rem/2»,
        Int.tmod_eq_emod_of_nonneg n0]
      """
  end
end
