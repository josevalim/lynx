# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/fibonacci.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true:
#
#   * c/recursive/Fibonacci01-1.yml and java/jayhorn-recursive/SatFibonacci01.yml:
#     int x with x <= 46 and x != INT_MIN, asserting fibonacci(x) >= x - 1.
#   * c/recursive/Fibonacci02.yml and java/jayhorn-recursive/SatFibonacci02.yml:
#     asserting fibonacci(9) == 34.
#   * c/recursive/Fibonacci03.yml and java/jayhorn-recursive/SatFibonacci03.yml:
#     int x with x <= 46, asserting x < 9 || fibonacci(x) >= 34.
#
# The Java tasks are the same programs as their C counterparts. The bounds only
# avoid int32 overflow, so the laws hold for every integer.
ExUnit.start()

defmodule SVBench.FibonacciTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def fibonacci(n) when n < 1, do: 0
  def fibonacci(1), do: 1
  def fibonacci(n), do: fibonacci(n - 1) + fibonacci(n - 2)

  laws "Fibonacci" do
    termination_suffix &__MODULE__.fibonacci/1, ~LEAN"partial_fixpoint"

    prelude ~LEAN"""
    module

    public import Lynx

    public section

    namespace FibonacciProof

    /-- The Fibonacci numbers the translated function computes on naturals. -/
    @[expose] def fibNat : Nat → Nat
      | 0 => 0
      | 1 => 1
      | n + 2 => fibNat (n + 1) + fibNat n

    theorem fibNat_pos (n : Nat) (positive : 1 ≤ n) : 1 ≤ fibNat n := by
      induction n using fibNat.induct with
      | case1 => omega
      | case2 => simp [fibNat]
      | case3 n ih _ =>
        simp only [fibNat]
        have := ih (by omega)
        omega

    theorem fibNat_mono {n m : Nat} (le : n ≤ m) : fibNat n ≤ fibNat m := by
      induction le with
      | refl => exact Nat.le_refl _
      | step _ ih =>
        rename_i k _
        refine Nat.le_trans ih ?_
        cases k with
        | zero => simp [fibNat]
        | succ k => simp only [fibNat]; omega

    theorem fibNat_ge (n : Nat) : n ≤ fibNat n + 1 := by
      induction n using fibNat.induct with
      | case1 => simp [fibNat]
      | case2 => simp [fibNat]
      | case3 n ih _ =>
        simp only [fibNat]
        cases n with
        | zero => simp [fibNat]
        | succ n =>
          have := fibNat_pos (n + 1) (by omega)
          simp only [fibNat] at ih ⊢
          omega

    end FibonacciProof
    """

    law fibonacci01_1(x),
      requires: is_integer(x),
      expects: fibonacci(x) >= x - 1,
      proof: ~LEAN"""
      have below (n : Int) (low : n < 1) :
          «fibonacci/1» (.integer n) = .ok (.integer 0) := by
        rw [«fibonacci/1».eq_def]
        simp [low]
      have bridge (k : Nat) :
          «fibonacci/1» (.integer k) = .ok (.integer (FibonacciProof.fibNat k)) := by
        induction k using FibonacciProof.fibNat.induct with
        | case1 => simpa [FibonacciProof.fibNat] using below 0 (by omega)
        | case2 => rw [«fibonacci/1».eq_def]; simp [FibonacciProof.fibNat]
        | case3 k next previous =>
          rw [«fibonacci/1».eq_def]
          simp only [Lynx.Except.guard_eq, Erlang.erlang.«</2_integers», Lynx.Except.tryWith_ok,
            show ¬ ((k + 2 : Nat) : Int) < 1 by omega, if_false, Lynx.Term.false]
          split
          · rename_i one; simp at one
          · push_cast at next previous
            simp [show (k : Int) + 1 + 1 - 2 = k by omega, next, previous, FibonacciProof.fibNat]
      cases x <;> simp [«fibonacci01_1:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i x
      by_cases low : x < 1
      · simp [«fibonacci01_1:ensures/1», below x low]
        omega
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x by omega)
        have := FibonacciProof.fibNat_ge k
        simp [«fibonacci01_1:ensures/1», bridge k]
        omega
      """

    law fibonacci02,
      expects: fibonacci(9) == 34,
      proof: ~LEAN"""
      have below (n : Int) (low : n < 1) :
          «fibonacci/1» (.integer n) = .ok (.integer 0) := by
        rw [«fibonacci/1».eq_def]
        simp [low]
      have bridge (k : Nat) :
          «fibonacci/1» (.integer k) = .ok (.integer (FibonacciProof.fibNat k)) := by
        induction k using FibonacciProof.fibNat.induct with
        | case1 => simpa [FibonacciProof.fibNat] using below 0 (by omega)
        | case2 => rw [«fibonacci/1».eq_def]; simp [FibonacciProof.fibNat]
        | case3 k next previous =>
          rw [«fibonacci/1».eq_def]
          simp only [Lynx.Except.guard_eq, Erlang.erlang.«</2_integers», Lynx.Except.tryWith_ok,
            show ¬ ((k + 2 : Nat) : Int) < 1 by omega, if_false, Lynx.Term.false]
          split
          · rename_i one; simp at one
          · push_cast at next previous
            simp [show (k : Int) + 1 + 1 - 2 = k by omega, next, previous, FibonacciProof.fibNat]
      have nine : «fibonacci/1» (.integer 9) = .ok (.integer 34) := bridge 9
      simp [«fibonacci02:ensures/0», nine]
      """

    law fibonacci03(x),
      requires: is_integer(x),
      expects: x < 9 or fibonacci(x) >= 34,
      proof: ~LEAN"""
      have below (n : Int) (low : n < 1) :
          «fibonacci/1» (.integer n) = .ok (.integer 0) := by
        rw [«fibonacci/1».eq_def]
        simp [low]
      have bridge (k : Nat) :
          «fibonacci/1» (.integer k) = .ok (.integer (FibonacciProof.fibNat k)) := by
        induction k using FibonacciProof.fibNat.induct with
        | case1 => simpa [FibonacciProof.fibNat] using below 0 (by omega)
        | case2 => rw [«fibonacci/1».eq_def]; simp [FibonacciProof.fibNat]
        | case3 k next previous =>
          rw [«fibonacci/1».eq_def]
          simp only [Lynx.Except.guard_eq, Erlang.erlang.«</2_integers», Lynx.Except.tryWith_ok,
            show ¬ ((k + 2 : Nat) : Int) < 1 by omega, if_false, Lynx.Term.false]
          split
          · rename_i one; simp at one
          · push_cast at next previous
            simp [show (k : Int) + 1 + 1 - 2 = k by omega, next, previous, FibonacciProof.fibNat]
      cases x <;> simp [«fibonacci03:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i x
      by_cases small : x < 9
      · simp [«fibonacci03:ensures/1», small]
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x by omega)
        have := FibonacciProof.fibNat_mono (show 9 ≤ k by omega)
        rw [show FibonacciProof.fibNat 9 = 34 by rfl] at this
        simp [«fibonacci03:ensures/1», bridge k, small]
        omega
      """
  end
end
