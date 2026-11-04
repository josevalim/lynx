# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/hanoi.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true,
# all with int n bounded to 1..31 to avoid int32 overflow:
#
#   * c/recursive/recHanoi01.yml and java/jayhorn-recursive/SatHanoi01.yml,
#     asserting that hanoi(n) equals the moves counted by applyHanoi. The Java
#     task is the same program. The global move counter is returned instead.
#   * c/recursive/recHanoi02-2.yml, asserting hanoi(n) >= 0.
#   * c/recursive/recHanoi03-2.yml, asserting hanoi(n) >= n.
#
# The laws hold for every n >= 1. hanoi(n) diverges for n < 1.
ExUnit.start()

defmodule SVBench.HanoiTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def hanoi(1), do: 1
  def hanoi(n), do: 2 * hanoi(n - 1) + 1

  def apply_hanoi(0, _from, _to, _via), do: 0

  def apply_hanoi(n, from, to, via) do
    1 + apply_hanoi(n - 1, from, via, to) + apply_hanoi(n - 1, via, to, from)
  end

  laws "Hanoi" do
    termination_suffix &__MODULE__.hanoi/1, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.apply_hanoi/4, ~LEAN"partial_fixpoint"

    prelude ~LEAN"""
    module

    public import Lynx

    public section

    namespace HanoiProof

    theorem moves_ge (k : Nat) : (k : Int) + 2 ≤ 2 ^ (k + 1) := by
      induction k with
      | zero => decide
      | succ k ih => rw [Int.pow_succ]; omega

    end HanoiProof
    """

    law rec_hanoi01(n),
      requires: is_integer(n) and n >= 1,
      expects: hanoi(n) == apply_hanoi(n, 1, 3, 2),
      proof: ~LEAN"""
      have hanoi (k : Nat) :
          «hanoi/1» (.integer ((k : Int) + 1)) = .ok (.integer (2 ^ (k + 1) - 1)) := by
        induction k with
        | zero => rw [«hanoi/1».eq_def]; rfl
        | succ k ih =>
          rw [«hanoi/1».eq_def]
          split
          · simp_all <;> omega
          · simp [show ((k + 1 : Nat) : Int) + 1 - 1 = (k : Int) + 1 by omega, ih, Int.pow_succ]
            omega
      have moves (k : Nat) : ∀ source target via,
          «apply_hanoi/4» (.integer k) source target via = .ok (.integer (2 ^ k - 1)) := by
        induction k with
        | zero => intro source target via; rw [«apply_hanoi/4».eq_def]; rfl
        | succ k ih =>
          intro source target via
          rw [«apply_hanoi/4».eq_def]
          split
          · simp_all <;> omega
          · simp [ih, Int.pow_succ]
            omega
      cases n <;> simp [«rec_hanoi01:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have h := hanoi (n - 1).toNat
      have m := moves n.toNat (.integer 1) (.integer 3) (.integer 2)
      rw [show (((n - 1).toNat : Nat) : Int) + 1 = n by omega, show (n - 1).toNat + 1 = n.toNat by omega] at h
      rw [Int.toNat_of_nonneg (by omega)] at m
      simp [«rec_hanoi01:ensures/1», h, m]
      """

    law rec_hanoi02_2(n),
      requires: is_integer(n) and n >= 1,
      expects: hanoi(n) >= 0,
      proof: ~LEAN"""
      have hanoi (k : Nat) :
          «hanoi/1» (.integer ((k : Int) + 1)) = .ok (.integer (2 ^ (k + 1) - 1)) := by
        induction k with
        | zero => rw [«hanoi/1».eq_def]; rfl
        | succ k ih =>
          rw [«hanoi/1».eq_def]
          split
          · simp_all <;> omega
          · simp [show ((k + 1 : Nat) : Int) + 1 - 1 = (k : Int) + 1 by omega, ih, Int.pow_succ]
            omega
      cases n <;> simp [«rec_hanoi02_2:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have h := hanoi (n - 1).toNat
      rw [show (((n - 1).toNat : Nat) : Int) + 1 = n by omega,
        show (n - 1).toNat + 1 = n.toNat by omega] at h
      have := HanoiProof.moves_ge (n - 1).toNat
      rw [show (n - 1).toNat + 1 = n.toNat by omega] at this
      simp [«rec_hanoi02_2:ensures/1», h]
      omega
      """

    law rec_hanoi03_2(n),
      requires: is_integer(n) and n >= 1,
      expects: hanoi(n) >= n,
      proof: ~LEAN"""
      have hanoi (k : Nat) :
          «hanoi/1» (.integer ((k : Int) + 1)) = .ok (.integer (2 ^ (k + 1) - 1)) := by
        induction k with
        | zero => rw [«hanoi/1».eq_def]; rfl
        | succ k ih =>
          rw [«hanoi/1».eq_def]
          split
          · simp_all <;> omega
          · simp [show ((k + 1 : Nat) : Int) + 1 - 1 = (k : Int) + 1 by omega, ih, Int.pow_succ]
            omega
      cases n <;> simp [«rec_hanoi03_2:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have h := hanoi (n - 1).toNat
      rw [show (((n - 1).toNat : Nat) : Int) + 1 = n by omega,
        show (n - 1).toNat + 1 = n.toNat by omega] at h
      have := HanoiProof.moves_ge (n - 1).toNat
      rw [show (n - 1).toNat + 1 = n.toNat by omega] at this
      simp [«rec_hanoi03_2:ensures/1», h]
      omega
      """
  end
end
