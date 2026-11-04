# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/ackermann.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true:
#
#   * c/recursive/Ackermann01-2.yml and java/jayhorn-recursive/SatAckermann01.yml:
#     m, n in 0..3 and 0..23, asserting ackermann(m, n) >= 0. Law ackermann01_2.
#   * c/recursive/Ackermann03.yml and java/jayhorn-recursive/SatAckermann02.yml:
#     same domain, asserting ackermann(2, 2) == 7. Law ackermann03.
#   * c/recursive/Ackermann04.yml and java/jayhorn-recursive/SatAckermann03.yml:
#     same domain, asserting m < 2 or n < 2 or ackermann(m, n) >= 7. Law ackermann04.
#
# The bounds avoid int32 overflow. The laws hold for all non-negative integers,
# and ackermann03 and ackermann04 generalize to ackermann(2, n) == 2 * n + 3 and
# ackermann(m, n) >= 2 * n + 3 for m >= 2. Negative inputs diverge, as in C.
ExUnit.start()

defmodule SVBench.AckermannTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def ackermann(0, n), do: n + 1
  def ackermann(m, 0), do: ackermann(m - 1, 1)
  def ackermann(m, n), do: ackermann(m - 1, ackermann(m, n - 1))

  laws "Ackermann" do
    termination_suffix &__MODULE__.ackermann/2, ~LEAN"partial_fixpoint"

    prelude ~LEAN"""
    module
    public import Lynx
    public section

    namespace SVBench.Ackermann

    /-- The Ackermann function over natural numbers, structural in both arguments
    so that its equations hold by definition. -/
    @[expose] noncomputable def ack : Nat → Nat → Nat
      | 0, n => n + 1
      | m + 1, n => Nat.rec (motive := fun _ => Nat) (ack m 1) (fun _ r => ack m r) n

    theorem ack_zero (n : Nat) : ack 0 n = n + 1 := rfl
    theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := rfl
    theorem ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := rfl

    theorem lt_ack : ∀ m n, n < ack m n
      | 0, n => by rw [ack_zero]; omega
      | m + 1, 0 => by have := lt_ack m 1; rw [ack_succ_zero]; omega
      | m + 1, n + 1 => by
        have inner := lt_ack (m + 1) n
        have outer := lt_ack m (ack (m + 1) n)
        rw [ack_succ_succ]; omega

    theorem ack_lt_succ (m n : Nat) : ack m n < ack m (n + 1) := by
      cases m with
      | zero => rw [ack_zero, ack_zero]; omega
      | succ m => rw [ack_succ_succ]; exact lt_ack m (ack (m + 1) n)

    theorem ack_mono (m : Nat) {n n' : Nat} (le : n ≤ n') : ack m n ≤ ack m n' := by
      induction le with
      | refl => exact Nat.le_refl _
      | step _ ih => exact Nat.le_trans ih (Nat.le_of_lt (ack_lt_succ _ _))

    theorem ack_succ_le : ∀ m n, ack m (n + 1) ≤ ack (m + 1) n
      | m, 0 => by rw [ack_succ_zero]; exact Nat.le_refl _
      | m, n + 1 => by
        have bound : n + 2 ≤ ack (m + 1) n := by
          have := ack_succ_le m n; have := lt_ack m (n + 1); omega
        rw [ack_succ_succ]; exact ack_mono m bound

    theorem ack_le_succ_left (m n : Nat) : ack m n ≤ ack (m + 1) n :=
      Nat.le_trans (Nat.le_of_lt (ack_lt_succ m n)) (ack_succ_le m n)

    theorem ack_two (n : Nat) : ack 2 n = 2 * n + 3 := by
      have one (n : Nat) : ack 1 n = n + 2 := by
        induction n with
        | zero => rfl
        | succ n ih =>
          have step : ack 1 (n + 1) = ack 1 n + 1 := by rw [ack_succ_succ 0 n, ack_zero]
          omega
      induction n with
      | zero => rfl
      | succ n ih =>
        have step : ack 2 (n + 1) = ack 1 (ack 2 n) := by rw [ack_succ_succ 1 n]
        rw [step, one]; omega

    theorem ack_ge (m n : Nat) (two : 2 ≤ m) : 2 * n + 3 ≤ ack m n := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le two
      clear two
      induction k with
      | zero => simp [ack_two]
      | succ k ih => exact Nat.le_trans ih (ack_le_succ_left (2 + k) n)

    end SVBench.Ackermann
    """

    law ackermann01_2(m, n),
      requires: is_integer(m) and m >= 0 and is_integer(n) and n >= 0,
      expects: ackermann(m, n) >= 0,
      proof: ~LEAN"""
      open SVBench.Ackermann in
      have bridge (m : Nat) : ∀ n : Nat,
          «ackermann/2» (.integer m) (.integer n) = .ok (.integer (ack m n)) := by
        induction m with
        | zero => intro n; rw [«ackermann/2».eq_def]; simp [ack_zero]
        | succ m outer =>
          intro n
          induction n with
          | zero =>
            have := outer 1
            rw [«ackermann/2».eq_def]
            split <;> simp_all [ack_succ_zero] <;> omega
          | succ n inner =>
            have := outer (ack (m + 1) n)
            rw [«ackermann/2».eq_def]
            split <;> simp_all [ack_succ_succ] <;> omega
      cases m <;> simp [«ackermann01_2:requires/2», Erlang.erlang.«is_integer/1»] at requires
      cases n <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i m n
      have returned := bridge m.toNat n.toNat
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at returned
      simp [«ackermann01_2:ensures/2», returned]
      """

    law ackermann03(n),
      requires: is_integer(n) and n >= 0,
      expects: ackermann(2, n) == 2 * n + 3,
      proof: ~LEAN"""
      open SVBench.Ackermann in
      have bridge (m : Nat) : ∀ n : Nat,
          «ackermann/2» (.integer m) (.integer n) = .ok (.integer (ack m n)) := by
        induction m with
        | zero => intro n; rw [«ackermann/2».eq_def]; simp [ack_zero]
        | succ m outer =>
          intro n
          induction n with
          | zero =>
            have := outer 1
            rw [«ackermann/2».eq_def]
            split <;> simp_all [ack_succ_zero] <;> omega
          | succ n inner =>
            have := outer (ack (m + 1) n)
            rw [«ackermann/2».eq_def]
            split <;> simp_all [ack_succ_succ] <;> omega
      cases n <;> simp [«ackermann03:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have returned : «ackermann/2» (.integer 2) (.integer n) = .ok (.integer (2 * n + 3)) := by
        have model := bridge 2 n.toNat
        rw [SVBench.Ackermann.ack_two] at model
        simpa [Int.toNat_of_nonneg requires] using model
      simp [«ackermann03:ensures/1», returned]
      """

    law ackermann04(m, n),
      requires: is_integer(m) and m >= 0 and is_integer(n) and n >= 0,
      expects: m < 2 or ackermann(m, n) >= 2 * n + 3,
      proof: ~LEAN"""
      open SVBench.Ackermann in
      have bridge (m : Nat) : ∀ n : Nat,
          «ackermann/2» (.integer m) (.integer n) = .ok (.integer (ack m n)) := by
        induction m with
        | zero => intro n; rw [«ackermann/2».eq_def]; simp [ack_zero]
        | succ m outer =>
          intro n
          induction n with
          | zero =>
            have := outer 1
            rw [«ackermann/2».eq_def]
            split <;> simp_all [ack_succ_zero] <;> omega
          | succ n inner =>
            have := outer (ack (m + 1) n)
            rw [«ackermann/2».eq_def]
            split <;> simp_all [ack_succ_succ] <;> omega
      cases m <;> simp [«ackermann04:requires/2», Erlang.erlang.«is_integer/1»] at requires
      cases n <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i m n
      have returned := bridge m.toNat n.toNat
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at returned
      by_cases small : m < 2
      · simp [«ackermann04:ensures/2», small]
      · have bound := SVBench.Ackermann.ack_ge m.toNat n.toNat (by omega)
        simp [«ackermann04:ensures/2», small, returned]
        omega
      """
  end
end
