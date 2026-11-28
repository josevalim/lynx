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

    prelude "ackermann/prelude"

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
      cases n <;> simp at requires
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
      cases n <;> simp at requires
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
