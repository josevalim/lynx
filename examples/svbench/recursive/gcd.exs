# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/gcd.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true:
#
#   * c/recursive/gcd01-1.yml and java/jayhorn-recursive/SatGcd.yml: int m, n with
#     0 < m <= 2147483647 and 0 < n <= 2147483647, asserting that
#     `z < 1 && m > 0 && n > 0` fails for z = gcd(m, n). The Java task is the same
#     program. The law holds for all integers.
#
#   * c/recursive/gcd02.yml: the same bounds, with a gcd that reaches the error on
#     non-positive arguments, asserting that gcd(m, n) divides m. The law keeps
#     the positive inputs, which the error requires, and drops the upper bounds.
ExUnit.start()

defmodule SVBench.GcdTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def gcd(y1, y2) when y1 <= 0 or y2 <= 0, do: 0
  def gcd(y, y), do: y
  def gcd(y1, y2) when y1 > y2, do: gcd(y1 - y2, y2)
  def gcd(y1, y2), do: gcd(y1, y2 - y1)

  def checked_gcd(y1, y2) when y1 <= 0 or y2 <= 0, do: :erlang.error(:reach_error)
  def checked_gcd(y, y), do: y
  def checked_gcd(y1, y2) when y1 > y2, do: checked_gcd(y1 - y2, y2)
  def checked_gcd(y1, y2), do: checked_gcd(y1, y2 - y1)

  def divides(_n, 0), do: true
  def divides(n, m) when n > m, do: false
  def divides(n, m), do: divides(n, m - n)

  laws "gcd" do
    termination_suffix &__MODULE__.gcd/2, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.checked_gcd/2, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.divides/2, ~LEAN"partial_fixpoint"

    law gcd01_1(m, n),
      requires: is_integer(m) and is_integer(n),
      expects: gcd(m, n) >= 1 or m <= 0 or n <= 0,
      proof: ~LEAN"""
      have positive (k : Nat) : ∀ a b : Int, 0 < a → 0 < b → a + b ≤ k →
          ∃ r : Int, «gcd/2» (.integer a) (.integer b) = .ok (.integer r) ∧ 1 ≤ r := by
        induction k with
        | zero => intro a b _ _ _; omega
        | succ k ih =>
          intro a b a0 b0 bound
          rw [«gcd/2».eq_def]
          by_cases same : a = b
          · subst same
            exact ⟨a, by simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», show ¬ a ≤ 0 by omega], by omega⟩
          · by_cases larger : b < a
            · obtain ⟨r, returned, one⟩ := ih (a - b) b (by omega) b0 (by omega)
              exact ⟨r, by simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», show ¬ a ≤ 0 by omega, show ¬ b ≤ 0 by omega,
                show ¬ b = a by omega, larger, returned], one⟩
            · obtain ⟨r, returned, one⟩ := ih a (b - a) a0 (by omega) (by omega)
              exact ⟨r, by simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», show ¬ a ≤ 0 by omega, show ¬ b ≤ 0 by omega,
                show ¬ b = a by omega, larger, returned], one⟩
      cases m <;> cases n <;> simp [«gcd01_1:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i m n
      by_cases m0 : 0 < m
      · by_cases n0 : 0 < n
        · obtain ⟨r, returned, one⟩ := positive (m + n).toNat m n m0 n0 (by omega)
          simp [«gcd01_1:ensures/2», returned, show 1 ≤ r from one]
        · have returned : «gcd/2» (.integer m) (.integer n) = .ok (.integer 0) := by
            rw [«gcd/2».eq_def]; simp [Lynx.Except.guard, show ¬ m ≤ 0 by omega, show n ≤ 0 by omega]
          simp [«gcd01_1:ensures/2», returned, show ¬ m ≤ 0 by omega, show n ≤ 0 by omega]
      · have returned : «gcd/2» (.integer m) (.integer n) = .ok (.integer 0) := by
          rw [«gcd/2».eq_def]; simp [Lynx.Except.guard, show m ≤ 0 by omega]
        simp [«gcd01_1:ensures/2», returned, show m ≤ 0 by omega]
      """

    law gcd02(m, n),
      requires: is_integer(m) and is_integer(n) and m > 0 and n > 0,
      expects: divides(checked_gcd(m, n), m),
      proof: ~LEAN"""
      have gcd (k : Nat) : ∀ a b : Int, 0 < a → 0 < b → a + b ≤ k →
          ∃ r : Int, «checked_gcd/2» (.integer a) (.integer b) = .ok (.integer r) ∧
            1 ≤ r ∧ r ∣ a ∧ r ∣ b := by
        induction k with
        | zero => intro a b _ _ _; omega
        | succ k ih =>
          intro a b a0 b0 bound
          rw [«checked_gcd/2».eq_def]
          by_cases same : a = b
          · subst same
            exact ⟨a, by simp [Lynx.Except.guard, show ¬ a ≤ 0 by omega], by omega,
              Int.dvd_refl a, Int.dvd_refl a⟩
          · by_cases larger : b < a
            · obtain ⟨r, returned, one, ra, rb⟩ := ih (a - b) b (by omega) b0 (by omega)
              refine ⟨r, by simp [Lynx.Except.guard, show ¬ a ≤ 0 by omega, show ¬ b ≤ 0 by omega,
                show ¬ b = a by omega, larger, returned], one, ?_, rb⟩
              simpa using Int.dvd_add ra rb
            · obtain ⟨r, returned, one, ra, rb⟩ := ih a (b - a) a0 (by omega) (by omega)
              refine ⟨r, by simp [Lynx.Except.guard, show ¬ a ≤ 0 by omega, show ¬ b ≤ 0 by omega,
                show ¬ b = a by omega, larger, returned], one, ra, ?_⟩
              simpa using Int.dvd_add rb ra
      have divides (k : Nat) : ∀ r m : Int, 1 ≤ r → 0 ≤ m → r ∣ m → m ≤ k →
          «divides/2» (.integer r) (.integer m) = .ok (.atom "true") := by
        induction k with
        | zero =>
          intro r m _ _ _ _
          obtain rfl : m = 0 := by omega
          rw [«divides/2».eq_def]
          rfl
        | succ k ih =>
          intro r m one nonneg dvd bound
          rw [«divides/2».eq_def]
          split
          · rfl
          · rename_i nonzero
            have positive : 0 < m := by
              by_cases zero : m = 0
              · subst zero; simp at nonzero
              · omega
            have le : r ≤ m := Int.le_of_dvd positive dvd
            simp [Lynx.Except.guard, show ¬ m < r by omega]
            exact ih r (m - r) one (by omega) (Int.dvd_sub dvd (Int.dvd_refl r)) (by omega)
      cases m <;> simp [«gcd02:requires/2», Erlang.erlang.«is_integer/1»] at requires
      cases n <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i m n
      obtain ⟨r, returned, one, rm, _⟩ := gcd (m + n).toNat m n requires.1 requires.2 (by omega)
      simp [«gcd02:ensures/2», returned, divides m.toNat r m one (by omega) rm (by omega)]
      """
  end
end
