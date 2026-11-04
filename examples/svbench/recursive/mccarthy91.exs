# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/mccarthy91.exs
# SV-COMP tasks (sv-benchmarks 2e1723f), property unreach-call, expected verdict true:
#
#   * c/recursive/McCarthy91-2.yml: x any int, asserting
#     f91(x) == 91 or (x > 101 and f91(x) == x - 10). Law mccarthy91_2.
#   * java/jayhorn-recursive/SatMccarthy91.yml: x any int, asserting
#     x > 101 or f91(x) == 91. Law sat_mccarthy91.
#
# Both laws hold for every integer.
ExUnit.start()

defmodule SVBench.McCarthy91Test do
  use ExUnit.Case, async: true
  use Lynx.Case

  def f91(x) when x > 100, do: x - 10
  def f91(x), do: f91(f91(x + 11))

  laws "McCarthy91" do
    termination_suffix &__MODULE__.f91/1, ~LEAN"partial_fixpoint"

    law mccarthy91_2(x),
      requires: is_integer(x),
      expects: f91(x) == 91 or (x > 101 and f91(x) == x - 10),
      proof: ~LEAN"""
      have f91 (k : Nat) : ∀ n : Int, 101 - n ≤ k →
          «f91/1» (.integer n) = .ok (.integer (if 100 < n then n - 10 else 91)) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro n bound
          rw [«f91/1».eq_def]
          by_cases high : 100 < n
          · simp [high]
          · simp only [Erlang.erlang.«>/2_integers», high, if_false, Lynx.Except.guard, Erlang.erlang.«+/2_integers»]
            have inner := ih (k - 1) (by omega) (n + 11) (by omega)
            by_cases near : 89 < n
            · rw [if_pos (show 100 < n + 11 by omega), show n + 11 - 10 = n + 1 by omega] at inner
              have outer := ih (k - 1) (by omega) (n + 1) (by omega)
              by_cases top : 100 < n + 1 <;> simp [inner, outer, top, high] <;> omega
            · rw [if_neg (show ¬ 100 < n + 11 by omega)] at inner
              have outer := ih (k - 1) (by omega) 91 (by omega)
              simp [inner, outer, high]
      cases x <;> simp [«mccarthy91_2:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have result := f91 (101 - n).toNat n (by omega)
      by_cases high : 100 < n
      · by_cases above : 101 < n <;> by_cases fixed : n - 10 = 91 <;>
          simp [«mccarthy91_2:ensures/1», result, high, above, fixed] <;> omega
      · simp [«mccarthy91_2:ensures/1», result, high]
      """

    law sat_mccarthy91(x),
      requires: is_integer(x),
      expects: x > 101 or f91(x) == 91,
      proof: ~LEAN"""
      have f91 (k : Nat) : ∀ n : Int, 101 - n ≤ k →
          «f91/1» (.integer n) = .ok (.integer (if 100 < n then n - 10 else 91)) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro n bound
          rw [«f91/1».eq_def]
          by_cases high : 100 < n
          · simp [high]
          · simp only [Erlang.erlang.«>/2_integers», high, if_false, Lynx.Except.guard, Erlang.erlang.«+/2_integers»]
            have inner := ih (k - 1) (by omega) (n + 11) (by omega)
            by_cases near : 89 < n
            · rw [if_pos (show 100 < n + 11 by omega), show n + 11 - 10 = n + 1 by omega] at inner
              have outer := ih (k - 1) (by omega) (n + 1) (by omega)
              by_cases top : 100 < n + 1 <;> simp [inner, outer, top, high] <;> omega
            · rw [if_neg (show ¬ 100 < n + 11 by omega)] at inner
              have outer := ih (k - 1) (by omega) 91 (by omega)
              simp [inner, outer, high]
      cases x <;> simp [«sat_mccarthy91:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have result := f91 (101 - n).toNat n (by omega)
      by_cases above : 101 < n
      · simp [«sat_mccarthy91:ensures/1», above]
      · by_cases high : 100 < n
        · have : n = 101 := by omega
          subst this
          simp [«sat_mccarthy91:ensures/1», result]
        · simp [«sat_mccarthy91:ensures/1», result, high, above]
      """
  end
end
