# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/prod4br_ll.exs
# SV-COMP task c/nla-digbench/prod4br-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws x and y from `int` and assumes y >= 1. The law holds for all
# integers x and all integers y >= 0. Division and remainder truncate, as in C.
# Negative y is excluded: with negative x the loop then diverges, for example
# from a = b = -1.
ExUnit.start()

defmodule SVBench.Prod4brLlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def loop(x, y, a, b, p, q) do
    check(q + a * b * p == x * y)

    if a != 0 and b != 0 do
      cond do
        rem(a, 2) == 0 and rem(b, 2) == 0 -> loop(x, y, div(a, 2), div(b, 2), 4 * p, q)
        rem(a, 2) == 1 and rem(b, 2) == 0 -> loop(x, y, a - 1, b, p, q + b * p)
        rem(a, 2) == 0 and rem(b, 2) == 1 -> loop(x, y, a, b - 1, p, q + a * p)
        true -> loop(x, y, a - 1, b - 1, p, q + (a - 1 + (b - 1) + 1) * p)
      end
    else
      {q, a, b}
    end
  end

  def main(x, y) do
    {q, a, b} = loop(x, y, x, y, 1, 0)
    q == x * y and a * b == 0
  end

  laws "prod4br-ll" do
    termination_suffix &__MODULE__.loop/6, ~LEAN"partial_fixpoint"

    law prod4br_ll(x, y),
      requires: is_integer(x) and is_integer(y) and y >= 0,
      expects: main(x, y),
      proof: ~LEAN"""
      have parity (a : Int) : 2 * a.tdiv 2 + a.tmod 2 = a ∧ (0 ≤ a → 0 ≤ a.tmod 2 ∧ a.tmod 2 < 2) ∧
          (a ≤ 0 → -2 < a.tmod 2 ∧ a.tmod 2 ≤ 0) := by
        refine ⟨Int.mul_tdiv_add_tmod a 2,
          fun h => ⟨Int.tmod_nonneg 2 h, Int.tmod_lt_of_pos a (by decide)⟩, fun h => ?_⟩
        have nonneg := Int.tmod_nonneg 2 (show 0 ≤ -a by omega)
        have lt := Int.tmod_lt_of_pos (-a) (show (0 : Int) < 2 by decide)
        rw [Int.neg_tmod] at nonneg lt
        omega
      -- The measure is 2b, plus one while a is odd: the step for odd a and even b keeps b.
      have loop (x y : Int) (k : Nat) : ∀ a b p q : Int, 0 ≤ b → 2 * b ≤ k →
          (a.tmod 2 ≠ 0 → 2 * b + 1 ≤ k) → q + a * b * p = x * y →
          ∃ a' b', «loop/6» (.integer x) (.integer y) (.integer a) (.integer b) (.integer p)
            (.integer q) = .ok (.tuple #[.integer (x * y), .integer a', .integer b']) ∧
            a' * b' = 0 := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro a b p q nonneg hb ha inv
          rw [«loop/6».eq_def]
          by_cases stop : a = 0 ∨ b = 0
          · refine ⟨a, b, ?_, by rcases stop with h | h <;> simp [h]⟩
            rcases stop with h | h <;> subst h <;> simp at inv <;> simp [«check/1», inv]
          · have a0 : a ≠ 0 := by omega
            have b0 : b ≠ 0 := by omega
            obtain ⟨pa, pa1, pa2⟩ := parity a
            obtain ⟨pb, pb1, pb2⟩ := parity b
            obtain ⟨pa', pa1', pa2'⟩ := parity (a - 1)
            have rb : b.tmod 2 = 0 ∨ b.tmod 2 = 1 := by omega
            have ra : a.tmod 2 = -1 ∨ a.tmod 2 = 0 ∨ a.tmod 2 = 1 := by omega
            rcases rb with rb | rb <;> rcases ra with ra | ra | ra
            · obtain ⟨a', b', ret, zero⟩ := ih (k - 1) (by omega) (a - 1) (b - 1) p
                (q + (a - 1 + (b - 1) + 1) * p) (by omega) (by omega) (fun _ => by omega) (by grind)
              exact ⟨a', b', by simp [«check/1», inv, a0, b0, ra, rb, ret], zero⟩
            · obtain ⟨a', b', ret, zero⟩ := ih (k - 1) (by omega) (a.tdiv 2) (b.tdiv 2) (4 * p) q
                (by omega) (by omega) (fun _ => by omega) (by grind)
              exact ⟨a', b', by simp [«check/1», inv, a0, b0, ra, rb, ret], zero⟩
            · obtain ⟨a', b', ret, zero⟩ := ih (k - 1) (by omega) (a - 1) b p (q + b * p)
                (by omega) (by omega) (fun _ => by omega) (by grind)
              exact ⟨a', b', by simp [«check/1», inv, a0, b0, ra, rb, ret], zero⟩
            · obtain ⟨a', b', ret, zero⟩ := ih (k - 1) (by omega) (a - 1) (b - 1) p
                (q + (a - 1 + (b - 1) + 1) * p) (by omega) (by omega) (fun _ => by omega) (by grind)
              exact ⟨a', b', by simp [«check/1», inv, a0, b0, ra, rb, ret], zero⟩
            · obtain ⟨a', b', ret, zero⟩ := ih (k - 1) (by omega) a (b - 1) p (q + a * p)
                (by omega) (by omega) (fun _ => by omega) (by grind)
              exact ⟨a', b', by simp [«check/1», inv, a0, b0, ra, rb, ret], zero⟩
            · obtain ⟨a', b', ret, zero⟩ := ih (k - 1) (by omega) (a - 1) (b - 1) p
                (q + (a - 1 + (b - 1) + 1) * p) (by omega) (by omega) (fun _ => by omega) (by grind)
              exact ⟨a', b', by simp [«check/1», inv, a0, b0, ra, rb, ret], zero⟩
      cases x <;> cases y <;>
        simp [«prod4br_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      obtain ⟨a', b', ret, zero⟩ := loop x y (2 * y + 1).toNat x y 1 0 requires (by omega)
        (fun _ => by omega) (by simp)
      simp [«prod4br_ll:ensures/2», «main/2», ret, zero]
      """
  end
end
