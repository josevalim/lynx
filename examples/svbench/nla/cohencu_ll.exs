# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/cohencu_ll.exs
# SV-COMP task c/nla-digbench/cohencu-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
# The task's input is an unsigned short stored into a short (int16);
# the law holds for every integer.
ExUnit.start()

defmodule SVBench.CohencuLLTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def main(a) do
    {n, x, y, z} = loop(a, 0, 0, 1, 6)

    z == 6 * n + 6 and 6 * a * x - x * z + 12 * x == 0 and
      a * z - 6 * a - 2 * y + 2 * z - 10 == 0 and
      2 * y * y - 3 * x * z - 18 * x - 10 * y + 3 * z - 10 == 0 and
      z * z - 12 * y - 6 * z + 12 == 0 and y * z - 18 * x - 12 * y + 2 * z - 6 == 0
  end

  defp loop(a, n, x, y, z) do
    check(
      z == 6 * n + 6 and y == 3 * n * n + 3 * n + 1 and x == n * n * n and
        y * z - 18 * x - 12 * y + 2 * z - 6 == 0 and z * z - 12 * y - 6 * z + 12 == 0
    )

    if n <= a do
      loop(a, n + 1, x + y, y + z, z + 6)
    else
      {n, x, y, z}
    end
  end

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  laws "cohencu-ll" do
    termination_suffix &__MODULE__.loop/5, ~LEAN"partial_fixpoint"

    law cohencu_ll(a),
      requires: is_integer(a),
      expects: main(a),
      proof: ~LEAN"""
      have step (a n : Int) :
          «loop/5» (.integer a) (.integer n) (.integer (n * n * n))
              (.integer (3 * n * n + 3 * n + 1)) (.integer (6 * n + 6)) =
            if n ≤ a then
              «loop/5» (.integer a) (.integer (n + 1)) (.integer ((n + 1) * (n + 1) * (n + 1)))
                (.integer (3 * (n + 1) * (n + 1) + 3 * (n + 1) + 1)) (.integer (6 * (n + 1) + 6))
            else
              .ok (.tuple #[.integer n, .integer (n * n * n), .integer (3 * n * n + 3 * n + 1),
                .integer (6 * n + 6)]) := by
        rw [«loop/5».eq_def]
        simp
        simp (disch := grind) only [if_pos]
        simp only [«check/1»]
        by_cases le : n ≤ a <;> simp [le]
        rw [show n * n * n + (3 * n * n + 3 * n + 1) = (n + 1) * (n + 1) * (n + 1) by grind,
          show 3 * n * n + 3 * n + 1 + (6 * n + 6) = 3 * (n + 1) * (n + 1) + 3 * (n + 1) + 1 by grind,
          show 6 * n + 6 + 6 = 6 * (n + 1) + 6 by omega]
      have loop (a : Int) (k : Nat) : ∀ n : Int, a + 1 - n ≤ k → ∃ m, a < m ∧ (m = n ∨ m = a + 1) ∧
          «loop/5» (.integer a) (.integer n) (.integer (n * n * n))
              (.integer (3 * n * n + 3 * n + 1)) (.integer (6 * n + 6)) =
            .ok (.tuple #[.integer m, .integer (m * m * m), .integer (3 * m * m + 3 * m + 1),
              .integer (6 * m + 6)]) := by
        induction k with
        | zero => intro n bound; exact ⟨n, by omega, .inl rfl, by rw [step, if_neg (by omega)]⟩
        | succ k ih =>
          intro n bound
          rw [step]
          by_cases le : n ≤ a
          · obtain ⟨m, above, which, returned⟩ := ih (n + 1) (by omega)
            exact ⟨m, above, by omega, by rw [if_pos le, returned]⟩
          · exact ⟨n, by omega, .inl rfl, by rw [if_neg le]⟩
      clear step
      cases a <;> simp [«cohencu_ll:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      obtain ⟨m, above, which, returned⟩ := loop a (a + 1).toNat 0 (by omega)
      simp only [show (0 : Int) * 0 * 0 = 0 by rfl, show 3 * (0 : Int) * 0 + 3 * 0 + 1 = 1 by rfl,
        show 6 * (0 : Int) + 6 = 6 by rfl] at returned
      simp only [«cohencu_ll:ensures/1», «main/1», returned]
      simp
      grind
      """
  end
end
