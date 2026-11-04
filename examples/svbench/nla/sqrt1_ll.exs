# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/sqrt1_ll.exs
# SV-COMP task c/nla-digbench/sqrt1-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
# The task's input is an int (int32); the law holds for every integer.
ExUnit.start()

defmodule SVBench.Sqrt1LLTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def main(n) do
    {a, s, t} = loop(n, 0, 1, 1)
    t == 2 * a + 1 and s == (a + 1) * (a + 1) and t * t - 4 * s + 2 * t + 1 == 0
  end

  defp loop(n, a, s, t) do
    check(t == 2 * a + 1 and s == (a + 1) * (a + 1) and t * t - 4 * s + 2 * t + 1 == 0)

    if s <= n do
      t = t + 2
      loop(n, a + 1, s + t, t)
    else
      {a, s, t}
    end
  end

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  laws "sqrt1-ll" do
    termination_suffix &__MODULE__.loop/4, ~LEAN"partial_fixpoint"

    law sqrt1_ll(n),
      requires: is_integer(n),
      expects: main(n),
      proof: ~LEAN"""
      have step (n a : Int) :
          «loop/4» (.integer n) (.integer a) (.integer ((a + 1) * (a + 1))) (.integer (2 * a + 1)) =
            if (a + 1) * (a + 1) ≤ n then
              «loop/4» (.integer n) (.integer (a + 1)) (.integer ((a + 1 + 1) * (a + 1 + 1)))
                (.integer (2 * (a + 1) + 1))
            else
              .ok (.tuple #[.integer a, .integer ((a + 1) * (a + 1)), .integer (2 * a + 1)]) := by
        rw [«loop/4».eq_def]
        simp
        simp (disch := grind) only [if_pos]
        simp only [«check/1»]
        by_cases le : (a + 1) * (a + 1) ≤ n <;> simp [le]
        rw [show (a + 1) * (a + 1) + (2 * a + 1 + 2) = (a + 1 + 1) * (a + 1 + 1) by grind,
          show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega]
      have loop (n : Int) (fuel : Nat) : ∀ a : Int, 0 ≤ a → n - a ≤ fuel → ∃ m,
          «loop/4» (.integer n) (.integer a) (.integer ((a + 1) * (a + 1))) (.integer (2 * a + 1)) =
            .ok (.tuple #[.integer m, .integer ((m + 1) * (m + 1)), .integer (2 * m + 1)]) := by
        induction fuel with
        | zero =>
          intro a nonneg bound
          have grows := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ a + 1 by omega)
            (show 0 ≤ a + 1 by omega)
          exact ⟨a, by rw [step, if_neg (by grind)]⟩
        | succ fuel ih =>
          intro a nonneg bound
          rw [step]
          by_cases le : (a + 1) * (a + 1) ≤ n
          · obtain ⟨m, returned⟩ := ih (a + 1) (by omega) (by omega)
            exact ⟨m, by rw [if_pos le, returned]⟩
          · exact ⟨a, by rw [if_neg le]⟩
      clear step
      cases n <;> simp [«sqrt1_ll:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      obtain ⟨m, returned⟩ := loop n n.toNat 0 (by omega) (by omega)
      simp only [show ((0 : Int) + 1) * (0 + 1) = 1 by rfl, show 2 * (0 : Int) + 1 = 1 by rfl] at returned
      simp only [«sqrt1_ll:ensures/1», «main/1», returned]
      simp
      grind
      """
  end
end
