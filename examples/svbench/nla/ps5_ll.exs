# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/ps5_ll.exs
# SV-COMP task c/nla-digbench/ps5-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
# The task's input is a short (int16) and assumes k <= 256, bounds that only avoid
# overflow; the law holds for every integer.
ExUnit.start()

defmodule SVBench.Ps5LLTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def main(k) do
    {_c, y, x} = loop(k, 0, 0, 0)

    6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y == 0 and
      k * y == y * y
  end

  defp loop(k, c, y, x) do
    check(6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y == 0)

    if c < k do
      y = y + 1
      loop(k, c + 1, y, y * y * y * y + x)
    else
      {c, y, x}
    end
  end

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  laws "ps5-ll" do
    termination_suffix &__MODULE__.loop/4, ~LEAN"partial_fixpoint"

    law ps5_ll(k),
      requires: is_integer(k),
      expects: main(k),
      proof: ~LEAN"""
      have step (k y x : Int) (invariant : 30 * x = 6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - y) :
          «loop/4» (.integer k) (.integer y) (.integer y) (.integer x) =
            if y < k then
              «loop/4» (.integer k) (.integer (y + 1)) (.integer (y + 1))
                (.integer ((y + 1) * (y + 1) * (y + 1) * (y + 1) + x))
            else
              .ok (.tuple #[.integer y, .integer y, .integer x]) := by
        rw [«loop/4».eq_def]
        simp
        simp (disch := grind) only [if_pos]
        simp only [«check/1»]
        by_cases lt : y < k <;> simp [lt]
      have loop (k : Int) (fuel : Nat) : ∀ y x : Int, k - y ≤ fuel →
          30 * x = 6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - y →
          ∃ m z, ¬ m < k ∧ (m = y ∨ m = k) ∧ 30 * z = 6 * m * m * m * m * m + 15 * m * m * m * m + 10 * m * m * m - m ∧
            «loop/4» (.integer k) (.integer y) (.integer y) (.integer x) =
              .ok (.tuple #[.integer m, .integer m, .integer z]) := by
        induction fuel with
        | zero =>
          intro y x bound invariant
          exact ⟨y, x, by omega, .inl rfl, invariant, by rw [step k y x invariant, if_neg (by omega)]⟩
        | succ fuel ih =>
          intro y x bound invariant
          rw [step k y x invariant]
          by_cases lt : y < k
          · obtain ⟨m, z, done, which, invariant, returned⟩ :=
              ih (y + 1) ((y + 1) * (y + 1) * (y + 1) * (y + 1) + x) (by omega) (by grind)
            exact ⟨m, z, done, by omega, invariant, by rw [if_pos lt, returned]⟩
          · exact ⟨y, x, lt, .inl rfl, invariant, by rw [if_neg lt]⟩
      clear step
      cases k <;> simp [«ps5_ll:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i k
      obtain ⟨m, z, done, which, invariant, returned⟩ := loop k (k - 0).toNat 0 0 (by omega) (by decide)
      simp only [«ps5_ll:ensures/1», «main/1», returned]
      simp
      grind
      """
  end
end
