# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/geo1_ll.exs
# SV-COMP task c/nla-digbench/geo1-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
# The task's inputs are ints (int32) and assumes z >= 1 and k >= 1. The invariant
# holds for any z and the loop ends for any k, so the law holds for all integers.
ExUnit.start()

defmodule SVBench.Geo1LLTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def main(z, k) do
    {x, y, _c} = loop(z, k, 1, z, 1)
    x = x * (z - 1)
    1 + x - y == 0
  end

  defp loop(z, k, x, y, c) do
    check(x * z - x - y + 1 == 0)

    if c < k do
      loop(z, k, x * z + 1, y * z, c + 1)
    else
      {x, y, c}
    end
  end

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  laws "geo1-ll" do
    termination_suffix &__MODULE__.loop/5, ~LEAN"partial_fixpoint"

    law geo1_ll(z, k),
      requires: is_integer(z) and is_integer(k),
      expects: main(z, k),
      proof: ~LEAN"""
      have step (z k x y c : Int) (invariant : x * z - x - y + 1 = 0) :
          «loop/5» (.integer z) (.integer k) (.integer x) (.integer y) (.integer c) =
            if c < k then
              «loop/5» (.integer z) (.integer k) (.integer (x * z + 1)) (.integer (y * z))
                (.integer (c + 1))
            else
              .ok (.tuple #[.integer x, .integer y, .integer c]) := by
        rw [«loop/5».eq_def]
        simp
        simp (disch := grind) only [if_pos]
        simp only [«check/1»]
        by_cases lt : c < k <;> simp [lt]
      have loop (z k : Int) (fuel : Nat) : ∀ x y c : Int, k - c ≤ fuel → x * z - x - y + 1 = 0 →
          ∃ x' y' c', x' * z - x' - y' + 1 = 0 ∧
            «loop/5» (.integer z) (.integer k) (.integer x) (.integer y) (.integer c) =
              .ok (.tuple #[.integer x', .integer y', .integer c']) := by
        induction fuel with
        | zero =>
          intro x y c bound invariant
          exact ⟨x, y, c, invariant, by rw [step z k x y c invariant, if_neg (by omega)]⟩
        | succ fuel ih =>
          intro x y c bound invariant
          rw [step z k x y c invariant]
          by_cases lt : c < k
          · obtain ⟨x', y', c', invariant', returned⟩ :=
              ih (x * z + 1) (y * z) (c + 1) (by omega) (by grind)
            exact ⟨x', y', c', invariant', by rw [if_pos lt, returned]⟩
          · exact ⟨x, y, c, invariant, by rw [if_neg lt]⟩
      clear step
      simp [«geo1_ll:requires/2»] at requires
      obtain ⟨integerZ, integerK⟩ := requires
      cases z <;> simp [Erlang.erlang.«is_integer/1»] at integerZ
      cases k <;> simp [Erlang.erlang.«is_integer/1»] at integerK
      rename_i z k
      obtain ⟨x, y, c, invariant, returned⟩ := loop z k (k - 1).toNat 1 z 1 (by omega) (by omega)
      simp only [«geo1_ll:ensures/2», «main/2», returned]
      simp
      grind
      """
  end
end
