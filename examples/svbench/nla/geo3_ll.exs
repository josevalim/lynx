# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/geo3_ll.exs
# SV-COMP task c/nla-digbench/geo3-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
# The task's inputs are ints (int32); the law holds for all integers. The task's
# main returns x, which is not part of the property.
ExUnit.start()

defmodule SVBench.Geo3LLTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def main(z, a, k) do
    az = a * z
    {x, y, _c} = loop(z, a, k, az, a, 1, 1)
    z * x - x + a - az * y == 0
  end

  defp loop(z, a, k, az, x, y, c) do
    check(z * x - x + a - az * y == 0)

    if c < k do
      loop(z, a, k, az, x * z + a, y * z, c + 1)
    else
      {x, y, c}
    end
  end

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  laws "geo3-ll" do
    termination_suffix &__MODULE__.loop/7, ~LEAN"partial_fixpoint"

    law geo3_ll(z, a, k),
      requires: is_integer(z) and is_integer(a) and is_integer(k),
      expects: main(z, a, k),
      proof: ~LEAN"""
      have step (z a k az x y c : Int) (invariant : z * x - x + a - az * y = 0) :
          «loop/7» (.integer z) (.integer a) (.integer k) (.integer az) (.integer x) (.integer y)
              (.integer c) =
            if c < k then
              «loop/7» (.integer z) (.integer a) (.integer k) (.integer az) (.integer (x * z + a))
                (.integer (y * z)) (.integer (c + 1))
            else
              .ok (.tuple #[.integer x, .integer y, .integer c]) := by
        rw [«loop/7».eq_def]
        simp
        simp (disch := grind) only [if_pos]
        simp only [«check/1»]
        by_cases lt : c < k <;> simp [lt]
      have loop (z a k az : Int) (fuel : Nat) : ∀ x y c : Int, k - c ≤ fuel →
          z * x - x + a - az * y = 0 →
          ∃ x' y' c', z * x' - x' + a - az * y' = 0 ∧
            «loop/7» (.integer z) (.integer a) (.integer k) (.integer az) (.integer x) (.integer y)
                (.integer c) =
              .ok (.tuple #[.integer x', .integer y', .integer c']) := by
        induction fuel with
        | zero =>
          intro x y c bound invariant
          exact ⟨x, y, c, invariant, by rw [step z a k az x y c invariant, if_neg (by omega)]⟩
        | succ fuel ih =>
          intro x y c bound invariant
          rw [step z a k az x y c invariant]
          by_cases lt : c < k
          · obtain ⟨x', y', c', invariant', returned⟩ :=
              ih (x * z + a) (y * z) (c + 1) (by omega) (by grind)
            exact ⟨x', y', c', invariant', by rw [if_pos lt, returned]⟩
          · exact ⟨x, y, c, invariant, by rw [if_neg lt]⟩
      clear step
      simp [«geo3_ll:requires/3»] at requires
      obtain ⟨⟨integerZ, integerA⟩, integerK⟩ := requires
      cases z <;> simp [Erlang.erlang.«is_integer/1»] at integerZ
      cases a <;> simp [Erlang.erlang.«is_integer/1»] at integerA
      cases k <;> simp [Erlang.erlang.«is_integer/1»] at integerK
      rename_i z a k
      obtain ⟨x, y, c, invariant, returned⟩ :=
        loop z a k (a * z) (k - 1).toNat a 1 1 (by omega) (by grind)
      simp [«geo3_ll:ensures/3», «main/3», returned]
      grind
      """
  end
end
