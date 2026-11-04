# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/bresenham_ll.exs
# SV-COMP task c/nla-digbench/bresenham-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws X and Y from `int`. The law holds for all integers X and Y.
ExUnit.start()

defmodule SVBench.BresenhamLlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def loop(xx, yy, x, y, v) do
    check(2 * (yy * x) - 2 * (xx * y) - xx + 2 * yy - v == 0)

    if x <= xx do
      if v < 0 do
        loop(xx, yy, x + 1, y, v + 2 * yy)
      else
        loop(xx, yy, x + 1, y + 1, v + 2 * (yy - xx))
      end
    else
      {x, y, v}
    end
  end

  def main(xx, yy) do
    {x, y, v} = loop(xx, yy, 0, 0, 2 * yy - xx)
    2 * (yy * x) - 2 * (x * y) - xx + 2 * yy - v + 2 * y == 0
  end

  laws "bresenham-ll" do
    termination_suffix &__MODULE__.loop/5, ~LEAN"partial_fixpoint"

    law bresenham_ll(xx, yy),
      requires: is_integer(xx) and is_integer(yy),
      expects: main(xx, yy),
      proof: ~LEAN"""
      have loop (xx yy : Int) (k : Nat) : ∀ x y v : Int, (xx + 1 - x).toNat ≤ k →
          (x ≤ xx + 1 ∨ y = 0) → 2 * (yy * x) - 2 * (xx * y) - xx + 2 * yy - v = 0 →
          ∃ x' y' v', «loop/5» (.integer xx) (.integer yy) (.integer x) (.integer y)
            (.integer v) = .ok (.tuple #[.integer x', .integer y', .integer v']) ∧
            2 * (yy * x') - 2 * (xx * y') - xx + 2 * yy - v' = 0 ∧ (x' = xx + 1 ∨ y' = 0) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro x y v bound reach inv
          rw [«loop/5».eq_def]
          by_cases more : x ≤ xx
          · by_cases neg : v < 0
            · obtain ⟨x', y', v', ret, post⟩ := ih (xx + 1 - (x + 1)).toNat (by omega) (x + 1) y
                (v + 2 * yy) (by omega) (by omega) (by grind)
              exact ⟨x', y', v', by simp [«check/1», inv, more, neg, ret], post⟩
            · obtain ⟨x', y', v', ret, post⟩ := ih (xx + 1 - (x + 1)).toNat (by omega) (x + 1)
                (y + 1) (v + 2 * (yy - xx)) (by omega) (by omega) (by grind)
              exact ⟨x', y', v', by simp [«check/1», inv, more, neg, ret], post⟩
          · exact ⟨x, y, v, by simp [«check/1», inv, more], inv, by omega⟩
      cases xx <;> cases yy <;>
        simp [«bresenham_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i xx yy
      obtain ⟨x, y, v, ret, inv, last⟩ := loop xx yy (xx + 1).toNat 0 0 (2 * yy - xx) (by omega)
        (by omega) (by grind)
      rcases last with rfl | rfl <;> simp [«bresenham_ll:ensures/2», «main/2», ret] <;> grind
      """
  end
end
