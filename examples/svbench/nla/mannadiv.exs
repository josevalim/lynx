# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/mannadiv.exs
# SV-COMP task c/nla-digbench/mannadiv.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws x1 and x2 from `int` and assumes x1 >= 0 and x2 != 0. The law
# holds for all integers x1 >= 0 and all integers x2: the assertions do not
# need x2 != 0. Negative x1 is excluded, as the loop then diverges.
ExUnit.start()

defmodule SVBench.MannadivTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def loop(x1, x2, y1, y2, y3) do
    check(y1 * x2 + y2 + y3 == x1)

    if y3 != 0 do
      if y2 + 1 == x2 do
        loop(x1, x2, y1 + 1, 0, y3 - 1)
      else
        loop(x1, x2, y1, y2 + 1, y3 - 1)
      end
    else
      {y1, y2}
    end
  end

  def main(x1, x2) do
    {y1, y2} = loop(x1, x2, 0, 0, x1)
    y1 * x2 + y2 == x1
  end

  laws "mannadiv" do
    termination_suffix &__MODULE__.loop/5, ~LEAN"partial_fixpoint"

    law mannadiv(x1, x2),
      requires: is_integer(x1) and is_integer(x2) and x1 >= 0,
      expects: main(x1, x2),
      proof: ~LEAN"""
      have loop (x1 x2 : Int) (k : Nat) : ∀ y1 y2 y3 : Int, y3.toNat ≤ k → 0 ≤ y3 →
          y1 * x2 + y2 + y3 = x1 → ∃ y1' y2', «loop/5» (.integer x1) (.integer x2) (.integer y1)
            (.integer y2) (.integer y3) = .ok (.tuple #[.integer y1', .integer y2']) ∧
            y1' * x2 + y2' = x1 := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro y1 y2 y3 bound nonneg inv
          rw [«loop/5».eq_def]
          by_cases zero : y3 = 0
          · subst zero
            exact ⟨y1, y2, by simp at inv; simp [«check/1», inv], by simpa using inv⟩
          · by_cases wrap : y2 + 1 = x2
            · obtain ⟨y1', y2', ret, post⟩ := ih (y3 - 1).toNat (by omega) (y1 + 1) 0 (y3 - 1)
                (by omega) (by omega) (by grind)
              exact ⟨y1', y2', by simp [«check/1», inv, zero, wrap, ret], post⟩
            · obtain ⟨y1', y2', ret, post⟩ := ih (y3 - 1).toNat (by omega) y1 (y2 + 1) (y3 - 1)
                (by omega) (by omega) (by grind)
              exact ⟨y1', y2', by simp [«check/1», inv, zero, wrap, ret], post⟩
      cases x1 <;> cases x2 <;>
        simp [«mannadiv:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i x1 x2
      obtain ⟨y1, y2, ret, post⟩ := loop x1 x2 x1.toNat 0 0 x1 (by omega) requires (by simp)
      simp [«mannadiv:ensures/2», «main/2», ret, post]
      """
  end
end
