# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/prodbin_ll.exs
# SV-COMP task c/nla-digbench/prodbin-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws a and b from `int` and assumes b >= 1. The law holds for all
# integers a and all integers b >= 0. Negative b breaks the invariant, as C's
# remainder of an odd negative number is -1, not 1.
ExUnit.start()

defmodule SVBench.ProdbinLlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def loop(a, b, x, y, z) do
    check(z + x * y == a * b)

    if y != 0 do
      if rem(y, 2) == 1 do
        loop(a, b, 2 * x, div(y - 1, 2), z + x)
      else
        loop(a, b, 2 * x, div(y, 2), z)
      end
    else
      z
    end
  end

  def main(a, b), do: loop(a, b, a, b, 0) == a * b

  laws "prodbin-ll" do
    termination_suffix &__MODULE__.loop/5, ~LEAN"partial_fixpoint"

    law prodbin_ll(a, b),
      requires: is_integer(a) and is_integer(b) and b >= 0,
      expects: main(a, b),
      proof: ~LEAN"""
      have loop (a b : Int) (k : Nat) : ∀ x y z : Int, y.toNat ≤ k → 0 ≤ y →
          z + x * y = a * b → «loop/5» (.integer a) (.integer b) (.integer x) (.integer y)
            (.integer z) = .ok (.integer (a * b)) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro x y z bound nonneg inv
          rw [«loop/5».eq_def]
          by_cases zero : y = 0
          · subst zero
            simp at inv
            simp [«check/1», inv]
          · by_cases odd : y % 2 = 1
            · have next := ih ((y - 1) / 2).toNat (by omega) (2 * x) ((y - 1) / 2) (z + x)
                (by omega) (by omega) (by
                  have half : y - 1 = 2 * ((y - 1) / 2) := by omega
                  grind)
              simp [«check/1», inv, zero, odd, next, nonneg, show 1 ≤ y by omega]
            · have next := ih (y / 2).toNat (by omega) (2 * x) (y / 2) z
                (by omega) (by omega) (by
                  have half : y = 2 * (y / 2) := by omega
                  grind)
              simp [«check/1», inv, zero, odd, next, nonneg]
      cases a <;> cases b <;>
        simp [«prodbin_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a b
      simp [«prodbin_ll:ensures/2», «main/2», loop a b b.toNat a b 0 (by omega) requires (by simp)]
      """
  end
end
