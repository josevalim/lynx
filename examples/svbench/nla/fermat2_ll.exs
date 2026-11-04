# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/fermat2_ll.exs
# SV-COMP task c/nla-digbench/fermat2-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws A and R from `int` and assumes (R - 1)^2 < A and A % 2 == 1.
# The law holds for all integers under the same assumptions, which also make
# the loop end: they bound u by A + 2 and v by A.
ExUnit.start()

defmodule SVBench.Fermat2LlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def loop(a, u, v, r) do
    check(4 * (a + r) == u * u - v * v - 2 * u + 2 * v)

    cond do
      r == 0 -> {u, v}
      r > 0 -> loop(a, u, v + 2, r - v)
      true -> loop(a, u + 2, v, r + u)
    end
  end

  def main(a, r) do
    {u, v} = loop(a, 2 * r + 1, 1, r * r - a)
    4 * a == u * u - v * v - 2 * u + 2 * v
  end

  laws "fermat2-ll" do
    termination_suffix &__MODULE__.loop/4, ~LEAN"partial_fixpoint"

    law fermat2_ll(a, r),
      requires: is_integer(a) and is_integer(r) and (r - 1) * (r - 1) < a and rem(a, 2) == 1,
      expects: main(a, r),
      proof: ~LEAN"""
      cases a <;> cases r <;> simp [«fermat2_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a r
      obtain ⟨square, odd⟩ := requires
      have sqLe (t n : Int) (low : -n ≤ t) (high : t ≤ n) : t * t ≤ n * n := by
        by_cases nonneg : 0 ≤ t
        · exact Int.mul_self_le_mul_self nonneg high
        · have := Int.mul_self_le_mul_self (show 0 ≤ -t by omega) (show -t ≤ n by omega)
          simpa [Int.neg_mul_neg] using this
      have sqNonneg (t : Int) : 0 ≤ t * t := by
        by_cases nonneg : 0 ≤ t
        · exact Int.mul_nonneg nonneg nonneg
        · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      have positive : 0 < a := by have := sqNonneg (r - 1); omega
      rw [Int.tmod_eq_emod_of_nonneg (by omega)] at odd
      have step (u v w : Int) (invariant : 4 * (a + w) = u * u - v * v - 2 * u + 2 * v) :
          «loop/4» (.integer a) (.integer u) (.integer v) (.integer w) =
            if w = 0 then .ok (.tuple #[.integer u, .integer v])
            else if 0 < w then «loop/4» (.integer a) (.integer u) (.integer (v + 2)) (.integer (w - v))
            else «loop/4» (.integer a) (.integer (u + 2)) (.integer v) (.integer (w + u)) := by
        rw [«loop/4».eq_def]
        simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers», Erlang.erlang.«-/2_integers»,
          Erlang.erlang.«==/2_integers», Lynx.Except.ok_bind]
        simp (disch := grind) only [if_pos]
        simp only [«check/1», Lynx.Term.true, Lynx.Except.ok_bind]
        by_cases zero : w = 0
        · simp [zero]
        · by_cases more : 0 < w <;> simp [zero, more]
      have loop (k : Nat) : ∀ u v w : Int, ((a + 2 - u) + (a - v)).toNat ≤ k →
          4 * (a + w) = u * u - v * v - 2 * u + 2 * v → u % 2 = 1 → v % 2 = 1 →
          -a ≤ u → u ≤ a + 2 → 1 ≤ v → v ≤ a →
          ∃ u' v', «loop/4» (.integer a) (.integer u) (.integer v) (.integer w) =
              .ok (.tuple #[.integer u', .integer v']) ∧
            4 * a = u' * u' - v' * v' - 2 * u' + 2 * v' := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro u v w bound invariant uOdd vOdd uLow uHigh vLow vHigh
          rw [step u v w invariant]
          by_cases zero : w = 0
          · exact ⟨u, v, by simp [zero], by subst zero; grind⟩
          · by_cases more : 0 < w
            · have room : v + 2 ≤ a := by
                rcases (show v + 2 ≤ a ∨ v = a by omega) with fits | full
                · exact fits
                · have := sqLe (u - 1) (a + 1) (by omega) (by omega)
                  subst full
                  grind
              obtain ⟨u', v', ret, h⟩ := ih ((a + 2 - u) + (a - (v + 2))).toNat (by omega) u (v + 2)
                (w - v) (by omega) (by grind) uOdd (by omega) uLow uHigh (by omega) room
              exact ⟨u', v', by simp [zero, more, ret], h⟩
            · have room : u ≤ a := by
                rcases (show u ≤ a ∨ u = a + 2 by omega) with fits | full
                · exact fits
                · have := sqLe (v - 1) (a - 1) (by omega) (by omega)
                  subst full
                  grind
              obtain ⟨u', v', ret, h⟩ := ih ((a + 2 - (u + 2)) + (a - v)).toNat (by omega) (u + 2) v
                (w + u) (by omega) (by grind) (by omega) vOdd (by omega) (by omega) vLow vHigh
              exact ⟨u', v', by simp [zero, more, ret], h⟩
      clear step
      obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 1 := ⟨a / 2, by omega⟩
      have rHigh : r ≤ m + 1 := by
        rcases (show r ≤ m + 1 ∨ m + 1 ≤ r - 1 by omega) with fits | over
        · exact fits
        · have := Int.mul_self_le_mul_self (show 0 ≤ m + 1 by omega) over
          have := sqNonneg m
          grind
      have rLow : -m + 1 ≤ r := by
        rcases (show -m + 1 ≤ r ∨ m + 1 ≤ 1 - r by omega) with fits | over
        · exact fits
        · have := Int.mul_self_le_mul_self (show 0 ≤ m + 1 by omega) over
          have := sqNonneg m
          grind
      obtain ⟨u, v, ret, h⟩ := loop (((2 * m + 1) + 2 - (2 * r + 1)) + ((2 * m + 1) - 1)).toNat
        (2 * r + 1) 1 (r * r - (2 * m + 1)) (by omega) (by grind) (by omega) (by decide) (by omega)
        (by omega) (by decide) (by omega)
      simp [«fermat2_ll:ensures/2», «main/2», ret, h]
      """
  end
end
