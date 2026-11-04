# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/lcm2.exs
# SV-COMP task c/nla-digbench/lcm2.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws a and b from `unsigned` and assumes 1 <= a, b <= 65535.
# The law holds for all integers a, b >= 1 (the lower bounds are needed for
# the loop to end; the upper bounds only avoid unsigned overflow).
ExUnit.start()

defmodule SVBench.Lcm2Test do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def loop(a, b, x, y, u, v) do
    check(x * u + y * v == 2 * a * b)

    cond do
      x == y -> {x, y, u, v}
      x > y -> loop(a, b, x - y, y, u, v + u)
      true -> loop(a, b, x, y - x, u + v, v)
    end
  end

  def main(a, b) do
    {x, y, u, v} = loop(a, b, a, b, b, a)
    x * u + y * v == 2 * a * b
  end

  laws "lcm2" do
    termination_suffix &__MODULE__.loop/6, ~LEAN"partial_fixpoint"

    law lcm2(a, b),
      requires: is_integer(a) and is_integer(b) and a >= 1 and b >= 1,
      expects: main(a, b),
      proof: ~LEAN"""
      cases a <;> cases b <;> simp [«lcm2:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a b
      have step (x y u v : Int) (invariant : x * u + y * v = 2 * a * b) :
          «loop/6» (.integer a) (.integer b) (.integer x) (.integer y) (.integer u) (.integer v) =
            if x = y then .ok (.tuple #[.integer x, .integer y, .integer u, .integer v])
            else if y < x then
              «loop/6» (.integer a) (.integer b) (.integer (x - y)) (.integer y) (.integer u)
                (.integer (v + u))
            else
              «loop/6» (.integer a) (.integer b) (.integer x) (.integer (y - x)) (.integer (u + v))
                (.integer v) := by
        rw [«loop/6».eq_def]
        simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind,
          Erlang.erlang.«==/2_integers», invariant, if_true, «check/1», Lynx.Term.true]
        by_cases same : x = y
        · simp [same]
        · by_cases more : y < x <;> simp [same, more]
      have loop (k : Nat) : ∀ x y u v : Int, (x + y).toNat ≤ k → 1 ≤ x → 1 ≤ y →
          x * u + y * v = 2 * a * b →
          ∃ g u' v', «loop/6» (.integer a) (.integer b) (.integer x) (.integer y) (.integer u)
              (.integer v) = .ok (.tuple #[.integer g, .integer g, .integer u', .integer v']) ∧
            g * u' + g * v' = 2 * a * b := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro x y u v bound hx hy invariant
          rw [step x y u v invariant]
          by_cases same : x = y
          · subst same
            exact ⟨x, u, v, by simp, invariant⟩
          · by_cases more : y < x
            · obtain ⟨g, u', v', ret, h⟩ :=
                ih (x - y + y).toNat (by omega) (x - y) y u (v + u) (by omega) (by omega) hy (by grind)
              exact ⟨g, u', v', by simp [same, more, ret], h⟩
            · obtain ⟨g, u', v', ret, h⟩ :=
                ih (x + (y - x)).toNat (by omega) x (y - x) (u + v) v (by omega) hx (by omega) (by grind)
              exact ⟨g, u', v', by simp [same, more, ret], h⟩
      clear step
      obtain ⟨g, u, v, ret, h⟩ := loop (a + b).toNat a b b a (by omega) requires.1 requires.2 (by grind)
      simp [«lcm2:ensures/2», «main/2», ret, h]
      """
  end
end
