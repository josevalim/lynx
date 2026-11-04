# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/egcd_ll.exs
# SV-COMP task c/nla-digbench/egcd-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws x and y from `int`. The law holds for all integers
# x, y >= 1 (the task's assumptions, needed for the loop to end).
ExUnit.start()

defmodule SVBench.EgcdLlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def egcd(x, y, a, b, p, q, r, s) do
    check(1 == p * s - r * q)
    check(a == y * r + x * p)
    check(b == x * q + y * s)

    cond do
      a == b -> {a, b, p, q, r, s}
      a > b -> egcd(x, y, a - b, b, p - q, q, r - s, s)
      true -> egcd(x, y, a, b - a, p, q - p, r, s - r)
    end
  end

  def main(x, y) do
    {a, b, p, q, r, s} = egcd(x, y, x, y, 1, 0, 0, 1)
    a - b == 0 and p * x + r * y - b == 0 and q * r - p * s + 1 == 0 and q * x + s * y - b == 0
  end

  laws "egcd-ll" do
    termination_suffix &__MODULE__.egcd/8, ~LEAN"partial_fixpoint"

    law egcd_ll(x, y),
      requires: is_integer(x) and is_integer(y) and x >= 1 and y >= 1,
      expects: main(x, y),
      proof: ~LEAN"""
      cases x <;> cases y <;>
        simp [«egcd_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      have pos : 1 ≤ x ∧ 1 ≤ y := by
        by_cases h1 : 1 ≤ x <;> by_cases h2 : 1 ≤ y <;> simp [h1, h2] at requires
        exact ⟨h1, h2⟩
      have loop (k : Nat) : ∀ a b p q r s : Int, (a + b).toNat ≤ k → 1 ≤ a → 1 ≤ b →
          p * s - r * q = 1 → y * r + x * p = a → x * q + y * s = b →
          ∃ g p' q' r' s', «egcd/8» (.integer x) (.integer y) (.integer a) (.integer b)
            (.integer p) (.integer q) (.integer r) (.integer s) =
              .ok (.tuple #[.integer g, .integer g, .integer p', .integer q', .integer r',
                .integer s']) ∧
            p' * s' - r' * q' = 1 ∧ y * r' + x * p' = g ∧ x * q' + y * s' = g := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro a b p q r s bound ha hb det ea eb
          rw [«egcd/8».eq_def]
          simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«-/2_integers»,
            Erlang.erlang.«+/2_integers», det, ea, eb, Erlang.erlang.«==/2_integers», if_true, «check/1», Lynx.Term.true,
            Lynx.Except.ok_bind]
          by_cases same : a = b
          · subst same
            exact ⟨a, p, q, r, s, by simp, det, ea, eb⟩
          · by_cases more : b < a
            · obtain ⟨g, p', q', r', s', ret, h⟩ := ih (a - b + b).toNat (by omega) (a - b) b
                (p - q) q (r - s) s (by omega) (by omega) hb (by grind) (by grind) eb
              exact ⟨g, p', q', r', s', by simp [same, more, ret], h⟩
            · obtain ⟨g, p', q', r', s', ret, h⟩ := ih (a + (b - a)).toNat (by omega) a (b - a)
                p (q - p) r (s - r) (by omega) ha (by omega) (by grind) ea (by grind)
              exact ⟨g, p', q', r', s', by simp [same, more, ret], h⟩
      obtain ⟨g, p, q, r, s, ret, det, ea, eb⟩ :=
        loop (x + y).toNat x y 1 0 0 1 (by omega) pos.1 pos.2 (by decide) (by omega) (by omega)
      simp [«egcd_ll:ensures/2», «main/2», ret, show p * x + r * y - g = 0 by grind,
        show q * r - p * s + 1 = 0 by grind, show q * x + s * y - g = 0 by grind]
      """
  end
end
