# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/egcd3_ll.exs
# SV-COMP task c/nla-digbench/egcd3-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws x and y from `int` and assumes x, y >= 1. The law holds for
# all integers x, y >= 1 (needed for the loops to end).
ExUnit.start()

defmodule SVBench.Egcd3LlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def outer(x, y, a, b, p, q, r, s) do
    if b == 0 do
      {a, p, q, r, s}
    else
      {c, k} = middle(x, y, a, b, p, q, r, s, a, 0)
      outer(x, y, b, c, q, p - q * k, s, r - s * k)
    end
  end

  def middle(x, y, a, b, p, q, r, s, c, k) do
    if c >= b do
      {d, v} = innermost(x, y, a, b, p, q, r, s, c, k, 1, b)
      middle(x, y, a, b, p, q, r, s, c - v, k + d)
    else
      {c, k}
    end
  end

  def innermost(x, y, a, b, p, q, r, s, c, k, d, v) do
    check(a == y * r + x * p)
    check(b == x * q + y * s)
    check(a == k * b + c)
    check(v == b * d)
    if c >= 2 * v, do: innermost(x, y, a, b, p, q, r, s, c, k, 2 * d, 2 * v), else: {d, v}
  end

  def main(x, y) do
    {a, p, q, r, s} = outer(x, y, x, y, 1, 0, 0, 1)
    p * x - q * x + r * y - s * y == a
  end

  laws "egcd3-ll" do
    termination_suffix &__MODULE__.outer/8, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.middle/10, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.innermost/12, ~LEAN"partial_fixpoint"

    law egcd3_ll(x, y),
      requires: is_integer(x) and is_integer(y) and x >= 1 and y >= 1,
      expects: main(x, y),
      proof: ~LEAN"""
      cases x <;> cases y <;> simp [«egcd3_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      have stepInnermost (a b p q r s c k d v : Int) (ea : a = y * r + x * p)
          (eb : b = x * q + y * s) (ek : a = k * b + c) (ev : v = b * d) :
          «innermost/12» (.integer x) (.integer y) (.integer a) (.integer b) (.integer p) (.integer q)
              (.integer r) (.integer s) (.integer c) (.integer k) (.integer d) (.integer v) =
            if 2 * v ≤ c then
              «innermost/12» (.integer x) (.integer y) (.integer a) (.integer b) (.integer p)
                (.integer q) (.integer r) (.integer s) (.integer c) (.integer k) (.integer (2 * d))
                (.integer (2 * v))
            else .ok (.tuple #[.integer d, .integer v]) := by
        rw [«innermost/12».eq_def]
        simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers»,
          Erlang.erlang.«==/2_integers», Erlang.erlang.«>=/2_integers», Lynx.Except.ok_bind]
        simp (disch := grind) only [if_pos]
        simp only [«check/1», Lynx.Term.true, Lynx.Except.ok_bind]
        by_cases more : 2 * v ≤ c <;> simp [more]
      have innermost (a b p q r s c k : Int) (hb : 1 ≤ b) (ea : a = y * r + x * p)
          (eb : b = x * q + y * s) (ek : a = k * b + c) (m : Nat) :
          ∀ d v : Int, (c - v).toNat ≤ m → 1 ≤ d → v ≤ c → v = b * d →
          ∃ d' v', «innermost/12» (.integer x) (.integer y) (.integer a) (.integer b) (.integer p)
              (.integer q) (.integer r) (.integer s) (.integer c) (.integer k) (.integer d)
              (.integer v) = .ok (.tuple #[.integer d', .integer v']) ∧
            1 ≤ d' ∧ v' ≤ c ∧ v' = b * d' := by
        induction m using Nat.strongRecOn with
        | _ m ih =>
          intro d v bound hd hv ev
          rw [stepInnermost a b p q r s c k d v ea eb ek ev]
          have positive : 1 ≤ v := by
            have := Int.mul_le_mul hb hd (by omega) (by omega); rw [ev]; simpa using this
          by_cases more : 2 * v ≤ c
          · obtain ⟨d', v', ret, h⟩ :=
              ih (c - 2 * v).toNat (by omega) (2 * d) (2 * v) (by omega) (by omega) more (by grind)
            exact ⟨d', v', by simp [more, ret], h⟩
          · exact ⟨d, v, by simp [more], hd, hv, ev⟩
      clear stepInnermost
      have middle (a b p q r s : Int) (hb : 1 ≤ b) (ea : a = y * r + x * p) (eb : b = x * q + y * s)
          (m : Nat) : ∀ c k : Int, c.toNat ≤ m → 0 ≤ c → a = k * b + c →
          ∃ c' k', «middle/10» (.integer x) (.integer y) (.integer a) (.integer b) (.integer p)
              (.integer q) (.integer r) (.integer s) (.integer c) (.integer k) =
              .ok (.tuple #[.integer c', .integer k']) ∧ 0 ≤ c' ∧ c' < b ∧ a = k' * b + c' := by
        induction m using Nat.strongRecOn with
        | _ m ih =>
          intro c k bound hc ek
          rw [«middle/10».eq_def]
          by_cases more : b ≤ c
          · obtain ⟨d, v, ret, hd, hv, ev⟩ :=
              innermost a b p q r s c k hb ea eb ek (c - b).toNat 1 b (by omega) (by omega) more
                (by simp)
            have positive : 1 ≤ v := by
              have := Int.mul_le_mul hb hd (by omega) (by omega); rw [ev]; simpa using this
            obtain ⟨c', k', ret', h⟩ :=
              ih (c - v).toNat (by omega) (c - v) (k + d) (by omega) (by omega) (by grind)
            exact ⟨c', k', by simp [more, ret, ret'], h⟩
          · exact ⟨c, k, by simp [more], hc, by omega, ek⟩
      clear innermost
      have outer (m : Nat) : ∀ a b p q r s : Int, b.toNat ≤ m → 0 ≤ a → 0 ≤ b →
          a = y * r + x * p → b = x * q + y * s →
          ∃ g p' q' r' s', «outer/8» (.integer x) (.integer y) (.integer a) (.integer b)
              (.integer p) (.integer q) (.integer r) (.integer s) =
              .ok (.tuple #[.integer g, .integer p', .integer q', .integer r', .integer s']) ∧
            q' * x + s' * y = 0 ∧ p' * x + r' * y = g := by
        induction m using Nat.strongRecOn with
        | _ m ih =>
          intro a b p q r s bound ha hb ea eb
          rw [«outer/8».eq_def]
          by_cases zero : b = 0
          · subst zero
            exact ⟨a, p, q, r, s, by simp, by grind, by grind⟩
          · obtain ⟨c, k, ret, hc, hcb, ek⟩ :=
              middle a b p q r s (by omega) ea eb a.toNat a 0 (Nat.le_refl _) ha (by simp)
            obtain ⟨g, p', q', r', s', ret', h⟩ :=
              ih c.toNat (by omega) b c q (p - q * k) s (r - s * k) (by omega) (by omega) hc (by grind)
                (by grind)
            exact ⟨g, p', q', r', s', by simp [zero, ret, ret'], h⟩
      clear middle
      obtain ⟨g, p, q, r, s, ret, h1, h2⟩ :=
        outer y.toNat x y 1 0 0 1 (by omega) (by omega) (by omega) (by simp) (by simp)
      simp [«egcd3_ll:ensures/2», «main/2», ret, show p * x - q * x + r * y - s * y = g by grind]
      """
  end
end
