# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/egcd2_ll.exs
# SV-COMP task c/nla-digbench/egcd2-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws x and y from `int`, assumes x, y >= 1, and assumes x * y and
# y * y fit in an int. The law holds for all integers x, y >= 1 (needed for the
# loops to end); the product bounds only avoid overflow.
ExUnit.start()

defmodule SVBench.Egcd2LlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def outer(x, y, xy, yy, a, b, p, q, r, s) do
    if b == 0 do
      {a, p, q, r, s}
    else
      {c, k} = inner(x, y, xy, yy, a, b, p, q, r, s, a, 0)
      outer(x, y, xy, yy, b, c, q, p - q * k, s, r - s * k)
    end
  end

  def inner(x, y, xy, yy, a, b, p, q, r, s, c, k) do
    check(a == k * b + c)
    check(a == y * r + x * p)
    check(b == x * q + y * s)
    check(q * xy + s * yy - q * x - b * y - s * y + b == 0)
    if c >= b, do: inner(x, y, xy, yy, a, b, p, q, r, s, c - b, k + 1), else: {c, k}
  end

  def main(x, y) do
    {a, p, q, r, s} = outer(x, y, x * y, y * y, x, y, 1, 0, 0, 1)
    q * x + s * y == 0 and p * x + r * y == a
  end

  laws "egcd2-ll" do
    termination_suffix &__MODULE__.outer/10, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.inner/12, ~LEAN"partial_fixpoint"

    law egcd2_ll(x, y),
      requires: is_integer(x) and is_integer(y) and x >= 1 and y >= 1,
      expects: main(x, y),
      proof: ~LEAN"""
      cases x <;> cases y <;> simp [«egcd2_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      have stepInner (a b p q r s c k : Int) (ek : a = k * b + c) (ea : a = y * r + x * p)
          (eb : b = x * q + y * s) :
          «inner/12» (.integer x) (.integer y) (.integer (x * y)) (.integer (y * y)) (.integer a) (.integer b)
              (.integer p) (.integer q) (.integer r) (.integer s) (.integer c) (.integer k) =
            if b ≤ c then
              «inner/12» (.integer x) (.integer y) (.integer (x * y)) (.integer (y * y)) (.integer a) (.integer b)
                (.integer p) (.integer q) (.integer r) (.integer s) (.integer (c - b)) (.integer (k + 1))
            else .ok (.tuple #[.integer c, .integer k]) := by
        rw [«inner/12».eq_def]
        simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers», Erlang.erlang.«-/2_integers»,
          Erlang.erlang.«==/2_integers», Erlang.erlang.«>=/2_integers», Lynx.Except.ok_bind]
        simp (disch := grind) only [if_pos]
        simp only [«check/1», Lynx.Term.true, Lynx.Except.ok_bind]
        by_cases more : b ≤ c <;> simp [more]
      have inner (a b p q r s : Int) (hb : 1 ≤ b) (ea : a = y * r + x * p) (eb : b = x * q + y * s)
          (m : Nat) : ∀ c k : Int, c.toNat ≤ m → 0 ≤ c → a = k * b + c →
          ∃ c' k', «inner/12» (.integer x) (.integer y) (.integer (x * y)) (.integer (y * y)) (.integer a) (.integer b)
              (.integer p) (.integer q) (.integer r) (.integer s) (.integer c) (.integer k) =
              .ok (.tuple #[.integer c', .integer k']) ∧ 0 ≤ c' ∧ c' < b ∧ a = k' * b + c' := by
        induction m using Nat.strongRecOn with
        | _ m ih =>
          intro c k bound hc ek
          rw [stepInner a b p q r s c k ek ea eb]
          by_cases more : b ≤ c
          · obtain ⟨c', k', ret, h⟩ :=
              ih (c - b).toNat (by omega) (c - b) (k + 1) (by omega) (by omega) (by grind)
            exact ⟨c', k', by simp [more, ret], h⟩
          · exact ⟨c, k, by simp [more], hc, by omega, ek⟩
      clear stepInner
      have outer (m : Nat) : ∀ a b p q r s : Int, b.toNat ≤ m → 0 ≤ a → 0 ≤ b →
          a = y * r + x * p → b = x * q + y * s →
          ∃ g p' q' r' s', «outer/10» (.integer x) (.integer y) (.integer (x * y)) (.integer (y * y)) (.integer a)
              (.integer b) (.integer p) (.integer q) (.integer r) (.integer s) =
              .ok (.tuple #[.integer g, .integer p', .integer q', .integer r', .integer s']) ∧
            q' * x + s' * y = 0 ∧ p' * x + r' * y = g := by
        induction m using Nat.strongRecOn with
        | _ m ih =>
          intro a b p q r s bound ha hb ea eb
          rw [«outer/10».eq_def]
          by_cases zero : b = 0
          · subst zero
            exact ⟨a, p, q, r, s, by simp, by grind, by grind⟩
          · obtain ⟨c, k, ret, hc, hcb, ek⟩ :=
              inner a b p q r s (by omega) ea eb a.toNat a 0 (Nat.le_refl _) ha (by simp)
            obtain ⟨g, p', q', r', s', ret', h⟩ :=
              ih c.toNat (by omega) b c q (p - q * k) s (r - s * k) (by omega) (by omega) hc (by grind)
                (by grind)
            exact ⟨g, p', q', r', s', by simp [zero, ret, ret'], h⟩
      clear inner
      obtain ⟨g, p, q, r, s, ret, h1, h2⟩ :=
        outer y.toNat x y 1 0 0 1 (by omega) (by omega) (by omega) (by simp) (by simp)
      simp [«egcd2_ll:ensures/2», «main/2», ret, h1, h2]
      """
  end
end
