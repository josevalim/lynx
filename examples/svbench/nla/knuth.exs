# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/knuth.exs
# SV-COMP task c/nla-digbench/knuth.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# Deviations from the C program:
#
#   * `unsigned` arithmetic is modelled with unbounded integers. The proof
#     shows that every branch preserves the asserted invariants as integer
#     identities, whichever branch is taken, so they also hold modulo 2^32.
#
#   * `sqrt(n)` truncated to `unsigned` is computed with an integer square
#     root, which agrees with the double computation for `n < UINT_MAX / 8`.
#
#   * The task draws n and a from `unsigned` and assumes `n < UINT_MAX / 8`
#     and `a > 2`. The law holds for all integers n, and all integers a other
#     than 0 and 2, which would divide by zero. Division and remainder
#     truncate, as in C, and the invariants only rely on `n = div(n, m) * m +
#     rem(n, m)`.
ExUnit.start()

defmodule SVBench.KnuthTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def isqrt(n, s) when (s + 1) * (s + 1) <= n, do: isqrt(n, s + 1)
  def isqrt(_n, s), do: s

  def knuth(n, a, d, r, k, q, s, t) do
    check(d * d * q - 2 * q * d - 4 * r * d + 4 * k * d + 8 * r == 8 * n)
    check(k * t == t * t)

    check(
      d * d * q - 2 * d * q - 4 * d * r + 4 * d * t + 4 * a * k - 4 * a * t - 8 * n + 8 * r == 0
    )

    check(d * k - d * t - a * k + a * t == 0)

    if s >= d and r != 0 do
      cond do
        2 * r + q < k -> knuth(n, a, d + 2, 2 * r - k + q + d + 2, r, q + 4, s, r)
        2 * r + q < d + k + 2 -> knuth(n, a, d + 2, 2 * r - k + q, r, q, s, r)
        2 * r + q < 2 * d + k + 4 -> knuth(n, a, d + 2, 2 * r - k + q - d - 2, r, q - 4, s, r)
        true -> knuth(n, a, d + 2, 2 * r - k + q - 2 * d - 4, r, q - 8, s, r)
      end
    else
      :ok
    end
  end

  def main(n, a) do
    d = a
    knuth(n, a, d, rem(n, d), rem(n, d - 2), 4 * (div(n, d - 2) - div(n, d)), isqrt(n, 0), 0)
  end

  laws "knuth" do
    termination_suffix &__MODULE__.isqrt/2, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.knuth/8, ~LEAN"partial_fixpoint"

    law knuth(n, a),
      requires: is_integer(n) and is_integer(a) and a != 0 and a != 2,
      expects: main(n, a) == :ok,
      proof: ~LEAN"""
      cases n <;> cases a <;>
        simp [«knuth:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i n a
      have nonzero : a ≠ 0 ∧ a ≠ 2 := by
        by_cases h0 : a = 0 <;> by_cases h2 : a = 2 <;> simp [h0, h2] at requires
        exact ⟨h0, h2⟩
      have isqrt (k : Nat) : ∀ s : Int, 0 ≤ s → (n - s).toNat ≤ k →
          ∃ v, «isqrt/2» (.integer n) (.integer s) = .ok (.integer v) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro s nonneg bound
          rw [«isqrt/2».eq_def]
          by_cases more : (s + 1) * (s + 1) ≤ n
          · have grow : s + 1 ≤ (s + 1) * (s + 1) := by
              have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ s + 1 by omega) (show 0 ≤ s + 1 by omega)
              simpa using this
            obtain ⟨v, ret⟩ := ih (n - (s + 1)).toNat (by omega) (s + 1) (by omega) (by omega)
            exact ⟨v, by simp [Lynx.Except.guard, Lynx.Except.tryWith, more, ret]⟩
          · exact ⟨s, by simp [Lynx.Except.guard, Lynx.Except.tryWith, more]⟩
      have loop (s : Int) (m : Nat) : ∀ d r k q t : Int, (s - d + 2).toNat ≤ m →
          d * d * q - 2 * q * d - 4 * r * d + 4 * k * d + 8 * r = 8 * n →
          k * t = t * t →
          d * d * q - 2 * d * q - 4 * d * r + 4 * d * t + 4 * a * k - 4 * a * t - 8 * n + 8 * r = 0 →
          d * k - d * t - a * k + a * t = 0 →
          «knuth/8» (.integer n) (.integer a) (.integer d) (.integer r) (.integer k) (.integer q)
            (.integer s) (.integer t) = .ok (.atom "ok") := by
        induction m using Nat.strongRecOn with
        | _ m ih =>
          intro d r k q t bound i1 i2 i3 i4
          rw [«knuth/8».eq_def]
          simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«-/2_integers»,
            Erlang.erlang.«+/2_integers», Erlang.erlang.«==/2_integers», i1, i2, i3, i4, if_true, «check/1», Lynx.Term.true,
            Lynx.Except.ok_bind, Lynx.Except.pure_eq_ok]
          by_cases go : d ≤ s
          · by_cases zero : r = 0
            · simp [go, zero]
            · have step := ih (s - (d + 2) + 2).toNat (by omega) (d + 2)
              by_cases c1 : 2 * r + q < k
              · simp [go, zero, c1, step (2 * r - k + q + d + 2) r (q + 4) r (by omega)
                  (by grind) rfl (by grind) (by grind)]
              · by_cases c2 : 2 * r + q < d + k + 2
                · simp [go, zero, c1, c2, step (2 * r - k + q) r q r (by omega)
                    (by grind) rfl (by grind) (by grind)]
                · by_cases c3 : 2 * r + q < 2 * d + k + 4
                  · simp [go, zero, c1, c2, c3, step (2 * r - k + q - d - 2) r (q - 4) r
                      (by omega) (by grind) rfl (by grind) (by grind)]
                  · simp [go, zero, c1, c2, c3, step (2 * r - k + q - 2 * d - 4) r (q - 8) r
                      (by omega) (by grind) rfl (by grind) (by grind)]
          · simp [go]
      obtain ⟨s, root⟩ := isqrt n.toNat 0 (by omega) (by omega)
      have byA := Int.mul_tdiv_add_tmod n a
      have byB := Int.mul_tdiv_add_tmod n (a - 2)
      have start := loop s (s - a + 2).toNat a (n.tmod a) (n.tmod (a - 2))
        (4 * (n.tdiv (a - 2) - n.tdiv a)) 0 (by omega) (by grind) (by simp) (by grind) (by grind)
      simp [«knuth:ensures/2», «main/2», Erlang.erlang.«==/2», Erlang.erlang.«rem/2», Erlang.erlang.«div/2»,
        nonzero, show a - 2 ≠ 0 by omega, root, start]
      """
  end
end
