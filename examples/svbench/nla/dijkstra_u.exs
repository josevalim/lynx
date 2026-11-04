# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/dijkstra_u.exs
# SV-COMP task c/nla-digbench/dijkstra-u.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws n from `unsigned` and assumes n < UINT_MAX / 4, so that
# q = 4 * q cannot wrap around and loop forever. With unbounded integers, the
# law holds for every integer n. Unsigned division of nonnegative values is
# Elixir's div/2, and the asserted identities hold exactly, so they also hold
# modulo 2^32.
ExUnit.start()

defmodule SVBench.DijkstraUTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def grow(n, q), do: if(q <= n, do: grow(n, 4 * q), else: q)

  def descend(n, p, q, r, h) do
    check(r < 2 * p + q)
    check(p * p + r * q == n * q)

    check(
      h * h * h - 12 * h * n * q + 16 * n * p * q - h * q * q - 4 * p * q * q + 12 * h * q * r -
        16 * p * q * r == 0
    )

    check(
      h * h * n - 4 * h * n * p + 4 * (n * n) * q - n * q * q - h * h * r + 4 * h * p * r -
        8 * n * q * r + q * q * r + 4 * q * r * r == 0
    )

    check(
      h * h * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r - 4 * p * q * r == 0
    )

    check(p * p - n * q + q * r == 0)

    if q == 1 do
      {p, r, h}
    else
      q = div(q, 4)
      h = p + q
      p = div(p, 2)
      if r >= h, do: descend(n, p + q, q, r - h, h), else: descend(n, p, q, r, h)
    end
  end

  def main(n) do
    q = grow(n, 1)
    {p, r, h} = descend(n, 0, q, n, 0)

    h * h * h - 12 * h * n + 16 * n * p + 12 * h * r - 16 * p * r - h - 4 * p == 0 and
      p * p - n + r == 0 and h * h * p - 4 * h * n + 4 * n * p + 4 * h * r - 4 * p * r - p == 0
  end

  laws "dijkstra-u" do
    termination_suffix &__MODULE__.grow/2, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.descend/5, ~LEAN"partial_fixpoint"

    law dijkstra_u(n),
      requires: is_integer(n),
      expects: main(n),
      proof: ~LEAN"""
      cases n <;> simp [«dijkstra_u:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have four (j : Nat) : (4 : Int) ^ j = 2 ^ j * 2 ^ j := by
        rw [← Int.mul_pow]; rfl
      have step (p q r h : Int) (c1 : r < 2 * p + q) (c2 : p * p + r * q = n * q)
          (c3 : h * h * h - 12 * h * n * q + 16 * n * p * q - h * q * q - 4 * p * q * q + 12 * h * q * r - 16 * p * q * r = 0)
          (c4 : h * h * n - 4 * h * n * p + 4 * (n * n) * q - n * q * q - h * h * r + 4 * h * p * r - 8 * n * q * r + q * q * r + 4 * q * r * r = 0)
          (c5 : h * h * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r - 4 * p * q * r = 0)
          (c6 : p * p - n * q + q * r = 0) :
          «descend/5» (.integer n) (.integer p) (.integer q) (.integer r) (.integer h) =
            if q = 1 then .ok (.tuple #[.integer p, .integer r, .integer h])
            else if p + q.tdiv 4 ≤ r then
              «descend/5» (.integer n) (.integer (p.tdiv 2 + q.tdiv 4)) (.integer (q.tdiv 4))
                (.integer (r - (p + q.tdiv 4))) (.integer (p + q.tdiv 4))
            else
              «descend/5» (.integer n) (.integer (p.tdiv 2)) (.integer (q.tdiv 4)) (.integer r)
                (.integer (p + q.tdiv 4)) := by
        rw [«descend/5».eq_def]
        simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers», Erlang.erlang.«-/2_integers»,
          Erlang.erlang.«==/2_integers», Erlang.erlang.«</2_integers», Erlang.erlang.«>=/2_integers»,
          Erlang.erlang.«div/2_integers», Lynx.Except.ok_bind, c1, c2, c3, c4, c5, c6, if_true,
          «check/1», Lynx.Term.true]
        by_cases one : q = 1
        · simp [one]
        · by_cases more : p + q.tdiv 4 ≤ r <;> simp [one, more]
      -- The asserted identities follow from p * p + r * q = n * q and the last h.
      have polys (p q r h : Int) (main : p * p + r * q = n * q)
          (shape : (h = 0 ∧ p = 0 ∧ r = n) ∨ h = 2 * p - q ∨ h = 2 * p + q) :
          h * h * h - 12 * h * n * q + 16 * n * p * q - h * q * q - 4 * p * q * q + 12 * h * q * r - 16 * p * q * r = 0 ∧
          h * h * n - 4 * h * n * p + 4 * (n * n) * q - n * q * q - h * h * r + 4 * h * p * r - 8 * n * q * r + q * q * r + 4 * q * r * r = 0 ∧
          h * h * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r - 4 * p * q * r = 0 ∧ p * p - n * q + q * r = 0 := by
        rcases shape with ⟨rfl, rfl, rfl⟩ | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
      have descend (k : Nat) : ∀ (s p q r h : Int), q = 4 ^ k → p = s * 2 ^ k →
          p * p + r * q = n * q → r < 2 * p + q →
          ((h = 0 ∧ p = 0 ∧ r = n) ∨ h = 2 * p - q ∨ h = 2 * p + q) →
          ∃ p' r' h', «descend/5» (.integer n) (.integer p) (.integer q) (.integer r) (.integer h) =
              .ok (.tuple #[.integer p', .integer r', .integer h']) ∧ p' * p' + r' = n ∧
            ((h' = 0 ∧ p' = 0 ∧ r' = n) ∨ h' = 2 * p' - 1 ∨ h' = 2 * p' + 1) := by
        induction k with
        | zero =>
          intro s p q r h hq hp main below shape
          obtain ⟨c3, c4, c5, c6⟩ := polys p q r h main shape
          rw [step p q r h below main c3 c4 c5 c6]
          simp only [Int.pow_zero] at hq
          subst hq
          exact ⟨p, r, h, by simp, by grind, by simpa using shape⟩
        | succ j ih =>
          intro s p q r h hq hp main below shape
          obtain ⟨c3, c4, c5, c6⟩ := polys p q r h main shape
          rw [step p q r h below main c3 c4 c5 c6]
          have positive := Int.pow_pos (n := 4) (m := j) (by decide)
          have q4 : q = 4 * 4 ^ j := by rw [hq, Int.pow_succ, Int.mul_comm]
          have p2 : p = 2 * (s * 2 ^ j) := by rw [hp, Int.pow_succ]; grind
          have qDiv : q.tdiv 4 = 4 ^ j := by rw [q4]; exact Int.mul_tdiv_cancel_left _ (by decide)
          have pDiv : p.tdiv 2 = s * 2 ^ j := by rw [p2]; exact Int.mul_tdiv_cancel_left _ (by decide)
          rw [if_neg (by omega), qDiv, pDiv]
          by_cases more : p + 4 ^ j ≤ r
          · obtain ⟨p', r', h', ret, h1, h2⟩ := ih (s + 2 ^ j) (s * 2 ^ j + 4 ^ j) (4 ^ j)
              (r - (p + 4 ^ j)) (p + 4 ^ j) rfl (by rw [four]; grind) (by grind) (by grind)
              (.inr (.inl (by grind)))
            exact ⟨p', r', h', by rw [if_pos more]; exact ret, h1, h2⟩
          · obtain ⟨p', r', h', ret, h1, h2⟩ := ih s (s * 2 ^ j) (4 ^ j) r (p + 4 ^ j) rfl rfl
              (by grind) (by omega) (.inr (.inr (by grind)))
            exact ⟨p', r', h', by rw [if_neg more]; exact ret, h1, h2⟩
      clear step polys
      have grow (m : Nat) : ∀ k : Nat, (n + 1 - 4 ^ k).toNat ≤ m →
          ∃ K : Nat, «grow/2» (.integer n) (.integer (4 ^ k)) = .ok (.integer (4 ^ K)) ∧ n < 4 ^ K := by
        induction m using Nat.strongRecOn with
        | _ m ih =>
          intro k bound
          rw [«grow/2».eq_def]
          have positive := Int.pow_pos (n := 4) (m := k) (by decide)
          have next : (4 : Int) * 4 ^ k = 4 ^ (k + 1) := by rw [Int.pow_succ, Int.mul_comm]
          by_cases fits : 4 ^ k ≤ n
          · obtain ⟨K, ret, h⟩ := ih (n + 1 - 4 ^ (k + 1)).toNat (by rw [← next]; omega) (k + 1)
              (Nat.le_refl _)
            exact ⟨K, by simp [fits, next, ret], h⟩
          · exact ⟨k, by simp [fits], by omega⟩
      obtain ⟨K, grown, above⟩ := grow (n + 1 - 4 ^ 0).toNat 0 (Nat.le_refl _)
      simp only [Int.pow_zero] at grown
      obtain ⟨p, r, h, ret, main, shape⟩ :=
        descend K 0 0 (4 ^ K) n 0 rfl (by simp) (by simp) (by omega) (.inl ⟨rfl, rfl, rfl⟩)
      clear descend grow
      simp only [«dijkstra_u:ensures/1», «main/1», grown, Lynx.Except.ok_bind, ret]
      rcases shape with ⟨rfl, rfl, rfl⟩ | rfl | rfl <;> simp <;> grind
      """
  end
end
