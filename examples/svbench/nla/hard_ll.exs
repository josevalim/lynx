# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/hard_ll.exs
# SV-COMP task c/nla-digbench/hard-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws A and B from `unsigned` and assumes B >= 1. The law holds for
# all integers A and all integers B >= 1. B <= 0 is excluded, as the first loop
# then diverges for A >= B.
ExUnit.start()

defmodule SVBench.HardLlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def up(a, b, r, d, p, q) do
    check(q == 0)
    check(r == a)
    check(d == b * p)
    if r >= d, do: up(a, b, r, 2 * d, 2 * p, q), else: {r, d, p, q}
  end

  def down(a, b, r, d, p, q) do
    check(a == q * b + r)
    check(d == b * p)

    if p != 1 do
      d = div(d, 2)
      p = div(p, 2)
      if r >= d, do: down(a, b, r - d, d, p, q + p), else: down(a, b, r, d, p, q)
    else
      {r, d, q}
    end
  end

  def main(a, b) do
    {r, d, p, q} = up(a, b, a, b, 1, 0)
    {r, d, q} = down(a, b, r, d, p, q)
    a == d * q + r and b == d
  end

  laws "hard-ll" do
    termination_suffix &__MODULE__.up/6, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.down/6, ~LEAN"partial_fixpoint"

    law hard_ll(a, b),
      requires: is_integer(a) and is_integer(b) and b >= 1,
      expects: main(a, b),
      proof: ~LEAN"""
      have pos : ∀ n : Nat, (0 : Int) < 2 ^ n := fun n => by
        induction n with
        | zero => decide
        | succ n ih => rw [Int.pow_succ]; omega
      have up (a b : Int) (positive : 1 ≤ b) (k : Nat) : ∀ n : Nat, (a + 1 - b * 2 ^ n).toNat ≤ k →
          ∃ m : Nat, «up/6» (.integer a) (.integer b) (.integer a) (.integer (b * 2 ^ n))
            (.integer (2 ^ n)) (.integer 0) =
              .ok (.tuple #[.integer a, .integer (b * 2 ^ m), .integer (2 ^ m), .integer 0]) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro n bound
          rw [«up/6».eq_def]
          by_cases more : b * 2 ^ n ≤ a
          · have double : 2 * (2 : Int) ^ n = 2 ^ (n + 1) := by rw [Int.pow_succ]; omega
            have scaled : 2 * (b * (2 : Int) ^ n) = b * 2 ^ (n + 1) := by rw [← double]; grind
            have grows : 1 * 2 ^ n ≤ b * 2 ^ n := Int.mul_le_mul_of_nonneg_right positive (Int.le_of_lt (pos n))
            have := pos n
            obtain ⟨m, ret⟩ := ih (a + 1 - b * 2 ^ (n + 1)).toNat (by rw [← scaled]; omega) (n + 1)
              (by omega)
            exact ⟨m, by simp [«check/1», more, double, scaled, ret]⟩
          · exact ⟨n, by simp [«check/1», more]⟩
      have down (a b : Int) (positive : 1 ≤ b) : ∀ (n : Nat) (r q : Int), a = q * b + r → ∃ r' q',
          «down/6» (.integer a) (.integer b) (.integer r) (.integer (b * 2 ^ n)) (.integer (2 ^ n))
            (.integer q) = .ok (.tuple #[.integer r', .integer b, .integer q']) ∧ a = q' * b + r' := by
        intro n
        induction n with
        | zero =>
          intro r q inv
          rw [«down/6».eq_def]
          exact ⟨r, q, by simp [«check/1», ← inv], inv⟩
        | succ m ih =>
          intro r q inv
          rw [«down/6».eq_def]
          have double : (2 : Int) ^ (m + 1) = 2 ^ m * 2 := Int.pow_succ 2 m
          have half : ((2 : Int) ^ (m + 1)).tdiv 2 = 2 ^ m := by
            rw [Int.tdiv_eq_ediv_of_nonneg (Int.le_of_lt (pos _)), double,
              Int.mul_ediv_cancel _ (by decide)]
          have scaledHalf : (b * (2 : Int) ^ (m + 1)).tdiv 2 = b * 2 ^ m := by
            have nonneg := Int.mul_nonneg (show 0 ≤ b by omega) (Int.le_of_lt (pos m))
            rw [Int.tdiv_eq_ediv_of_nonneg (by rw [double]; grind), double, ← Int.mul_assoc,
              Int.mul_ediv_cancel _ (by decide)]
          have ne : (2 : Int) ^ (m + 1) ≠ 1 := by have := pos m; omega
          by_cases more : b * 2 ^ m ≤ r
          · obtain ⟨r', q', ret, post⟩ := ih (r - b * 2 ^ m) (q + 2 ^ m) (by grind)
            exact ⟨r', q', by simp [«check/1», ← inv, ne, half, scaledHalf, more, ret], post⟩
          · obtain ⟨r', q', ret, post⟩ := ih r q inv
            exact ⟨r', q', by simp [«check/1», ← inv, ne, half, scaledHalf, more, ret], post⟩
      cases a <;> cases b <;>
        simp [«hard_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a b
      obtain ⟨m, up⟩ := up a b requires (a + 1 - b * 2 ^ 0).toNat 0 (by omega)
      simp only [Int.pow_zero, Int.mul_one] at up
      obtain ⟨r, q, ret, post⟩ := down a b requires m a 0 (by simp)
      simp [«hard_ll:ensures/2», «main/2», up, ret]
      grind
      """
  end
end
