# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/divbin2.exs
# SV-COMP task c/nla-digbench/divbin2.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws A from `unsigned` and fixes B = 1. The law holds for all
# integers A. In C, A >= 2^31 makes b wrap to 0 and the first loop diverge;
# with unbounded integers both loops end for every input.
ExUnit.start()

defmodule SVBench.Divbin2Test do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def up(r, b) do
    if r >= b, do: up(r, 2 * b), else: b
  end

  def down(a, q, r, b) do
    check(a == q * b + r)

    if b != 1 do
      b = div(b, 2)
      if r >= b, do: down(a, 2 * q + 1, r - b, b), else: down(a, 2 * q, r, b)
    else
      {q, r, b}
    end
  end

  def main(a) do
    b = up(a, 1)
    {q, r, b} = down(a, 0, a, b)
    a == q * b + r
  end

  laws "divbin2" do
    termination_suffix &__MODULE__.up/2, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.down/4, ~LEAN"partial_fixpoint"

    law divbin2(a),
      requires: is_integer(a),
      expects: main(a),
      proof: ~LEAN"""
      have pos : ∀ n : Nat, (0 : Int) < 2 ^ n := fun n => by
        induction n with
        | zero => decide
        | succ n ih => rw [Int.pow_succ]; omega
      have up (r : Int) (k : Nat) : ∀ n : Nat, (r + 1 - 2 ^ n).toNat ≤ k →
          ∃ m : Nat, «up/2» (.integer r) (.integer (2 ^ n)) = .ok (.integer (2 ^ m)) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro n bound
          rw [«up/2».eq_def]
          by_cases more : 2 ^ n ≤ r
          · have double : 2 * (2 : Int) ^ n = 2 ^ (n + 1) := by rw [Int.pow_succ]; omega
            have := pos n
            obtain ⟨m, ret⟩ := ih (r + 1 - 2 ^ (n + 1)).toNat (by rw [← double]; omega) (n + 1)
              (by omega)
            exact ⟨m, by simp [more, double, ret]⟩
          · exact ⟨n, by simp [more]⟩
      have down (a : Int) : ∀ (n : Nat) (q r : Int), a = q * 2 ^ n + r → ∃ q' r',
          «down/4» (.integer a) (.integer q) (.integer r) (.integer (2 ^ n)) =
            .ok (.tuple #[.integer q', .integer r', .integer 1]) ∧ a = q' * 1 + r' := by
        intro n
        induction n with
        | zero =>
          intro q r inv
          rw [«down/4».eq_def]
          simp at inv
          exact ⟨q, r, by simp [«check/1», ← inv], by simpa using inv⟩
        | succ m ih =>
          intro q r inv
          rw [«down/4».eq_def]
          have half : ((2 : Int) ^ (m + 1)).tdiv 2 = 2 ^ m := by
            rw [Int.tdiv_eq_ediv_of_nonneg (Int.le_of_lt (pos _)), Int.pow_succ,
              Int.mul_ediv_cancel _ (by decide)]
          have double : (2 : Int) ^ (m + 1) = 2 ^ m * 2 := Int.pow_succ 2 m
          have ne : (2 : Int) ^ (m + 1) ≠ 1 := by have := pos m; omega
          by_cases more : 2 ^ m ≤ r
          · obtain ⟨q', r', ret, post⟩ := ih (2 * q + 1) (r - 2 ^ m) (by rw [double] at inv; grind)
            exact ⟨q', r', by simp [«check/1», ← inv, ne, half, more, ret], post⟩
          · obtain ⟨q', r', ret, post⟩ := ih (2 * q) r (by rw [double] at inv; grind)
            exact ⟨q', r', by simp [«check/1», ← inv, ne, half, more, ret], post⟩
      cases a <;> simp [«divbin2:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      obtain ⟨m, up⟩ := up a (a + 1 - 2 ^ 0).toNat 0 (by omega)
      simp only [Int.pow_zero] at up
      obtain ⟨q, r, ret, post⟩ := down a m 0 a (by simp)
      simp [«divbin2:ensures/1», «main/1», up, ret]
      omega
      """
  end
end
