# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/cohendiv_ll.exs
# SV-COMP task c/nla-digbench/cohendiv-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws x and y from `int`. The law holds for all integers x, and
# all integers y >= 1 (the task's assumption, needed for the loop to end).
ExUnit.start()

defmodule SVBench.CohendivLlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def divide(x, y, q, r, a, b) do
    check(b == y * a)
    check(x == q * y + r)

    if r >= y do
      {a, b} = double(x, y, q, r, 1, y)
      divide(x, y, q + a, r - b, a, b)
    else
      {q, r}
    end
  end

  def double(x, y, q, r, a, b) do
    check(b == y * a)
    check(x == q * y + r)
    check(r >= 0)

    if r >= 2 * b do
      check(r >= 2 * y * a)
      double(x, y, q, r, 2 * a, 2 * b)
    else
      {a, b}
    end
  end

  def main(x, y) do
    {q, r} = divide(x, y, 0, x, 0, 0)
    x == q * y + r
  end

  laws "cohendiv-ll" do
    termination_suffix &__MODULE__.divide/6, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.double/6, ~LEAN"partial_fixpoint"

    law cohendiv_ll(x, y),
      requires: is_integer(x) and is_integer(y) and y >= 1,
      expects: main(x, y),
      proof: ~LEAN"""
      have double (k : Nat) : ∀ q r y a : Int, (r - y * a).toNat ≤ k → 1 ≤ y → 1 ≤ a →
          y * a ≤ r → ∃ a', «double/6» (.integer (q * y + r)) (.integer y) (.integer q)
            (.integer r) (.integer a) (.integer (y * a)) =
              .ok (.tuple #[.integer a', .integer (y * a')]) ∧ 1 ≤ a' ∧ y * a' ≤ r := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro q r y a bound hy ha hr
          rw [«double/6».eq_def]
          have pos : 1 ≤ y * a := by
            have := Int.mul_le_mul hy ha (by omega) (by omega)
            omega
          have nonneg : 0 ≤ r := by omega
          by_cases more : 2 * (y * a) ≤ r
          · have step : y * (2 * a) = 2 * (y * a) := by grind
            obtain ⟨a', ret, ha', hr'⟩ := ih (r - y * (2 * a)).toNat (by rw [step]; omega) q r y
              (2 * a) (by omega) hy (by omega) (by rw [step]; omega)
            refine ⟨a', ?_, ha', hr'⟩
            rw [step] at ret
            simp [«check/1», Lynx.Term.true, nonneg, more, ret,
              show 2 * y * a = 2 * (y * a) by grind]
          · exact ⟨a, by simp [«check/1», Lynx.Term.true, nonneg, more], ha, hr⟩
      have divide (k : Nat) : ∀ q r y a : Int, r.toNat ≤ k → 1 ≤ y →
          ∃ q' r', «divide/6» (.integer (q * y + r)) (.integer y) (.integer q)
            (.integer r) (.integer a) (.integer (y * a)) =
              .ok (.tuple #[.integer q', .integer r']) ∧ q * y + r = q' * y + r' := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro q r y a bound hy
          rw [«divide/6».eq_def]
          by_cases more : y ≤ r
          · obtain ⟨a', ret, ha', hr'⟩ := double (r - y * 1).toNat q r y 1 (by omega) hy
              (by omega) (by omega)
            have pos : 1 ≤ y * a' := by
              have := Int.mul_le_mul hy ha' (by omega) (by omega)
              omega
            obtain ⟨q', r', ret', sum⟩ := ih (r - y * a').toNat (by omega) (q + a') (r - y * a')
              y a' (by omega) hy
            refine ⟨q', r', ?_, by grind⟩
            have same : (q + a') * y + (r - y * a') = q * y + r := by grind
            rw [same] at ret'
            simp only [Int.mul_one] at ret
            simp [«check/1», Lynx.Term.true, more, ret, ret']
          · exact ⟨q, r, by simp [«check/1», Lynx.Term.true, more], rfl⟩
      cases x <;> cases y <;>
        simp [«cohendiv_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      obtain ⟨q, r, ret, sum⟩ := divide x.toNat 0 x y 0 (by omega) (by omega)
      simp only [Int.zero_mul, Int.zero_add, Int.mul_zero] at ret
      simp [«cohendiv_ll:ensures/2», «main/2», ret, ← sum]
      """
  end
end
