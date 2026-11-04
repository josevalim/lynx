# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/fermat1_ll.exs
# SV-COMP task c/nla-digbench/fermat1-ll.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws A and R from `int` and assumes (R - 1)^2 < A and A % 2 == 1.
# The law holds for all integers under the same assumptions, which also make
# the loops end: they bound u by A + 2 and v by A.
ExUnit.start()

defmodule SVBench.Fermat1LlTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def outer(a, u, v, r) do
    check(4 * (a + r) == u * u - v * v - 2 * u + 2 * v)

    if r == 0 do
      {u, v}
    else
      {v, r} = down(a, u, v, r)
      {u, r} = up(a, u, v, r)
      outer(a, u, v, r)
    end
  end

  def down(a, u, v, r) do
    check(4 * (a + r) == u * u - v * v - 2 * u + 2 * v)
    if r > 0, do: down(a, u, v + 2, r - v), else: {v, r}
  end

  def up(a, u, v, r) do
    check(4 * (a + r) == u * u - v * v - 2 * u + 2 * v)
    if r < 0, do: up(a, u + 2, v, r + u), else: {u, r}
  end

  def main(a, r) do
    {u, v} = outer(a, 2 * r + 1, 1, r * r - a)
    4 * a == u * u - v * v - 2 * u + 2 * v
  end

  laws "fermat1-ll" do
    termination_suffix &__MODULE__.outer/4, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.down/4, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.up/4, ~LEAN"partial_fixpoint"

    law fermat1_ll(a, r),
      requires: is_integer(a) and is_integer(r) and (r - 1) * (r - 1) < a and rem(a, 2) == 1,
      expects: main(a, r),
      proof: ~LEAN"""
      cases a <;> cases r <;> simp [«fermat1_ll:requires/2», Erlang.erlang.«is_integer/1»] at requires
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
      -- While r > 0, v can grow, and while r < 0, u can grow, within their bounds.
      have roomV (u v w : Int) (invariant : 4 * (a + w) = u * u - v * v - 2 * u + 2 * v)
          (vOdd : v % 2 = 1) (uLow : -a ≤ u) (uHigh : u ≤ a + 2) (vHigh : v ≤ a) (more : 0 < w) :
          v + 2 ≤ a := by
        rcases (show v + 2 ≤ a ∨ v = a by omega) with fits | full
        · exact fits
        · have := sqLe (u - 1) (a + 1) (by omega) (by omega)
          subst full
          grind
      have roomU (u v w : Int) (invariant : 4 * (a + w) = u * u - v * v - 2 * u + 2 * v)
          (uOdd : u % 2 = 1) (uHigh : u ≤ a + 2) (vLow : 1 ≤ v) (vHigh : v ≤ a) (less : w < 0) :
          u ≤ a := by
        rcases (show u ≤ a ∨ u = a + 2 by omega) with fits | full
        · exact fits
        · have := sqLe (v - 1) (a - 1) (by omega) (by omega)
          subst full
          grind
      have down (u : Int) (uOdd : u % 2 = 1) (uLow : -a ≤ u) (uHigh : u ≤ a + 2) (k : Nat) :
          ∀ v w : Int, (a - v).toNat ≤ k → 4 * (a + w) = u * u - v * v - 2 * u + 2 * v →
          v % 2 = 1 → 1 ≤ v → v ≤ a →
          ∃ v' w', «down/4» (.integer a) (.integer u) (.integer v) (.integer w) =
              .ok (.tuple #[.integer v', .integer w']) ∧
            4 * (a + w') = u * u - v' * v' - 2 * u + 2 * v' ∧ v' % 2 = 1 ∧ v ≤ v' ∧ v' ≤ a ∧
            w' ≤ 0 ∧ (0 < w → v < v') ∧ (¬ 0 < w → v' = v ∧ w' = w) := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro v w bound invariant vOdd vLow vHigh
          rw [«down/4».eq_def]
          simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers»,
            Erlang.erlang.«-/2_integers», Erlang.erlang.«==/2_integers», Lynx.Except.ok_bind,
            Lynx.Term.true, Erlang.erlang.«>/2_integers»]
          rw [if_pos invariant]
          simp only [«check/1», Lynx.Except.ok_bind]
          by_cases more : 0 < w
          · have room := roomV u v w invariant vOdd uLow uHigh vHigh more
            obtain ⟨v', w', ret, h⟩ := ih (a - (v + 2)).toNat (by omega) (v + 2) (w - v) (by omega)
              (by grind) (by omega) (by omega) room
            exact ⟨v', w', by simp [more, ret], h.1, h.2.1, by omega, h.2.2.2.1, h.2.2.2.2.1,
              fun _ => by omega, fun h' => absurd more h'⟩
          · exact ⟨v, w, by simp [more], invariant, vOdd, Int.le_refl _, vHigh, by omega,
              fun h' => absurd h' more, fun _ => ⟨rfl, rfl⟩⟩
      have up (v : Int) (vOdd : v % 2 = 1) (vLow : 1 ≤ v) (vHigh : v ≤ a) (k : Nat) :
          ∀ u w : Int, (a + 2 - u).toNat ≤ k → 4 * (a + w) = u * u - v * v - 2 * u + 2 * v →
          u % 2 = 1 → -a ≤ u → u ≤ a + 2 →
          ∃ u' w', «up/4» (.integer a) (.integer u) (.integer v) (.integer w) =
              .ok (.tuple #[.integer u', .integer w']) ∧
            4 * (a + w') = u' * u' - v * v - 2 * u' + 2 * v ∧ u' % 2 = 1 ∧ u ≤ u' ∧ u' ≤ a + 2 ∧
            (w < 0 → u < u') := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro u w bound invariant uOdd uLow uHigh
          rw [«up/4».eq_def]
          simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers»,
            Erlang.erlang.«-/2_integers», Erlang.erlang.«==/2_integers», Lynx.Except.ok_bind,
            Lynx.Term.true, Erlang.erlang.«</2_integers»]
          rw [if_pos invariant]
          simp only [«check/1», Lynx.Except.ok_bind]
          by_cases less : w < 0
          · have room := roomU u v w invariant uOdd uHigh vLow vHigh less
            obtain ⟨u', w', ret, h⟩ := ih (a + 2 - (u + 2)).toNat (by omega) (u + 2) (w + u)
              (by omega) (by grind) (by omega) (by omega) (by omega)
            exact ⟨u', w', by simp [less, ret], h.1, h.2.1, by omega, h.2.2.2.1, fun _ => by omega⟩
          · exact ⟨u, w, by simp [less], invariant, uOdd, Int.le_refl _, uHigh,
              fun h' => absurd h' less⟩
      have outer (k : Nat) : ∀ u v w : Int, ((a + 2 - u) + (a - v)).toNat ≤ k →
          4 * (a + w) = u * u - v * v - 2 * u + 2 * v → u % 2 = 1 → v % 2 = 1 →
          -a ≤ u → u ≤ a + 2 → 1 ≤ v → v ≤ a →
          ∃ u' v', «outer/4» (.integer a) (.integer u) (.integer v) (.integer w) =
              .ok (.tuple #[.integer u', .integer v']) ∧
            4 * a = u' * u' - v' * v' - 2 * u' + 2 * v' := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro u v w bound invariant uOdd vOdd uLow uHigh vLow vHigh
          rw [«outer/4».eq_def]
          simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers»,
            Erlang.erlang.«-/2_integers», Erlang.erlang.«==/2_integers», Lynx.Except.ok_bind,
            Lynx.Term.true]
          rw [if_pos invariant]
          simp only [«check/1», Lynx.Except.ok_bind]
          by_cases zero : w = 0
          · exact ⟨u, v, by simp [zero], by subst zero; grind⟩
          · obtain ⟨v₁, w₁, retDown, invDown, vOdd₁, vGrow, vHigh₁, wNonpos, vStep, vStay⟩ :=
              down u uOdd uLow uHigh (a - v).toNat v w (Nat.le_refl _) invariant vOdd vLow vHigh
            obtain ⟨u₁, w₂, retUp, invUp, uOdd₁, uGrow, uHigh₁, uStep⟩ :=
              up v₁ vOdd₁ (by omega) vHigh₁ (a + 2 - u).toNat u w₁ (Nat.le_refl _) invDown uOdd uLow
                uHigh
            have progress : u < u₁ ∨ v < v₁ := by
              by_cases more : 0 < w
              · exact .inr (vStep more)
              · obtain ⟨rfl, rfl⟩ := vStay more
                exact .inl (uStep (by omega))
            obtain ⟨u', v', ret, h⟩ := ih ((a + 2 - u₁) + (a - v₁)).toNat (by omega) u₁ v₁ w₂ (by omega)
              invUp uOdd₁ vOdd₁ (by omega) uHigh₁ (by omega) vHigh₁
            exact ⟨u', v', by simp [zero, retDown, retUp, ret], h⟩
      clear down up roomU roomV
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
      obtain ⟨u, v, ret, h⟩ := outer (((2 * m + 1) + 2 - (2 * r + 1)) + ((2 * m + 1) - 1)).toNat
        (2 * r + 1) 1 (r * r - (2 * m + 1)) (by omega) (by grind) (by omega) (by decide) (by omega)
        (by omega) (by decide) (by omega)
      simp [«fermat1_ll:ensures/2», «main/2», ret, h]
      """
  end
end
