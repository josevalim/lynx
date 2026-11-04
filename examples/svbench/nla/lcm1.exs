# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/nla/lcm1.exs
# SV-COMP task c/nla-digbench/lcm1.yml (sv-benchmarks 2e1723f).
# Property: unreach-call, expected verdict: true.
#
# The task draws a and b from `unsigned` and assumes 1 <= a, b <= 65535.
# The law holds for all integers a, b >= 1 (the lower bounds are needed for
# the loops to end; the upper bounds only avoid unsigned overflow).
ExUnit.start()

defmodule SVBench.Lcm1Test do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp check(true), do: :ok
  defp check(false), do: :erlang.error(:reach_error)

  def outer(a, b, x, y, u, v) do
    check(x * u + y * v == a * b)

    if x == y do
      {x, y, u, v}
    else
      {x, v} = reduce_x(a, b, x, y, u, v)
      {y, u} = reduce_y(a, b, x, y, u, v)
      outer(a, b, x, y, u, v)
    end
  end

  def reduce_x(a, b, x, y, u, v) do
    check(x * u + y * v == a * b)
    if x > y, do: reduce_x(a, b, x - y, y, u, v + u), else: {x, v}
  end

  def reduce_y(a, b, x, y, u, v) do
    check(x * u + y * v == a * b)
    if x < y, do: reduce_y(a, b, x, y - x, u + v, v), else: {y, u}
  end

  def main(a, b) do
    {x, y, u, v} = outer(a, b, a, b, b, 0)
    u * y + v * y == a * b and x == y
  end

  laws "lcm1" do
    termination_suffix &__MODULE__.outer/6, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.reduce_x/6, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.reduce_y/6, ~LEAN"partial_fixpoint"

    law lcm1(a, b),
      requires: is_integer(a) and is_integer(b) and a >= 1 and b >= 1,
      expects: main(a, b),
      proof: ~LEAN"""
      cases a <;> cases b <;> simp [«lcm1:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a b
      have stepX (x y u v : Int) (invariant : x * u + y * v = a * b) :
          «reduce_x/6» (.integer a) (.integer b) (.integer x) (.integer y) (.integer u) (.integer v) =
            if y < x then
              «reduce_x/6» (.integer a) (.integer b) (.integer (x - y)) (.integer y) (.integer u)
                (.integer (v + u))
            else .ok (.tuple #[.integer x, .integer v]) := by
        rw [«reduce_x/6».eq_def]
        simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind,
          Erlang.erlang.«==/2_integers», invariant, if_true, «check/1», Lynx.Term.true]
        by_cases more : y < x <;> simp [more]
      have stepY (x y u v : Int) (invariant : x * u + y * v = a * b) :
          «reduce_y/6» (.integer a) (.integer b) (.integer x) (.integer y) (.integer u) (.integer v) =
            if x < y then
              «reduce_y/6» (.integer a) (.integer b) (.integer x) (.integer (y - x)) (.integer (u + v))
                (.integer v)
            else .ok (.tuple #[.integer y, .integer u]) := by
        rw [«reduce_y/6».eq_def]
        simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind,
          Erlang.erlang.«==/2_integers», invariant, if_true, «check/1», Lynx.Term.true]
        by_cases less : x < y <;> simp [less]
      have reduceX (y u : Int) (hy : 1 ≤ y) (k : Nat) : ∀ x v : Int, x.toNat ≤ k → 1 ≤ x →
          x * u + y * v = a * b →
          ∃ x' v', «reduce_x/6» (.integer a) (.integer b) (.integer x) (.integer y) (.integer u)
              (.integer v) = .ok (.tuple #[.integer x', .integer v']) ∧
            1 ≤ x' ∧ x' ≤ y ∧ x' ≤ x ∧ (y < x → x' < x) ∧ x' * u + y * v' = a * b := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro x v bound hx invariant
          rw [stepX x y u v invariant]
          by_cases more : y < x
          · obtain ⟨x', v', ret, h⟩ :=
              ih (x - y).toNat (by omega) (x - y) (v + u) (by omega) (by omega) (by grind)
            exact ⟨x', v', by simp [more, ret], h.1, h.2.1, by omega, fun _ => by omega, h.2.2.2.2⟩
          · exact ⟨x, v, by simp [more], hx, by omega, Int.le_refl _, fun h => absurd h more, invariant⟩
      have reduceY (x v : Int) (hx : 1 ≤ x) (k : Nat) : ∀ y u : Int, y.toNat ≤ k → 1 ≤ y →
          x * u + y * v = a * b →
          ∃ y' u', «reduce_y/6» (.integer a) (.integer b) (.integer x) (.integer y) (.integer u)
              (.integer v) = .ok (.tuple #[.integer y', .integer u']) ∧
            1 ≤ y' ∧ y' ≤ x ∧ y' ≤ y ∧ (x < y → y' < y) ∧ x * u' + y' * v = a * b := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro y u bound hy invariant
          rw [stepY x y u v invariant]
          by_cases less : x < y
          · obtain ⟨y', u', ret, h⟩ :=
              ih (y - x).toNat (by omega) (y - x) (u + v) (by omega) (by omega) (by grind)
            exact ⟨y', u', by simp [less, ret], h.1, h.2.1, by omega, fun _ => by omega, h.2.2.2.2⟩
          · exact ⟨y, u, by simp [less], hy, by omega, Int.le_refl _, fun h => absurd h less, invariant⟩
      clear stepX stepY
      have outer (k : Nat) : ∀ x y u v : Int, (x + y).toNat ≤ k → 1 ≤ x → 1 ≤ y →
          x * u + y * v = a * b →
          ∃ g u' v', «outer/6» (.integer a) (.integer b) (.integer x) (.integer y) (.integer u)
              (.integer v) = .ok (.tuple #[.integer g, .integer g, .integer u', .integer v']) ∧
            g * u' + g * v' = a * b := by
        induction k using Nat.strongRecOn with
        | _ k ih =>
          intro x y u v bound hx hy invariant
          rw [«outer/6».eq_def]
          simp only [Erlang.erlang.«*/2_integers», Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind,
            Erlang.erlang.«==/2_integers», invariant, if_true, «check/1», Lynx.Term.true]
          by_cases same : x = y
          · subst same
            exact ⟨x, u, v, by simp, invariant⟩
          · obtain ⟨x', v', retX, hx1, hxy, hxx, hlt, invX⟩ := reduceX y u hy x.toNat x v (Nat.le_refl _) hx invariant
            obtain ⟨y', u', retY, hy1, hyx, hyy, hlt', invY⟩ := reduceY x' v' hx1 y.toNat y u (Nat.le_refl _) hy invX
            obtain ⟨g, u'', v'', ret, h⟩ := ih (x' + y').toNat (by omega) x' y' u' v' (by omega) hx1 hy1 invY
            exact ⟨g, u'', v'', by simp [same, retX, retY, ret], h⟩
      obtain ⟨g, u, v, ret, h⟩ := outer (a + b).toNat a b b 0 (by omega) requires.1 requires.2 (by grind)
      simp [«lcm1:ensures/2», «main/2», ret, show u * g + v * g = a * b by grind]
      """
  end
end
