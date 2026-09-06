import Lynx.Term
import Std

namespace Lynx.Term

/-- Erlang term order for the represented types: integer < atom < nil < cons.
Atoms use Unicode codepoint order; cons cells compare heads, then tails,
including improper tails. See https://www.erlang.org/doc/system/expressions.html#term-comparisons.
-/
def compare : Term → Term → Ordering
  | .integer x, .integer y => Ord.compare x y
  | .integer _, _ => .lt
  | _, .integer _ => .gt
  | .atom x, .atom y => Ord.compare x y
  | .atom _, _ => .lt
  | _, .atom _ => .gt
  | .nil, .nil => .eq
  | .nil, .cons _ _ => .lt
  | .cons _ _, .nil => .gt
  | .cons x xs, .cons y ys => (compare x y).then (compare xs ys)

theorem compare_eq_spec (a b : Term) : compare a b = .eq ↔ a = b := by
  induction a generalizing b <;> cases b <;>
    simp_all [compare]

theorem compare_swap_spec (a b : Term) : compare a b = (compare b a).swap := by
  induction a generalizing b <;> cases b <;>
    simp_all only [compare, Ordering.swap_then, Ordering.swap_eq, Ordering.swap_lt,
      Ordering.swap_gt]
  all_goals exact Std.OrientedOrd.eq_swap

theorem compare_le_trans_spec (a b c : Term)
    (ab : (compare a b).isLE) (bc : (compare b c).isLE) :
    (compare a c).isLE := by
  induction a generalizing b c <;> cases b <;> cases c <;>
    simp only [compare, Ordering.isLE_lt, Ordering.isLE_eq, Ordering.isLE_gt,
      Bool.false_eq_true] at ab bc ⊢
  all_goals try contradiction
  all_goals try trivial
  all_goals try exact Std.TransOrd.isLE_trans ab bc
  case cons.cons.cons ah ats ihh iht bh bt ch ct =>
    have hab := Ordering.isLE_left_of_isLE_then ab
    have hbc := Ordering.isLE_left_of_isLE_then bc
    have hac := ihh bh ch hab hbc
    cases e : compare ah ch with
    | lt => simp
    | gt => simp [e] at hac
    | eq =>
      have same := (compare_eq_spec ah ch).mp e
      subst ch
      have eqAB : compare ah bh = .eq := by
        rw [compare_swap_spec bh ah] at hbc
        cases h : compare ah bh <;> simp_all
      have same := (compare_eq_spec ah bh).mp eqAB
      subst bh
      have self := (compare_eq_spec ah ah).mpr rfl
      simp only [self, Ordering.eq_then] at ab bc ⊢
      exact iht bt ct ab bc

theorem compare_le_total_spec (a b : Term) :
    (compare a b).isLE ∨ (compare b a).isLE := by
  rw [compare_swap_spec b a]
  cases compare a b <;> decide

/-- Non-strict Erlang term order, used in mathematical specifications. -/
abbrev le (a b : Term) : Prop := (compare a b).isLE

end Lynx.Term
