namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Lists of terms: positions and replacements. -/

theorem nth1_cons {k : Int} (hk : k ≠ 1) (h t : Term) :
    Erlang.lists.«nth_1/2» (.integer k) (.cons h t) = Erlang.lists.«nth_1/2» (.integer (k - 1)) t := by
  conv => lhs; rw [Erlang.lists.«nth_1/2».eq_def]
  split
  · rename_i h₁ _; simp only [Term.integer.injEq] at h₁; omega
  · rename_i h₁ _; simp only [Term.cons.injEq] at h₁; obtain ⟨rfl, rfl⟩ := h₁; simp
  · exfalso; simp_all

theorem nth1_list : ∀ (xs : List Term) (j : Nat) (h : j < xs.length),
    Erlang.lists.«nth_1/2» (.integer ((j : Int) + 1)) (Term.list xs) = .ok xs[j]
  | x :: xs, 0, _ => by
    rw [Erlang.lists.«nth_1/2».eq_def]; rfl
  | x :: xs, j + 1, h => by
    have ih := nth1_list xs j (by simp at h; omega)
    rw [show Term.list (x :: xs) = .cons x (Term.list xs) from rfl, nth1_cons (by omega)]
    rw [show ((j + 1 : Nat) : Int) + 1 - 1 = (j : Int) + 1 by omega]
    exact ih

theorem nth_list (xs : List Term) (j : Nat) (h : j < xs.length) :
    Erlang.lists.«nth/2» (.integer ((j : Int) + 1)) (Term.list xs) = .ok xs[j] := by
  match xs, j, h with
  | x :: xs, 0, _ => rfl
  | x :: xs, j + 1, h =>
    have := nth1_list (x :: xs) (j + 1) h
    unfold Erlang.lists.«nth/2»
    split
    · rename_i h₁ _; simp only [Term.integer.injEq] at h₁; omega
    · have gt : ((j + 1 : Nat) : Int) + 1 > 1 := by omega
      have c : Ord.compare ((j : Int) + 1 + 1) 1 = Ordering.gt := by
        first
          | exact Int.compare_eq_gt.mpr (by omega)
          | (simp only [compare, compareOfLessAndEq]; split <;> first | omega | (split <;> first | rfl | omega))
      simp [Term.list, Erlang.erlang.«>/2», Erlang.erlang.«and/2», c] at this ⊢
      exact this

theorem replace_cons {k : Int} (hk : k ≠ 0) (h t v : Term) :
    Elixir.List.«do_replace_at/3» (.cons h t) (.integer k) v = (do
      let r ← Elixir.List.«do_replace_at/3» t (.integer (k - 1)) v
      pure (.cons h r)) := by
  conv => lhs; rw [Elixir.List.«do_replace_at/3».eq_def]
  split
  · rename_i h₁; simp at h₁
  · rename_i h₁; simp only [Term.integer.injEq] at h₁; omega
  · rename_i heq _; simp only [Term.cons.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    rw [Erlang.erlang.«-/2_integers», Lynx.Except.ok_bind]
  · exfalso; simp_all

theorem do_replace_list : ∀ (xs : List Term) (j : Nat) (v : Term), j < xs.length →
    Elixir.List.«do_replace_at/3» (Term.list xs) (.integer j) v = .ok (Term.list (xs.set j v))
  | x :: xs, 0, v, _ => by rw [Elixir.List.«do_replace_at/3».eq_def]; rfl
  | x :: xs, j + 1, v, h => by
    have ih := do_replace_list xs j v (by simp at h; omega)
    rw [show Term.list (x :: xs) = .cons x (Term.list xs) from rfl, replace_cons (by omega)]
    rw [show ((j + 1 : Nat) : Int) - 1 = (j : Int) by omega, ih]
    rfl

theorem replace_list (xs : List Term) (j : Nat) (v : Term) (h : j < xs.length) :
    Elixir.List.«replace_at/3» (Term.list xs) (.integer j) v = .ok (Term.list (xs.set j v)) := by
  have c : Ord.compare (j : Int) 0 ≠ Ordering.lt := by
    first
      | exact fun e => absurd (Int.compare_eq_lt.mp e) (by omega)
      | (simp only [compare, compareOfLessAndEq]; split <;> first | omega | (split <;> simp))
  have run := do_replace_list xs j v h
  unfold Elixir.List.«replace_at/3»
  cases xs with
  | nil => simp at h
  | cons x xs =>
    simp [Erlang.erlang.«is_list/1», Erlang.erlang.«is_integer/1», Erlang.erlang.«</2», c,
      Term.list, Lynx.Except.andAlso] at run ⊢
    exact run

end Elixir.STTDescrProofsTest.Nest
