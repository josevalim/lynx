namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term}

theorem eqv_perm {A B : List Term} (p : A.Perm B)
    (h : A.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) : Eqv κ A B := by
  induction p with
  | nil => exact Eqv.refl _
  | cons x _ ih => exact Eqv.cons x (ih (List.pairwise_cons.1 h).2)
  | swap x y l =>
    have hyx : Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) ≠ .eq := (List.pairwise_cons.1 h).1 x (by simp)
    have := eqv_move (κ := κ) (A := [y]) (B := l) (x := x) (by simpa using hyx)
    simpa using this
  | trans p1 _ ih1 ih2 =>
    exact (ih1 h).trans (ih2 ((p1.pairwise_iff fun e => fun e' => e (c_eq_symm e')).1 h))

end

section
variable {κ : Term → Term}

theorem and_tt : Erlang.erlang.«and/2» (.atom "true") (.atom "true") = .ok (.atom "true") := by
  simp [Erlang.erlang.«and/2»]

theorem small2 {a b : Term} (h : Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .lt) : SA κ [a, b] := by
  simp [SA, h]

theorem small3 {a b c : Term} (h1 : Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .lt) (h2 : Term.compare (Term.fuel (κ b) (κ c)) (κ b) (κ c) = .lt) :
    SA κ [a, b, c] := by
  simp [SA, h1, h2, c_lt_trans h1 h2]

/-- `lists:ukeysort/2` returns the strictly key-sorted list of the first element of each key. -/
theorem ukeysort_spec (i : Int) (hi : 0 < i) (L : List Term) (kl : ∀ x ∈ L, KdK (.integer i) κ x) :
    ∃ R, Erlang.lists.«ukeysort/2» (.integer i) (Term.list L) = .ok (Term.list R) ∧ SA κ R ∧
      Eqv κ R L := by
  rw [Erlang.lists.«ukeysort/2».eq_def]
  simp only [Erlang.erlang.«>/2_integers», hi, ↓reduceIte, Lynx.Except.ok_bind, Term.true, and_tt,
    Lynx.Except.guard_ok]
  match L with
  | [] => exact ⟨[], by simp, by simp, Eqv.refl _⟩
  | [x] => exact ⟨[x], by simp, by simp [SA], Eqv.refl _⟩
  | X :: Y :: T =>
  have kx := kl X (by simp)
  have ky := kl Y (by simp)
  have kt : ∀ x ∈ T, KdK (.integer i) κ x := fun x hx => kl x (by simp [hx])
  simp only [kx.1, ky.1, Lynx.Except.ok_bind, eq_ok, lt_ok, le_ok, g_if]
  by_cases e : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .eq
  · simp only [e, ↓reduceIte]
    obtain ⟨R, run, s, er⟩ := uksort1 (I := .integer i) (κ := κ) T.length X T (by omega) kx kt
    exact ⟨R, run, s, er.trans (drop_at (P := [X]) (y := X) (by simp) e)⟩
  simp only [e, ↓reduceIte]
  by_cases l : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .lt
  · simp only [l, Ordering.isLT_lt, ↓reduceIte]
    match T with
    | [] => exact ⟨[X, Y], by simp, small2 l, Eqv.refl _⟩
    | [Z] =>
      have kz := (kl Z (by simp)).1
      simp only [kz, Lynx.Except.ok_bind]
      by_cases e2 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
      · simp only [e2, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 l, drop_at (P := [X, Y]) (L := []) (y := Y) (by simp) e2⟩
      simp only [e2, ↓reduceIte]
      by_cases l2 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
      · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
        exact ⟨[X, Y, Z], by simp, small3 l l2, Eqv.refl _⟩
      simp only [not_islt l2, Bool.false_eq_true, ↓reduceIte]
      have zy := lt_swap_of e2 l2
      by_cases e3 : Term.compare (Term.fuel (κ Z) (κ X)) (κ Z) (κ X) = .eq
      · simp only [e3, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 l,
          drop_at (P := [X, Y]) (L := []) (y := X) (by simp) (c_eq_symm e3)⟩
      simp only [e3, ↓reduceIte]
      have e3' : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) ≠ .eq := fun h => e3 (c_eq_symm h)
      by_cases l3 : (Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z)).isLE = true
      · simp only [l3, ↓reduceIte]
        have xz := le_ne_lt l3 e3'
        have s := small3 xz zy
        exact ⟨[X, Z, Y], by simp, s, eqv_perm (.cons X (.swap Y Z [])) s.ne⟩
      simp only [l3, Bool.false_eq_true, ↓reduceIte]
      have s := small3 (not_le_lt l3) l
      exact ⟨[Z, X, Y], by simp, s, eqv_perm (List.perm_append_singleton Z [X, Y]).symm s.ne⟩
    | Z :: W :: T' =>
      simp only []
      obtain ⟨R, run, s, er⟩ := (uks1 (I := .integer i) (κ := κ) (T'.length + 2)).1 X Y (Z :: W :: T') []
        [] (by simp) (by simp [SD]; exact c_gt_of_lt l)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
        (by simp [RunsD]) kt
      have := eqv_move (κ := κ) (A := [Y]) (B := Z :: W :: T') (x := X)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => e (c_eq_symm h))
      exact ⟨R, by simpa using run, s, er.trans (by simpa using this)⟩
  simp only [not_islt l, Bool.false_eq_true, ↓reduceIte]
  have yx := lt_swap_of e l
  have swap : ∀ T, Eqv κ (Y :: X :: T) (X :: Y :: T) := fun T => by
    have := eqv_move (κ := κ) (A := [Y]) (B := T) (x := X)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => e (c_eq_symm h))
    simpa using this
  match T with
  | [] => exact ⟨[Y, X], by simp, small2 yx, swap []⟩
  | [Z] =>
    have kz := (kl Z (by simp)).1
    simp only [kz, Lynx.Except.ok_bind]
    by_cases e2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
    · simp only [e2, ↓reduceIte]
      exact ⟨[Y, X], by simp, small2 yx,
        (swap []).trans (drop_at (P := [X, Y]) (L := []) (y := X) (by simp) e2)⟩
    simp only [e2, ↓reduceIte]
    by_cases l2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
    · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
      exact ⟨[Y, X, Z], by simp, small3 yx l2, swap [Z]⟩
    simp only [not_islt l2, Bool.false_eq_true, ↓reduceIte]
    have zx := lt_swap_of e2 l2
    by_cases e3 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
    · simp only [e3, ↓reduceIte]
      exact ⟨[Y, X], by simp, small2 yx,
        (swap []).trans (drop_at (P := [X, Y]) (L := []) (y := Y) (by simp) e3)⟩
    simp only [e3, ↓reduceIte]
    by_cases l3 : (Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z)).isLE = true
    · simp only [l3, ↓reduceIte]
      have s := small3 (le_ne_lt l3 e3) zx
      exact ⟨[Y, Z, X], by simp, s, eqv_perm (List.perm_append_singleton X [Y, Z]) s.ne⟩
    simp only [l3, Bool.false_eq_true, ↓reduceIte]
    have s := small3 (not_le_lt l3) yx
    exact ⟨[Z, Y, X], by simp, s, eqv_perm (List.reverse_perm [X, Y, Z]) s.ne⟩
  | Z :: W :: T' =>
    simp only []
    obtain ⟨R, run, s, er⟩ := uks2 (I := .integer i) (κ := κ) (T'.length + 2) Y (Z :: W :: T') [X]
      (by simp) (small2 yx) (by simp)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
      kt
    exact ⟨R, by simpa using run, s, er.trans (by simpa using swap (Z :: W :: T'))⟩

end

end Elixir.STTDescrProofsTest.USort
