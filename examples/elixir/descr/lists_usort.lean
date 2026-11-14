namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem usort1 (n : Nat) : ∀ X L, L.length ≤ n → KdU X → (∀ x ∈ L, KdU x) →
    ∃ Res, Erlang.lists.«usort_1/2» X (Term.list L) = .ok (Term.list Res) ∧
      SA (fun x : Term => x) Res ∧ Eqv (fun x : Term => x) Res (X :: L) := by
  induction n with
  | zero =>
    intro X L len _ _
    cases L with
    | cons => simp at len
    | nil =>
      rw [Erlang.lists.«usort_1/2».eq_def]
      exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | succ n ih =>
  intro X L len kx kl
  cases L with
  | nil =>
    rw [Erlang.lists.«usort_1/2».eq_def]
    exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | cons Z L =>
  have kz := kl Z (by simp)
  have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
  rw [Erlang.lists.«usort_1/2».eq_def]
  simp only [eq_ok, lt_ok, g_if]
  by_cases e1 : Term.compare (Term.fuel X Z) X Z = .eq
  · simp only [e1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := ih X L (by simp at len; omega) kx kl'
    exact ⟨Res, run, s, er.trans (drop_at (κ := (fun x : Term => x)) (P := [X]) (y := X) (by simp) e1)⟩
  simp only [e1, ↓reduceIte]
  have swap : Eqv (fun x : Term => x) ([Z, X] ++ L) (X :: Z :: L) := by
    have := eqv_move (κ := (fun x : Term => x)) (A := [X]) (B := L) (x := Z) (fun y hy => by
      simp at hy; subst hy; exact e1)
    simpa using this.symm
  by_cases l1 : (Term.compare (Term.fuel X Z) X Z).isLT = true
  · simp only [l1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := (us1 L.length).1 X Z L [] [] (by omega)
      (by simp [SD]; exact c_gt_of_lt (islt_lt l1))
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
      (by simp [RunsD]) kl'
    exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩
  simp only [l1, Bool.false_eq_true, ↓reduceIte]
  have zx := gt_of_ne (not_islt' l1) e1
  obtain ⟨Res, run, s, er⟩ := (us2 L.length).1 X Z L [] [] (by omega)
    (by simp [SA]; exact zx)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
    (by simp [RunsA]) kl'
  exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩

/-- `lists:usort/1` returns the strictly sorted list of the first element of each class of equal
terms, for terms that never compare equal to a cons cell. -/
theorem usort_spec (L : List Term) (kl : ∀ x ∈ L, KdU x) :
    ∃ R, Erlang.lists.«usort/1» (Term.list L) = .ok (Term.list R) ∧ SA (fun x : Term => x) R ∧ Eqv (fun x : Term => x) R L := by
  rw [Erlang.lists.«usort/1».eq_def]
  match L with
  | [] => exact ⟨[], by simp, by simp, Eqv.refl _⟩
  | [x] => exact ⟨[x], by simp, by simp [SA], Eqv.refl _⟩
  | X :: Y :: T =>
  have kx := kl X (by simp)
  have ky := kl Y (by simp)
  have kt : ∀ x ∈ T, KdU x := fun x hx => kl x (by simp [hx])
  simp only [lt_ok, gt_ok, eq_ok, g_if]
  by_cases l : (Term.compare (Term.fuel X Y) X Y).isLT = true
  · simp only [l, ↓reduceIte]
    have xy := islt_lt l
    have xy' : Term.compare (Term.fuel X Y) X Y ≠ .eq := by simp [xy]
    have swap : ∀ T, Eqv (fun x : Term => x) (Y :: X :: T) (X :: Y :: T) := fun T => by
      have := eqv_move (κ := (fun x : Term => x)) (A := [Y]) (B := T) (x := X)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => xy' (c_eq_symm h))
      simpa using this
    match T with
    | [] => exact ⟨[X, Y], by simp, small2 (κ := (fun x : Term => x)) xy, Eqv.refl _⟩
    | [Z] =>
      simp only []
      by_cases l2 : (Term.compare (Term.fuel Y Z) Y Z).isLT = true
      · simp only [l2, ↓reduceIte]
        exact ⟨[X, Y, Z], by simp, small3 xy (islt_lt l2), Eqv.refl _⟩
      simp only [l2, Bool.false_eq_true, ↓reduceIte]
      by_cases e2 : Term.compare (Term.fuel Y Z) Y Z = .eq
      · simp only [e2, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 (κ := (fun x : Term => x)) xy, drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := Y) (by simp) e2⟩
      simp only [e2, ↓reduceIte]
      have zy := gt_of_ne (not_islt' l2) e2
      by_cases l3 : (Term.compare (Term.fuel Z X) Z X).isLT = true
      · simp only [l3, ↓reduceIte]
        have s := small3 (κ := (fun x : Term => x)) (islt_lt l3) xy
        exact ⟨[Z, X, Y], by simp, s, eqv_perm (List.perm_append_singleton Z [X, Y]).symm s.ne⟩
      simp only [l3, Bool.false_eq_true, ↓reduceIte]
      by_cases e3 : Term.compare (Term.fuel Z X) Z X = .eq
      · simp only [e3, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 (κ := (fun x : Term => x)) xy,
          drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := X) (by simp) (c_eq_symm e3)⟩
      simp only [e3, ↓reduceIte]
      have s := small3 (κ := (fun x : Term => x)) (gt_of_ne (not_islt' l3) e3) zy
      exact ⟨[X, Z, Y], by simp, s, eqv_perm (.cons X (.swap Y Z [])) s.ne⟩
    | Z :: W :: T' =>
      simp only []
      obtain ⟨R, run, s, er⟩ := (us1 (T'.length + 2)).1 X Y (Z :: W :: T') [] [] (by simp)
        (by simp [SD]; exact c_gt_of_lt xy)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
        (by simp [RunsD]) kt
      exact ⟨R, by simpa using run, s, er.trans (by simpa using swap (Z :: W :: T'))⟩
  simp only [l, Bool.false_eq_true, ↓reduceIte]
  by_cases g : (Term.compare (Term.fuel X Y) X Y).isGT = true
  · simp only [g, ↓reduceIte]
    have yx := isgt_lt g
    have xy' : Term.compare (Term.fuel X Y) X Y ≠ .eq := by intro e; simp [e] at g
    have swap : ∀ T, Eqv (fun x : Term => x) (Y :: X :: T) (X :: Y :: T) := fun T => by
      have := eqv_move (κ := (fun x : Term => x)) (A := [Y]) (B := T) (x := X)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => xy' (c_eq_symm h))
      simpa using this
    match T with
    | [] => exact ⟨[Y, X], by simp, small2 (κ := (fun x : Term => x)) yx, swap []⟩
    | [Z] =>
      simp only []
      by_cases l2 : (Term.compare (Term.fuel X Z) X Z).isLT = true
      · simp only [l2, ↓reduceIte]
        exact ⟨[Y, X, Z], by simp, small3 yx (islt_lt l2), swap [Z]⟩
      simp only [l2, Bool.false_eq_true, ↓reduceIte]
      by_cases e2 : Term.compare (Term.fuel X Z) X Z = .eq
      · simp only [e2, ↓reduceIte]
        exact ⟨[Y, X], by simp, small2 (κ := (fun x : Term => x)) yx,
          (swap []).trans (drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := X) (by simp) e2)⟩
      simp only [e2, ↓reduceIte]
      have zx := gt_of_ne (not_islt' l2) e2
      by_cases l3 : (Term.compare (Term.fuel Z Y) Z Y).isLT = true
      · simp only [l3, ↓reduceIte]
        have s := small3 (κ := (fun x : Term => x)) (islt_lt l3) yx
        exact ⟨[Z, Y, X], by simp, s, eqv_perm (List.reverse_perm [X, Y, Z]) s.ne⟩
      simp only [l3, Bool.false_eq_true, ↓reduceIte]
      by_cases e3 : Term.compare (Term.fuel Z Y) Z Y = .eq
      · simp only [e3, ↓reduceIte]
        exact ⟨[Y, X], by simp, small2 (κ := (fun x : Term => x)) yx,
          (swap []).trans (drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := Y) (by simp) (c_eq_symm e3))⟩
      simp only [e3, ↓reduceIte]
      have s := small3 (κ := (fun x : Term => x)) (gt_of_ne (not_islt' l3) e3) zx
      exact ⟨[Y, Z, X], by simp, s, eqv_perm (List.perm_append_singleton X [Y, Z]) s.ne⟩
    | Z :: W :: T' =>
      simp only []
      obtain ⟨R, run, s, er⟩ := (us2 (T'.length + 2)).1 X Y (Z :: W :: T') [] [] (by simp)
        (by simp [SA]; exact yx)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
        (by simp [RunsA]) kt
      exact ⟨R, by simpa using run, s, er.trans (by simpa using swap (Z :: W :: T'))⟩
  simp only [g, Bool.false_eq_true, ↓reduceIte]
  have e : Term.compare (Term.fuel X Y) X Y = .eq := by
    cases h : Term.compare (Term.fuel X Y) X Y <;> simp_all
  obtain ⟨R, run, s, er⟩ := usort1 T.length X T (by omega) kx kt
  exact ⟨R, run, s, er.trans (drop_at (κ := (fun x : Term => x)) (P := [X]) (y := X) (by simp) e)⟩

end Elixir.STTDescrProofsTest.USort
