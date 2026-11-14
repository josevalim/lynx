namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {I : Term} {κ : Term → Term}

theorem uks2 (n : Nat) : ∀ Y L R, L.length ≤ n → SA κ (Y :: R) → R ≠ [] → (∀ x ∈ Y :: R, (KdK I κ) x) →
    (∀ x ∈ L, (KdK I κ) x) →
    ∃ Res, Erlang.lists.«ukeysplit_2/5» I Y (κ Y) (Term.list L) (Term.list R) = .ok (Term.list Res) ∧
      SA κ Res ∧ Eqv κ Res ((Y :: R) ++ L) := by
  induction n with
  | zero =>
    intro Y L R len sr _ _ _
    cases L with
    | cons => simp at len
    | nil =>
      rw [Erlang.lists.«ukeysplit_2/5».eq_def]
      exact ⟨Y :: R, by simp, sr, by simpa using Eqv.refl (Y :: R)⟩
  | succ n ih =>
  intro Y L R len sr rn kr kl
  cases L with
  | nil =>
    rw [Erlang.lists.«ukeysplit_2/5».eq_def]
    exact ⟨Y :: R, by simp, sr, by simpa using Eqv.refl (Y :: R)⟩
  | cons Z L =>
  have kz := kl Z (by simp)
  have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
  have len' : L.length ≤ n := by simp at len; omega
  have sr' := SA_cons.1 sr
  rw [Erlang.lists.«ukeysplit_2/5».eq_def]
  simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
  by_cases e1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
  · simp only [e1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := ih Y L R len' sr rn kr kl'
    have dd := drop_at (κ := κ) (P := Y :: R) (L := L) (y := Y) (z := Z) (by simp) e1
    exact ⟨Res, run, s, er.trans dd⟩
  simp only [e1, ↓reduceIte]
  by_cases l1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
  · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
    have rv := rev2 R []
    simp only [List.append_nil] at rv
    simp only [rv, Lynx.Except.ok_bind]
    obtain ⟨Res, run, s, er⟩ := (uks1 (I := I) (κ := κ) L.length).1 Y Z L [] [R.reverse] (by omega)
      (by simp [SD]; exact c_gt_of_lt l1)
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl; exact kz; exact kr _ (by simp))
      (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact ⟨by simpa using rn, SD_reverse.2 sr'.2, fun x hx => kr x (by simp at hx; simp [hx])⟩)
      kl'
    refine ⟨Res, by simpa using run, s, er.trans ?_⟩
    -- rev R ++ [Z, Y] ++ L ≈ Y :: R ++ Z :: L
    have e2 := eqv_move (κ := κ) (A := R ++ [Z]) (B := L) (x := Y) (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl
      · rw [c_swap, sr'.1 y hy]; simp
      · intro e; exact e1 (c_eq_symm e))
    have e3 := (eqv_reverse (κ := κ) (SA.ne sr'.2)).append (Eqv.refl (Z :: Y :: L))
    simp only [List.append_assoc, List.cons_append, List.nil_append] at e2 e3 ⊢
    simpa using e3.trans e2
  have zy := lt_swap_of e1 l1
  simp only [not_islt l1, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨Res, run, s, er⟩ := ih Z L (Y :: R) len' (SA_cons.2 ⟨SA.lt_all sr zy, sr⟩) (by simp)
    (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kr x (by simpa using hx))
    kl'
  have := eqv_move (κ := κ) (A := Y :: R) (B := L) (x := Z) (fun y hy => by
    have := SA.lt_all sr zy y hy; rw [c_swap, this]; simp)
  exact ⟨Res, by simpa using run, s, er.trans (by simpa using this.symm)⟩

theorem uksort1 (n : Nat) : ∀ X L, L.length ≤ n → (KdK I κ) X → (∀ x ∈ L, (KdK I κ) x) →
    ∃ Res, Erlang.lists.«ukeysort_1/4» I X (κ X) (Term.list L) = .ok (Term.list Res) ∧
      SA κ Res ∧ Eqv κ Res (X :: L) := by
  induction n with
  | zero =>
    intro X L len _ _
    cases L with
    | cons => simp at len
    | nil =>
      rw [Erlang.lists.«ukeysort_1/4».eq_def]
      exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | succ n ih =>
  intro X L len kx kl
  cases L with
  | nil =>
    rw [Erlang.lists.«ukeysort_1/4».eq_def]
    exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | cons Z L =>
  have kz := kl Z (by simp)
  have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
  rw [Erlang.lists.«ukeysort_1/4».eq_def]
  simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
  by_cases e1 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
  · simp only [e1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := ih X L (by simp at len; omega) kx kl'
    exact ⟨Res, run, s, er.trans (drop_at (P := [X]) (y := X) (by simp) e1)⟩
  simp only [e1, ↓reduceIte]
  have swap : Eqv κ ([Z, X] ++ L) (X :: Z :: L) := by
    have := eqv_move (κ := κ) (A := [X]) (B := L) (x := Z) (fun y hy => by
      simp at hy; subst hy; exact e1)
    simpa using this.symm
  by_cases l1 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
  · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := (uks1 (I := I) (κ := κ) L.length).1 X Z L [] [] (by omega)
      (by simp [SD]; exact c_gt_of_lt l1)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
      (by simp [RunsD]) kl'
    exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩
  have zx := lt_swap_of e1 l1
  simp only [not_islt l1, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨Res, run, s, er⟩ := uks2 (I := I) (κ := κ) L.length Z L [X] (by omega)
    (by simp [SA]; exact zx) (by simp)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
    kl'
  exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩

end

end Elixir.STTDescrProofsTest.USort
