namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term}

/-- An element moved into the middle of a run, past keys it does not share. -/
theorem ins_mid {P A B L : List Term} {z : Term}
    (h : ∀ y ∈ A ++ B, Term.compare (Term.fuel (κ y) (κ z)) (κ y) (κ z) ≠ .eq) :
    Eqv κ (P ++ (A ++ z :: B) ++ L) (P ++ (A ++ B) ++ z :: L) := by
  have e1 := eqv_move (κ := κ) (A := A) (B := B ++ L) (x := z) (fun y hy => h y (by simp [hy]))
  have e2 := eqv_move (κ := κ) (A := A ++ B) (B := L) (x := z) h
  simp only [List.append_assoc] at e1 e2 ⊢
  exact (Eqv.refl P).append (e1.trans e2.symm)

theorem drop_at {P L : List Term} {y z : Term} (hy : y ∈ P) (e : Term.compare (Term.fuel (κ y) (κ z)) (κ y) (κ z) = .eq) :
    Eqv κ (P ++ L) (P ++ z :: L) := (eqv_drop hy e).symm

theorem not_islt {a b : Term} (h : ¬Term.compare (Term.fuel a b) a b = .lt) : ¬(Term.compare (Term.fuel a b) a b).isLT = true := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all

theorem lt_swap_of {a b : Term} (e : ¬Term.compare (Term.fuel a b) a b = .eq) (l : ¬Term.compare (Term.fuel a b) a b = .lt) :
    Term.compare (Term.fuel b a) b a = .lt := by
  cases e' : Term.compare (Term.fuel a b) a b
  · exact absurd e' l
  · exact absurd e' e
  · exact c_lt_of_gt e'

theorem nil_cmp {R : List Term} : Term.compare (Term.fuel (Term.list R) .nil) (Term.list R) .nil = .eq ↔ R = [] := by
  cases R <;> simp

end

section
variable {I : Term} {κ : Term → Term}

theorem uks1_end (X Y : Term) (R : List Term) (Rs : List (List Term)) (sc : SD κ (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, (KdK I κ) x) (rs : RunsD (κ := κ) (KdK I κ) Rs) :
    ∃ Res, Erlang.lists.«ukeysplit_1/8» I X (κ X) Y (κ Y) (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA κ Res ∧
      Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ []) := by
  rw [Erlang.lists.«ukeysplit_1/8».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (ukm_mergel (I := I) (κ := κ) (4 * (Rs.length + 2) + 1)).2
    ((Y :: X :: R) :: Rs) [] (by simp; omega) (by simp) (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨by simp, sc, kc⟩
      · exact rs r hr) (by simp [RunsA])
  exact ⟨Res, by simpa using run, sr, by simpa using er⟩

theorem uks11_end (X Y S : Term) (R : List Term) (Rs : List (List Term)) (sc : SD κ (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, (KdK I κ) x) (ks : (KdK I κ) S) (rs : RunsD (κ := κ) (KdK I κ) Rs) :
    ∃ Res, Erlang.lists.«ukeysplit_1_1/10» I X (κ X) Y (κ Y) (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) S (κ S) = .ok (Term.list Res) ∧ SA κ Res ∧
      Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ [S]) := by
  rw [Erlang.lists.«ukeysplit_1_1/10».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (ukm_mergel (I := I) (κ := κ) (4 * (Rs.length + 3) + 1)).2
    ([S] :: (Y :: X :: R) :: Rs) [] (by simp; omega) (by simp) (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact ⟨by simp, by simp [SD], by simpa using ks⟩
      · exact ⟨by simp, sc, kc⟩
      · exact rs r hr) (by simp [RunsA])
  exact ⟨Res, by simpa using run, sr, by simpa using er⟩

theorem uks1 (n : Nat) :
    (∀ X Y L R Rs, L.length ≤ n → SD κ (Y :: X :: R) → (∀ x ∈ Y :: X :: R, (KdK I κ) x) →
      RunsD (κ := κ) (KdK I κ) Rs → (∀ x ∈ L, (KdK I κ) x) →
      ∃ Res, Erlang.lists.«ukeysplit_1/8» I X (κ X) Y (κ Y) (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA κ Res ∧
        Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ L)) ∧
    (∀ X Y L R Rs S, L.length ≤ n → SD κ (Y :: X :: R) → (∀ x ∈ Y :: X :: R, (KdK I κ) x) →
      Term.compare (Term.fuel (κ S) (κ X)) (κ S) (κ X) = .lt → (KdK I κ) S → RunsD (κ := κ) (KdK I κ) Rs → (∀ x ∈ L, (KdK I κ) x) →
      ∃ Res, Erlang.lists.«ukeysplit_1_1/10» I X (κ X) Y (κ Y) (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) S (κ S) = .ok (Term.list Res) ∧ SA κ Res ∧
        Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ S :: L)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro X Y L R Rs len sc kc rs _
      cases L with
      | cons => simp at len
      | nil => exact uks1_end X Y R Rs sc kc rs
    · intro X Y L R Rs S len sc kc _ ks rs _
      cases L with
      | cons => simp at len
      | nil => exact uks11_end X Y S R Rs sc kc ks rs
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro X Y L R Rs len sc kc rs kl
    cases L with
    | nil => exact uks1_end X Y R Rs sc kc rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .lt := c_lt_of_gt (sc'.1 X (by simp))
    rw [Erlang.lists.«ukeysplit_1/8».eq_def]
    simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
    by_cases e1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := Y) (z := Z)
        (by simp) e1
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have zy : Term.compare (Term.fuel (κ Z) (κ Y)) (κ Z) (κ Y) ≠ .eq := fun e => e1 (c_eq_symm e)
    by_cases l1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
    · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
      have gz := SD.gt_all sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih1 Y Z L (X :: R) Rs len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R) (L := L) (z := Z)
        (fun y hy => by have := gz y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l1' := not_islt l1
    simp only [l1', Bool.false_eq_true, ↓reduceIte]
    have gzy := lt_swap_of e1 l1
    by_cases e2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := X) (z := Z)
        (by simp) e2
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have sx := SD_cons.1 sc'.2
    by_cases l2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
    · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
      have gzx := SD.gt_all sc'.2 (c_gt_of_lt l2)
      obtain ⟨Res, run, sr, er⟩ := ih1 Z Y L (X :: R) Rs len'
        (SD_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact c_gt_of_lt gzy
            · exact sc'.1 w (by simpa using hw), SD_cons.2 ⟨gzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hy
          rcases hy with rfl | hy
          · intro e; exact zy (c_eq_symm e)
          · have := gzx y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l2' := not_islt l2
    simp only [l2', Bool.false_eq_true, ↓reduceIte]
    have gzx := lt_swap_of e2 l2
    cases R with
    | nil =>
      simp only [Term.compare_self, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L [Z] Rs len'
        (by simp [SD]; exact ⟨⟨sc'.1 X (by simp), c_gt_of_lt (c_lt_trans gzx yx)⟩, c_gt_of_lt gzx⟩)
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact kc x (by simp)
          · exact kc x (by simp)
          · exact kz)
        rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
    | cons r R =>
      have : ¬Term.compare (Term.fuel (Term.list (r :: R)) .nil) (Term.list (r :: R)) .nil = .eq := by simp
      simp only [this, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L (r :: R) Rs Z len' sc kc gzx kz rs kl'
      exact ⟨Res, run, sr, by simpa using er⟩
  · intro X Y L R Rs S len sc kc sx ks rs kl
    cases L with
    | nil => exact uks11_end X Y S R Rs sc kc ks rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .lt := c_lt_of_gt (sc'.1 X (by simp))
    have sy := c_lt_trans sx yx
    rw [Erlang.lists.«ukeysplit_1_1/10».eq_def]
    simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
    by_cases e1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := Y)
        (z := Z) (by simp) e1
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have zy : Term.compare (Term.fuel (κ Z) (κ Y)) (κ Z) (κ Y) ≠ .eq := fun e => e1 (c_eq_symm e)
    by_cases l1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
    · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
      have gz := SD.gt_all sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih2 Y Z L (X :: R) Rs S len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        sy ks rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R ++ [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · have := gz y hy; rw [c_swap, this]; simp
          · rw [c_lt_trans sy l1]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l1' := not_islt l1
    simp only [l1', Bool.false_eq_true, ↓reduceIte]
    have gzy := lt_swap_of e1 l1
    by_cases e2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := X)
        (z := Z) (by simp) e2
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    by_cases l2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
    · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
      have gzx := SD.gt_all sc'.2 (c_gt_of_lt l2)
      obtain ⟨Res, run, sr, er⟩ := ih2 Z Y L (X :: R) Rs S len'
        (SD_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact c_gt_of_lt gzy
            · exact sc'.1 w (by simpa using hw), SD_cons.2 ⟨gzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        (c_lt_trans sx l2) ks rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R ++ [S]) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | hy | rfl
          · intro e; exact zy (c_eq_symm e)
          · rw [c_swap, gzx _ (by simp)]; simp
          · rw [c_swap, gzx y (by simp [hy])]; simp
          · rw [c_lt_trans sx l2]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l2' := not_islt l2
    simp only [l2', Bool.false_eq_true, ↓reduceIte]
    have rs' : RunsD (κ := κ) (KdK I κ) ((Y :: X :: R) :: Rs) := by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨by simp, sc, kc⟩
      · exact rs r hr
    by_cases e3 : Term.compare (Term.fuel (κ S) (κ Z)) (κ S) (κ Z) = .eq
    · simp only [e3, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := S)
        (z := Z) (by simp) e3
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e3, ↓reduceIte]
    by_cases l3 : Term.compare (Term.fuel (κ S) (κ Z)) (κ S) (κ Z) = .lt
    · simp only [l3, Ordering.isLT_lt, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 S Z L [] ((Y :: X :: R) :: Rs) len'
        (by simp [SD]; exact c_gt_of_lt l3)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact ks)
        rs' kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R) (A := []) (B := [S]) (L := L)
        (z := Z) (fun y hy => by simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; exact e3)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l3' := not_islt l3
    simp only [l3', Bool.false_eq_true, ↓reduceIte]
    have gzs := lt_swap_of e3 l3
    obtain ⟨Res, run, sr, er⟩ := ih1 Z S L [] ((Y :: X :: R) :: Rs) len'
      (by simp [SD]; exact c_gt_of_lt gzs)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ks; exact kz)
      rs' kl'
    exact ⟨Res, by simpa using run, sr, by simpa using er⟩

end

end Elixir.STTDescrProofsTest.USort
