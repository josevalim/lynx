namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem isgt_lt {a b : Term} (h : (Term.compare (Term.fuel a b) a b).isGT = true) : Term.compare (Term.fuel b a) b a = .lt := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all [c_lt_of_gt]

theorem not_isgt {a b : Term} (h : ¬(Term.compare (Term.fuel a b) a b).isGT = true) : Term.compare (Term.fuel a b) a b ≠ .gt := by
  intro e; simp [e] at h

theorem lt_of_ne {a b : Term} (g : Term.compare (Term.fuel a b) a b ≠ .gt) (e : ¬Term.compare (Term.fuel a b) a b = .eq) :
    Term.compare (Term.fuel a b) a b = .lt := by
  cases h : Term.compare (Term.fuel a b) a b <;> simp_all

theorem islt_lt {a b : Term} (h : (Term.compare (Term.fuel a b) a b).isLT = true) : Term.compare (Term.fuel a b) a b = .lt := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all

theorem not_islt' {a b : Term} (h : ¬(Term.compare (Term.fuel a b) a b).isLT = true) : Term.compare (Term.fuel a b) a b ≠ .lt := by
  intro e; simp [e] at h

theorem gt_of_ne {a b : Term} (l : Term.compare (Term.fuel a b) a b ≠ .lt) (e : ¬Term.compare (Term.fuel a b) a b = .eq) :
    Term.compare (Term.fuel b a) b a = .lt := by
  cases h : Term.compare (Term.fuel a b) a b
  · exact absurd h l
  · exact absurd h e
  · exact c_lt_of_gt h

theorem us1_end (X Y : Term) (R : List Term) (Rs : List (List Term)) (sc : SD (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (rs : RunsD (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_1/5» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ []) := by
  rw [Erlang.lists.«usplit_1/5».eq_def]
  cases R <;>
  · obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 2) + 1)).2 true
      ((Y :: X :: _) :: Rs) [] (by simp; omega) (by simp) (runsD_cons ⟨by simp, sc, kc⟩ rs)
      (by simp [RunsA])
    exact ⟨Res, by simpa [modeT] using run, sr, by simpa [rcontent] using er⟩

theorem us11_end (X Y S : Term) (R : List Term) (Rs : List (List Term)) (sc : SD (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (ks : KdU S) (rs : RunsD (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_1_1/6» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ [S]) := by
  rw [Erlang.lists.«usplit_1_1/6».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 3) + 1)).2 true
    ([S] :: (Y :: X :: R) :: Rs) [] (by simp; omega) (by simp)
    (runsD_cons ⟨by simp, by simp [SD], by simpa using ks⟩ (runsD_cons ⟨by simp, sc, kc⟩ rs))
    (by simp [RunsA])
  exact ⟨Res, by simpa [modeT] using run, sr, by simpa [rcontent] using er⟩

theorem us1 (n : Nat) :
    (∀ X Y L R Rs, L.length ≤ n → SD (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      RunsD (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_1/5» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ L)) ∧
    (∀ X Y L R Rs S, L.length ≤ n → SD (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      Term.compare (Term.fuel S X) S X = .lt → KdU S → RunsD (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_1_1/6» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ S :: L)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro X Y L R Rs len sc kc rs _
      cases L with
      | cons => simp at len
      | nil => exact us1_end X Y R Rs sc kc rs
    · intro X Y L R Rs S len sc kc _ ks rs _
      cases L with
      | cons => simp at len
      | nil => exact us11_end X Y S R Rs sc kc ks rs
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro X Y L R Rs len sc kc rs kl
    cases L with
    | nil => exact us1_end X Y R Rs sc kc rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel X Y) X Y = .lt := c_lt_of_gt (sc'.1 X (by simp))
    rw [Erlang.lists.«usplit_1/5».eq_def]
    simp only [eq_ok, gt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isGT = true
    · simp only [g1, ↓reduceIte]
      have l1 := isgt_lt g1
      have gz := SD.gt_all (κ := (fun x : Term => x)) sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih1 Y Z L (X :: R) Rs len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R) (L := L) (z := Z)
        (fun y hy => by have := gz y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := Y) (z := Z)
        (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have gzy := lt_of_ne (not_isgt g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isGT = true
    · simp only [g2, ↓reduceIte]
      have l2 := isgt_lt g2
      have gzx := SD.gt_all (κ := (fun x : Term => x)) sc'.2 (c_gt_of_lt l2)
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
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hy
          rcases hy with rfl | hy
          · intro e; exact zy (c_eq_symm e)
          · have := gzx y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := X) (z := Z)
        (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have gzx := lt_of_ne (not_isgt g2) e2
    cases R with
    | nil =>
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
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L (r :: R) Rs Z len' sc kc gzx kz rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
  · intro X Y L R Rs S len sc kc sx ks rs kl
    cases L with
    | nil => exact us11_end X Y S R Rs sc kc ks rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel X Y) X Y = .lt := c_lt_of_gt (sc'.1 X (by simp))
    have sy := c_lt_trans sx yx
    rw [Erlang.lists.«usplit_1_1/6».eq_def]
    simp only [eq_ok, gt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isGT = true
    · simp only [g1, ↓reduceIte]
      have l1 := isgt_lt g1
      have gz := SD.gt_all (κ := (fun x : Term => x)) sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih2 Y Z L (X :: R) Rs S len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        sy ks rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R ++ [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with hy | rfl
          · have := gz y (by simpa using hy); rw [c_swap, this]; simp
          · rw [c_lt_trans sy l1]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := Y)
        (z := Z) (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have gzy := lt_of_ne (not_isgt g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isGT = true
    · simp only [g2, ↓reduceIte]
      have l2 := isgt_lt g2
      have gzx := SD.gt_all (κ := (fun x : Term => x)) sc'.2 (c_gt_of_lt l2)
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
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R ++ [S]) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | hy | rfl
          · intro e; exact zy (c_eq_symm e)
          · rw [c_swap, gzx _ (by simp)]; simp
          · rw [c_swap, gzx y (by simp [hy])]; simp
          · rw [c_lt_trans sx l2]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := X)
        (z := Z) (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have rs' : RunsD (κ := (fun x : Term => x)) KdU ((Y :: X :: R) :: Rs) := runsD_cons ⟨by simp, sc, kc⟩ rs
    by_cases g3 : (Term.compare (Term.fuel Z S) Z S).isGT = true
    · simp only [g3, ↓reduceIte]
      have l3 := isgt_lt g3
      obtain ⟨Res, run, sr, er⟩ := ih1 S Z L [] ((Y :: X :: R) :: Rs) len'
        (by simp [SD]; exact c_gt_of_lt l3)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact ks)
        rs' kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (A := []) (B := [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          subst hy; rw [l3]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g3, Bool.false_eq_true, ↓reduceIte]
    by_cases e3 : Term.compare (Term.fuel Z S) Z S = .eq
    · simp only [e3, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := S)
        (z := Z) (by simp) (c_eq_symm e3)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e3, ↓reduceIte]
    have gzs := lt_of_ne (not_isgt g3) e3
    obtain ⟨Res, run, sr, er⟩ := ih1 Z S L [] ((Y :: X :: R) :: Rs) len'
      (by simp [SD]; exact c_gt_of_lt gzs)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ks; exact kz)
      rs' kl'
    exact ⟨Res, by simpa using run, sr, by simpa using er⟩

end Elixir.STTDescrProofsTest.USort
