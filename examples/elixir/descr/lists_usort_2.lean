namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem us2_end (X Y : Term) (R : List Term) (Rs : List (List Term)) (sc : SA (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (rs : RunsA (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_2/5» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ []) := by
  rw [Erlang.lists.«usplit_2/5».eq_def]
  cases R <;>
  · obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 2))).1 false
      ((Y :: X :: _) :: Rs) [] (by simp; omega) (by simp) (runsA_cons ⟨by simp, sc, kc⟩ rs)
      (by simp [RunsD])
    exact ⟨Res, by simpa [modeT] using run, sr, by simpa [ucontent] using er⟩

theorem us21_end (X Y S : Term) (R : List Term) (Rs : List (List Term)) (sc : SA (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (ks : KdU S) (rs : RunsA (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_2_1/6» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ [S]) := by
  rw [Erlang.lists.«usplit_2_1/6».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 3))).1 false
    ([S] :: (Y :: X :: R) :: Rs) [] (by simp; omega) (by simp)
    (runsA_cons ⟨by simp, by simp [SA], by simpa using ks⟩ (runsA_cons ⟨by simp, sc, kc⟩ rs))
    (by simp [RunsD])
  exact ⟨Res, by simpa [modeT] using run, sr, by simpa [ucontent] using er⟩

theorem us2 (n : Nat) :
    (∀ X Y L R Rs, L.length ≤ n → SA (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      RunsA (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_2/5» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ L)) ∧
    (∀ X Y L R Rs S, L.length ≤ n → SA (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      Term.compare (Term.fuel X S) X S = .lt → KdU S → RunsA (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_2_1/6» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ S :: L)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro X Y L R Rs len sc kc rs _
      cases L with
      | cons => simp at len
      | nil => exact us2_end X Y R Rs sc kc rs
    · intro X Y L R Rs S len sc kc _ ks rs _
      cases L with
      | cons => simp at len
      | nil => exact us21_end X Y S R Rs sc kc ks rs
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro X Y L R Rs len sc kc rs kl
    cases L with
    | nil => exact us2_end X Y R Rs sc kc rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SA_cons.1 sc
    have yx : Term.compare (Term.fuel Y X) Y X = .lt := sc'.1 X (by simp)
    rw [Erlang.lists.«usplit_2/5».eq_def]
    simp only [eq_ok, lt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isLT = true
    · simp only [g1, ↓reduceIte]
      have l1 := islt_lt g1
      have lz := SA.lt_all (κ := (fun x : Term => x)) sc l1
      obtain ⟨Res, run, sr, er⟩ := ih1 Y Z L (X :: R) Rs len' (SA_cons.2 ⟨lz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R) (L := L) (z := Z)
        (fun y hy => by have := lz y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := Y) (z := Z)
        (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have yz := gt_of_ne (not_islt' g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isLT = true
    · simp only [g2, ↓reduceIte]
      have l2 := islt_lt g2
      have lzx := SA.lt_all (κ := (fun x : Term => x)) sc'.2 l2
      obtain ⟨Res, run, sr, er⟩ := ih1 Z Y L (X :: R) Rs len'
        (SA_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact yz
            · exact sc'.1 w (by simpa using hw), SA_cons.2 ⟨lzx, sc'.2⟩⟩)
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
          · have := lzx y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := X) (z := Z)
        (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have xz := gt_of_ne (not_islt' g2) e2
    cases R with
    | nil =>
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L [Z] Rs len'
        (by simp [SA]; exact ⟨⟨yx, c_lt_trans yx xz⟩, xz⟩)
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact kc x (by simp)
          · exact kc x (by simp)
          · exact kz)
        rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
    | cons r R =>
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L (r :: R) Rs Z len' sc kc xz kz rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
  · intro X Y L R Rs S len sc kc xs ks rs kl
    cases L with
    | nil => exact us21_end X Y S R Rs sc kc ks rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SA_cons.1 sc
    have yx : Term.compare (Term.fuel Y X) Y X = .lt := sc'.1 X (by simp)
    have ys := c_lt_trans yx xs
    rw [Erlang.lists.«usplit_2_1/6».eq_def]
    simp only [eq_ok, lt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isLT = true
    · simp only [g1, ↓reduceIte]
      have l1 := islt_lt g1
      have lz := SA.lt_all (κ := (fun x : Term => x)) sc l1
      obtain ⟨Res, run, sr, er⟩ := ih2 Y Z L (X :: R) Rs S len' (SA_cons.2 ⟨lz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        ys ks rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R ++ [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with hy | rfl
          · have := lz y (by simpa using hy); rw [c_swap, this]; simp
          · rw [c_swap, c_lt_trans l1 ys]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc xs ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := Y)
        (z := Z) (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have yz := gt_of_ne (not_islt' g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isLT = true
    · simp only [g2, ↓reduceIte]
      have l2 := islt_lt g2
      have lzx := SA.lt_all (κ := (fun x : Term => x)) sc'.2 l2
      obtain ⟨Res, run, sr, er⟩ := ih2 Z Y L (X :: R) Rs S len'
        (SA_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact yz
            · exact sc'.1 w (by simpa using hw), SA_cons.2 ⟨lzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        (c_lt_trans l2 xs) ks rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R ++ [S]) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | hy | rfl
          · intro e; exact zy (c_eq_symm e)
          · rw [c_swap, lzx _ (by simp)]; simp
          · rw [c_swap, lzx y (by simp [hy])]; simp
          · rw [c_swap, c_lt_trans l2 xs]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc xs ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := X)
        (z := Z) (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have rs' : RunsA (κ := (fun x : Term => x)) KdU ((Y :: X :: R) :: Rs) := runsA_cons ⟨by simp, sc, kc⟩ rs
    by_cases g3 : (Term.compare (Term.fuel Z S) Z S).isLT = true
    · simp only [g3, ↓reduceIte]
      have l3 := islt_lt g3
      obtain ⟨Res, run, sr, er⟩ := ih1 S Z L [] ((Y :: X :: R) :: Rs) len'
        (by simp [SA]; exact l3)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact ks)
        rs' kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (A := []) (B := [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          subst hy; rw [c_swap, l3]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g3, Bool.false_eq_true, ↓reduceIte]
    by_cases e3 : Term.compare (Term.fuel Z S) Z S = .eq
    · simp only [e3, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc xs ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := S)
        (z := Z) (by simp) (c_eq_symm e3)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e3, ↓reduceIte]
    have sz := gt_of_ne (not_islt' g3) e3
    obtain ⟨Res, run, sr, er⟩ := ih1 Z S L [] ((Y :: X :: R) :: Rs) len'
      (by simp [SA]; exact sz)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ks; exact kz)
      rs' kl'
    exact ⟨Res, by simpa using run, sr, by simpa using er⟩

end Elixir.STTDescrProofsTest.USort
