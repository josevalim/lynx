namespace Elixir.STTDescrProofsTest.USort
open Lynx

/-- Elements of `usort/1` never equal a cons, the head sentinel of `umergel/3`. -/
def KdU (x : Term) : Prop := ∀ a b, Term.compare (Term.fuel x (.cons a b)) x (.cons a b) ≠ .eq

theorem um2 (n : Nat) :
    (∀ T1 T2 M H2 HdM, T1.length + T2.length + 1 ≤ n → Pre (fun x : Term => x) KdU M T1 (H2 :: T2) [] →
      HdOK (fun x : Term => x) M HdM (H2 :: T2) →
      ∃ R, Erlang.lists.«umerge2_1/5» (Term.list T1) (Term.list T2) (Term.list M) HdM H2 =
        .ok (Term.list R) ∧ Res (fun x : Term => x) M T1 (H2 :: T2) [] R) ∧
    (∀ T1 H1 T2 M, T1.length + 1 + T2.length ≤ n → Pre (fun x : Term => x) KdU M (H1 :: T1) T2 [] →
      (∀ y ∈ T2, Above (fun x : Term => x) M y) →
      ∃ R, Erlang.lists.«umerge2_2/4» (Term.list T1) (Term.list T2) (Term.list M) H1 =
        .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) T2 [] R) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩
  | succ n ih =>
  constructor
  · intro T1 T2 M H2 HdM len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    cases T1 with
    | nil =>
      rw [Erlang.lists.«umerge2_1/5».eq_def]
      simp only [eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
      · obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        refine ⟨_, by simp only [c2, ite_true, rev2], tr _ (res_congr (by simp) (res_fin p'.sm p'.sb ab))⟩
      · obtain ⟨p', tr⟩ := pushB p (u2.2 c2) (by simp) (by simp)
        refine ⟨_, by simpa [c2] using rev2 T2 (H2 :: M), tr _ (res_congr (by simp)
          (res_fin p'.sm p'.sb fun y hy => above_cons (u2.2 c2) ((SA_cons.1 p.sb).1 y hy)))⟩
    | cons H1 T1 =>
      rw [Erlang.lists.«umerge2_1/5».eq_def]
      simp only [le_ok, eq_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 H1 (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1, Bool.false_eq_true, ↓reduceIte]
        have c1' := not_le_lt c1
        by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
        · simp only [c2, ↓reduceIte]
          obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
          obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 M (by simp at len; omega) p' ab
          exact ⟨R, run, tr R res⟩
        · simp only [c2, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushB p (u2.2 c2) (by simpa using c1') (by simp)
          obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
            (fun y hy => above_cons (u2.2 c2) ((SA_cons.1 p.sb).1 y hy))
          exact ⟨R, by simpa using run, tr R res⟩
  · intro T1 H1 T2 M len p ab
    cases T2 with
    | nil =>
      rw [Erlang.lists.«umerge2_2/4».eq_def]
      obtain ⟨p', tr⟩ := pushA p (by simp) (by simp)
      refine ⟨_, by simpa using rev2 T1 (H1 :: M), tr _ (res_fin p'.sm p'.sa p'.ua)⟩
    | cons H2 T2 =>
      rw [Erlang.lists.«umerge2_2/4».eq_def]
      simp only [le_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 H1 (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1, Bool.false_eq_true, ↓reduceIte]
        have hx := ab H2 (by simp)
        obtain ⟨p', tr⟩ := pushB p hx (by simpa using not_le_lt c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
          (fun y hy => above_cons hx ((SA_cons.1 p.sb).1 y hy))
        exact ⟨R, by simpa using run, tr R res⟩

theorem um3 (n : Nat) :
    (∀ T1 T2 T3 M H2 H3 HdM, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M T1 (H2 :: T2) (H3 :: T3) → HdOK (fun x : Term => x) M HdM (H2 :: T2 ++ H3 :: T3) →
      ∃ R, Erlang.lists.«umerge3_1/7» (Term.list T1) HdM (Term.list T2) H2 (Term.list M)
        (Term.list T3) H3 = .ok (Term.list R) ∧ Res (fun x : Term => x) M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 T2 H3 T3 M HdM, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M (H1 :: T1) T2 (H3 :: T3) → (∀ y ∈ T2, Above (fun x : Term => x) M y) → HdOK (fun x : Term => x) M HdM (H3 :: T3) →
      ∃ R, Erlang.lists.«umerge3_2/7» (Term.list T1) H1 (Term.list T2) HdM (Term.list M)
        (Term.list T3) H3 = .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) T2 (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 T3 M, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above (fun x : Term => x) M y) → (∀ y ∈ T3, Above (fun x : Term => x) M y) →
      (Term.compare (Term.fuel H1 H2) H1 H2).isLE →
      ∃ R, Erlang.lists.«umerge3_12_3/6» (Term.list T1) H1 (Term.list T2) H2
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) (H2 :: T2) T3 R) ∧
    (∀ H1 T1 H2 T2 T3 M, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above (fun x : Term => x) M y) → (∀ y ∈ T3, Above (fun x : Term => x) M y) →
      Term.compare (Term.fuel H2 H1) H2 H1 = .lt →
      ∃ R, Erlang.lists.«umerge3_21_3/6» (Term.list T1) H1 (Term.list T2) H2
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) (H2 :: T2) T3 R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := um2 n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ukeymerge3_1
    intro T1 T2 T3 M H2 H3 HdM len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    rw [Erlang.lists.«umerge3_1/7».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 M H3 HdM (by simp at len; omega) (pre_BC p' ab)
          (hd_sub hd fun a ha => List.mem_append_right _ ha)
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simp) (by simpa using c23)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 (H2 :: M) H3 H2 (by simp at len; omega)
          (pre_BC p' (above_tail p.sb a2)) hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := m2.2 T2 H2 T3 M (by simp at len; omega)
          (pre_BC p' (above_all p.sb a2)) ac
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simp) (by simpa using c32)
      obtain ⟨R, run, res⟩ := m2.2 T2 H2 T3 (H3 :: M) (by simp at len; omega)
        (pre_BC p' (above_all p.sb (above_cons a3 c32))) (above_tail p.sc a3)
      exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
    | cons H1 T1 =>
      have a1 := p.ua H1 (by simp)
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 H1 (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13, Bool.false_eq_true, ↓reduceIte]
        have c31 := not_le_lt c13
        have b2 : ∀ y ∈ H2 :: T2, Above (fun x : Term => x) M y := above_all p.sb (by
          cases e : Term.compare (Term.fuel H1 H2) H1 H2
          · exact above_lt a1 e
          · exact fun m hm => c_lt_eq (a1 m hm) e
          · simp [e] at c12)
        by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
        · simp only [c3, ↓reduceIte]
          obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 M (by simp at len; omega) p' b2 ac c12
          exact ⟨R, run, tr R res⟩
        simp only [c3, ↓reduceIte]
        have a3 := u3.2 c3
        obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
          (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 M H2 (by simp at len; omega) p' ab
          (by obtain ⟨m, M', hM, hm⟩ := u2.1 c2; subst hM; exact hm)
        exact ⟨R, run, tr R res⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) H2
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 M (by simp at len; omega) p'
          (above_all p.sb a2) ac c21
        exact ⟨R, run, tr R res⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_2
    intro H1 T1 T2 H3 T3 M HdM len p ab hd
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    have a1 := p.ua H1 (by simp)
    rw [Erlang.lists.«umerge3_2/7».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simp) (by simpa using c13)
        obtain ⟨R, run, res⟩ := m2.1 T1 T3 (H1 :: M) H3 H1 (by simp at len; omega) (pre_AC p') hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      have c31 := not_le_lt c13
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := m2.2 T1 H1 T3 M (by simp at len; omega) (pre_AC p') ac
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simp)
      obtain ⟨R, run, res⟩ := m2.2 T1 H1 T3 (H3 :: M) (by simp at len; omega) (pre_AC p')
        (above_tail p.sc a3)
      exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
    | cons H2 T2 =>
      have a2 := ab H2 (by simp)
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 H1
            (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13, Bool.false_eq_true, ↓reduceIte]
        have c31 := not_le_lt c13
        by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
        · simp only [c3, ↓reduceIte]
          obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 M (by simp at len; omega) p' ab ac c12
          exact ⟨R, run, tr R res⟩
        simp only [c3, ↓reduceIte]
        have a3 := u3.2 c3
        obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
          (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) H2 (by simp at len; omega) p'
          (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 M (by simp at len; omega) p' ab ac c21
        exact ⟨R, run, tr R res⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_12_3
    intro H1 T1 H2 T2 T3 M len p ab ac c12
    rw [Erlang.lists.«umerge3_12_3/6».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simp)
      obtain ⟨R, run, res⟩ := m2.1 T1 T2 (H1 :: M) H2 H1 (by simp at len; omega) p' hd_self
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      simp only [le_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
        obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 H1
          (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      have c31 := not_le_lt c13
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
      obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_21_3
    intro H1 T1 H2 T2 T3 M len p ab ac c21
    have a2 := ab H2 (by simp)
    rw [Erlang.lists.«umerge3_21_3/6».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := m2.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
        (above_tail p.sb a2)
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      simp only [le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) H2
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩


end Elixir.STTDescrProofsTest.USort
