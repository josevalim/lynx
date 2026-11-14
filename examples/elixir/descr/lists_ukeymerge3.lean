namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term} {Kd : Term → Prop}

theorem hd_sub {M S S' : List Term} {h : Term} (hd : HdOK κ M h S) (sub : ∀ x ∈ S', x ∈ S) :
    HdOK κ M h S' := by
  cases M with
  | nil => exact fun x hx => hd x (sub x hx)
  | cons m M => exact hd

theorem pre_BC {M B C : List Term} (p : Pre κ Kd M [] B C) (ab : ∀ y ∈ B, Above κ M y) :
    Pre κ Kd M B C [] :=
  ⟨p.sm, p.sb, p.sc, SA_nil, p.kb, p.kc, fun _ h => by simp at h, ab, p.uc, fun _ h => by simp at h⟩

theorem pre_AC {M A C : List Term} (p : Pre κ Kd M A [] C) : Pre κ Kd M A C [] :=
  ⟨p.sm, p.sa, p.sc, SA_nil, p.ka, p.kc, fun _ h => by simp at h, p.ua, p.uc, fun _ h => by simp at h⟩

theorem above_all {M B : List Term} {x : Term} (s : SA κ (x :: B)) (hx : Above κ M x) :
    ∀ y ∈ x :: B, Above κ M y := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact above_lt hx ((SA_cons.1 s).1 y hy)

theorem above_tail {M B : List Term} {x : Term} (s : SA κ (x :: B)) (hx : Above κ M x) :
    ∀ y ∈ B, Above κ (x :: M) y :=
  fun y hy => above_cons hx ((SA_cons.1 s).1 y hy)

end

section
variable {I : Term} {κ : Term → Term}

theorem ukm3 (n : Nat) :
    (∀ T1 T2 T3 M H2 H3 HdM D, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre κ (KdK I κ)) M T1 (H2 :: T2) (H3 :: T3) → HdOK κ M HdM (H2 :: T2 ++ H3 :: T3) →
      ∃ R, Erlang.lists.«ukeymerge3_1/11» I (Term.list T1) D HdM (κ H2) H2 (Term.list T2) (Term.list M)
        (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧ Res κ M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 T2 H3 T3 M HdM D, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre κ (KdK I κ)) M (H1 :: T1) T2 (H3 :: T3) → (∀ y ∈ T2, Above κ M y) → HdOK κ M HdM (H3 :: T3) →
      ∃ R, Erlang.lists.«ukeymerge3_2/11» I (κ H1) (Term.list T1) H1 (Term.list T2) HdM D (Term.list M)
        (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧ Res κ M (H1 :: T1) T2 (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 T3 M, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above κ M y) → (∀ y ∈ T3, Above κ M y) →
      (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE →
      ∃ R, Erlang.lists.«ukeymerge3_12_3/9» I (κ H1) (Term.list T1) H1 (κ H2) H2 (Term.list T2)
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res κ M (H1 :: T1) (H2 :: T2) T3 R) ∧
    (∀ H1 T1 H2 T2 T3 M, T1.length + T2.length + T3.length + 2 ≤ n →
      (Pre κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above κ M y) → (∀ y ∈ T3, Above κ M y) →
      Term.compare (Term.fuel (κ H2) (κ H1)) (κ H2) (κ H1) = .lt →
      ∃ R, Erlang.lists.«ukeymerge3_21_3/9» I (κ H1) (Term.list T1) H1 (κ H2) H2 (Term.list T2)
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res κ M (H1 :: T1) (H2 :: T2) T3 R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := ukm2 (I := I) (κ := κ) n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ukeymerge3_1
    intro T1 T2 T3 M H2 H3 HdM D len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    rw [Erlang.lists.«ukeymerge3_1/11».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 M H3 HdM (by simp at len; omega) (pre_BC p' ab)
          (hd_sub hd fun a ha => List.mem_append_right _ ha)
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simp) (by simpa using c23)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 (H2 :: M) H3 (κ H2) (by simp at len; omega)
          (pre_BC p' (above_tail p.sb a2)) hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c23]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
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
      have k1 := (p.ka H1 (by simp)).1
      have a1 := p.ua H1 (by simp)
      simp only [k1, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 (κ H1) D (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13]
        have c31 := not_le_lt c13
        have b2 : ∀ y ∈ H2 :: T2, Above κ M y := above_all p.sb (by
          cases e : Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)
          · exact above_lt a1 e
          · exact fun m hm => c_lt_eq (a1 m hm) e
          · simp [e] at c12)
        by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
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
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 M HdM (Term.list T2) (by simp at len; omega) p' ab
          (hd_sub hd fun a ha => List.mem_append_right _ ha)
        exact ⟨R, run, tr R res⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) (κ H2) (Term.list T2)
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
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
    intro H1 T1 T2 H3 T3 M HdM D len p ab hd
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    have a1 := p.ua H1 (by simp)
    rw [Erlang.lists.«ukeymerge3_2/11».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simp) (by simpa using c13)
        obtain ⟨R, run, res⟩ := m2.1 T1 T3 (H1 :: M) H3 (κ H1) (by simp at len; omega) (pre_AC p') hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c13]
      have c31 := not_le_lt c13
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
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
      have k2 := (p.kb H2 (by simp)).1
      have a2 := ab H2 (by simp)
      simp only [k2, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 (κ H1) (Term.list T1)
            (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13]
        have c31 := not_le_lt c13
        by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
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
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) (κ H2) D (by simp at len; omega) p'
          (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel (κ H3) HdM) (κ H3) HdM = .eq
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
    rw [Erlang.lists.«ukeymerge3_12_3/9».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simp)
      obtain ⟨R, run, res⟩ := m2.1 T1 T2 (H1 :: M) H2 (κ H1) (by simp at len; omega) p' hd_self
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      simp only [k3, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
        obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 (κ H1) (Term.list T1)
          (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c13]
      have c31 := not_le_lt c13
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
      obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_21_3
    intro H1 T1 H2 T2 T3 M len p ab ac c21
    have a2 := ab H2 (by simp)
    rw [Erlang.lists.«ukeymerge3_21_3/9».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := m2.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
        (above_tail p.sb a2)
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      simp only [k3, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) (κ H2) (Term.list T2)
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23]
      have c32 := not_le_lt c23
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩

end

end Elixir.STTDescrProofsTest.USort
