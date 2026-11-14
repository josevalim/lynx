namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem le_ne_lt {a b : Term} (h : (Term.compare (Term.fuel a b) a b).isLE = true) (ne : ¬Term.compare (Term.fuel a b) a b = .eq) :
    Term.compare (Term.fuel a b) a b = .lt := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all

theorem le_le {a b : Term} (h : Term.compare (Term.fuel a b) a b = .lt) : (Term.compare (Term.fuel a b) a b).isLE = true := by
  simp [h]

section
variable {κ : Term → Term} {Kd : Term → Prop}

theorem preD_BC {M B C : List Term} (p : PreD κ Kd M [] B C) : PreD κ Kd M B C [] :=
  ⟨p.sm, p.sb, p.sc, SD_nil, p.kb, p.kc, fun _ h => by simp at h, p.ub, p.uc, fun _ h => by simp at h⟩

theorem preD_AC {M A C : List Term} (p : PreD κ Kd M A [] C) : PreD κ Kd M A C [] :=
  ⟨p.sm, p.sa, p.sc, SD_nil, p.ka, p.kc, fun _ h => by simp at h, p.ua, p.uc, fun _ h => by simp at h⟩

/-- The head of a descending source is above the rest of it. -/
theorem sd_head {x y : Term} {B : List Term} (s : SD κ (x :: y :: B)) :
    Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt := c_lt_of_gt ((SD_cons.1 s).1 y (by simp))

end

section
variable {I : Term} {κ : Term → Term}

theorem rkm2 (n : Nat) :
    (∀ T1 H2 T2 M, 2 * (T1.length + T2.length + 1) + 1 ≤ n → (PreD κ (KdK I κ)) M T1 (H2 :: T2) [] →
      ∃ R, Erlang.lists.«rukeymerge2_1/6» I (Term.list T1) (κ H2) (Term.list T2) (Term.list M) H2 =
        .ok (Term.list R) ∧ ResD κ M T1 (H2 :: T2) [] R) ∧
    (∀ H1 T1 H2M T2 M, 2 * (T1.length + T2.length + 2) ≤ n → (PreD κ (KdK I κ)) M (H1 :: T1) (H2M :: T2) [] →
      (Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M)).isLE = true →
      ∃ R, Erlang.lists.«rukeymerge2_2/8» I (Term.list T1) (κ H1) (Term.list T2) (Term.list M)
        (κ H2M) H2M H1 = .ok (Term.list R) ∧ ResD κ M (H1 :: T1) (H2M :: T2) [] R) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro T1 H2 T2 M len p
    rw [Erlang.lists.«rukeymerge2_1/6».eq_def]
    cases T1 with
    | nil =>
      obtain ⟨p', tr⟩ := pushDB p (by simp) (by simp)
      exact ⟨_, by simpa using rev2 T2 (H2 :: M), tr _ (resD_congr (by simp) (resD_fin p'.sm p'.sb p'.ub))⟩
    | cons H1 T1 =>
      have k1 := (p.ka H1 (by simp)).1
      simp only [k1, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        exact ih2 H1 T1 H2 T2 M (by simp at len; omega) p c12
      simp only [c12]
      obtain ⟨p', tr⟩ := pushDA p (by simpa using not_le_lt c12) (by simp)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p'
      exact ⟨R, by simpa using run, tr R res⟩
  · intro H1 T1 H2M T2 M len p c1
    rw [Erlang.lists.«rukeymerge2_2/8».eq_def]
    cases T2 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simp)
        exact ⟨_, by simpa using rev2 T1 (H1 :: M), tr1 _ (tr2 _ (resD_fin p2.sm p2.sa p2.ua))⟩
      simp only [e, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using le_ne_lt c1 e) (by simp)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simp)
      exact ⟨_, by simpa using rev2 T1 (H1 :: H2M :: M),
        tr1 _ (tr2 _ (resD_fin p2.sm p2.sa p2.ua))⟩
    | cons H2 T2 =>
      have k2 := (p.kb H2 (by simp)).1
      have s2 := sd_head p.sb
      simp only [k2, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simp)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 (H2M :: M) (by simp at len; omega) p1 c12
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using le_ne_lt c1 e) (by simp)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: H2M :: M) (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩

theorem rkm3 (n : Nat) :
    (∀ T1 H2 T2 H3 T3 M D1 D2, 2 * (T1.length + T2.length + T3.length + 2) + 1 ≤ n →
      (PreD κ (KdK I κ)) M T1 (H2 :: T2) (H3 :: T3) →
      ∃ R, Erlang.lists.«rukeymerge3_1/11» I (Term.list T1) D1 D2 (κ H2) H2 (Term.list T2) (Term.list M)
        (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧ ResD κ M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2M T2 H3 T3 M, 2 * (T1.length + T2.length + T3.length + 3) ≤ n →
      (PreD κ (KdK I κ)) M (H1 :: T1) (H2M :: T2) (H3 :: T3) → (Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M)).isLE = true →
      Term.compare (Term.fuel (κ H3) (κ H2M)) (κ H3) (κ H2M) = .lt →
      ∃ R, Erlang.lists.«rukeymerge3_2/11» I (κ H1) H1 (Term.list T1) (Term.list T2) H2M (κ H2M)
        (Term.list M) (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧
        ResD κ M (H1 :: T1) (H2M :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (T1.length + T2.length + T3.length + 3) ≤ n →
      (PreD κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true →
      (Term.compare (Term.fuel (κ H2) (κ H3M)) (κ H2) (κ H3M)).isLE = true →
      ∃ R, Erlang.lists.«rukeymerge3_12_3/11» I (κ H1) H1 (Term.list T1) (κ H2) H2 (Term.list T2)
        (Term.list M) (κ H3M) H3M (Term.list T3) = .ok (Term.list R) ∧
        ResD κ M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (T1.length + T2.length + T3.length + 3) ≤ n →
      (PreD κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → Term.compare (Term.fuel (κ H2) (κ H1)) (κ H2) (κ H1) = .lt →
      (Term.compare (Term.fuel (κ H1) (κ H3M)) (κ H1) (κ H3M)).isLE = true →
      ∃ R, Erlang.lists.«rukeymerge3_21_3/11» I (κ H1) H1 (Term.list T1) (κ H2) H2 (Term.list T2)
        (Term.list M) (κ H3M) H3M (Term.list T3) = .ok (Term.list R) ∧
        ResD κ M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := rkm2 (I := I) (κ := κ) n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- rukeymerge3_1
    intro T1 H2 T2 H3 T3 M D1 D2 len p
    rw [Erlang.lists.«rukeymerge3_1/11».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H2 T2 H3 T3 M (by simp at len; omega) (preD_BC p) c23
        exact ⟨R, run, resD_congr (by simp) res⟩
      simp only [c23]
      obtain ⟨p1, tr1⟩ := pushDB p (by simp) (by simpa using not_le_lt c23)
      obtain ⟨R, run, res⟩ := m2.1 T2 H3 T3 (H2 :: M) (by simp at len; omega) (preD_BC p1)
      exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
    | cons H1 T1 =>
      have k1 := (p.ka H1 (by simp)).1
      simp only [k1, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
        · simp only [c23, ↓reduceIte]
          exact ih12 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 c23
        simp only [c23]
        exact ih2 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 (not_le_lt c23)
      simp only [c12]
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        exact ih21 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p (not_le_lt c12) c13
      simp only [c13]
      obtain ⟨p1, tr1⟩ := pushDA p (by simpa using not_le_lt c12) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) D1 D2 (by simp at len; omega) p1
      exact ⟨R, by simpa using run, tr1 R res⟩
  · -- rukeymerge3_2
    intro H1 T1 H2M T2 H3 T3 M len p c1 c3
    rw [Erlang.lists.«rukeymerge3_2/11».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: M) (by simp at len; omega) (preD_AC p2)
        exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H1 T1 H3 T3 (H2M :: M) (by simp at len; omega) (preD_AC p1) c13
        exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
      simp only [c13]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: H2M :: M) (by simp at len; omega) (preD_AC p2)
      exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
    | cons H2 T2 =>
      have k2 := (p.kb H2 (by simp)).1
      have s2 := sd_head p.sb
      simp only [k2, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simpa using c3)
        by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
        · simp only [c23, ↓reduceIte]
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12 c23
          exact ⟨R, by simpa using run, tr1 R res⟩
        simp only [c23]
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12
          (not_le_lt c23)
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) H1 (Term.list T1) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c21 c13
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H2M :: M) H1 (Term.list T1)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
  · -- rukeymerge3_12_3
    intro H1 T1 H2 T2 H3M T3 M len p c12 c23
    rw [Erlang.lists.«rukeymerge3_12_3/11».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H2) (κ H3M)) (κ H2) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H2) (by simp) e
        obtain ⟨R, run, res⟩ := m2.2 H1 T1 H2 T2 M (by simp at len; omega) p1 c12
        exact ⟨R, run, tr1 R res⟩
      simp only [e, ↓reduceIte]
      have l23 := le_ne_lt c23 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
      obtain ⟨R, run, res⟩ := m2.2 H1 T1 H2 T2 (H3M :: M) (by simp at len; omega) p1 c12
      exact ⟨R, by simpa using run, tr1 R res⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      have s3 := sd_head p.sc
      simp only [k3, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c23' : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23', ↓reduceIte]
        have l23 := c_le_lt c23' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c12 c23'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c23']
      have c32 := not_le_lt c23'
      by_cases e : Term.compare (Term.fuel (κ H2) (κ H3M)) (κ H2) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H2) (by simp) e
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p1 c12 c32
        exact ⟨R, run, tr1 R res⟩
      simp only [e, ↓reduceIte]
      have l23 := le_ne_lt c23 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
      obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c12 c32
      exact ⟨R, by simpa using run, tr1 R res⟩
  · -- rukeymerge3_21_3
    intro H1 T1 H2 T2 H3M T3 M len p c21 c13
    rw [Erlang.lists.«rukeymerge3_21_3/11».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H3M)) (κ H1) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
        obtain ⟨R, run, res⟩ := m2.1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l13 := le_ne_lt c13 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := m2.1 T1 H2 T2 (H1 :: H3M :: M) (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      have s3 := sd_head p.sc
      simp only [k3, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c13' : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13', ↓reduceIte]
        have l13 := c_le_lt c13' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c21 c13'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13']
      have c31 := not_le_lt c13'
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H3M)) (κ H1) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) H1 (Term.list T1) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l13 := le_ne_lt c13 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H3M :: M) H1 (Term.list T1)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩

end

end Elixir.STTDescrProofsTest.USort
