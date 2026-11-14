namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem rm2 (n : Nat) :
    (∀ T1 H2 T2 M, 2 * (T1.length + T2.length + 1) + 1 ≤ n → (PreD (fun x : Term => x) KdU) M T1 (H2 :: T2) [] →
      ∃ R, Erlang.lists.«rumerge2_1/4» (Term.list T1) (Term.list T2) (Term.list M) H2 =
        .ok (Term.list R) ∧ ResD (fun x : Term => x) M T1 (H2 :: T2) [] R) ∧
    (∀ H1 T1 H2M T2 M, 2 * (T1.length + T2.length + 2) ≤ n → (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2M :: T2) [] →
      (Term.compare (Term.fuel H1 H2M) H1 H2M).isLE = true →
      ∃ R, Erlang.lists.«rumerge2_2/5» (Term.list T1) (Term.list T2) (Term.list M) H2M H1 = .ok (Term.list R) ∧ ResD (fun x : Term => x) M (H1 :: T1) (H2M :: T2) [] R) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro T1 H2 T2 M len p
    rw [Erlang.lists.«rumerge2_1/4».eq_def]
    cases T1 with
    | nil =>
      obtain ⟨p', tr⟩ := pushDB p (by simp) (by simp)
      exact ⟨_, by simpa using rev2 T2 (H2 :: M), tr _ (resD_congr (by simp) (resD_fin p'.sm p'.sb p'.ub))⟩
    | cons H1 T1 =>
      simp only [le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        exact ih2 H1 T1 H2 T2 M (by simp at len; omega) p c12
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p', tr⟩ := pushDA p (by simpa using not_le_lt c12) (by simp)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p'
      exact ⟨R, by simpa using run, tr R res⟩
  · intro H1 T1 H2M T2 M len p c1
    rw [Erlang.lists.«rumerge2_2/5».eq_def]
    cases T2 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
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
      have s2 := sd_head p.sb
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simp)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 (H2M :: M) (by simp at len; omega) p1 c12
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
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

theorem rm3 (n : Nat) :
    (∀ T1 H2 T2 H3 T3 M, 2 * (T1.length + T2.length + T3.length + 2) + 1 ≤ n →
      (PreD (fun x : Term => x) KdU) M T1 (H2 :: T2) (H3 :: T3) →
      ∃ R, Erlang.lists.«rumerge3_1/6» (Term.list T1) (Term.list T2) H2 (Term.list M)
        (Term.list T3) H3 = .ok (Term.list R) ∧ ResD (fun x : Term => x) M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2M T2 H3 T3 M, 2 * (T1.length + T2.length + T3.length + 3) ≤ n →
      (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2M :: T2) (H3 :: T3) → (Term.compare (Term.fuel H1 H2M) H1 H2M).isLE = true →
      Term.compare (Term.fuel H3 H2M) H3 H2M = .lt →
      ∃ R, Erlang.lists.«rumerge3_2/7» (Term.list T1) (Term.list T2) H2M
        (Term.list M) (Term.list T3) H3 H1 = .ok (Term.list R) ∧
        ResD (fun x : Term => x) M (H1 :: T1) (H2M :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (T1.length + T2.length + T3.length + 3) ≤ n →
      (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true →
      (Term.compare (Term.fuel H2 H3M) H2 H3M).isLE = true →
      ∃ R, Erlang.lists.«rumerge3_12_3/7» (Term.list T1) (Term.list T2) H2
        (Term.list M) (Term.list T3) H3M H1 = .ok (Term.list R) ∧
        ResD (fun x : Term => x) M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (T1.length + T2.length + T3.length + 3) ≤ n →
      (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → Term.compare (Term.fuel H2 H1) H2 H1 = .lt →
      (Term.compare (Term.fuel H1 H3M) H1 H3M).isLE = true →
      ∃ R, Erlang.lists.«rumerge3_21_3/7» (Term.list T1) (Term.list T2) H2
        (Term.list M) (Term.list T3) H3M H1 = .ok (Term.list R) ∧
        ResD (fun x : Term => x) M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := rm2 n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- rukeymerge3_1
    intro T1 H2 T2 H3 T3 M len p
    rw [Erlang.lists.«rumerge3_1/6».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H2 T2 H3 T3 M (by simp at len; omega) (preD_BC p) c23
        exact ⟨R, run, resD_congr (by simp) res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simp) (by simpa using not_le_lt c23)
      obtain ⟨R, run, res⟩ := m2.1 T2 H3 T3 (H2 :: M) (by simp at len; omega) (preD_BC p1)
      exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
    | cons H1 T1 =>
      simp only [le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
        · simp only [c23, ↓reduceIte]
          exact ih12 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 c23
        simp only [c23, Bool.false_eq_true, ↓reduceIte]
        exact ih2 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 (not_le_lt c23)
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        exact ih21 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p (not_le_lt c12) c13
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDA p (by simpa using not_le_lt c12) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) (by simp at len; omega) p1
      exact ⟨R, by simpa using run, tr1 R res⟩
  · -- rukeymerge3_2
    intro H1 T1 H2M T2 H3 T3 M len p c1 c3
    rw [Erlang.lists.«rumerge3_2/7».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: M) (by simp at len; omega) (preD_AC p2)
        exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H1 T1 H3 T3 (H2M :: M) (by simp at len; omega) (preD_AC p1) c13
        exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: H2M :: M) (by simp at len; omega) (preD_AC p2)
      exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
    | cons H2 T2 =>
      have s2 := sd_head p.sb
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simpa using c3)
        by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
        · simp only [c23, ↓reduceIte]
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12 c23
          exact ⟨R, by simpa using run, tr1 R res⟩
        simp only [c23, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12
          (not_le_lt c23)
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c21 c13
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H2M :: M)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
  · -- rukeymerge3_12_3
    intro H1 T1 H2 T2 H3M T3 M len p c12 c23
    rw [Erlang.lists.«rumerge3_12_3/7».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H2 H3M) H2 H3M = .eq
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
      have s3 := sd_head p.sc
      simp only [le_ok, eq_ok, g_if]
      by_cases c23' : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23', ↓reduceIte]
        have l23 := c_le_lt c23' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c12 c23'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c23', Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23'
      by_cases e : Term.compare (Term.fuel H2 H3M) H2 H3M = .eq
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
    rw [Erlang.lists.«rumerge3_21_3/7».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H1 H3M) H1 H3M = .eq
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
      have s3 := sd_head p.sc
      simp only [le_ok, eq_ok, g_if]
      by_cases c13' : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13', ↓reduceIte]
        have l13 := c_le_lt c13' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c21 c13'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13', Bool.false_eq_true, ↓reduceIte]
      have c31 := not_le_lt c13'
      by_cases e : Term.compare (Term.fuel H1 H3M) H1 H3M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l13 := le_ne_lt c13 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H3M :: M)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩


end Elixir.STTDescrProofsTest.USort
