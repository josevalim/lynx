namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem g_if {α : Type} (p : Prop) [Decidable p] (body next : Unit → Except Exception α) :
    Lynx.Except.guard (.ok (if p then Term.atom "true" else Term.atom "false")) body next =
      if p then body () else next () := by
  by_cases h : p <;> simp [h]

theorem eq_ok (a b : Term) : Erlang.erlang.«==/2» a b =
    .ok (if Term.compare (Term.fuel a b) a b = .eq then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«==/2»]

theorem le_ok (a b : Term) : Erlang.erlang.«=</2» a b =
    .ok (if (Term.compare (Term.fuel a b) a b).isLE = true then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«=</2»]

theorem lt_ok (a b : Term) : Erlang.erlang.«</2» a b =
    .ok (if (Term.compare (Term.fuel a b) a b).isLT = true then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«</2»]

theorem gt_ok (a b : Term) : Erlang.erlang.«>/2» a b =
    .ok (if (Term.compare (Term.fuel a b) a b).isGT = true then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«>/2»]

/-- Keyed elements of `ukeysort/2`: `element/2` yields the key, which never equals a cons. -/
def KdK (I : Term) (κ : Term → Term) (x : Term) : Prop :=
  Erlang.erlang.«element/2» I x = .ok (κ x) ∧ ∀ a b, Term.compare (Term.fuel (κ x) (.cons a b)) (κ x) (.cons a b) ≠ .eq

theorem rev2 (l : List Term) : ∀ acc : List Term,
    Erlang.lists.«reverse/2» (Term.list l) (Term.list acc) = .ok (Term.list (l.reverse ++ acc)) := by
  induction l with
  | nil => intro acc; simp [Erlang.lists.«reverse/2»]
  | cons x xs ih => intro acc; simpa [Term.list, Erlang.lists.«reverse/2»] using ih (x :: acc)

theorem not_le_lt {a b : Term} (h : ¬(Term.compare (Term.fuel a b) a b).isLE = true) : Term.compare (Term.fuel b a) b a = .lt := by
  cases e : Term.compare (Term.fuel a b) a b
  · simp [e] at h
  · simp [e] at h
  · exact c_lt_of_gt e

section
variable {κ : Term → Term} {Kd : Term → Prop}

/-- The accumulator plus one ascending source, reversed onto it. -/
theorem res_fin {M T : List Term} (sm : SD κ M) (st : SA κ T) (ht : ∀ y ∈ T, Above κ M y) :
    Res κ M T [] [] (T.reverse ++ M) := by
  obtain ⟨s, e⟩ := finish sm st ht; exact ⟨s, by simpa using e⟩

theorem resD_fin {M T : List Term} (sm : SA κ M) (st : SD κ T) (ht : ∀ y ∈ T, Below κ M y) :
    ResD κ M T [] [] (T.reverse ++ M) := by
  obtain ⟨s, e⟩ := finishD sm st ht; exact ⟨s, by simpa using e⟩

end

section
variable {I : Term} {κ : Term → Term}

theorem ukm2 (n : Nat) :
    (∀ T1 T2 M H2 HdM, T1.length + T2.length + 1 ≤ n → Pre κ (KdK I κ) M T1 (H2 :: T2) [] →
      HdOK κ M HdM (H2 :: T2) →
      ∃ R, Erlang.lists.«ukeymerge2_1/7» I (Term.list T1) (κ H2) HdM (Term.list T2) (Term.list M) H2 =
        .ok (Term.list R) ∧ Res κ M T1 (H2 :: T2) [] R) ∧
    (∀ T1 H1 T2 M, T1.length + 1 + T2.length ≤ n → Pre κ (KdK I κ) M (H1 :: T1) T2 [] →
      (∀ y ∈ T2, Above κ M y) →
      ∃ R, Erlang.lists.«ukeymerge2_2/6» I (Term.list T1) (κ H1) H1 (Term.list T2) (Term.list M) =
        .ok (Term.list R) ∧ Res κ M (H1 :: T1) T2 [] R) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩
  | succ n ih =>
  constructor
  · intro T1 T2 M H2 HdM len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    cases T1 with
    | nil =>
      rw [Erlang.lists.«ukeymerge2_1/7».eq_def]
      simp only [eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
      · obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        refine ⟨_, by simp only [c2, ite_true, rev2], tr _ (res_congr (by simp) (res_fin p'.sm p'.sb ab))⟩
      · obtain ⟨p', tr⟩ := pushB p (u2.2 c2) (by simp) (by simp)
        refine ⟨_, by simpa [c2] using rev2 T2 (H2 :: M), tr _ (res_congr (by simp)
          (res_fin p'.sm p'.sb fun y hy => above_cons (u2.2 c2) ((SA_cons.1 p.sb).1 y hy)))⟩
    | cons H1 T1 =>
      have k1 := (p.ka H1 (by simp)).1
      rw [Erlang.lists.«ukeymerge2_1/7».eq_def]
      simp only [k1, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 (κ H1) (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1]
        have c1' := not_le_lt c1
        by_cases c2 : Term.compare (Term.fuel (κ H2) HdM) (κ H2) HdM = .eq
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
      rw [Erlang.lists.«ukeymerge2_2/6».eq_def]
      obtain ⟨p', tr⟩ := pushA p (by simp) (by simp)
      refine ⟨_, by simpa using rev2 T1 (H1 :: M), tr _ (res_fin p'.sm p'.sa p'.ua)⟩
    | cons H2 T2 =>
      have k2 := (p.kb H2 (by simp)).1
      rw [Erlang.lists.«ukeymerge2_2/6».eq_def]
      simp only [k2, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 (κ H1) (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1]
        have hx := ab H2 (by simp)
        obtain ⟨p', tr⟩ := pushB p hx (by simpa using not_le_lt c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
          (fun y hy => above_cons hx ((SA_cons.1 p.sb).1 y hy))
        exact ⟨R, by simpa using run, tr R res⟩

end

end Elixir.STTDescrProofsTest.USort
