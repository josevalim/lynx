namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term} {Kd : Term → Prop}

theorem pre_nil {A B C : List Term} (sa : SA κ A) (sb : SA κ B) (sc : SA κ C) (ka : ∀ x ∈ A, Kd x)
    (kb : ∀ x ∈ B, Kd x) (kc : ∀ x ∈ C, Kd x) : Pre κ Kd [] A B C :=
  ⟨SD_nil, sa, sb, sc, ka, kb, kc, fun _ _ _ h => by simp at h,
    fun _ _ => Or.inl fun _ h => by simp at h, fun _ _ => Or.inl fun _ h => by simp at h⟩

theorem preD_nil {A B C : List Term} (sa : SD κ A) (sb : SD κ B) (sc : SD κ C) (ka : ∀ x ∈ A, Kd x)
    (kb : ∀ x ∈ B, Kd x) (kc : ∀ x ∈ C, Kd x) : PreD κ Kd [] A B C :=
  ⟨SA_nil, sa, sb, sc, ka, kb, kc, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h,
    fun _ _ _ h => by simp at h⟩

/-- A merge of nonempty keyed sources from an empty accumulator is a descending run. -/
theorem run_of_res {A B C R : List Term} (r : Res κ [] A B C R) (ne : A ++ B ++ C ≠ [])
    (k : ∀ x ∈ A ++ B ++ C, Kd x) : R ≠ [] ∧ SD κ R ∧ ∀ x ∈ R, Kd x :=
  ⟨eqv_ne_nil r.2 (by simpa using ne), r.1, kd_of_eqv r.1.ne r.2 (by simpa using k)⟩

theorem run_of_resD {A B C R : List Term} (r : ResD κ [] A B C R) (ne : A ++ B ++ C ≠ [])
    (k : ∀ x ∈ A ++ B ++ C, Kd x) : R ≠ [] ∧ SA κ R ∧ ∀ x ∈ R, Kd x :=
  ⟨eqv_ne_nil r.2 (by simpa using ne), r.1, kd_of_eqv r.1.ne r.2 (by simpa using k)⟩

theorem runsA_cons {r : List Term} {Rs : List (List Term)} (h : r ≠ [] ∧ SA κ r ∧ ∀ x ∈ r, Kd x)
    (hs : RunsA (κ := κ) Kd Rs) : RunsA (κ := κ) Kd (r :: Rs) := by
  intro r' hr; simp only [List.mem_cons] at hr; rcases hr with rfl | hr; exact h; exact hs r' hr

theorem runsD_cons {r : List Term} {Rs : List (List Term)} (h : r ≠ [] ∧ SD κ r ∧ ∀ x ∈ r, Kd x)
    (hs : RunsD (κ := κ) Kd Rs) : RunsD (κ := κ) Kd (r :: Rs) := by
  intro r' hr; simp only [List.mem_cons] at hr; rcases hr with rfl | hr; exact h; exact hs r' hr

end

/-- The run order of `umergel/3` and `rumergel/3`. -/
def modeT (asc : Bool) : Term := if asc then .atom "asc" else .atom "desc"

/-- Contents of a `umergel/3` state: in ascending mode runs come oldest first and the
accumulator newest first; in descending mode the other way around. -/
def ucontent (asc : Bool) (Rs Acc : List (List Term)) : List Term :=
  if asc then Acc.reverse.flatten ++ Rs.flatten else Rs.reverse.flatten ++ Acc.flatten

def rcontent (asc : Bool) (Rs Acc : List (List Term)) : List Term :=
  if asc then Rs.reverse.flatten ++ Acc.flatten else Acc.reverse.flatten ++ Rs.flatten

theorem kdu_cons {S : List Term} {a b : Term} (k : ∀ x ∈ S, KdU x) :
    ∀ x ∈ S, Term.compare (Term.fuel ((fun x : Term => x) x) (.cons a b)) ((fun x : Term => x) x) (.cons a b) ≠ .eq := fun x hx => k x hx a b

theorem um_mergel (n : Nat) :
    (∀ asc Rs Acc, 4 * (Rs.length + Acc.length) + 2 * min Acc.length 1 ≤ n →
      1 ≤ Rs.length + Acc.length → RunsA (κ := (fun x : Term => x)) KdU Rs → RunsD (κ := (fun x : Term => x)) KdU Acc →
      ∃ R, Erlang.lists.«umergel/3» (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list))
        (modeT asc) = .ok (Term.list R) ∧ SA (fun x : Term => x) R ∧ Eqv (fun x : Term => x) R (ucontent asc Rs Acc)) ∧
    (∀ asc Rs Acc, 4 * (Rs.length + Acc.length) + 2 * min Acc.length 1 + 1 ≤ n →
      1 ≤ Rs.length + Acc.length → RunsD (κ := (fun x : Term => x)) KdU Rs → RunsA (κ := (fun x : Term => x)) KdU Acc →
      ∃ R, Erlang.lists.«rumergel/3» (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list))
        (modeT asc) = .ok (Term.list R) ∧ SA (fun x : Term => x) R ∧ Eqv (fun x : Term => x) R (rcontent asc Rs Acc)) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro asc Rs Acc len one ra rd
    rw [Erlang.lists.«umergel/3».eq_def]
    match Rs with
    | [] =>
      cases Acc with
      | nil => simp at one
      | cons A Acc =>
      obtain ⟨na, _, _⟩ := rd A (by simp)
      obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil na
      simp only [List.map_nil, List.map_cons]
      obtain ⟨R, run, sr, er⟩ := ih2 asc ((a :: A') :: Acc) [] (by simp at len ⊢; omega) (by simp) rd
        (by simp [RunsA])
      refine ⟨R, by simpa using run, sr, ?_⟩
      cases asc <;> simpa [ucontent, rcontent] using er
    | [L] =>
      obtain ⟨nl, sl, kl⟩ := ra L (by simp)
      obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil nl
      cases Acc with
      | nil =>
        refine ⟨h :: t, by simp, sl, ?_⟩
        cases asc <;> simpa [ucontent] using Eqv.refl (κ := (fun x : Term => x)) (h :: t)
      | cons A Acc =>
        obtain ⟨na, _, _⟩ := rd A (by simp)
        obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil na
        have rv := rev2 (h :: t) []
        simp only [List.append_nil] at rv
        simp only [List.map_nil, List.map_cons]
        simp only [← Term.list_cons, rv, Lynx.Except.ok_bind]
        obtain ⟨R, run, sr, er⟩ := ih2 asc ((h :: t).reverse :: (a :: A') :: Acc) []
          (by simp at len ⊢; omega) (by simp)
          (runsD_cons ⟨by simp, SD_reverse.2 sl, fun x hx => kl x (List.mem_reverse.1 hx)⟩ rd)
          (by simp [RunsA])
        refine ⟨R, by simpa using run, sr, er.trans ?_⟩
        have rv' := eqv_reverse (κ := (fun x : Term => x)) sl.ne
        rw [List.reverse_cons] at rv'
        cases asc
        · simp only [rcontent, ucontent, Bool.false_eq_true, ↓reduceIte, List.reverse_nil,
            List.flatten_nil, List.nil_append, List.flatten_cons, List.reverse_cons,
            List.append_nil]
          exact Eqv.append rv' (Eqv.refl _)
        · simp only [rcontent, ucontent, ↓reduceIte, List.reverse_cons, List.flatten_append,
            List.flatten_cons, List.flatten_nil, List.append_nil,
            List.append_assoc]
          exact Eqv.append (Eqv.refl _) (Eqv.append (Eqv.refl _) rv')
    | [r1, r2] =>
      obtain ⟨n1, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (um2 (t2.length + 1 + (h1 :: t1).length)).2 t2 h2 (h1 :: t1) [] (by simp)
          (pre_nil s2 s1 SA_nil k2 k1 (by simp)) (fun _ _ _ h => by simp at h)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 false [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsA]) (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc [] Acc.flatten (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (um2 (t1.length + 1 + (h2 :: t2).length)).2 t1 h1 (h2 :: t2) [] (by simp)
          (pre_nil s1 s2 SA_nil k1 k2 (by simp)) (fun _ _ _ h => by simp at h)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 true [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsA]) (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten [] (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
    | r1 :: r2 :: r3 :: L =>
      obtain ⟨n1, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := ra r3 (by simp)
      have rl : RunsA (κ := (fun x : Term => x)) KdU L := fun r hr => ra r (by simp [hr])
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨h3, t3, rfl⟩ := List.exists_cons_of_ne_nil n3
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (um3 ((h3 :: t3).length + t2.length + t1.length + 2)).1 (h3 :: t3) t2 t1 []
          h2 h1 (.cons h2 h1) (by simp) (pre_nil s3 s2 s1 k3 k2 k1) (by
            intro x hx; simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
            rcases hx with rfl | hx | rfl | hx
            · exact k2 _ (by simp) _ _
            · exact k2 x (by simp [hx]) _ _
            · exact k1 _ (by simp) _ _
            · exact k1 x (by simp [hx]) _ _)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k3 x hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 false L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc L.reverse.flatten Acc.flatten (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (um3 ((h1 :: t1).length + t2.length + t3.length + 2)).1 (h1 :: t1) t2 t3 []
          h2 h3 (.cons h2 h3) (by simp) (pre_nil s1 s2 s3 k1 k2 k3) (by
            intro x hx; simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
            rcases hx with rfl | hx | rfl | hx
            · exact k2 _ (by simp) _ _
            · exact k2 x (by simp [hx]) _ _
            · exact k3 _ (by simp) _ _
            · exact k3 x (by simp [hx]) _ _)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k1 x hx; exact k2 x hx; exact k3 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 true L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten L.flatten (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
  · intro asc Rs Acc len one rd ra
    rw [Erlang.lists.«rumergel/3».eq_def]
    match Rs with
    | [] =>
      simp only [List.map_nil]
      obtain ⟨R, run, sr, er⟩ := ih1 asc Acc [] (by simp at len one ⊢; omega) (by simpa using one) ra
        (by simp [RunsD])
      refine ⟨R, run, sr, ?_⟩
      cases asc <;> simpa [ucontent, rcontent] using er
    | [L] =>
      obtain ⟨nl, sl, kl⟩ := rd L (by simp)
      obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil nl
      have rv := rev2 (h :: t) []
      simp only [List.append_nil] at rv
      simp only [List.map_nil, List.map_cons]
      simp only [← Term.list_cons, rv, Lynx.Except.ok_bind]
      obtain ⟨R, run, sr, er⟩ := ih1 asc ((h :: t).reverse :: Acc) [] (by simp at len ⊢; omega) (by simp)
        (runsA_cons ⟨by simp, SA_reverse.2 sl, fun x hx => kl x (List.mem_reverse.1 hx)⟩ ra)
        (by simp [RunsD])
      refine ⟨R, by simpa using run, sr, er.trans ?_⟩
      have rv' := eqv_reverse (κ := (fun x : Term => x)) sl.ne
      rw [List.reverse_cons] at rv'
      cases asc
      · simp only [rcontent, ucontent, Bool.false_eq_true, ↓reduceIte, List.reverse_cons,
          List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
        exact Eqv.append (Eqv.refl _) rv'
      · simp only [rcontent, ucontent, ↓reduceIte, List.reverse_nil, List.flatten_nil, List.nil_append,
          List.flatten_cons, List.reverse_cons,
          List.append_nil]
        exact Eqv.append rv' (Eqv.refl _)
    | [r1, r2] =>
      obtain ⟨n1, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (rm2 (2 * ((h1 :: t1).length + t2.length + 1) + 1)).1 (h1 :: t1) h2 t2 []
          (by simp) (preD_nil s1 s2 SD_nil k1 k2 (by simp))
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 false [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsD]) (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten [] (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (rm2 (2 * ((h2 :: t2).length + t1.length + 1) + 1)).1 (h2 :: t2) h1 t1 []
          (by simp) (preD_nil s2 s1 SD_nil k2 k1 (by simp))
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 true [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsD]) (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc [] Acc.flatten (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this
    | r1 :: r2 :: r3 :: L =>
      obtain ⟨n1, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := rd r3 (by simp)
      have rl : RunsD (κ := (fun x : Term => x)) KdU L := fun r hr => rd r (by simp [hr])
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨h3, t3, rfl⟩ := List.exists_cons_of_ne_nil n3
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (rm3 (2 * ((h1 :: t1).length + t2.length + t3.length + 2) + 1)).1
          (h1 :: t1) h2 t2 h3 t3 [] (by simp) (preD_nil s1 s2 s3 k1 k2 k3)
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k1 x hx; exact k2 x hx; exact k3 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 false L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten L.flatten (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (rm3 (2 * ((h3 :: t3).length + t2.length + t1.length + 2) + 1)).1
          (h3 :: t3) h2 t2 h1 t1 [] (by simp) (preD_nil s3 s2 s1 k3 k2 k1)
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k3 x hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 true L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc L.reverse.flatten Acc.flatten (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this

end Elixir.STTDescrProofsTest.USort
