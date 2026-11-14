namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term}

theorem eqv_ne_nil {R S : List Term} (e : Eqv κ R S) (h : S ≠ []) : R ≠ [] := by
  obtain ⟨x, S', rfl⟩ := List.exists_cons_of_ne_nil h
  intro hr
  have := e (κ x)
  simp [hr, lk_cons] at this

theorem lk_mem {s z : Term} {A : List Term} (h : lk κ s A = some z) : z ∈ A := by
  induction A with
  | nil => simp at h
  | cons y ys ih =>
    by_cases e : Term.compare (Term.fuel (κ y) s) (κ y) s = .eq
    · simp [lk_cons, e] at h; simp [h]
    · simp [lk_cons, e] at h; simp [ih h]

theorem lk_self {x : Term} {A : List Term}
    (h : A.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) (hx : x ∈ A) :
    lk κ (κ x) A = some x := by
  induction A with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    simp only [List.mem_cons] at hx
    by_cases e : x = y
    · subst e; simp [lk_cons]
    · have hx' : x ∈ ys := hx.resolve_left e
      simp [lk_cons, h.1 x hx', ih h.2 hx']

theorem mem_of_eqv {R S : List Term} {x : Term}
    (h : R.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) (e : Eqv κ R S) (hx : x ∈ R) :
    x ∈ S := lk_mem ((e (κ x)).symm.trans (lk_self h hx))

theorem eqv_acc {R M X : List Term} (P Q : List Term) (er : Eqv κ R (P ++ M ++ Q)) (em : Eqv κ M X) :
    Eqv κ R (P ++ X ++ Q) := er.trans (((Eqv.refl P).append em).append (Eqv.refl Q))

/-- Members of a merge of keyed sources are keyed. -/
theorem kd_of_eqv {Kd : Term → Prop} {M S : List Term}
    (h : M.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) (e : Eqv κ M S)
    (k : ∀ x ∈ S, Kd x) : ∀ x ∈ M, Kd x := fun x hx => k x (mem_of_eqv h e hx)

/-- Nonempty runs of keyed elements, ascending or descending. -/
def RunsA (Kd : Term → Prop) (Rs : List (List Term)) : Prop :=
  ∀ r ∈ Rs, r ≠ [] ∧ SA κ r ∧ ∀ x ∈ r, Kd x

def RunsD (Kd : Term → Prop) (Rs : List (List Term)) : Prop :=
  ∀ r ∈ Rs, r ≠ [] ∧ SD κ r ∧ ∀ x ∈ r, Kd x

end

section
variable {I : Term} {κ : Term → Term}

theorem ukm_mergel (n : Nat) :
    (∀ Rs Acc, 4 * (Rs.length + Acc.length) + 2 * min Acc.length 1 ≤ n →
      1 ≤ Rs.length + Acc.length → RunsA (κ := κ) (KdK I κ) Rs → RunsD (κ := κ) (KdK I κ) Acc →
      ∃ R, Erlang.lists.«ukeymergel/3» I (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list)) =
        .ok (Term.list R) ∧ SA κ R ∧ Eqv κ R (Acc.reverse.flatten ++ Rs.flatten)) ∧
    (∀ Rs Acc, 4 * (Rs.length + Acc.length) + 2 * min Acc.length 1 + 1 ≤ n →
      1 ≤ Rs.length + Acc.length → RunsD (κ := κ) (KdK I κ) Rs → RunsA (κ := κ) (KdK I κ) Acc →
      ∃ R, Erlang.lists.«rukeymergel/3» I (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list)) =
        .ok (Term.list R) ∧ SA κ R ∧ Eqv κ R (Rs.reverse.flatten ++ Acc.flatten)) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro Rs Acc len one ra rd
    rw [Erlang.lists.«ukeymergel/3».eq_def]
    match Rs with
    | [] =>
      simp only [List.map_nil]
      obtain ⟨R, run, sr, er⟩ := ih2 Acc [] (by simp at len one ⊢; omega) (by simpa using one) rd
        (by simp [RunsA])
      exact ⟨R, run, sr, by simpa using er⟩
    | [L] =>
      cases Acc with
      | nil =>
        obtain ⟨_, sl, _⟩ := ra L (by simp)
        exact ⟨L, by simp, sl, by simpa using Eqv.refl L⟩
      | cons A Acc =>
        obtain ⟨nl, sl, kl⟩ := ra L (by simp)
        have rv := rev2 L []
        simp only [List.append_nil] at rv
        simp only [List.map_cons, List.map_nil, ← Term.list_nil, rv,
          Lynx.Except.ok_bind]
        obtain ⟨R, run, sr, er⟩ := ih2 (L.reverse :: A :: Acc) [] (by simp at len ⊢; omega) (by simp)
          (by
            intro r hr
            simp only [List.mem_cons] at hr
            rcases hr with rfl | hr
            · exact ⟨by simpa using nl, SD_reverse.2 sl, fun x hx => kl x (by simpa using hx)⟩
            · exact rd r (by simp [hr]))
          (by simp [RunsA])
        refine ⟨R, by simpa using run, sr, er.trans ?_⟩
        simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc]
        exact Eqv.append (Eqv.refl _) (Eqv.append (Eqv.refl _) (eqv_reverse sl.ne))
    | [r1, r2] =>
      obtain ⟨n1, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨H1, T1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      have e1 := (k1 H1 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (ukm2 (I := I) (κ := κ) (T1.length + 1 + (H2 :: T2).length)).2 T1 H1 (H2 :: T2) []
        (by omega) ⟨SD_nil, s1, s2, SA_nil, k1, k2, by simp, fun _ _ _ h => by simp at h,
          fun _ _ => Or.inl fun _ h => by simp at h, by simp⟩ (fun _ _ _ h => by simp at h)
      simp only [List.map_cons, List.map_nil, e1, run,
        Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih1 [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
        (by simp [RunsA]) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.append_nil, List.mem_append] at hx
              rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)⟩
          · exact rd r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc Acc.reverse.flatten [] (by simpa using er) em
      simpa using this
    | r1 :: r2 :: r3 :: L =>
      obtain ⟨_, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := ra r3 (by simp)
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨H3, T3, rfl⟩ := List.exists_cons_of_ne_nil n3
      have e2 := (k2 H2 (by simp)).1
      have e3 := (k3 H3 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (ukm3 (I := I) (κ := κ) (r1.length + T2.length + T3.length + 2)).1
        r1 T2 T3 [] H2 H3 (.cons H2 H3) (Term.list (Acc.map Term.list)) (by omega)
        ⟨SD_nil, s1, s2, s3, k1, k2, k3, fun _ _ _ h => by simp at h,
          fun _ _ => Or.inl fun _ h => by simp at h, fun _ _ => Or.inl fun _ h => by simp at h⟩
        (fun x hx => by
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
          rcases hx with h | h | h | h
          · subst h; exact (k2 x (by simp)).2 _ _
          · exact (k2 x (by simp [h])).2 _ _
          · subst h; exact (k3 x (by simp)).2 _ _
          · exact (k3 x (by simp [h])).2 _ _)
      simp only [List.map_cons, e2, e3, run, Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih1 L (M :: Acc) (by simp at len ⊢; omega) (by simp only [List.length_cons]; omega)
        (fun r hr => ra r (by simp [hr])) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.mem_append] at hx
              rcases hx with (hx | hx) | hx
              · exact k1 x hx
              · exact k2 x hx
              · exact k3 x hx)⟩
          · exact rd r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc Acc.reverse.flatten L.flatten (by simpa using er) em
      simpa using this
  · intro Rs Acc len one rd ra
    rw [Erlang.lists.«rukeymergel/3».eq_def]
    match Rs with
    | [] =>
      simp only [List.map_nil]
      obtain ⟨R, run, sr, er⟩ := ih1 Acc [] (by simp at len one ⊢; omega) (by simpa using one) ra
        (by simp [RunsD])
      exact ⟨R, run, sr, by simpa using er⟩
    | [L] =>
      obtain ⟨nl, sl, kl⟩ := rd L (by simp)
      have rv := rev2 L []
      simp only [List.append_nil] at rv
      simp only [List.map_cons, List.map_nil, ← Term.list_nil, rv,
        Lynx.Except.ok_bind]
      obtain ⟨R, run, sr, er⟩ := ih1 (L.reverse :: Acc) [] (by simp at len ⊢; omega) (by simp)
        (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨by simpa using nl, SA_reverse.2 sl, fun x hx => kl x (by simpa using hx)⟩
          · exact ra r hr)
        (by simp [RunsD])
      refine ⟨R, by simpa using run, sr, er.trans ?_⟩
      simp only [List.reverse_nil, List.flatten_nil, List.nil_append, List.flatten_cons,
        List.reverse_cons, List.append_nil]
      exact Eqv.append (eqv_reverse sl.ne) (Eqv.refl _)
    | [r2, r1] =>
      obtain ⟨n1, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨H1, T1, rfl⟩ := List.exists_cons_of_ne_nil n1
      have e2 := (k2 H2 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (rkm2 (I := I) (κ := κ) (2 * ((H1 :: T1).length + T2.length + 1) + 1)).1
        (H1 :: T1) H2 T2 [] (by omega) ⟨SA_nil, s1, s2, SD_nil, k1, k2, by simp, fun _ _ _ h => by simp at h,
          fun _ _ _ h => by simp at h, by simp⟩
      simp only [List.map_cons, List.map_nil, e2, run,
        Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih2 [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
        (by simp [RunsD]) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.append_nil, List.mem_append] at hx
              rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)⟩
          · exact ra r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc [] Acc.flatten (by simpa using er) em
      simpa using this
    | r3 :: r2 :: r1 :: L =>
      obtain ⟨_, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := rd r3 (by simp)
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨H3, T3, rfl⟩ := List.exists_cons_of_ne_nil n3
      have e2 := (k2 H2 (by simp)).1
      have e3 := (k3 H3 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (rkm3 (I := I) (κ := κ)
        (2 * (r1.length + T2.length + T3.length + 2) + 1)).1
        r1 H2 T2 H3 T3 [] (Term.list (Acc.map Term.list)) .nil (by omega)
        ⟨SA_nil, s1, s2, s3, k1, k2, k3, fun _ _ _ h => by simp at h,
          fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
      simp only [List.map_cons, e2, e3, run, Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih2 L (M :: Acc) (by simp at len ⊢; omega) (by simp only [List.length_cons]; omega)
        (fun r hr => rd r (by simp [hr])) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.mem_append] at hx
              rcases hx with (hx | hx) | hx
              · exact k1 x hx
              · exact k2 x hx
              · exact k3 x hx)⟩
          · exact ra r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc L.reverse.flatten Acc.flatten (by simpa using er) em
      simpa using this

end

end Elixir.STTDescrProofsTest.USort
