namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- Lists sorted strictly by their keys. -/
def SKL (dl : List (Term × Term)) : Prop := dl.Pairwise fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt

/-- Lists of atoms sorted strictly. -/
def SAK (ks : List Term) : Prop := ks.Pairwise fun a b => Term.compare (Term.fuel a b) a b = .lt

theorem map_pairs_val (m : Nat) (val : Term) : ∀ K : List Term,
    Erlang.lists.«map_1/2» (D m) (.function "Elixir.Module.Types.Descr" "-fields_put_all_new/3-fun-0-" 1 #[val])
      (Term.list K) = .ok (fieldsTerm (K.map fun k => (k, val)))
  | [] => by simp [Erlang.lists.«map_1/2», fieldsTerm]
  | k :: K => by
    have := map_pairs_val m val K
    simp only [fieldsTerm] at this ⊢
    rw [Erlang.lists.«map_1/2».eq_def]
    simp [this, Elixir.Module.Types.Descr.«-fields_put_all_new/3-fun-0-/2»]

theorem fpa_nil_keys (m : Nat) (val : Term) (dl : List (Term × Term)) :
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (fieldsTerm dl) .nil val = .ok (fieldsTerm dl) := by
  rw [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def]
  cases dl <;> rfl

theorem fpa_nil_fields (m : Nat) (val k : Term) (K : List Term) :
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (fieldsTerm []) (Term.list (k :: K)) val =
      .ok (fieldsTerm ((k :: K).map fun k => (k, val))) := by
  rw [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def]
  have := map_pairs_val m val K
  simp only [fieldsTerm, List.map_nil] at this ⊢
  simp [Erlang.lists.«map/2», Erlang.erlang.«is_function/2», this,
    Elixir.Module.Types.Descr.«-fields_put_all_new/3-fun-0-/2»]

theorem skl_cons {x : Term × Term} {dl : List (Term × Term)} :
    SKL (x :: dl) ↔ (∀ y ∈ dl, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt) ∧ SKL dl := List.pairwise_cons

theorem sak_cons {k : Term} {K : List Term} :
    SAK (k :: K) ↔ (∀ y ∈ K, Term.compare (Term.fuel k y) k y = .lt) ∧ SAK K := List.pairwise_cons

theorem atom_cmp_eq {a b : String} : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b) = .eq ↔ a = b := by
  simp

theorem lookup_cons_ne {k1 k : Term} {v1 : Term} {dl : List (Term × Term)} (ne : compareExact (fuel k k1) k k1 ≠ .eq) :
    mapLookup ((k1, v1) :: dl) k = mapLookup dl k := by
  simp [mapLookup, ne]

theorem lookup_cons_eq {k1 k : Term} {v1 : Term} {dl : List (Term × Term)} (e : compareExact (fuel k k1) k k1 = .eq) :
    mapLookup ((k1, v1) :: dl) k = some v1 := by
  simp [mapLookup, e]

/-- `fields_put_all_new/3` over all the keys of a list that includes the keys of the fields gives each key its
field, or the value. -/
theorem fpa_run (m : Nat) (val : Term) : ∀ (K : List Term) (dl : List (Term × Term)),
    SAK K → (∀ k ∈ K, ∃ s, k = .atom s) → SKL dl → (∀ e ∈ dl, e.1 ∈ K) →
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (fieldsTerm dl) (Term.list K) val =
      .ok (fieldsTerm (K.map fun k => (k, (mapLookup dl k).getD val)))
  | [], dl, _, _, _, hd => by
    have : dl = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he => by simpa using hd e he
    subst this
    exact fpa_nil_keys m val []
  | k :: K, [], sk, ka, _, _ => by
    simpa [mapLookup] using fpa_nil_fields m val k K
  | k :: K, (k1, v1) :: dl, sk, ka, sd, hd => by
    have sd' := skl_cons.1 sd
    have sk' := sak_cons.1 sk
    obtain ⟨s, rfl⟩ := ka k (by simp)
    have hk1 := hd (k1, v1) (by simp)
    simp only [List.mem_cons] at hk1
    obtain ⟨s1, rfl⟩ : ∃ s1, k1 = .atom s1 := by
      rcases hk1 with h | h
      · exact ⟨s, h⟩
      · exact ka k1 (by simp [h])
    rw [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def]
    simp only [fieldsTerm_cons, USort.lt_ok, USort.gt_ok, USort.g_if]
    -- the least key of the list is at most the first key of the fields
    have notlt : ¬Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s) = .lt := by
      intro l
      rcases hk1 with h | h
      · cases h; simp at l
      · have := sk'.1 _ h; rw [USort.c_swap, l] at this; simp at this
    have nl : ¬(Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s)).isLT = Bool.true := USort.not_islt notlt
    simp only [nl, Bool.false_eq_true, ↓reduceIte]
    by_cases g : (Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s)).isGT = Bool.true
    · simp only [g, ↓reduceIte]
      have g' := USort.isgt_lt g
      have rest := fpa_run m val K ((.atom s1, v1) :: dl) sk'.2 (fun k hk => ka k (by simp [hk])) sd (by
        intro e he
        have := hd e he
        simp only [List.mem_cons] at this
        rcases this with h | h
        · exfalso
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · simp only at h; rw [h] at g'; simp at g'
          · have := sd'.1 e he; rw [h] at this; rw [USort.c_swap, g'] at this; simp at this
        · exact h)
      have ne : compareExact (fuel (.atom s) (.atom s1)) (.atom s) (.atom s1) ≠ .eq := by
        intro e; simp at e; subst e; simp at g'
      have none : mapLookup dl (.atom s) = none := by
        simp only [mapLookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
        intro e he c
        rw [atom_compareExact_eq] at c
        have := sd'.1 e he; rw [c] at this
        exact notlt this
      simp only [List.map_cons, lookup_cons_ne ne, fieldsTerm_cons, none, Option.getD_none]
      rw [show (Term.tuple ⟨[.atom s1, v1]⟩).cons (fieldsTerm dl) = fieldsTerm ((.atom s1, v1) :: dl) from rfl,
        rest]
      rfl
    · simp only [g, Bool.false_eq_true, ↓reduceIte]
      have e : s1 = s := by
        cases h : Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s) with
        | lt => exact absurd h notlt
        | eq => simpa using h
        | gt => simp [h] at g
      subst e
      have rest := fpa_run m val K dl sk'.2 (fun k hk => ka k (by simp [hk])) sd'.2 (by
        intro e he
        rcases (List.mem_cons.mp (hd e (by simp [he]))) with h | h
        · have := sd'.1 e he; rw [h] at this; simp at this
        · exact h)
      simp only [rest, Lynx.Except.ok_bind, List.map_cons, fieldsTerm_cons,
        lookup_cons_eq (show compareExact (fuel (.atom s1) (.atom s1)) (.atom s1) (.atom s1) = .eq by simp), Option.getD_some]
      have congr : K.map (fun k => (k, (mapLookup ((.atom s1, v1) :: dl) k).getD val)) =
          K.map (fun k => (k, (mapLookup dl k).getD val)) := by
        refine List.map_congr_left fun k hk => ?_
        obtain ⟨s', rfl⟩ := ka k (by simp [hk])
        have ne : compareExact (fuel (.atom s') (.atom s1)) (.atom s') (.atom s1) ≠ .eq := by
          intro c; simp at c; subst c; have := sk'.1 _ hk; simp at this
        rw [lookup_cons_ne ne]
      rw [congr]
      rfl

theorem exact_ok (a b : Term) : Erlang.erlang.«=:=/2» a b =
    .ok (if compareExact (fuel a b) a b = .eq then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«=:=/2»]

theorem lookup_none_of {k : Term} {dl : List (Term × Term)} (h : ∀ e ∈ dl, compareExact (fuel k e.1) k e.1 ≠ .eq) :
    mapLookup dl k = none := by
  simp only [mapLookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  exact h

section
variable {t : Term} {n : Nat}

/-- Domains: sorted atom keys with element types of a level. -/
def DomL (t : Term) (n : Nat) (dl : List (Term × Term)) : Prop :=
  SKL dl ∧ ∀ e ∈ dl, (∃ s, e.1 = .atom s) ∧ (level t n).E e.2

/-- `map_put_domain/4` adds a value at sorted keys, joining it with the values already there. -/
theorem mpd_run {m : Nat} (hm : (level t n).K ≤ m) {v : Term} (hv : (level t n).E v) :
    ∀ (N : Nat) (dl : List (Term × Term)) (ks : List Term), dl.length + ks.length ≤ N → DomL t n dl → SAK ks →
      (∀ k ∈ ks, ∃ s, k = .atom s) →
      ∃ dl', Elixir.Module.Types.Descr.«map_put_domain/4» (D m) (fieldsTerm dl) (Term.list ks) v v =
        .ok (fieldsTerm dl') ∧ DomL t n dl' ∧ (∀ e ∈ dl', e.1 ∈ dl.map Prod.fst ∨ e.1 ∈ ks) ∧
        ∀ s, ((mapLookup dl' (.atom s)).isNone ↔ (mapLookup dl (.atom s)).isNone ∧ Term.atom s ∉ ks) ∧
          ∀ U', mapLookup dl' (.atom s) = some U' → ∀ x, (level t n).den U' x ↔
            ((∃ U, mapLookup dl (.atom s) = some U ∧ (level t n).den U x) ∨ (Term.atom s ∈ ks ∧ (level t n).den v x)) := by
  intro N
  induction N with
  | zero =>
    intro dl ks len hd sk ka
    have h1 : dl = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1 h2
    refine ⟨[], by rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]; rfl, hd, by simp, fun s => ?_⟩
    simp [mapLookup]
  | succ N ih =>
  intro dl ks len hd sk ka
  cases ks with
  | nil =>
    refine ⟨dl, ?_, hd, fun e he => Or.inl (List.mem_map.mpr ⟨e, he, rfl⟩), fun s => ⟨by simp, ?_⟩⟩
    · rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]; cases dl <;> rfl
    · intro U' h x; simp [h]
  | cons k ks =>
  have sk' := sak_cons.1 sk
  obtain ⟨s2, rfl⟩ := ka k (by simp)
  have ka' : ∀ k ∈ ks, ∃ s, k = .atom s := fun k hk => ka k (by simp [hk])
  have mem2 : ∀ s, (Term.atom s ∈ Term.atom s2 :: ks) ↔ (s = s2 ∨ Term.atom s ∈ ks) := by simp
  cases dl with
  | nil =>
    obtain ⟨dl', run, hd', keys, sem⟩ := ih [] ks (by simp at len ⊢; omega) hd sk'.2 ka'
    refine ⟨(.atom s2, v) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
      simp only [fieldsTerm, List.map_nil] at run ⊢
      simp [run]
    · rcases keys y hy with h | h
      · simp at h
      · exact sk'.1 _ h
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨⟨s2, rfl⟩, hv⟩
      · exact hd'.2 e he
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inr (by simp)
      · rcases keys e he with h | h
        · simp at h
        · exact Or.inr (by simp [h])
    · rw [lookup_cons_atom, mem2]
      by_cases e : s2 = s
      · subst e
        simp only [ite_true, Option.isNone_some, Bool.false_eq_true, true_or, not_true_eq_false, and_false,
          Option.some.injEq]
        refine ⟨trivial, fun U' h x => ?_⟩
        subst h; simp [mapLookup]
      · have ne : ¬s = s2 := fun h => e h.symm
        simp only [e, ite_false, ne, false_or]
        exact sem s
  | cons x dl =>
  obtain ⟨k1, v1⟩ := x
  have sd' := skl_cons.1 hd.1
  obtain ⟨⟨s1, hs1⟩, hv1⟩ := hd.2 (k1, v1) (by simp)
  simp only at hs1 hv1
  subst hs1
  have hdt : DomL t n dl := ⟨sd'.2, fun e he => hd.2 e (by simp [he])⟩
  -- keys of the tail are above the first key
  have tail_gt : ∀ e ∈ dl, Term.compare (Term.fuel (.atom s1) e.1) (.atom s1) e.1 = .lt := sd'.1
  rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
  simp only [fieldsTerm_cons, USort.lt_ok, exact_ok, USort.g_if]
  by_cases l : (Term.compare (Term.fuel (.atom s1) (.atom s2)) (.atom s1) (.atom s2)).isLT = Bool.true
  · simp only [l, ↓reduceIte]
    have l' := USort.islt_lt l
    obtain ⟨dl', run, hd', keys, sem⟩ := ih dl (.atom s2 :: ks) (by simp at len ⊢; omega) hdt sk ka
    refine ⟨(.atom s1, v1) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
    · simp [run, fieldsTerm_cons]
    · rcases keys y hy with h | h
      · obtain ⟨e, he, hey⟩ := List.mem_map.mp h; rw [← hey]; exact tail_gt e he
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · rw [h]; exact l'
        · exact USort.c_lt_trans l' (sk'.1 _ h)
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨⟨s1, rfl⟩, hv1⟩
      · exact hd'.2 e he
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl (by simp)
      · rcases keys e he with h | h
        · exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)
        · exact Or.inr h
    · rw [lookup_cons_atom, lookup_cons_atom]
      by_cases e : s1 = s
      · subst e
        have nk : Term.atom s1 ∉ Term.atom s2 :: ks := by
          intro h; simp only [List.mem_cons] at h
          rcases h with h | h
          · rw [h] at l'; simp at l'
          · have := USort.c_lt_trans l' (sk'.1 _ h); simp at this
        simp only [ite_true, Option.isNone_some, Bool.false_eq_true, false_and, Option.some.injEq]
        refine ⟨trivial, fun U' h x => ?_⟩
        subst h; simp [nk]
      · simp only [e, ite_false]
        exact sem s
  simp only [l, Bool.false_eq_true, ↓reduceIte]
  by_cases q : compareExact (fuel (.atom s2) (.atom s1)) (.atom s2) (.atom s1) = .eq
  · simp only [q, ↓reduceIte]
    have e21 : s1 = s2 := by have := (atom_compareExact_eq _ _).mp q; simp at this; exact this
    subst e21
    obtain ⟨c, hc, rc, sc, -⟩ := (level t n).ef.union hv1 hv
    obtain ⟨dl', run, hd', keys, sem⟩ := ih dl ks (by simp at len ⊢; omega) hdt sk'.2 ka'
    refine ⟨(.atom s1, c) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
    · simp [rc m hm, run, fieldsTerm_cons]
    · rcases keys y hy with h | h
      · obtain ⟨e, he, hey⟩ := List.mem_map.mp h; rw [← hey]; exact tail_gt e he
      · exact sk'.1 _ h
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨⟨s1, rfl⟩, hc⟩
      · exact hd'.2 e he
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl (by simp)
      · rcases keys e he with h | h
        · exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)
        · exact Or.inr (by simp [h])
    · rw [lookup_cons_atom, lookup_cons_atom, mem2]
      by_cases e : s1 = s
      · subst e
        simp only [ite_true, Option.isNone_some, Bool.false_eq_true, false_and, Option.some.injEq]
        refine ⟨trivial, fun U' h x => ?_⟩
        subst h; simp [sc x]
      · have ne : ¬s = s1 := fun h => e h.symm
        simp only [e, ite_false, ne, false_or]
        exact sem s
  simp only [q, ↓reduceIte]
  have l2 : Term.compare (Term.fuel (.atom s2) (.atom s1)) (.atom s2) (.atom s1) = .lt := by
    have nl := USort.not_islt' l
    have ne : ¬Term.compare (Term.fuel (.atom s1) (.atom s2)) (.atom s1) (.atom s2) = .eq := by
      intro c; simp at c; subst c; simp at q
    exact USort.gt_of_ne nl ne
  obtain ⟨dl', run, hd', keys, sem⟩ := ih ((.atom s1, v1) :: dl) ks (by simp at len ⊢; omega) hd sk'.2 ka'
  have none2 : mapLookup ((.atom s1, v1) :: dl) (.atom s2) = none := by
    apply lookup_none_of
    intro e he c
    rw [atom_compareExact_eq] at c
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp only at c; rw [c] at l2; simp at l2
    · have := USort.c_lt_trans l2 (tail_gt e he); rw [c] at this; simp at this
  refine ⟨(.atom s2, v) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
  · simp only [fieldsTerm_cons] at run
    rw [show (Term.tuple ⟨[.atom s1, v1]⟩).cons (fieldsTerm dl) = fieldsTerm ((.atom s1, v1) :: dl) from rfl]
    simp [run, fieldsTerm_cons]
  · rcases keys y hy with h | h
    · obtain ⟨e, he, hey⟩ := List.mem_map.mp h
      rw [← hey]
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact l2
      · exact USort.c_lt_trans l2 (tail_gt e he)
    · exact sk'.1 _ h
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨⟨s2, rfl⟩, hv⟩
    · exact hd'.2 e he
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact Or.inr (by simp)
    · rcases keys e he with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
  · rw [lookup_cons_atom, mem2]
    by_cases e : s2 = s
    · subst e
      simp only [ite_true, Option.isNone_some, Bool.false_eq_true, true_or, not_true_eq_false, and_false,
        Option.some.injEq, none2]
      refine ⟨trivial, fun U' h x => ?_⟩
      subst h; simp
    · have ne : ¬s = s2 := fun h => e h.symm
      simp only [e, ite_false, ne, false_or]
      exact sem s


end

end Elixir.STTDescrProofsTest.Nest
