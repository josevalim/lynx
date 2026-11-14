namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types with the node: operations on the node compute on its expansion. -/

theorem opt_union_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b S : Term)
    (hb : b ≠ .atom "term") (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) e b S =
      Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) (expN e k) b S := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def, Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem opt_union_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a S : Term)
    (ha : a ≠ .atom "term") (none : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) a e S =
      Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) a (expN e k) S := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def, Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem opt_inter_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b S : Term)
    (hb : b ≠ .atom "term") :
    Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) e b S =
      Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) (expN e k) b S := by
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_intersection/3».eq_def, Elixir.Module.Types.Descr.«opt_intersection/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [unfold_map, expN]
  all_goals simp_all [unfold_map, expN]

theorem opt_inter_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a S : Term)
    (ha : a ≠ .atom "term") :
    Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) a e S =
      Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) a (expN e k) S := by
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_intersection/3».eq_def, Elixir.Module.Types.Descr.«opt_intersection/3».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp_all [unfold_map, expN]
  all_goals simp_all [unfold_map, expN]

theorem opt_diff_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b S : Term)
    (hb : b ≠ .atom "term") (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) e b S =
      Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) (expN e k) b S := by
  obtain ⟨S₀, rfl, -⟩ := h
  have tne : Term.compare (Term.fuel (Term.tuple #[.reference r, .map S₀, gen]) (.atom "term")) (Term.tuple #[.reference r, .map S₀, gen]) (.atom "term") ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  have ene : Term.compare (Term.fuel (expN (.tuple #[.reference r, .map S₀, gen]) k) (.atom "term")) (expN (.tuple #[.reference r, .map S₀, gen]) k) (.atom "term") ≠ .eq := by
    simp only [expN]; rw [Term.compare_step]; simp [Compare.compareStep]
  rw [Elixir.Module.Types.Descr.«opt_difference/3».eq_def, Elixir.Module.Types.Descr.«opt_difference/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN, Elixir.Module.Types.Descr.«unfold/1»]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN, Elixir.Module.Types.Descr.«unfold/1»]

theorem opt_diff_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) a e S =
      Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) a (expN e k) S := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_difference/3».eq_def, Elixir.Module.Types.Descr.«opt_difference/3».eq_def]
  simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem opt_union_none_l (d : Dispatcher) {a b S : Term} (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (none : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) : Elixir.Module.Types.Descr.«opt_union/3» d a b S = .ok b := by
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem opt_union_none_r (d : Dispatcher) {a b S : Term} (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (na : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_union/3» d a b S = .ok a := by
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem opt_diff_none_r (d : Dispatcher) {a b S : Term} (bt : b ≠ .atom "term") (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_difference/3» d a b S = .ok a := by
  rw [Elixir.Module.Types.Descr.«opt_difference/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) bt
    · simp_all [Erlang.erlang.«==/2»]
  all_goals simp_all [Erlang.erlang.«==/2»]

theorem fuse_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (d : Dispatcher) (b n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d e b n = .ok (.atom "nil") := by
  obtain ⟨S, rfl, -⟩ := h
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3»
  simp [Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1», getMapKeys]
  repeat' split
  all_goals simp_all [Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«map_size/1»]

theorem aob_node {r : List Nat} {S : List (Term × Term)} {g : Term} :
    Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.tuple #[.reference r, .map S, g]) = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1»
  simp [getMapKeys]

theorem fuse_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (d : Dispatcher) (a n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d a e n = .ok (.atom "nil") := by
  obtain ⟨S, rfl, -⟩ := h
  obtain ⟨c, rc⟩ := aob_bool a
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3».eq_def]
  simp only [getMapKeys_tuple]
  split <;> cases c <;> simp [rc, aob_node, Lynx.Except.andAlso, boolAtom, isMember]

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types and the node `nd`. -/
def DEN (nd : Term) (E : Term → Prop) (a : Term) : Prop := E a ∨ IsT nd a

/-- The node holds the values of its expansion. -/
def denN (nd : Term) (den : Term → V → Prop) (a : Term) (v : V) : Prop :=
  (IsT nd a ∧ den (expN a (keyOf nd)) v) ∨ (¬IsT nd a ∧ den a v)

/-- Classes that hold the expansions of the node `nd`, and no node. -/
structure NodeOk (nd : Term) (E : Term → Prop) : Prop where
  exp : ∀ {e}, IsT nd e → E (expN e (keyOf nd))
  notN : ∀ {a}, E a → ¬IsT nd a

theorem isT_term : ¬IsT nd (.atom "term") := fun he => node_ne_term he rfl

theorem lh_expN {e : Term} (he : IsT nd e) : lh (expN e (keyOf nd)) = 1 := by
  apply Nat.le_antisymm
  · refine lh_map_le.mpr fun x mx => ?_
    have := mem_of_mem_mapEntries mx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
    have la : lh (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) = 0 :=
      lh_atomF ⟨⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil",
        by simp [amemV, mapLookup]⟩
    rcases this with rfl | rfl
    · exact Nat.le_of_eq (lh_litN he _)
    · simp only [la]; omega
  · have := lh_field_le (X := [(.atom "tuple", litN e (keyOf nd)), (.atom "atom", .tuple #[.atom "union",
      .map [(.atom "nil", .nil)]])]) (q := .atom "tuple") (x := litN e (keyOf nd)) (by simp [mapLookup])
    rw [lh_litN he _] at this
    exact this

theorem combo_expN {e : Term} (he : IsT nd e) : Combo nd (expN e (keyOf nd)) := by
  refine combo_map.mpr ⟨fun w hw => ?_, fun name w nt hw => ?_⟩
  · simp [mapLookup] at hw
    subst hw
    exact Or.inr (Bdd.leaf_iff.mpr ⟨e, he, rfl⟩)
  · simp only [mapLookup, List.find?_cons, compareExact_eq_atom, Term.atom.injEq] at hw
    by_cases t : name = "tuple"
    · exact absurd t nt
    · by_cases a : name = "atom"
      · subst a; simp at hw; subst hw
        exact lh_atomF ⟨⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil",
          by simp [amemV, mapLookup]⟩
      · simp [t, a] at hw

theorem denN_of {a : Term} {v : V} (hn : ¬IsT nd a) : denN nd den a v ↔ den a v := by
  simp [denN, hn]

theorem denN_node {a : Term} {v : V} (hn : IsT nd a) : denN nd den a v ↔ den (expN a (keyOf nd)) v := by
  simp [denN, hn]

/-- A type of the class with the node, as a type of the class: the node as its expansion. -/
theorem NodeOk.red (h : NodeOk nd E) {a : Term} (ha : DEN nd E a) : ∃ A, E A ∧ (∀ v, denN nd den a v ↔ den A v) ∧
    lh A = lh a ∧ (Combo nd a → Combo nd A) ∧ (a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd))) := by
  rcases ha with ha | ha
  · exact ⟨a, ha, fun v => denN_of (h.notN ha), rfl, id, Or.inl rfl⟩
  · exact ⟨_, h.exp ha, fun v => denN_node ha, by rw [lh_expN ha, lh_isT ha], fun _ => combo_expN ha, Or.inr ⟨ha, rfl⟩⟩

theorem DEN.ne_term {a A : Term} (r : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd))) (at' : a ≠ .atom "term") :
    A ≠ .atom "term" := by
  rcases r with rfl | ⟨-, rfl⟩
  · exact at'
  · exact expN_ne_term _ _

theorem DEN.ne_none {a A : Term} (r : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd)))
    (na : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) : ¬Term.compare (Term.fuel A (.map [])) A (.map []) = .eq := by
  rcases r with rfl | ⟨-, rfl⟩
  · exact na
  · exact expN_ne_none _ _

theorem isT_ne_none {a : Term} (ha : IsT nd a) : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq := node_ne_none ha.node

theorem red_inter {a b A B : Term} (ra : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd)))
    (rb : b = B ∨ (IsT nd b ∧ B = expN b (keyOf nd))) (bt : b ≠ .atom "term") (nA : A ≠ .atom "term") (m : Nat) :
    Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A B := by
  have e₁ : Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A b := by
    rcases ra with rfl | ⟨t, rfl⟩
    · rfl
    · exact inter_node_l t.node m (expand_isT t m) b bt
  rw [e₁]
  rcases rb with rfl | ⟨t, rfl⟩
  · rfl
  · exact inter_node_r t.node m (expand_isT t m) A nA

theorem red_diff {a b A B : Term} (ra : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd)))
    (rb : b = B ∨ (IsT nd b ∧ B = expN b (keyOf nd))) (nB : B ≠ .atom "term") (eB : ¬Term.compare (Term.fuel B (.map [])) B (.map []) = .eq)
    (m : Nat) :
    Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) A B := by
  have e₁ : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a B := by
    rcases rb with rfl | ⟨t, rfl⟩
    · rfl
    · exact diff_node_r t.node m (expand_isT t m) a
  rw [e₁]
  rcases ra with rfl | ⟨t, rfl⟩
  · rfl
  · exact diff_node_l t.node m (expand_isT t m) B nB eB

theorem an_inter (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ c, DEN nd E c ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
      (∀ v, denN nd den c v ↔ denN nd den a v ∧ denN nd den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨a, ha, fun m _ => inter_term_right _ _, fun v => ⟨fun x => ⟨x, dt v⟩, fun x => x.1⟩, fun N h₁ _ => h₁⟩
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨b, hb, fun m _ => inter_term_left _ _, fun v => ⟨fun x => ⟨dt v, x⟩, fun x => x.2⟩, fun N _ h₂ => h₂⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  obtain ⟨c, hc, run, sem, lc⟩ := ef.inter eA eB
  refine ⟨c, Or.inl hc, fun m hm => ?_, fun v => ?_, fun N h₁ h₂ => lc N (by omega) (by omega)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [red_inter rA rB bt (DEN.ne_term rA at') m']
    exact run _ (by omega)
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_diff (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ c, DEN nd E c ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
      (∀ v, denN nd den c v ↔ denN nd den a v ∧ ¬denN nd den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  have dn0 : ∀ v, ¬denN nd den (.map []) v := fun v d =>
    ef.den_none v ((denN_of (fun t => isT_map t)).mp d)
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.none, fun m _ => diff_term_right _ _, fun v => ⟨fun x => absurd x (dn0 v),
      fun x => absurd (dt v) x.2⟩, fun N _ _ => by rw [lh_nil_map]; omega⟩
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · have nb : ∀ v, ¬denN nd den b v := by
      rcases rB with rfl | ⟨t, -⟩
      · exact fun v d => ef.den_none' eB none v ((sB v).mp d)
      · exact absurd none (isT_ne_none t)
    exact ⟨a, ha, fun m _ => diff_none _ a b bt none, fun v => ⟨fun x => ⟨x, nb v⟩, fun x => x.1⟩, fun N h₁ _ => h₁⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨c, hc, run, sem, lc⟩ := ef.diff eA eB
  refine ⟨c, Or.inl hc, fun m hm => ?_, fun v => ?_, fun N h₁ h₂ => lc N (by omega) (by omega)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [red_diff rA rB (DEN.ne_term rB bt) (DEN.ne_none rB none) m']
    exact run _ (by omega)
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_union (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ c, DEN nd E c ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
      (∀ v, denN nd den c v ↔ denN nd den a v ∨ denN nd den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨_, Or.inl ef.term, fun m _ => union_term_l _ _, fun v => ⟨fun _ => Or.inl (dt v), fun _ => dt v⟩,
      fun N h₁ _ => h₁⟩
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.term, fun m _ => union_any_term _ _, fun v => ⟨fun _ => Or.inr (dt v), fun _ => dt v⟩,
      fun N _ h₂ => h₂⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  have nemp : ∀ {x X}, DEN nd E x → Term.compare (Term.fuel x (.map [])) x (.map []) = .eq → (x = X ∨ (IsT nd x ∧ X = expN x (keyOf nd))) →
      E X → (∀ v, denN nd den x v ↔ den X v) → ∀ v, ¬denN nd den x v := by
    intro x X _ none r eX s v d
    rcases r with rfl | ⟨t, -⟩
    · exact ef.den_none' eX none v ((s v).mp d)
    · exact absurd none (isT_ne_none t)
  by_cases na : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq
  · exact ⟨b, hb, fun m _ => union_none _ a b at' bt na,
      fun v => ⟨Or.inr, fun x => x.elim (fun d => absurd d (nemp ha na rA eA sA v)) id⟩, fun N _ h₂ => h₂⟩
  by_cases nb : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · exact ⟨a, ha, fun m _ => union_none_r _ a b at' bt na nb,
      fun v => ⟨Or.inl, fun x => x.elim id (fun d => absurd d (nemp hb nb rB eB sB v))⟩, fun N h₁ _ => h₁⟩
  obtain ⟨c, hc, run, sem, lc⟩ := ef.union eA eB
  refine ⟨c, Or.inl hc, fun m hm => ?_, fun v => ?_, fun N h₁ h₂ => lc N (by omega) (by omega)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) a b =
        Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) A b := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact union_node_l t.node m' (expand_isT t m') b bt nb
    have e₂ : Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) A b =
        Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) A B := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact union_node_r t.node m' (expand_isT t m') A (DEN.ne_term rA at') (DEN.ne_none rA na)
    rw [e₁, e₂]
    exact run _ (by omega)
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_opt_union (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (S : List (Term × Term)) {m : Nat}
    (ha : DEN nd E a) (hb : DEN nd E b) (hm : K + 1 ≤ m) : ∃ c, DEN nd E c ∧
      Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧
      ∀ v, denN nd den c v ↔ denN nd den a v ∨ denN nd den b v := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨_, Or.inl ef.term, opt_union_term_left _ _ _, fun v => ⟨fun _ => Or.inl (dt v), fun _ => dt v⟩⟩
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.term, opt_union_term_r _ _ _, fun v => ⟨fun _ => Or.inr (dt v), fun _ => dt v⟩⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  have nemp : ∀ {x X}, DEN nd E x → Term.compare (Term.fuel x (.map [])) x (.map []) = .eq → (x = X ∨ (IsT nd x ∧ X = expN x (keyOf nd))) →
      E X → (∀ v, denN nd den x v ↔ den X v) → ∀ v, ¬denN nd den x v := by
    intro x X _ none r eX s v d
    rcases r with rfl | ⟨t, -⟩
    · exact ef.den_none' eX none v ((s v).mp d)
    · exact absurd none (isT_ne_none t)
  by_cases na : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq
  · exact ⟨b, hb, opt_union_none_l _ at' bt na,
      fun v => ⟨Or.inr, fun x => x.elim (fun d => absurd d (nemp ha na rA eA sA v)) id⟩⟩
  by_cases nb : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · exact ⟨a, ha, opt_union_none_r _ at' bt na nb,
      fun v => ⟨Or.inl, fun x => x.elim id (fun d => absurd d (nemp hb nb rB eB sB v))⟩⟩
  obtain ⟨c, hc, run, sem⟩ := ef.opt_union S eA eB (show K ≤ m by omega)
  refine ⟨c, Or.inl hc, ?_, fun v => ?_⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) a b (.map S) =
        Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) A b (.map S) := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_union_node_l t.node m' (expand_isT t m') b _ bt nb
    have e₂ : Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) A b (.map S) =
        Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) A B (.map S) := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_union_node_r t.node m' (expand_isT t m') A _ (DEN.ne_term rA at') (DEN.ne_none rA na)
    rw [e₁, e₂, run]
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_opt_inter (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (S : List (Term × Term)) {m : Nat}
    (ha : DEN nd E a) (hb : DEN nd E b) (hm : K + 1 ≤ m) : ∃ c, DEN nd E c ∧
      Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧
      ∀ v, denN nd den c v ↔ denN nd den a v ∧ denN nd den b v := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨b, hb, opt_inter_term_l _ _ _, fun v => ⟨fun x => ⟨dt v, x⟩, fun x => x.2⟩⟩
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨a, ha, opt_inter_term_r _ _ _, fun v => ⟨fun x => ⟨x, dt v⟩, fun x => x.1⟩⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S eA eB (show K ≤ m by omega)
  refine ⟨c, Or.inl hc, ?_, fun v => ?_⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) a b (.map S) =
        Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) A b (.map S) := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_inter_node_l t.node m' (expand_isT t m') b _ bt
    have e₂ : Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) A b (.map S) =
        Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) A B (.map S) := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_inter_node_r t.node m' (expand_isT t m') A _ (DEN.ne_term rA at')
    rw [e₁, e₂, run]
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_opt_diff (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (S : List (Term × Term)) {m : Nat}
    (ha : DEN nd E a) (hb : DEN nd E b) (hm : K + 1 ≤ m) : ∃ c, DEN nd E c ∧
      Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧
      ∀ v, denN nd den c v ↔ denN nd den a v ∧ ¬denN nd den b v := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  have dn0 : ∀ v, ¬denN nd den (.map []) v := fun v d =>
    ef.den_none v ((denN_of (fun t => isT_map t)).mp d)
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.none, difference_term_term _ _ _, fun v => ⟨fun x => absurd x (dn0 v),
      fun x => absurd (dt v) x.2⟩⟩
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · have nb : ∀ v, ¬denN nd den b v := by
      rcases rB with rfl | ⟨t, -⟩
      · exact fun v d => ef.den_none' eB none v ((sB v).mp d)
      · exact absurd none (isT_ne_none t)
    exact ⟨a, ha, opt_diff_none_r _ bt none, fun v => ⟨fun x => ⟨x, nb v⟩, fun x => x.1⟩⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨c, hc, run, sem⟩ := ef.opt_diff S eA eB (show K ≤ m by omega)
  refine ⟨c, Or.inl hc, ?_, fun v => ?_⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) a b (.map S) =
        Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) a B (.map S) := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_diff_node_r t.node m' (expand_isT t m') a _
    have e₂ : Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) a B (.map S) =
        Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) A B (.map S) := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_diff_node_l t.node m' (expand_isT t m') B _ (DEN.ne_term rB bt) (DEN.ne_none rB none)
    rw [e₁, e₂, run]
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_cinter (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b c : Term} {m : Nat} (ha : DEN nd E a)
    (hb : DEN nd E b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 1 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) : Combo nd c := by
  by_cases bt : b = .atom "term"
  · subst bt; rw [inter_term_right] at run; cases run; exact ca
  by_cases at' : a = .atom "term"
  · subst at'; rw [inter_term_left] at run; cases run; exact cb
  obtain ⟨A, eA, -, -, cA, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, -, -, cB, rB⟩ := h.red (den := den) hb
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [red_inter rA rB bt (DEN.ne_term rA at') m'] at run
  exact ef.cinter eA eB (cA ca) (cB cb) (by omega) run

theorem an_cdiff (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b c : Term} {m : Nat} (ha : DEN nd E a)
    (hb : DEN nd E b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 1 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) : Combo nd c := by
  by_cases bt : b = .atom "term"
  · subst bt; rw [diff_term_right] at run; cases run; exact combo_none nd
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · rw [diff_none _ a b bt none] at run; cases run; exact ca
  obtain ⟨A, eA, -, -, cA, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, -, -, cB, rB⟩ := h.red (den := den) hb
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [red_diff rA rB (DEN.ne_term rB bt) (DEN.ne_none rB none) m'] at run
  exact ef.cdiff eA eB (cA ca) (cB cb) (by omega) run

/-- Expansions of the node hold values: nil. -/
theorem EF.expN_inh (ef : EF nd E V den tl K) {e : Term} (he : E (expN e (keyOf nd))) :
    ∃ v, den (expN e (keyOf nd)) v := by
  obtain ⟨b, run, ex⟩ := ef.empty [] he
  have r := run K (Nat.le_refl _)
  rw [empty_expN] at r
  have : b = Bool.false := by cases b <;> simp_all [boolAtom]
  subst this
  have hx := ex (lh (expN e (keyOf nd)) + 1) (Nat.lt_succ_self _) (safeN_nil _)
  exact Classical.byContradiction fun hn => absurd (hx.mpr fun w hw => hn ⟨w, hw⟩) (by decide)

theorem an_empty (ef : EF nd E V den tl K) (h : NodeOk nd E) {a : Term} (S : List (Term × Term)) (ha : DEN nd E a) :
    ∃ b : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh a < N → SafeN N S → (b = Bool.true ↔ ∀ v, ¬denN nd den a v) := by
  rcases ha with ha | ha
  · obtain ⟨b, run, ex⟩ := ef.empty S ha
    refine ⟨b, fun m hm => run m (by omega), fun N hN hS => ?_⟩
    rw [ex N hN hS]
    exact ⟨fun x v d => x v ((denN_of (h.notN ha)).mp d), fun x v d => x v ((denN_of (h.notN ha)).mpr d)⟩
  · refine ⟨idIn (refOf nd) S, fun m hm => ?_, fun N _ hS => ?_⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact empty_node ha.node m' S
    · rw [safeN_noid hS]
      obtain ⟨v, hv⟩ := ef.expN_inh (h.exp ha)
      exact ⟨fun x => absurd x (by decide), fun x => absurd ((denN_node ha).mpr hv) (x v)⟩

theorem an_cempty (ef : EF nd E V den tl K) (h : NodeOk nd E) {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool}
    (ha : DEN nd E a) (ca : Combo nd a) (hS : Safe1 nd S) (hm : K + 1 ≤ m)
    (run : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v, ¬denN nd den a v := by
  rcases ha with ha | ha
  · rw [ef.cempty ha ca hS (by omega) run]
    exact ⟨fun x v d => x v ((denN_of (h.notN ha)).mp d), fun x v d => x v ((denN_of (h.notN ha)).mpr d)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [empty_node ha.node m' S] at run
    have := safeN_noid hS.1 (refOf nd)
    simp only [idIn] at this
    rw [this] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    obtain ⟨v, hv⟩ := ef.expN_inh (h.exp ha)
    exact ⟨fun x => absurd x (by decide), fun x => absurd ((denN_node ha).mpr hv) (x v)⟩

theorem an_sub (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ s : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v, denN nd den a v → denN nd den b v) := by
  obtain ⟨A, eA, sA, -, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, -, -, rB⟩ := h.red (den := den) hb
  obtain ⟨s, run, sound⟩ := ef.sub eA eB
  refine ⟨s, fun m hm => ?_, fun st v d => (sB v).mpr (sound st v ((sA v).mp d))⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e₁ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b := by
    rcases rA with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_l t.node m' (expand_isT t m') b
  have e₂ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A B := by
    rcases rB with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_r t.node m' (expand_isT t m') A
  rw [e₁, e₂]
  exact run _ (by omega)

theorem an_subc (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b)
    (incl : ∀ v, denN nd den a v → denN nd den b v) {m : Nat} (hm : K + 1 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨A, eA, sA, -, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, -, -, rB⟩ := h.red (den := den) hb
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e₁ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b := by
    rcases rA with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_l t.node m' (expand_isT t m') b
  have e₂ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A B := by
    rcases rB with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_r t.node m' (expand_isT t m') A
  rw [e₁, e₂]
  exact ef.subc eA eB (fun v d => (sB v).mp (incl v ((sA v).mpr d))) _ (by omega)

theorem static_map_of (ef : EF nd E V den tl K) {b : Term} (hb : DEN nd E b) :
    ∀ X, b = .map X → mapLookup X (.atom "dynamic") = none := by
  intro X e
  subst e
  rcases hb with hb | hb
  · rcases ef.static hb with h | ⟨Y, h, sY⟩ | ⟨r, st, g, h⟩
    · cases h
    · cases h; exact sY
    · cases h
  · exact absurd hb isT_map

theorem an_disj (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ s : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v, denN nd den a v → denN nd den b v → False) := by
  -- the top type and the node: `disjoint?/2` checks the emptiness of the node, which holds nil
  by_cases ct : (a = .atom "term" ∧ IsT nd b) ∨ (IsT nd a ∧ b = .atom "term")
  · refine ⟨Bool.false, fun m hm => ?_, fun st => by cases st⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases ct with ⟨rfl, hb⟩ | ⟨ha, rfl⟩
    · rw [disjoint_term_l, empty_any_node hb m']; rfl
    · rw [disj_term_r, empty_any_node ha m']; rfl
  obtain ⟨A, eA, sA, -, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, -, -, rB⟩ := h.red (den := den) hb
  obtain ⟨s, run, sound⟩ := ef.disj eA eB
  refine ⟨s, fun m hm => ?_, fun st v da db => sound st v ((sA v).mp da) ((sB v).mp db)⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [← run (m' + 1) (by omega)]
  by_cases at' : a = .atom "term"
  · subst at'
    rcases rA with rfl | ⟨t, -⟩
    · rcases rB with rfl | ⟨t, -⟩
      · rfl
      · exact absurd (Or.inl ⟨rfl, t⟩) ct
    · exact absurd t isT_term
  by_cases bt : b = .atom "term"
  · subst bt
    rcases rB with rfl | ⟨t, -⟩
    · rcases rA with rfl | ⟨t, -⟩
      · rfl
      · exact absurd (Or.inr ⟨t, rfl⟩) ct
    · exact absurd t isT_term
  have e₁ : Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) a b =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A b := by
    rcases rA with rfl | ⟨t, rfl⟩
    · rfl
    · exact disj_node_l t.node m' (expand_isT t m') b bt (static_map_of ef hb)
  have e₂ : Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A b =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A B := by
    rcases rB with rfl | ⟨t, rfl⟩
    · rfl
    · refine disj_node_r t.node m' (expand_isT t m') A (DEN.ne_term rA at') fun X e => ?_
      rcases rA with rfl | ⟨t', rfl⟩
      · exact static_map_of ef ha X e
      · simp [expN] at e; subst e; simp [mapLookup]
  rw [e₁, e₂]

theorem an_fuse (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (n : Int) {m : Nat} (ha : DEN nd E a)
    (hb : DEN nd E b) (ne : compareExact (fuel a b) a b ≠ .eq) (hm : K + 1 ≤ m) : ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ (DEN nd E r ∧ ∀ v, denN nd den r v ↔ denN nd den a v ∨ denN nd den b v)) := by
  rcases ha with ha | ha
  rotate_left
  · exact ⟨_, fuse_node_l ha.node _ _ _, Or.inl rfl⟩
  rcases hb with hb | hb
  rotate_left
  · exact ⟨_, fuse_node_r hb.node _ _ _, Or.inl rfl⟩
  obtain ⟨r, run, out⟩ := ef.fuse n ha hb ne (show K ≤ m by omega)
  refine ⟨r, run, out.imp id fun ⟨hr, sem⟩ => ⟨Or.inl hr, fun v => ?_⟩⟩
  rw [denN_of (h.notN hr), denN_of (h.notN ha), denN_of (h.notN hb)]
  exact sem v

theorem noList_expN (e : Term) (k : Int) :
    noList [(.atom "tuple", litN e k), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] =
      [(.atom "tuple", litN e k), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] := by
  simp [noList]

theorem an_tail (ef : EF nd E V den tl K) (h : NodeOk nd E) {e : Term} (he : DEN nd E e) :
    ∃ e', (∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«list_tail_unfold/1» (D m) e = .ok e') ∧ DEN nd E e' ∧
      (∀ v, denN nd den e' v ↔ denN nd den e v ∧ ¬tl v) ∧ lh e' ≤ lh e := by
  rcases he with he | he
  · obtain ⟨e', run, he', sem, l⟩ := ef.tail he
    refine ⟨e', run, Or.inl he', fun v => ?_, l⟩
    rw [denN_of (h.notN he'), denN_of (h.notN he)]
    exact sem v
  · obtain ⟨e'', run'', -, sem'', -⟩ := ef.tail (h.exp he)
    have r := run'' 1 (Nat.le_refl _)
    simp only [expN] at r
    rw [tail_map, noList_expN] at r
    simp only [Except.ok.injEq] at r
    subst r
    refine ⟨_, fun m hm => ?_, Or.inl (h.exp he), fun v => ?_, Nat.le_of_eq (by rw [lh_expN he, lh_isT he])⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact tail_node he.node m' (expand_isT he m')
    · rw [denN_of (h.notN (h.exp he)), denN_node he]
      simp only [expN] at sem'' ⊢
      exact ⟨fun d => ⟨d, ((sem'' v).mp d).2⟩, fun d => d.1⟩

theorem node_cmp {r : List Nat} {S : List (Term × Term)} {g x : Term}
    (h : Term.compare (Term.fuel (.tuple #[.reference r, .map S, g]) x) (.tuple #[.reference r, .map S, g]) x = .eq) : IsNode x := by
  cases x <;> rw [compare_step] at h <;> simp [Compare.compareStep] at h
  rename_i ys
  obtain ⟨l⟩ := ys
  match l, h with
  | [a, b, c], h =>
    simp only [List.compareLex_cons_cons, Ordering.then_eq_eq, List.size_toArray, List.length_cons,
      List.length_nil] at h
    obtain ⟨-, ha, hb, -⟩ := h
    cases a <;> rw [compare_step] at ha <;> simp [Compare.compareStep] at ha
    obtain ⟨Y, rfl⟩ := map_cmp_shape hb
    exact ⟨_, _, _, rfl⟩
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | _ :: _ :: _ :: _ :: _, h => simp at h

theorem expN_exact {e e' : Term} (he : IsT nd e) (he' : IsT nd e') (k : Int) :
    compareExact (fuel (expN e k) (expN e' k)) (expN e k) (expN e' k) = .eq := by
  have ee := isT_exact he he'
  apply map_compareExact_eq_of_lookup
  intro q
  simp only [List.find?_cons, List.find?_nil]
  by_cases t : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
  · simp [t, litN, Term.list, compareExact_tuple, List.compareLex_cons_cons, compareExact_cons, ee,
      List.compareLex_nil_nil]
  by_cases a : compareExact (fuel q (.atom "atom")) q (.atom "atom") = .eq
  · simp [t, a]
  · simp [t, a]

theorem an_resp (ef : EF nd E V den tl K) (h : NodeOk nd E) {e e' : Term} {v : V} (he : DEN nd E e)
    (he' : DEN nd E e') (c : Term.compare (Term.fuel e e') e e' = .eq) (d : denN nd den e' v) : denN nd den e v := by
  rcases he with he | he <;> rcases he' with he' | he'
  · rw [denN_of (h.notN he')] at d
    rw [denN_of (h.notN he)]
    exact ef.resp he he' c d
  · obtain ⟨S, rfl, -⟩ := he'.node
    exact absurd (ef.node he (node_cmp (Lynx.Term.compare_eq_symm c))) (h.notN he)
  · obtain ⟨S, rfl, -⟩ := he.node
    exact absurd (ef.node he' (node_cmp c)) (h.notN he')
  · rw [denN_node he'] at d
    rw [denN_node he]
    exact ef.resp (h.exp he) (h.exp he') (compare_eq_of_compareExact_eq _ _ (expN_exact he he' _)) d

/-- Element types with the node: operations on the node compute on its expansion. -/
theorem addNode (ef : EF nd E V den tl K) (h : NodeOk nd E) :
    EF nd (DEN nd E) V (denN nd den) tl (K + 1) where
  pos := by omega
  term := Or.inl ef.term
  none := Or.inl ef.none
  den_term := fun v => (denN_of isT_term).mpr (ef.den_term v)
  static := fun {a} ha => by
    rcases ha with ha | ha
    · exact ef.static ha
    · obtain ⟨S, rfl, -⟩ := ha.node; exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
  node := fun {a} ha hn => by
    rcases ha with ha | ha
    · exact ef.node ha hn
    · exact ha
  low := fun {a} ha z => by
    rcases ha with ha | ha
    · exact ef.low ha z
    · rw [lh_isT ha] at z; cases z
  cinter := fun ha hb ca cb hm run => an_cinter ef h ha hb ca cb hm run
  cdiff := fun ha hb ca cb hm run => an_cdiff ef h ha hb ca cb hm run
  cempty := fun ha ca hS hm run => an_cempty ef h ha ca hS hm run
  inhabited := ef.inhabited
  resp := fun he he' c d => an_resp ef h he he' c d
  union := fun ha hb => an_union ef h ha hb
  inter := fun ha hb => an_inter ef h ha hb
  diff := fun ha hb => an_diff ef h ha hb
  opt_union := by intro a b S m ha hb hm; exact an_opt_union ef h S ha hb hm
  opt_inter := by intro a b S m ha hb hm; exact an_opt_inter ef h S ha hb hm
  opt_diff := by intro a b S m ha hb hm; exact an_opt_diff ef h S ha hb hm
  empty := fun S ha => an_empty ef h S ha
  sub := fun ha hb => an_sub ef h ha hb
  subc := fun ha hb incl m hm => an_subc ef h ha hb incl (by omega)
  disj := fun ha hb => an_disj ef h ha hb
  fuse := by intro a b n m ha hb ne hm; exact an_fuse ef h n ha hb ne hm
  tail := fun he => an_tail ef h he
  tl_witness := ef.tl_witness

end


/-! The bottom level: types over pure tuple fields, top list and map fields, and the node. -/

theorem pure_of_descr {nd : Term} {X : List (Term × Term)}
    (sX : DescrC FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") X) : PureMap nd X := by
  refine ⟨fun q h => ?_, fun name w hw => ?_⟩
  · obtain ⟨name, m, rfl⟩ := sX.keys q h
    rcases names_mem m with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rcases sX.fields name w hw with ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩
    · obtain ⟨b, rfl, h₁, h₂⟩ := f
      exact Or.inl (Or.inl ⟨rfl, b, rfl, h₁, h₂⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, f.1, f.2⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨by decide, by decide, by rw [show w = funTopT from f]; rfl⟩))
    · exact Or.inl f
    · exact Or.inr ⟨rfl, f⟩
    · exact Or.inl f

/-- The step to the bottom level. -/
theorem step0 (nd : Term) : StepOk nd (fun _ => Pure nd) 8 FunTop (OField (PureLit nd)) (FieldOk "list")
    (FieldOk "map") Resp Resp Resp FVT where
  ks := kinds0 nd (by omega)
  fc := fcOf 8
  ftop := rfl
  fz := fun hx _ => hx
  fvw := ⟨.nil, fun _ => Bool.true, resp_const _, trivial⟩
  nest := fun {a N} ha _ => by
    rcases ha with rfl | ⟨X, rfl, sX⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨X, rfl, pure_of_descr sX⟩)
  ops := fun _ => ⟨(pureOk nd).mono (by omega), (pureDiff nd).mono (by omega), (pureFun nd).mono (by omega)⟩
  tz := fun {x} fx z => by
    rcases fx with ⟨k, rfl⟩ | wx
    · exact ⟨k, rfl⟩
    · have := pure_one (Or.inr wx) (fun k h => by subst h; exact absurd (Bdd.leaf_iff.mp wx) (pureLit_not _ · ⟨_, rfl⟩))
      omega
  lz := fun {x} fx _ => by
    have := topF_of (Or.inl rfl) fx
    simp [topValue] at this
    exact this.symm
  mz := fun {x} fx _ => by
    have := topF_of (Or.inr rfl) fx
    simp [topValue] at this
    exact ⟨_, this.symm⟩
  treal := fun c {x} _ _ => ⟨fun _ => c, resp_const c, rfl⟩

/-- Maps of a single tuple field are exactly equal when their fields are. -/
theorem single_exact {A B : List (Term × Term)} {x y : Term}
    (tA : mapLookup A (.atom "tuple") = some x) (tB : mapLookup B (.atom "tuple") = some y)
    (sA : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    (sB : Erlang.erlang.«map_size/1» (.map B) = .ok (.integer 1)) (e : compareExact (fuel x y) x y = .eq) :
    compareExact (fuel (.map A) (.map B)) (.map A) (.map B) = .eq := by
  apply map_compareExact_eq_of_lookup
  intro q
  change Option.Rel _ (mapLookup A q) (mapLookup B q)
  by_cases hq : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
  · rw [mapLookup_congr hq, mapLookup_congr hq, tA, tB]
    exact Option.Rel.some e
  · have nA : mapLookup A q = none := by
      cases h : mapLookup A q with
      | none => rfl
      | some x => exact absurd (size_one_keys sA h tA) hq
    have nB : mapLookup B q = none := by
      cases h : mapLookup B q with
      | none => rfl
      | some x => exact absurd (size_one_keys sB h tB) hq
    rw [nA, nB]; exact Option.Rel.none

/-- Maps of a single top tuple field hold exactly the tuples. -/
theorem den_single_top {A : List (Term × Term)} {k : Term}
    (tA : mapLookup A (.atom "tuple") = some (.tuple #[k, .atom "open", .nil]))
    (sA : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1)) (v : PtG Resp Resp Resp FVT) :
    denD (.map A) v ↔ v.1.1 = "tuple" := by
  obtain ⟨⟨name, p⟩, -, -⟩ := v
  rw [denD_map]
  by_cases hn : name = "tuple"
  · subst hn; simp [tA, dn_tuple, denO_top]
  · simp [single_other sA tA hn, dn_none, hn]

/-- Leaves of pure tuple fields: the top leaf or the expansion literal. -/
theorem pure3 {nd k tag e : Term} (h : OField (PureLit nd) (.tuple ⟨[k, tag, e]⟩)) :
    (tag = .atom "open" ∧ e = .nil) ∨
      ∃ e₀, IsT nd e₀ ∧ k = .integer (keyOf nd) ∧ tag = .atom "closed" ∧ e = Term.list [.atom "term", e₀] := by
  rcases pure_cases h with ⟨k', ex⟩ | ex | ex | ⟨e₀, h₀, ex⟩ | ⟨j, e₀, c, u, d, h₀, ex⟩
  · simp at ex; exact Or.inl ⟨ex.2.1, ex.2.2⟩
  · cases ex
  · cases ex
  · simp [litN] at ex; exact Or.inr ⟨e₀, h₀, ex.1, ex.2.1, ex.2.2⟩
  · simp at ex

/-- Fusing types of the bottom level. -/
theorem fuse0 (nd : Term) : FuseOk 8 FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") Resp Resp Resp FVT := by
  intro a b n m ha hb ne hm
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, fuse_term_l _ _ _, Or.inl rfl⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, fuse_term_r _ _ _, Or.inl rfl⟩
  obtain ⟨u, hu, urun, usem, -⟩ := de_union (step0 nd) (Or.inr ⟨A, rfl, sA⟩) (Or.inr ⟨B, rfl, sB⟩)
  have run := urun m hm
  obtain ⟨c₁, r₁⟩ := aob_bool (.map A)
  obtain ⟨c₂, r₂⟩ := aob_bool (.map B)
  have second : ∃ r, (do
      let _19 ← Lynx.Except.andAlso (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A))
        (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B)) Bool.true
      Lynx.Except.guard (Except.ok (_19.isMember [Term.atom "false", Term.atom "nil"]))
        (fun _ => pure (Term.atom "nil")) fun _ => Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B)) = .ok r ∧
      (r = .atom "nil" ∨ (DEG FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") r ∧
        ∀ v : PtG Resp Resp Resp FVT, denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
    rw [r₁, r₂]
    cases c₁ <;> cases c₂ <;>
      simp [Lynx.Except.andAlso, boolAtom, isMember, run, hu, usem]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3».eq_def]
  simp only [getMapKeys_single]
  split
  · rename_i k₀ tag e₁ hA
    have hxA : mapLookup A (.atom "tuple") = some (.tuple ⟨[k₀, tag, e₁]⟩) := by
      cases h : mapLookup A (.atom "tuple") <;> simp_all
    split
    · rename_i k₁ tag₂ e₂ hB
      have hxB : mapLookup B (.atom "tuple") = some (.tuple ⟨[k₁, tag₂, e₂]⟩) := by
        cases h : mapLookup B (.atom "tuple") <;> simp_all
      obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      have pA := fieldC_tuple (sA.fields _ _ hxA)
      have pB := fieldC_tuple (sB.fields _ _ hxB)
      have fallback : ∀ (x : Except Exception Term),
          (∀ c₁ c₂ : Bool, Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A) = .ok (boolAtom c₁) →
            Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B) = .ok (boolAtom c₂) →
            x = .ok (if c₁ && c₂ then u else .atom "nil")) →
          ∃ r, x = .ok r ∧ (r = .atom "nil" ∨ (DEG FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") r ∧
            ∀ v : PtG Resp Resp Resp FVT, denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
        intro x hx
        refine ⟨_, hx c₁ c₂ r₁ r₂, ?_⟩
        cases c₁ <;> cases c₂ <;> simp [hu, usem]
      by_cases G : compareExact (fuel tag₂ tag) tag₂ tag = .eq ∧ sa = 1 ∧ sb = 1 ∧ 0 < n
      · obtain ⟨et, rfl, rfl, pos⟩ := G
        have sub : Erlang.erlang.«-/2» (.integer n) (.integer 1) = .ok (.integer (n - 1)) := by
          rw [Erlang.erlang.«-/2_integers»]
        have pc : compare n 0 = Ordering.gt := by exact Int.compare_eq_gt.mpr pos
        rcases pure3 pA with ⟨rfl, rfl⟩ | ⟨eA₀, hA₀, rfl, rfl, rfl⟩ <;>
          rcases pure3 pB with ⟨rfl, rfl⟩ | ⟨eB₀, hB₀, rfl, rfl, rfl⟩ <;> simp at et
        · obtain ⟨kf, hk, -⟩ := leaf_new_key "open" (Or.inl rfl) []
          simp only [Term.list] at hk
          refine ⟨_, ?_, Or.inr ⟨Or.inr ⟨[(.atom "tuple", .tuple #[.integer kf, .atom "open", .nil])], rfl,
            ⟨fun q h => ?_, fun name w h => ?_⟩⟩, fun v => ?_⟩⟩
          · simp [hsa, hsb, Erlang.erlang.«=:=/2», Lynx.Except.andAlso,
              Erlang.erlang.«and/2», Erlang.erlang.«==/2», Erlang.erlang.«>/2», pc, isMember]
            rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
            simp [Erlang.lists.«reverse/1», hk]
          · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
            by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
            · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
            · simp [e] at h
          · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq] at h
            by_cases e : name = "tuple"
            · subst e; simp at h; subst h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨kf, rfl⟩⟩))))
            · simp [e] at h
          · have one : mapLookup [(.atom "tuple", .tuple #[.integer kf, .atom "open", .nil])] (.atom "tuple") =
                some (.tuple #[.integer kf, .atom "open", .nil]) := by simp [mapLookup]
            rw [den_single_top one (by simp [Erlang.erlang.«map_size/1»]; rfl), den_single_top hxA hsa,
              den_single_top hxB hsb, or_self]
        · exfalso
          apply ne
          refine single_exact hxA hxB hsa hsb ?_
          have := pureLit_exact ⟨eB₀, hB₀, rfl⟩ ⟨eA₀, hA₀, rfl⟩
          simpa [litN, Term.list] using this
      · refine fallback _ fun c₁ c₂ r₁ r₂ => ?_
        have pc : compare n 0 = Ordering.gt ↔ 0 < n := Int.compare_eq_gt
        by_cases e₁ : compareExact (fuel tag₂ tag) tag₂ tag = .eq <;> by_cases e₂ : sa = 1 <;> by_cases e₃ : sb = 1 <;> by_cases e₄ : 0 < n <;>
          simp only [e₁, e₂, e₃, e₄, and_self, not_true_eq_false] at G <;>
          cases c₁ <;> cases c₂ <;>
          simp [hsa, hsb, e₁, e₂, e₃, e₄, pc, r₁, r₂, run, Erlang.erlang.«=:=/2»,
            Lynx.Except.andAlso, Erlang.erlang.«and/2», Erlang.erlang.«==/2»,
            Erlang.erlang.«>/2», isMember, boolAtom]
    · exact second
  · exact second

end Elixir.STTDescrProofsTest.Nest
