namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Negations of gradual types, and subtyping of gradual types by both bounds. -/

section
variable {L : Level}

/-- Negations swap the bounds. -/
def GNSem (L : Level) (a c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ ¬denD (upper a) v) ∧ ∀ v : TP L, denD (upper c) v ↔ ¬denD a v

theorem nsem_of_dsem {a c : Term} (h : DSem L (.atom "term") a c) : GNSem L a c :=
  ⟨fun v => by simp [h.1 v, denD_term], fun v => by simp [h.2 v, upper_term, denD_term]⟩

theorem nsem_term : GNSem L (.atom "term") (.map []) :=
  ⟨fun v => by simp [denD_nil, upper_term, denD_term], fun v => by simp [upper_nil, denD_nil, denD_term]⟩

theorem gc_neg {a : Term} (ha : GC L a) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c ∧ GNSem L a c := by
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, GC.tc tc_nil, by simp [Elixir.Module.Types.Descr.«bare_negation/1»],
      nsem_term⟩
  obtain ⟨c, hc, run, sem⟩ := gc_diff (GC.tc tc_term) ha hm
  exact ⟨c, hc, by simpa [Elixir.Module.Types.Descr.«bare_negation/1», Elixir.Module.Types.Descr.«term/0»] using run,
    nsem_of_dsem sem⟩

theorem gc_opt_neg {a : Term} (ha : GC L a) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok c ∧ GNSem L a c := by
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · refine ⟨_, GC.tc tc_nil, ?_, nsem_term⟩
    rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
    simp
  obtain ⟨c, hc, run, sem⟩ := gc_opt_diff (GC.tc tc_term) ha [] hm
  refine ⟨c, hc, ?_, nsem_of_dsem sem⟩
  rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
  simpa [Elixir.Module.Types.Descr.«opt_difference/2», Elixir.Module.Types.Descr.«term/0», unfold_map] using run

theorem gc_opt_union2 {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok c ∧ USem L a b c := by
  simpa [Elixir.Module.Types.Descr.«opt_union/2»] using gc_opt_union ha hb [] hm

theorem gc_opt_inter2 {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok c ∧ ISem L a b c := by
  simpa [Elixir.Module.Types.Descr.«opt_intersection/2»] using gc_opt_inter ha hb [] hm

theorem gc_opt_diff2 {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_difference/2» (D m) a b = .ok c ∧ DSem L a b c := by
  simpa [Elixir.Module.Types.Descr.«opt_difference/2»] using gc_opt_diff ha hb [] hm

/-- Each field of an included static type is covered by the other type. -/
theorem keysub_complete {m : Nat} (hm : L.K + 13 ≤ m) {A B : List (Term × Term)} (sA : DC L A) (sB : DC L B)
    (incl : ∀ v : TP L, denD (.map A) v → denD (.map B) v) : ∀ e ∈ mapEntries A, KeySub (D m) B e.1 e.2 := by
  intro e me
  have hx := mapLookup_of_mem_mapEntries me
  obtain ⟨name, mem, key⟩ := sA.keys e.1 (by simp [hx])
  rw [key] at hx ⊢
  have fx := sA.fields name e.2 hx
  have none : ∀ w, FC L name w → (∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (some w) p = Bool.false) →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) w (.map []) = .ok (.atom "true") :=
    fun w fw empty => fieldC_empty_none (tks L) (tfc L) (show L.K + 11 ≤ m by omega) fw (fun _ => trivial) empty
  have inc : ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (some e.2) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true := fun p ok h =>
    (denD_map ⟨(name, p), mem, ok⟩).mp (incl ⟨(name, p), mem, ok⟩ ((denD_map _).mpr (by rw [hx]; exact h)))
  cases hy : mapLookup B (.atom name) with
  | none =>
    refine Or.inr ⟨hy, none _ fx fun p ok => ?_⟩
    cases h : dn name (some e.2) p
    · rfl
    · have := inc p ok h; rw [hy, dn_none] at this; cases this
  | some y =>
    obtain ⟨w, run, k, sem⟩ := fieldC_diff (tks L) (tfc L) (show L.K + 11 + 2 ≤ m by omega) fx (sB.fields name y hy)
    refine Or.inl ⟨y, w, hy, run, ?_⟩
    cases kw : kept (.atom name, w)
    · rcases kept_of_ne kw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (none w (k kw).1 fun p ok => ?_))
      have := sem p ok
      rw [keptO_true kw] at this
      rw [this]
      cases h : dn name (some e.2) p
      · rfl
      · have := inc p ok h; rw [hy] at this; simp [this]

/-- The subtraction check of `subtype?/2` is complete on top-level types. -/
theorem esub_complete {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (incl : ∀ v : TP L, denD a v → denD b v) :
    Elixir.Module.Types.Descr.«empty_difference_subtype?/3» (D m) a b (.map []) = .ok (.atom "true") := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · simp [getMapKeys]
    · simp [getMapKeys_single, sA.static]
  have left : ∃ A, DC L A ∧ (∀ v : TP L, denD a v ↔ denD (.map A) v) ∧
      Elixir.Module.Types.Descr.«empty_difference_subtype?/3» (D m) a (.map B) (.map []) =
        (do
          let it ← Erlang.maps.«next/1» (Term.list ((mapEntries A).map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» (D m) it (.map B) (.map [])) := by
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · obtain ⟨T, term, sT, -, all⟩ := termT L
      refine ⟨T, sT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩, ?_⟩
      simp [getMapKeys, term, Erlang.maps.«iterator/1»]
    · exact ⟨A, sA, fun v => Iff.rfl, by simp [getMapKeys_single, sA.static, Erlang.maps.«iterator/1»]⟩
  obtain ⟨A, sA, eA, rA⟩ := left
  rw [rA]
  exact iterator_sub (D m) B (mapEntries A) (keysub_complete hm sA sB fun v h => incl v ((eA v).mpr h))

theorem sstatic_complete {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (incl : ∀ v : TP L, denD a v → denD b v) :
    Elixir.Module.Types.Descr.«subtype_static?/2» (D m) a b = .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«subtype_static?/2»
  by_cases same : compareExact (fuel b a) b a = .eq
  · simp [Erlang.erlang.«=:=/2», same]
  · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»,
      esub_complete ha hb hm incl]

end

end Elixir.STTDescrProofsTest.Nest
