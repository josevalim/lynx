namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Top-level types over the element types of a level: the top type or types whose function fields are arrows
between element types. Their plain and optimized operations hold the expected points, and their emptiness and
subtyping checks are exact. -/

/-- Top-level types over the element types of a level. -/
def TC (L : Level) (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) X

abbrev TP (L : Level) : Type := PtD L.E L.den L.tl (FVal L.E L.den)

/-- Top-level types whose function types may hold any literals, as the specs accept them. -/
def TCF (L : Level) (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ DescrC FunF (TField L.E) (LF L.E) (MField L.E) X

theorem tks (L : Level) : Kinds (L.K + 11) (TField L.E) (LF L.E) (MField L.E) (ValT L.E L.den) (ValLN L.E L.den L.tl)
    (ValMN L.E L.den) := (kinds L.ef).mono (by omega)

theorem tfc (L : Level) : FunC (L.K + 11) (FunA L.E) (FVal L.E L.den) (fun _ => True) True := funAC L.ef L.ef.subc

theorem lookup_out' {Fn TF LF MF : Term → Prop} {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {name : String}
    (h : name ∉ names) : mapLookup X (.atom name) = none := by
  cases hx : mapLookup X (.atom name) with
  | none => rfl
  | some x =>
    obtain ⟨name', m, e⟩ := sX.keys _ (by rw [hx]; rfl)
    simp only [Term.atom.injEq] at e
    subst e; exact absurd m h

section
variable {L : Level}

theorem termT (L : Level) : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) T ∧ T ≠ [] ∧
    ∀ v : TP L, denD (.map T) v := by
  obtain ⟨T, term, sT, ne, -, all⟩ := termC (FV := FVal L.E L.den) (tks L) (Fn := FunA L.E) funA_top
  exact ⟨T, term, sT, ne, fun v => (denD_map v).mpr (all _ v.2.1 _ v.2.2)⟩

theorem tc_nil : TC L (.map []) := Or.inr ⟨[], rfl, descrC_nil (Fn := FunA L.E)⟩

theorem denD_nil (v : TP L) : ¬denD (.map []) v := by simp [denD_map, mapLookup, dn_none]

theorem tc_union {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, union_term_l _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, union_term_r _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem, -⟩ := descr_union (tks L) (tfc L) (m := n) (by omega) sA sB
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

theorem tc_inter {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, inter_term_left _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, inter_term_right _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem, -⟩ := descr_inter (tks L) (tfc L) (m := n) (by omega) sA sB
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

theorem diff_none_right' (d : Dispatcher) {a : Term} (ha : TC L a) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map []) = .ok a := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]

theorem tc_diff {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, tc_nil, diff_term_right _ _, fun v => by simp [denD_nil, denD_term]⟩
  by_cases nB : B = []
  · subst nB
    exact ⟨a, ha, diff_none_right' _ ha, fun v => by simp [denD_nil]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, all⟩ := termT L
    obtain ⟨U, run, sU, sem, -⟩ := descr_diff (tks L) (tfc L) (m := n) (by omega) sT sB
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, (diff_term_left _ term sT.static sB.static nB).trans run, fun v => ?_⟩
    have := (denD_map v).mp (all v)
    simp only [denD_map, sem _ _ v.2.2, this, denD_term, true_and, Bool.true_and]
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run, sU, sem, -⟩ := descr_diff (tks L) (tfc L) (m := n) (by omega) sA sB
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

theorem tc_opt_union {a b : Term} (ha : TC L a) (hb : TC L b) (S : List (Term × Term)) {m : Nat}
    (hm : L.K + 13 ≤ m) : ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_left _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_union (tks L) (tfc L) (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

theorem tc_opt_inter {a b : Term} (ha : TC L a) (hb : TC L b) (S : List (Term × Term)) {m : Nat}
    (hm : L.K + 13 ≤ m) : ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, opt_inter_term_l _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, opt_inter_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_inter (tks L) (tfc L) (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

theorem tc_opt_diff {a b : Term} (ha : TC L a) (hb : TC L b) (S : List (Term × Term)) {m : Nat}
    (hm : L.K + 15 ≤ m) : ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, tc_nil, difference_term_term _ _ _, fun v => by simp [denD_nil, denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · by_cases nB : B = []
    · subst nB
      exact ⟨_, Or.inl rfl, difference_term_none _ _, fun v => by simp [denD_nil, denD_term]⟩
    obtain ⟨T, term, sT, -, all⟩ := termT L
    obtain ⟨U, run, sU, sem⟩ := descr_opt_diff (tks L) (tfc L) (m := n) (by omega) sT sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, (opt_diff_term_left _ _ term sT.static sB.static nB).trans run, fun v => ?_⟩
    have := (denD_map v).mp (all v)
    simp only [denD_map, sem _ _ v.2.2, this, denD_term, true_and, Bool.true_and]
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run, sU, sem⟩ := descr_opt_diff (tks L) (tfc L) (m := n) (by omega) sA sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- Types without points are checked empty. -/
theorem tc_empty {a : Term} (ha : TC L a) {m : Nat} (hm : L.K + 11 ≤ m) (none : ∀ v : TP L, ¬denD a v) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (.atom "true") := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact absurd (denD_term ptWit) (none ptWit)
  rw [empty_map_seen]
  refine descr_empty_none (tks L) (tfc L) trivial hm sX fun name p ok => ?_
  by_cases mem : name ∈ names
  · have := none ⟨(name, p), mem, ok⟩
    simpa [denD] using this
  · rw [lookup_out' sX mem, dn_none]

/-- Subtyping of top-level types is complete. -/
theorem tc_sub {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (incl : ∀ v : TP L, denD a v → denD b v) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨T, term, sT, -, all⟩ := termT L
  have left : ∃ A, DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) A ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) b ∧
      ∀ v : TP L, denD a v ↔ denD (.map A) v := by
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · exact ⟨T, sT, subtype_term_l term _ _, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩⟩
    · exact ⟨A, sA, rfl, fun v => Iff.rfl⟩
  obtain ⟨A, sA, eA, dA⟩ := left
  have right : ∃ B, DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) B ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) b =
        Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B) ∧
      ∀ v : TP L, denD b v ↔ denD (.map B) v := by
    rcases hb with rfl | ⟨B, rfl, sB⟩
    · exact ⟨T, sT, subtype_term_r term _ _, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩⟩
    · exact ⟨B, sB, rfl, fun v => Iff.rfl⟩
  obtain ⟨B, sB, eB, dB⟩ := right
  rw [eA, eB]
  refine descr_sub_complete (tks L) (tfc L) trivial (by omega) sA sB fun name p ok h => ?_
  by_cases mem : name ∈ names
  · have := (dB ⟨(name, p), mem, ok⟩).mp (incl _ ((dA _).mpr ((denD_map _).mpr h)))
    exact (denD_map _).mp this
  · rw [lookup_out' sA mem, dn_none] at h; cases h

end

end Elixir.STTDescrProofsTest.Nest
