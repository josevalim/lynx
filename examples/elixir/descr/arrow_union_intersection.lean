namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Unions and intersections of gradual types whose function types are arrows. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop} {H : Prop}

/-- Merging fields keeps them in their classes. -/
theorem mergeL_descr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {k : Nat} (hk : K + 1 ≤ k)
    {A B U : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : MergeL (Elixir.Module.Types.Descr.«bare_union/3» (D k)) A B U) : DescrC Fn TF LF MF U :=
  (union_gen (slh := False) (TV := TV) (LV := LV) (MV := MV) (FV := FV) sA sB _ h.1 h.2 fun _ _ _ fx fy =>
    let ⟨u, ru, fu, su, _⟩ := fieldC_union ks fc hk fx fy; ⟨u, ru, fu, su, False.elim⟩).1

/-- Intersecting fields keeps them in their classes. -/
theorem interL_descr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {k : Nat} (hk : K + 1 ≤ k)
    {A B I : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : InterL (Elixir.Module.Types.Descr.«bare_intersection/3» (D k)) A B I) : DescrC Fn TF LF MF I :=
  (inter_gen (slh := False) (TV := TV) (LV := LV) (MV := MV) (FV := FV) sA sB _ h.1 h.2 fun _ _ _ fx fy =>
    let ⟨w, rw', kw, sw⟩ := fieldC_inter ks fc hk fx fy; ⟨w, rw', fun h => ⟨(kw h).1, False.elim⟩, sw⟩).1

end

section
variable {t : Term} {n : Nat}

/-- Gradual types whose bounds are element types of the next level, so their function types are arrows. -/
def GD (t : Term) (n : Nat) (a : Term) : Prop :=
  GC (level t n) a ∧ DE (level t n).E (lower a) ∧ DE (level t n).E (upper a)

theorem de_map {X : List (Term × Term)} (h : DE (level t n).E (.map X)) :
    DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E) (MField (level t n).E) X := by
  rcases h with h | ⟨X', e, sX⟩
  · cases h
  · simp only [Term.map.injEq] at e; subst e; exact sX

/-- Element types of the next level are their own bounds. -/
theorem de_gd {a : Term} (ha : DE (level t n).E a) : GD t n a ∧ lower a = a ∧ upper a = a := by
  have tc := de_tc ha
  have e : lower a = a ∧ upper a = a := by
    rcases ha with rfl | ⟨X, rfl, sX⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨by simp [lower, rmDyn_static sX.static], upper_tc tc⟩
  exact ⟨⟨GC.tc tc, by rw [e.1]; exact ha, by rw [e.2]; exact ha⟩, e⟩

/-- Unions of dynamic parts keep arrows. -/
theorem dyn_union_de {k : Nat} (hk : (level t n).K + 12 ≤ k) {a b c : Term} (ha : DE (level t n).E a)
    (hb : DE (level t n).E b)
    (run : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) a b
      (.function "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok c) : DE (level t n).E c := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · have e : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) (.atom "term") b
        (.function "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl
    rw [e] at run; cases run; exact Or.inl rfl
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · have e : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) (.map A) (.atom "term")
        (.function "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl
    rw [e] at run; cases run; exact Or.inl rfl
  have st := stepOf (level t n).ef (level t n).none
  obtain ⟨U, rU, look⟩ := merge_gen (D (k + 1)) "Elixir.Module.Types.Descr" "bare_union" #[] _
    (fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure k q v₁ v₂) A B
    (fun q h => let ⟨n', _, e⟩ := sB.keys q h; ⟨n', e⟩) (fun q x y hx hy => by
      obtain ⟨name, -, rfl⟩ := sA.keys q (by simp [hx])
      obtain ⟨u, ru, -⟩ := fieldC_union st.ks st.fc (by omega) (sA.fields name x hx) (sB.fields name y hy)
      exact ⟨u, ru⟩)
  have e : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) (.map A) (.map B)
      (.function "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok (.map U) := by
    unfold Elixir.Module.Types.Descr.«dynamic_union/3»; simpa [unfold_map] using rU
  rw [e] at run; cases run
  refine Or.inr ⟨U, rfl, mergeL_descr st.ks st.fc (by omega) sA sB ⟨fun name => look _, fun q h => ?_⟩⟩
  cases hB : mapLookup B q with
  | none => rw [(look q).1 hB] at h; exact Or.inl h
  | some _ => exact Or.inr rfl

/-- Unions of gradual types whose function types are arrows unite both bounds and keep arrows. -/
theorem gd_union {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧ GD t n c ∧
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∨ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∨ denD (upper b) v) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ha, la, ua⟩ := ga
  obtain ⟨hb, lb, ub⟩ := gb
  have bounds : ∀ c, USem (level t n) a b c →
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∨ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∨ denD (upper b) v) := fun c sem =>
    ⟨fun v => (denD_lower c (toTPN v)).trans ((sem.1 _).trans
      (or_congr (denD_lower a (toTPN v)).symm (denD_lower b (toTPN v)).symm)), fun v => sem.2 (toTPN v)⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, union_term_l _ _, ⟨GC.tc tc_term, Or.inl rfl, Or.inl rfl⟩, bounds _ (usem_term_l _)⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, union_term_r _ _, ⟨GC.tc tc_term, Or.inl rfl, Or.inl rfl⟩, bounds _ (usem_term_r _)⟩
  by_cases nX : X = []
  · subst nX; exact ⟨_, union_nil_l _ _, ⟨hb, lb, ub⟩, bounds _ (usem_nil_l _)⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨_, union_nil_r _ _, ⟨ha, la, ua⟩, bounds _ (usem_nil_r _)⟩
  by_cases st : mapLookup X (.atom "dynamic") = none ∧ mapLookup Y (.atom "dynamic") = none
  · have eX : lower (.map X) = .map X ∧ upper (.map X) = .map X := by simp [lower, upper, rmDyn_static st.1, st.1]
    have eY : lower (.map Y) = .map Y ∧ upper (.map Y) = .map Y := by simp [lower, upper, rmDyn_static st.2, st.2]
    rw [eX.1] at la; rw [eY.1] at lb
    obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).union la lb
    obtain ⟨gc, lc, uc⟩ := de_gd dc
    exact ⟨c, run _ (by omega), gc, fun v => by rw [lc, eX.1, eY.1]; exact sem v,
      fun v => by rw [uc, eX.2, eY.2]; exact sem v⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp_all
  obtain ⟨c, hc, run, lo, up, U, rfl, look, rD⟩ := merge_aligned (bare_union_op (L := level t n) (n := k + 1) (by omega))
    (bare_union_op (n := k) (by omega)) (bare_union_dyn _) ha hb
  have st := stepOf (level t n).ef (level t n).none
  have dl : DE (level t n).E (lower (.map U)) :=
    Or.inr ⟨_, rfl, mergeL_descr st.ks st.fc (by omega) (de_map la) (de_map lb) look⟩
  exact ⟨_, (union_run_grad _ nX nY g).trans run, ⟨hc, dl, dyn_union_de (by omega) ua ub rD⟩, bounds _ ⟨lo, up⟩⟩

/-- Intersections of gradual types whose function types are arrows intersect both bounds and keep arrows. -/
theorem gd_inter {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧ GD t n c ∧
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∧ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∧ denD (upper b) v) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ha, la, ua⟩ := ga
  obtain ⟨hb, lb, ub⟩ := gb
  have bounds : ∀ c, ISem (level t n) a b c →
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∧ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∧ denD (upper b) v) := fun c sem =>
    ⟨fun v => (denD_lower c (toTPN v)).trans ((sem.1 _).trans
      (and_congr (denD_lower a (toTPN v)).symm (denD_lower b (toTPN v)).symm)), fun v => sem.2 (toTPN v)⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, inter_term_left _ _, ⟨hb, lb, ub⟩, bounds _ (isem_term_l _)⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, inter_term_right _ _, ⟨ha, la, ua⟩, bounds _ (isem_term_r _)⟩
  by_cases st : mapLookup X (.atom "dynamic") = none ∧ mapLookup Y (.atom "dynamic") = none
  · have eX : lower (.map X) = .map X ∧ upper (.map X) = .map X := by simp [lower, upper, rmDyn_static st.1, st.1]
    have eY : lower (.map Y) = .map Y ∧ upper (.map Y) = .map Y := by simp [lower, upper, rmDyn_static st.2, st.2]
    rw [eX.1] at la; rw [eY.1] at lb
    obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).inter la lb
    obtain ⟨gc, lc, uc⟩ := de_gd dc
    exact ⟨c, run _ (by omega), gc, fun v => by rw [lc, eX.1, eY.1]; exact sem v,
      fun v => by rw [uc, eX.2, eY.2]; exact sem v⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp_all
  obtain ⟨c, hc, run, sem, I, rfl, look, up⟩ := inter_aligned (bare_inter_op (L := level t n) (n := k + 1) (by omega))
    (bare_inter_op (n := k) (by omega)) (fun _ _ _ r t => bare_inter_dyn _ r t) ha hb
  have st := stepOf (level t n).ef (level t n).none
  have dl : DE (level t n).E (lower (.map I)) :=
    Or.inr ⟨_, rfl, interL_descr st.ks st.fc (by omega) (de_map la) (de_map lb) look⟩
  have du : DE (level t n).E (upper (.map I)) := by
    rcases up with ⟨none, -⟩ | run'
    · rw [show upper (.map I) = lower (.map I) by simp [upper, lower, none, rmDyn_static none]]; exact dl
    · rw [dyn_inter_bare _ ha.up_tc hb.up_tc] at run'
      obtain ⟨c', dc', rc', -⟩ := (ef_next t n).inter ua ub
      have e := (rc' (k + 1) (by omega)).symm.trans run'
      simp only [Except.ok.injEq] at e
      rw [← e]; exact dc'
  exact ⟨_, (inter_run_grad _ g).trans run, ⟨hc, dl, du⟩, bounds _ sem⟩

theorem boolAtom_inj {p q : Bool} (h : boolAtom p = boolAtom q) : p = q := by
  cases p <;> cases q <;> simp_all [boolAtom]

/-- Equality of gradual types whose function types are arrows compares both bounds exactly. -/
theorem gd_eq {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (boolAtom (bp (∀ v : PN t n,
      (denD (lower a) v ↔ denD (lower b) v) ∧ (denD (upper a) v ↔ denD (upper b) v)))) := by
  obtain ⟨s₁, s₂, r₁, r₂, r₃⟩ := gd_equal ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 hm
  rw [gd_sub ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 hm, Except.ok.injEq] at r₁
  rw [gd_sub gb.1 ga.1 gb.2.1 gb.2.2 ga.2.1 ga.2.2 hm, Except.ok.injEq] at r₂
  rw [r₃, ← boolAtom_inj r₁, ← boolAtom_inj r₂, bp_and]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
  simp only [SubN]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ v
    exact ⟨⟨h₁ v, h₃ v⟩, ⟨h₂ v, h₄ v⟩⟩
  · intro h
    exact ⟨⟨fun v => (h v).1.1, fun v => (h v).2.1⟩, fun v => (h v).1.2, fun v => (h v).2.2⟩

theorem gd_eq_true {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (lo : ∀ v : PN t n, denD (lower a) v ↔ denD (lower b) v) (up : ∀ v : PN t n, denD (upper a) v ↔ denD (upper b) v) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  rw [gd_eq ga gb hm, bp_true.mpr fun v => ⟨lo v, up v⟩]; rfl

/-- A type is a subtype of another exactly when their union is the other. -/
theorem gd_sub_union {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) c b = .ok (boolAtom s) := by
  obtain ⟨c, run, gc, lc, uc⟩ := gd_union ga gb hm
  refine ⟨c, _, run, gd_sub ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 (by omega), ?_⟩
  rw [gd_eq gc gb (by omega)]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
  simp only [SubN, lc, uc]
  constructor
  · intro h; exact ⟨fun v hv => (h v).1.mp (Or.inl hv), fun v hv => (h v).2.mp (Or.inl hv)⟩
  · intro h v; exact ⟨⟨fun h' => h'.elim (h.1 v) id, Or.inr⟩, ⟨fun h' => h'.elim (h.2 v) id, Or.inr⟩⟩

/-- A type is a subtype of another exactly when their intersection is the first. -/
theorem gd_sub_inter {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) c a = .ok (boolAtom s) := by
  obtain ⟨c, run, gc, lc, uc⟩ := gd_inter ga gb hm
  refine ⟨c, _, run, gd_sub ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 (by omega), ?_⟩
  rw [gd_eq gc ga (by omega)]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
  simp only [SubN, lc, uc]
  constructor
  · intro h; exact ⟨fun v hv => ((h v).1.mpr hv).2, fun v hv => ((h v).2.mpr hv).2⟩
  · intro h v; exact ⟨⟨And.left, fun h' => ⟨h', h.1 v h'⟩⟩, ⟨And.left, fun h' => ⟨h', h.2 v h'⟩⟩⟩

end

end Elixir.STTDescrProofsTest.Nest
