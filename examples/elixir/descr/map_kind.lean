namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Maps are a structural kind, and the three kinds together. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Valuations of map literals that maps of values induce. -/
def ValMN (E : Term → Prop) (den : Term → V → Prop) (ρ : Term → Bool) : Prop := ∃ w : MW V, ρ = valM E den w

theorem dn_mapW {x : Term} {p : Point} {w : MW V} (e : p.2.2 = valM E den w) :
    dn "map" (some x) p = denMF E den x w := by
  rw [dn_map, e]; rfl

theorem mfield_nz {w : Term} (fw : MField E w) : w ≠ .integer 0 := by
  rcases fw with ⟨k, rfl⟩ | ww
  · simp
  · exact bdd_ne_zero ww

theorem denMF_bot (w : MW V) : denMF E den (.atom "bdd_bot") w = Bool.false := by
  simp [denMF, denO, isOpenTop]

theorem mapKind (ef : EF nd E V den tl K) : KindOk (K + 2) "map" (MField E) (ValMN E den) where
  resp := fun _ ⟨w, e⟩ => e ▸ valM_resp w
  wit := ⟨_, fun _ => none, rfl⟩
  top := fun t ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ <;> try simp at h
    exact ⟨Or.inl ⟨_, rfl⟩, lh_top_leaf _, fun p _ => by rw [dn_map, denO_top]⟩
  congr := fun fx fx' e p ⟨w, hw⟩ => by
    rw [dn_mapW hw, dn_mapW hw]
    exact denMF_resp fx fx' e w
  union := fun fx fy => by
    obtain ⟨r, run, fr, sem, le⟩ := map_field_union (den := den) fx fy
    exact ⟨r, fun m _ => run _, fr, fun p ⟨w, hw⟩ => by rw [dn_mapW hw, dn_mapW hw, dn_mapW hw, sem], le⟩
  inter := fun fx fy => by
    obtain ⟨r, run, fr, sem, le⟩ := map_field_inter (den := den) fx fy
    refine ⟨r, fun m _ => run _, fun _ => ⟨fr, le⟩, fun p ⟨w, hw⟩ => ?_⟩
    cases k : kept (.atom "map", r)
    · rw [keptO_false k, dn_none, dn_mapW hw, dn_mapW hw, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (mfield_nz fr), denMF_bot]
    · rw [keptO_true k, dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]
  diff := fun fx fy => by
    obtain ⟨r, run, fr, sem, le⟩ := map_field_diff (den := den) fx fy
    refine ⟨r, fun m _ => run _, fun k => ⟨fr, le (kept_ne_bot k)⟩, fun p ⟨w, hw⟩ => ?_⟩
    cases k : kept (.atom "map", r)
    · rw [keptO_false k, dn_none, dn_mapW hw, dn_mapW hw, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (mfield_nz fr), denMF_bot]
    · rw [keptO_true k, dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]
  opt_union := by
    intro x y S m fx fy hm
    obtain ⟨r, run, fr, sem⟩ := map_field_opt_union ef (m := m) (by omega) fx fy S
    exact ⟨r, run, fr, fun p ⟨w, hw⟩ => by rw [dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]⟩
  opt_inter := by
    intro x y S m fx fy hm
    obtain ⟨r, run, fr, sem⟩ := map_field_opt_inter ef (m := m) hm fx fy S
    refine ⟨r, run, fun _ => fr, fun p ⟨w, hw⟩ => ?_⟩
    cases k : kept (.atom "map", r)
    · rw [keptO_false k, dn_none, dn_mapW hw, dn_mapW hw, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (mfield_nz fr), denMF_bot]
    · rw [keptO_true k, dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]
  opt_diff := by
    intro x y S m fx fy hm
    obtain ⟨r, run, k, d⟩ := map_field_opt_diff ef (m := m) (by omega) fx fy S
    refine ⟨r, run, fun kw => (k kw).1, fun p ⟨w, hw⟩ => ?_⟩
    cases kw : kept (.atom "map", r)
    · rw [keptO_false kw, dn_none, dn_mapW hw, dn_mapW hw, d kw]
    · rw [keptO_true kw, dn_mapW hw, dn_mapW hw, dn_mapW hw, (k kw).2]
  empty := fun S fx => by
    obtain ⟨b, run, ex⟩ := map_field_empty ef fx S
    refine ⟨b, run, fun N hx hS => (ex N hx hS).trans ⟨fun h p ⟨w, hw⟩ => by rw [dn_mapW hw]; exact h w,
      fun h w => by have := h (0, .nil, valM E den w) ⟨w, rfl⟩; rwa [dn_mapW rfl] at this⟩⟩

/-- The structural kinds over element types. -/
theorem kinds (ef : EF nd E V den tl K) : Kinds (K + 2) (TField E) (LF E) (MField E) (ValT E den) (ValLN E den tl)
    (ValMN E den) := ⟨tupleKind ef, listKind ef, mapKind ef⟩

theorem KindOk.mono {K K' : Nat} {name : String} {F : Term → Prop} {Val : (Term → Bool) → Prop}
    (k : KindOk K name F Val) (le : K ≤ K') : KindOk K' name F Val where
  resp := k.resp
  wit := k.wit
  top := k.top
  congr := k.congr
  union := fun fx fy => let ⟨w, run, h⟩ := k.union fx fy; ⟨w, fun m hm => run m (by omega), h⟩
  inter := fun fx fy => let ⟨w, run, h⟩ := k.inter fx fy; ⟨w, fun m hm => run m (by omega), h⟩
  diff := fun fx fy => let ⟨w, run, h⟩ := k.diff fx fy; ⟨w, fun m hm => run m (by omega), h⟩
  opt_union := fun {_ _} S {_} fx fy hm => k.opt_union S fx fy (by omega)
  opt_inter := fun {_ _} S {_} fx fy hm => k.opt_inter S fx fy (by omega)
  opt_diff := fun {_ _} S {_} fx fy hm => k.opt_diff S fx fy (by omega)
  empty := fun S fx => let ⟨b, run, h⟩ := k.empty S fx; ⟨b, fun m hm => run m (by omega), h⟩

theorem Kinds.mono {K K' : Nat} {TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
    (ks : Kinds K TF LF MF TV LV MV) (le : K ≤ K') : Kinds K' TF LF MF TV LV MV :=
  ⟨ks.t.mono le, ks.l.mono le, ks.m.mono le⟩

end Elixir.STTDescrProofsTest.Nest
