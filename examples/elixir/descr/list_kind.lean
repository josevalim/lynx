namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Lists are a structural kind. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Valuations of list literals that lists of values induce. -/
def ValLN (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (ρ : Term → Bool) : Prop :=
  ∃ v, ListVal tl v ∧ ρ = valL E den v

theorem dn_listL (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) {p : Point} {v : LV V} (e : p.2.2 = valL E den v) :
    dn "list" (some x) p = dL E den x v := by
  rw [dn_list, e, nl_denL ef wx]

theorem lf_nz {w : Term} (fw : LF E w) : w ≠ .integer 0 := bdd_ne_zero fw

theorem listKind (ef : EF nd E V den tl K) : KindOk (K + 2) "list" (LF E) (ValLN E den tl) where
  resp := fun _ ⟨v, _, e⟩ => e ▸ valL_resp v
  wit := let ⟨v, hv⟩ := nl_listVal_exists ef; ⟨_, v, hv, rfl⟩
  top := fun t ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> try simp at h
    exact ⟨Bdd.leaf_iff.mpr ⟨_, _, _, rfl, ef.term, ef.term⟩, lh_leaf_list,
      fun p _ => by simp [dn_list, denL, isListTop]⟩
  congr := fun fx fx' e p ⟨v, _, hv⟩ => by
    rw [dn_listL ef fx hv, dn_listL ef fx' hv]
    exact nl_dL_resp fx e v
  union := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := nl_bare_union ef fx fy
    exact ⟨w, fun m _ => run _, fw, fun p ⟨v, _, hv⟩ => by
      rw [dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem], le⟩
  inter := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := nl_bare_inter ef fx fy
    refine ⟨w, fun m _ => run _, fun _ => ⟨fw, le⟩, fun p ⟨v, _, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem]
  diff := fun {x y} fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := nl_bare_diff ef fx fy
    refine ⟨w, fun m _ => run _, fun k => ⟨fw, le (kept_ne_bot k)⟩, fun p ⟨v, _, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem]
  opt_union := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem, -⟩ := nl_opt_union ef fx fy
    exact ⟨w, run _ _, fw, fun p ⟨v, _, hv⟩ => by
      rw [dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem]⟩
  opt_inter := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := nl_opt_inter ef (m := m) (by omega) fx fy S
    refine ⟨w, run, fun _ => fw, fun p ⟨v, lv, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem v lv,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem v lv]
  opt_diff := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := nl_opt_diff ef (m := m) (by omega) fx fy S
    refine ⟨w, run, fun _ => fw, fun p ⟨v, lv, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem v lv,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem v lv]
  empty := fun S fx => by
    obtain ⟨b, run, ex⟩ := nl_empty_key ef fx S
    refine ⟨b, run, fun N hx hS => (ex N hx hS).trans ⟨fun h p ⟨v, lv, hv⟩ => by rw [dn_listL ef fx hv]; exact h v lv,
      fun h v lv => by have := h (0, .nil, valL E den v) ⟨v, lv, rfl⟩; rwa [dn_listL ef fx rfl] at this⟩⟩

end Elixir.STTDescrProofsTest.Nest
