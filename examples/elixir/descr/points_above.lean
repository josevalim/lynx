namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Values of the level above, as points. -/
def toPN (y : (level t (n + 1)).V) : PN t n := y

theorem den_succ {a : Term} (ha : DE (level t n).E a) (v : PN t n) : (level t (n + 1)).den a v ↔ denD a v :=
  denN_of (DEG.notT ha)

theorem e_succ {a : Term} (ha : DE (level t n).E a) : (level t (n + 1)).E a := Or.inl ha

theorem nilT_de : DE (level t n).E nilT :=
  single_de (by simp [names]) (Or.inl ⟨rfl, 4, rfl, by omega, by omega⟩)

theorem nilT_den (v : PN t n) : denD nilT v ↔ v.1.1 = "bitmap" ∧ v.1.2.1 = 2 := by
  rw [nilT, denD_single]
  simp only [dn_bitmap, bitOf, and_congr_right_iff]
  intro _
  have : (4 : Int).toNat = 2 ^ 2 := rfl
  rw [this, Nat.testBit_two_pow]
  simp [eq_comm]

/-- The empty list point. -/
def nilPt : PN t n := bPt 2 (by omega)

theorem nilPt_den : denD nilT (nilPt (t := t) (n := n)) := (nilT_den _).mpr ⟨rfl, rfl⟩

/-- List literals of element types of lists ending in the empty list. -/
theorem lf_nil {inner : Term} (hi : DE (level t n).E inner) (k : Int) :
    LF (level t (n + 1)).E (.tuple #[.integer k, inner, nilT]) :=
  Bdd.leaf_iff.mpr ⟨k, inner, nilT, rfl, e_succ hi, e_succ nilT_de⟩

/-- The point of a non-empty list of values of the next level. -/
noncomputable def lpt (v : LV (level t (n + 1)).V) (h : ListVal (level t (n + 1)).tl v) : PN t (n + 1) :=
  ⟨("list", (0, .nil, valL (level t (n + 1)).E (level t (n + 1)).den v)), by simp [names],
    ⟨valL_resp v, fun h => by simp at h, fun _ => ⟨v, h, rfl⟩, fun h => by simp at h, fun h => by simp at h,
      fun h => by simp at h⟩⟩

theorem list_val (q : PN t (n + 1)) (h : q.1.1 = "list") :
    ∃ v : LV (level t (n + 1)).V, ListVal (level t (n + 1)).tl v ∧
      q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v := by
  obtain ⟨⟨name, p⟩, mem, ok⟩ := q
  simp only at h
  subst h
  obtain ⟨v, hv, e⟩ := ok.2.2.1 rfl
  exact ⟨v, hv, e⟩

/-- Lists of the literal of lists of an element type ending in the empty list. -/
theorem dn_nil_list {inner : Term} (hi : DE (level t n).E inner) (k : Int) {p : Point} {v : LV (level t (n + 1)).V}
    (e : p.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v) :
    dn "list" (some (.tuple #[.integer k, inner, nilT])) p = Bool.true ↔
      (∀ y ∈ v.xs, denD inner (toPN y)) ∧ denD nilT (toPN v.last) := by
  rw [dn_listL (level t (n + 1)).ef (lf_nil hi k) e, dL, eval_leaf,
    valL_iff (level t (n + 1)).ef.semR ⟨k, inner, nilT, rfl, e_succ hi, e_succ nilT_de⟩, llitSem_iff]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun y m => (den_succ hi (toPN y)).mp (h₁ y m), (den_succ nilT_de (toPN v.last)).mp h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun y m => (den_succ hi (toPN y)).mpr (h₁ y m), (den_succ nilT_de (toPN v.last)).mpr h₂⟩⟩

/-- The list types of element types: lists of them ending in the empty list, and the empty list when `nil` holds. -/
def lTy (nil : Bool) (k : Int) (inner : Term) : Term :=
  if nil then .map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, inner, nilT])]
  else .map [(.atom "list", .tuple #[.integer k, inner, nilT])]

theorem lTy_de (nil : Bool) (k : Int) {inner : Term} (hi : DE (level t n).E inner) :
    DE (level t (n + 1)).E (lTy nil k inner) := by
  have fl : FieldC (FunA (level t (n + 1)).E) (TField (level t (n + 1)).E) (LF (level t (n + 1)).E)
      (MField (level t (n + 1)).E) "list" (.tuple #[.integer k, inner, nilT]) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, lf_nil hi k⟩)))
  cases nil
  · exact single_de (by simp [names]) fl
  · refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
    · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
      by_cases e : compareExact (fuel q (.atom "bitmap")) q (.atom "bitmap") = .eq
      · exact ⟨"bitmap", by simp [names], (compareExact_eq_atom _ _).mp e⟩
      · by_cases e' : compareExact (fuel q (.atom "list")) q (.atom "list") = .eq
        · exact ⟨"list", by simp [names], (compareExact_eq_atom _ _).mp e'⟩
        · simp [e, e'] at h
    · rw [lookup_cons_atom, lookup_cons_atom] at h
      by_cases e : "bitmap" = name
      · subst e; simp at h; subst h; exact Or.inl ⟨rfl, 4, rfl, by omega, by omega⟩
      · by_cases e' : "list" = name
        · subst e'; simp at h; subst h; exact fl
        · simp [e, e', mapLookup] at h

/-- The points of list types: the empty list when it holds it, and the lists of its element type ending in the empty
list. -/
theorem lTy_den (nil : Bool) (k : Int) {inner : Term} (hi : DE (level t n).E inner) (q : PN t (n + 1)) :
    denD (lTy nil k inner) q ↔ (nil = Bool.true ∧ q.1.1 = "bitmap" ∧ q.1.2.1 = 2) ∨
      (q.1.1 = "list" ∧ ∀ v : LV (level t (n + 1)).V, q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v →
        (∀ y ∈ v.xs, denD inner (toPN y)) ∧ denD nilT (toPN v.last)) := by
  by_cases hl : q.1.1 = "list"
  · obtain ⟨v, -, hv⟩ := list_val q hl
    have hdn := fun (v' : LV (level t (n + 1)).V) (e : q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v') =>
      dn_nil_list (p := q.1.2) hi k e
    have key : dn "list" (some (.tuple #[.integer k, inner, nilT])) q.1.2 = Bool.true ↔
        ∀ v : LV (level t (n + 1)).V, q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v →
          (∀ y ∈ v.xs, denD inner (toPN y)) ∧ denD nilT (toPN v.last) :=
      ⟨fun h v' e => (hdn v' e).mp h, fun h => (hdn v hv).mpr (h v hv)⟩
    cases nil <;> simp [lTy, denD_map, hl, mapLookup] <;> exact key
  · cases nil
    · simp [lTy, denD_map, hl, mapLookup, dn_none]
    · by_cases hb : q.1.1 = "bitmap"
      · have look : mapLookup [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, inner, nilT])]
            (.atom "bitmap") = some (.integer 4) := by simp [mapLookup]
        simp only [lTy, ite_true, denD_map, hb, look, true_and]
        rw [dn_bitmap, bitOf]
        have : (4 : Int).toNat = 2 ^ 2 := rfl
        rw [this, Nat.testBit_two_pow]
        simp [eq_comm]
      · have look : mapLookup [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, inner, nilT])]
            (.atom q.1.1) = none := by
          rw [lookup_cons_atom, lookup_cons_atom]; simp [Ne.symm hb, Ne.symm hl, mapLookup]
        simp [lTy, denD_map, look, dn_none, hb, hl]

end

end Elixir.STTDescrProofsTest.Nest
