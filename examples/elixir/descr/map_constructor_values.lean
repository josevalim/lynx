namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- The value of a pair of a map constructor. -/
def fv (x : Term) : Term :=
  match x with
  | .tuple es => es[1]?.getD .nil
  | _ => .nil

/-- The fields of sorted field pairs. -/
def toL (R : List Term) : List (Term × Term) := R.map fun x => (fk x, fv x)

theorem list_toL : ∀ (R : List Term), (∀ x ∈ R, ∃ (a : String) (f : Term), x = .tuple #[.atom a, f]) →
    Term.list R = fieldsTerm (toL R)
  | [], _ => rfl
  | x :: R, h => by
    obtain ⟨a, f, rfl⟩ := h x (by simp)
    have := list_toL R (fun y hy => h y (by simp [hy]))
    simp only [toL, List.map_cons, fieldsTerm_cons] at this ⊢
    rw [Term.list_cons, this]; rfl

theorem lookup_toL (s : String) : ∀ (R : List Term), (∀ x ∈ R, ∃ (a : String) (f : Term), x = .tuple #[.atom a, f]) →
    mapLookup (toL R) (.atom s) = (USort.lk fk (.atom s) R).map fv
  | [], _ => rfl
  | x :: R, h => by
    obtain ⟨a, f, rfl⟩ := h x (by simp)
    have ih := lookup_toL s R (fun y hy => h y (by simp [hy]))
    simp only [toL, List.map_cons] at ih ⊢
    rw [show fk (.tuple #[.atom a, f]) = .atom a from rfl, lookup_cons_atom, USort.lk_cons,
      show fk (.tuple #[.atom a, f]) = .atom a from rfl]
    by_cases e : a = s
    · subst e; simp
    · have ne : ¬Term.compare (Term.fuel (.atom a) (.atom s)) (.atom a) (.atom s) = .eq := by simpa using e
      simp only [e, ne, ite_false]
      exact ih

theorem static_closed (m : Nat) (x rest F : Term) :
    Elixir.Module.Types.Descr.«map_descr_static/3» (D m) (.atom "closed") F (.cons x rest) =
      (do let l ← Elixir.Module.Types.Descr.«map_new/2» (.cons x rest) F; pure (.map [(.atom "map", l)])) := by
  unfold Elixir.Module.Types.Descr.«map_descr_static/3»
  split <;> simp_all

theorem lookup_keys (f : Term → Term) (s : String) : ∀ (K : List Term), Term.atom s ∈ K →
    mapLookup (K.map fun k => (k, f k)) (.atom s) = some (f (.atom s))
  | [], h => by simp at h
  | k :: K, h => by
    by_cases e : compareExact (fuel (.atom s) k) (.atom s) k = .eq
    · rw [atom_compareExact_eq] at e; subst e; simp [mapLookup]
    · have h' : Term.atom s ∈ K := by
        rcases List.mem_cons.mp h with h | h
        · subst h; simp at e
        · exact h
      simp only [List.map_cons]
      rw [lookup_cons_ne e]
      exact lookup_keys f s K h'

/-- The domain kinds as atoms, in order. -/
theorem sak_kinds : SAK (domainKinds.map Term.atom) := by
  simp (config := { decide := true }) [SAK]

section
variable {t : Term} {n : Nat}

/-- The values a constructed map allows at the keys of a kind: those of the domain pairs naming it, or any value
for open maps and none for closed ones. -/
def CKind (tag : String) (fs : List Term) (s : String) (o : Option (level t n).V) : Prop :=
  o = none ∨ ∃ x, o = some x ∧
    ((DomAny fs s ∧ DomMem (t := t) (n := n) fs s x) ∨ (¬DomAny fs s ∧ tag = "open"))

/-- The values a constructed map allows at an atom key: those of the last field of the key, or of the atom
domain. -/
def CAtom (tag : String) (fs : List Term) (s : String) (o : Option (level t n).V) : Prop :=
  match USort.lk fk (.atom s) (fieldsRev fs) with
  | some x => FieldSem (level t n).den (fv x) o
  | none => CKind tag fs "atom" o

/-- The maps of a map constructor. -/
def CSem (tag : String) (fs : List Term) (w : MW (level t n).V) : Prop :=
  (∀ s, CAtom tag fs s (w (.atom s))) ∧ ∀ k i, CKind tag fs (domKind k) (w (.dom k i))

theorem domL_kinds {dl : List (Term × Term)} (hd : DomL t n dl) (hk : ∀ e ∈ dl, ∃ s ∈ domainKinds, e.1 = .atom s) :
    DomsV (level t n).E dl :=
  ⟨fun e he => ⟨by obtain ⟨s, ms, h⟩ := hk e he; exact ⟨s, h, ms⟩, (hd.2 e he).2⟩, hd.1⟩

/-- `map_descr/2` of static pairs is a map literal of the sorted last fields, under a tag of the domains. -/
theorem descr_leaf {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ (k : Int) (TAG : Term) (l : List (Term × Term)),
      Elixir.Module.Types.Descr.«map_descr/2» (D (m + 1)) (.atom tag) (Term.list fs) =
        .ok (.map [(.atom "map", .tuple #[.integer k, TAG, fieldsTerm l])]) ∧
      TagV (level t n).E TAG ∧ FieldsV (level t n).E l ∧ KeyOk (.tuple #[.integer k, TAG, fieldsTerm l]) ∧
      (∀ s, mapLookup l (.atom s) = (USort.lk fk (.atom s) (fieldsRev fs)).map fv) ∧
      ∀ kind ∈ domainKinds, ∀ o, TagSem (level t n).den TAG kind o ↔ CKind (t := t) (n := n) tag fs kind o := by
  obtain ⟨R, dl, b, rp, sr, er, hd, hs⟩ := descr_pairs_run hm fs h
  have memR : ∀ x ∈ R, ∃ (a : String) (v : Term) (o : Bool), x = .tuple #[.atom a, .tuple #[v, boolAtom o]] ∧
      (level t n).E v := fun x hx => fieldsRev_mem h (USort.mem_of_eqv sr.ne er hx)
  have shape : ∀ x ∈ R, ∃ (a : String) (f : Term), x = .tuple #[.atom a, f] := fun x hx => by
    obtain ⟨a, v, o, rfl, -⟩ := memR x hx; exact ⟨a, _, rfl⟩
  have lR := list_toL R shape
  have sl : FieldsV (level t n).E (toL R) := by
    refine ⟨fun e he => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      obtain ⟨a, v, o, rfl, hv⟩ := memR x hx
      exact ⟨⟨a, rfl⟩, ⟨v, o, rfl, hv⟩⟩
    · simp only [toL, List.pairwise_map]; exact sr
  have look : ∀ s, mapLookup (toL R) (.atom s) = (USort.lk fk (.atom s) (fieldsRev fs)).map fv := fun s => by
    rw [lookup_toL s R shape, er]
  have hnone : ∀ x, ¬(level t n).den (.map []) x := (level t n).ef.den_none
  unfold Elixir.Module.Types.Descr.«map_descr/2»
  simp only [rp, Lynx.Except.ok_bind]
  have hk : ∀ e ∈ dl, ∃ s ∈ domainKinds, e.1 = .atom s := hs.1
  cases dl with
  | nil =>
    have g : TagV (level t n).E (.atom tag) := by rcases ht with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)
    obtain ⟨k, rl, key⟩ := leaf_new_keyM g R
    rw [lR] at key
    have noAny : ∀ s, ¬DomAny fs s := fun s => ((hs.2 s).1).mp (by simp [mapLookup])
    refine ⟨k, .atom tag, toL R, ?_, g, sl, key, look, fun kind _ o => ?_⟩
    · rw [← lR]
      simp [Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2», rl,
        show fieldsTerm [] = .nil from rfl]
    · rw [tagSem_atom]
      cases o with
      | none => simp [CKind]
      | some x => simp [CKind, noAny]
  | cons d dl =>
  rcases ht with rfl | rfl
  · -- open maps fill the other kinds with `term()`
    have hK : ∀ e ∈ d :: dl, e.1 ∈ domainKinds.map Term.atom := fun e he => by
      obtain ⟨s, ms, h⟩ := hk e he; rw [h]; exact List.mem_map.mpr ⟨s, ms, rfl⟩
    have fp := fpa_run (m + 1) (.atom "term") (domainKinds.map Term.atom) (d :: dl) sak_kinds
      (fun k hk => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp hk; exact ⟨s, rfl⟩) hd.1 hK
    generalize hL : (domainKinds.map Term.atom).map (fun k => (k, (mapLookup (d :: dl) k).getD (.atom "term"))) = L
      at fp
    have lookL : ∀ kind ∈ domainKinds, mapLookup L (.atom kind) =
        some ((mapLookup (d :: dl) (.atom kind)).getD (.atom "term")) := fun kind mk => by
      rw [← hL]; exact lookup_keys _ kind _ (List.mem_map.mpr ⟨kind, mk, rfl⟩)
    have g : TagV (level t n).E (fieldsTerm L) := by
      refine Or.inr (Or.inr ⟨L, rfl, fun e he => ?_, ?_⟩)
      · rw [← hL] at he
        obtain ⟨k, hk', rfl⟩ := List.mem_map.mp he
        obtain ⟨s, ms, rfl⟩ := List.mem_map.mp hk'
        refine ⟨⟨s, rfl, ms⟩, ?_⟩
        cases hl : mapLookup (d :: dl) (.atom s) with
        | none => exact (level t n).ef.term
        | some U =>
          obtain ⟨e', he', rfl⟩ := lookup_mem hl
          exact (hd.2 e' he').2
      · rw [← hL, List.pairwise_map]; exact sak_kinds
    obtain ⟨k, rl, key⟩ := leaf_new_keyM g R
    rw [lR] at key
    refine ⟨k, fieldsTerm L, toL R, ?_, g, sl, key, look, fun kind mk o => ?_⟩
    · rw [← lR]
      have kl : Term.list [.atom "atom", .atom "binary", .atom "bitstring_no_binary", .atom "float", .atom "fun",
          .atom "integer", .atom "list", .atom "map", .atom "pid", .atom "port", .atom "reference", .atom "tuple"] =
          Term.list (domainKinds.map Term.atom) := rfl
      simp only [Elixir.Module.Types.Descr.«map_descr_static/3», fieldsTerm_cons, kl]
      simp only [← fieldsTerm_cons, fp, Lynx.Except.ok_bind, Elixir.Module.Types.Descr.«map_new/2», rl]
      rfl
    · rw [tagSem_dom_iff hnone, lookL kind mk]
      have sk := hs.2 kind
      cases hl : mapLookup (d :: dl) (.atom kind) with
      | none =>
        have na : ¬DomAny fs kind := sk.1.mp (by simp [hl])
        cases o <;> simp [CKind, na, (level t n).ef.den_term]
      | some U =>
        have da : DomAny fs kind := Classical.byContradiction fun h => by have := sk.1.mpr h; simp [hl] at this
        cases o with
        | none => simp [CKind]
        | some x => simp [CKind, da, sk.2 U hl x]
  · have g : TagV (level t n).E (fieldsTerm (d :: dl)) := Or.inr (Or.inr ⟨_, rfl, domL_kinds hd hk⟩)
    obtain ⟨k, rl, key⟩ := leaf_new_keyM g R
    rw [lR] at key
    refine ⟨k, fieldsTerm (d :: dl), toL R, ?_, g, sl, key, look, fun kind mk o => ?_⟩
    · rw [← lR, fieldsTerm_cons, static_closed, ← fieldsTerm_cons]
      simp [Elixir.Module.Types.Descr.«map_new/2», rl]
    · rw [tagSem_dom_iff hnone]
      have sk := hs.2 kind
      cases hl : mapLookup (d :: dl) (.atom kind) with
      | none =>
        have na : ¬DomAny fs kind := sk.1.mp (by simp [hl])
        cases o <;> simp [CKind, na]
      | some U =>
        have da : DomAny fs kind := Classical.byContradiction fun h => by have := sk.1.mpr h; simp [hl] at this
        cases o with
        | none => simp [CKind]
        | some x => simp [CKind, da, sk.2 U hl x]

theorem mapsOf_congr {H : Term} {Q Q' : MW (level t n).V → Prop} (h : MapsOf t n H Q) (e : ∀ w, Q w ↔ Q' w) :
    MapsOf t n H Q' := ⟨h.1, h.2.1, fun p w hw => (h.2.2 p w hw).trans (e w)⟩

/-- The maps of `map_descr/2` of static pairs. -/
theorem descr_maps {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ C, Elixir.Module.Types.Descr.«map_descr/2» (D (m + 1)) (.atom tag) (Term.list fs) = .ok C ∧
      MapsOf t n C (CSem (t := t) (n := n) tag fs) := by
  obtain ⟨k, TAG, l, run, g, sl, key, look, tags⟩ := descr_leaf hm tag ht fs h
  refine ⟨_, run, mapsOf_congr (mapsOf_one _ (mleaf_field g sl key)) fun w => ?_⟩
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [denMF_leaf (level t n).ef sl g]
  constructor
  · intro ms
    refine ⟨fun s => ?_, fun k i => (tags _ (domKind_mem k) _).mp (ms.doms k i)⟩
    have := ms.atoms s
    unfold FSem at this
    unfold CAtom
    rw [look] at this
    cases hx : USort.lk fk (.atom s) (fieldsRev fs) with
    | none => rw [hx] at this; exact (tags "atom" (by simp [domainKinds]) _).mp this
    | some x => rw [hx] at this; exact this
  · rintro ⟨ha, hd⟩
    refine ⟨fun s => ?_, fun k i => (tags _ (domKind_mem k) _).mpr (hd k i)⟩
    have := ha s
    unfold FSem
    unfold CAtom at this
    rw [look]
    cases hx : USort.lk fk (.atom s) (fieldsRev fs) with
    | none => rw [hx] at this; exact (tags "atom" (by simp [domainKinds]) _).mpr this
    | some x => rw [hx] at this; exact this

end

end Elixir.STTDescrProofsTest.Nest
