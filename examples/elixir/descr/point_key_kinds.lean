namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- The kind of keys of a point: the kind of its bit for bitmaps, otherwise its field. -/
def ptKind (v : PN t n) : String := if v.1.1 = "bitmap" then bitKind v.1.2.1 else v.1.1

/-- A point of a bitmap, at a bit. -/
def bPt (i : Nat) (h : i < 8) : PN t n := ⟨("bitmap", (i, .nil, fun _ => Bool.false)), by simp [names],
  ⟨resp_const _, fun _ => h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h⟩⟩

/-- A point of atoms, at a term. -/
def aPt (q : Term) : PN t n := ⟨("atom", (0, q, fun _ => Bool.false)), by simp [names],
  ⟨resp_const _, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h⟩⟩

theorem denD_field {Y : List (Term × Term)} (v : PN t n) :
    denD (.map Y) v ↔ ∃ x, mapLookup Y (.atom v.1.1) = some x ∧ dn v.1.1 (some x) v.1.2 = Bool.true := by
  rw [denD_map]
  cases mapLookup Y (.atom v.1.1) <;> simp [dn_none]

/-- A type restricted to one of its fields. -/
theorem field_de {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {name : String} {x : Term}
    (hx : mapLookup Y (.atom name) = some x) :
    DE (level t n).E (.map [(.atom name, x)]) ∧
      ∀ v : PN t n, denD (.map [(.atom name, x)]) v ↔ v.1.1 = name ∧ denD (.map Y) v := by
  have sY := de_map hY
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name' w h => ?_⟩, fun v => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
    by_cases e : compareExact (fuel q (.atom name)) q (.atom name) = .eq
    · rw [(compareExact_eq_atom _ _).mp e]
      exact sY.keys _ (by rw [hx]; rfl)
    · simp [e] at h
  · rw [lookup_cons_atom] at h
    by_cases e : name = name'
    · subst e
      simp at h
      subst h
      exact sY.fields _ _ hx
    · simp [e, mapLookup] at h
  · rw [denD_field, denD_field, lookup_cons_atom]
    by_cases e : name = v.1.1
    · rw [← e, hx]; simp
    · simp [e, mapLookup]
      exact fun h => absurd h.symm e

/-- Bitmaps of key types whose kinds include lists through the empty list. -/
def ListSkip (Y : List (Term × Term)) : Prop :=
  ∃ b : Nat, mapLookup Y (.atom "bitmap") = some (.integer b) ∧ b.testBit 2 = Bool.true

/-- The kinds of keys that a field of a key type contributes to its domain keys. -/
def Contrib (Y : List (Term × Term)) (name : String) (x : Term) (s : String) : Prop :=
  (name = "bitmap" ∧ ∃ b : Nat, x = .integer b ∧ ∃ i < 8, b.testBit i = Bool.true ∧ bitKind i = s) ∨
  (name = "atom" ∧ s = "atom" ∧ ∃ S, x = .tuple #[.atom "negation", .map S]) ∨
  (name ≠ "bitmap" ∧ name ≠ "atom" ∧ s = name ∧ ¬(name = "list" ∧ ListSkip Y) ∧
    ∃ v : PN t n, v.1.1 = name ∧ denD (.map Y) v)

theorem dom_step {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {name : String} {x : Term}
    (hx : mapLookup Y (.atom name) = some x) {m : Nat} (hm : (level t n).K + 23 ≤ m) (acc : List Term) :
    ∃ pre, Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4» (D m) (.map Y) (.atom name) x (Term.list acc) =
        .ok (Term.list (pre ++ acc)) ∧ (∀ d ∈ pre, ∃ s ∈ domainKinds, d = .atom s) ∧
      ∀ s, .atom s ∈ pre ↔ Contrib (t := t) (n := n) Y name x s := by
  have sY := de_map hY
  obtain ⟨name', mn, e⟩ := sY.keys (.atom name) (by rw [hx]; rfl)
  obtain rfl : name = name' := Term.atom.inj e
  have fx := sY.fields name x hx
  obtain ⟨dF, sF⟩ := field_de hY hx
  have emp := next_empty dF hm
  simp only [names, List.mem_cons, List.not_mem_nil, or_false] at mn
  have eb : bp (∀ v : PN t n, ¬denD (.map [(.atom name, x)]) v) =
      !bp (∃ v : PN t n, v.1.1 = name ∧ denD (.map Y) v) := by
    by_cases h : ∃ v : PN t n, v.1.1 = name ∧ denD (.map Y) v
    · obtain ⟨v, hv⟩ := h
      rw [bp_false.mpr fun h' => h' v ((sF v).mpr hv), bp_true.mpr ⟨v, hv⟩]; rfl
    · rw [bp_true.mpr fun v hv => h ⟨v, (sF v).mp hv⟩, bp_false.mpr h]; rfl
  rw [eb] at emp
  rcases mn with rfl | rfl | rfl | rfl | rfl | rfl
  · -- bitmap
    obtain ⟨b, rfl, -, -⟩ := fieldC_bitmap fx
    obtain ⟨pre, run, mem⟩ := bitmap_keys b acc
    refine ⟨pre, ?_, fun d md => ?_, fun s => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, run]
    · obtain ⟨i, hi, -, rfl⟩ := (mem d).mp md
      refine ⟨_, ?_, rfl⟩
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind, domainKinds]
    · rw [mem]
      simp only [Contrib, Term.atom.injEq, true_and]
      constructor
      · rintro ⟨i, hi, hb, rfl⟩
        exact Or.inl ⟨b, rfl, i, hi, hb, rfl⟩
      · rintro (⟨b', e, i, hi, hb, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · obtain rfl : b = b' := by have := Term.integer.inj e; omega
          exact ⟨i, hi, hb, rfl⟩
        · simp at h
        · exact absurd rfl h
  · -- atom
    obtain ⟨⟨pos, S, rfl, -⟩, q, hq⟩ := fieldC_atom fx
    cases pos
    · have ne : bp (∃ v : PN t n, v.1.1 = "atom" ∧ denD (.map Y) v) = Bool.true :=
        bp_true.mpr ⟨aPt q, rfl, (denD_field _).mpr ⟨_, hx, by simpa [aPt, dn_atom] using hq⟩⟩
      rw [ne] at emp
      simp only [Bool.false_eq_true, ↓reduceIte] at emp
      refine ⟨[.atom "atom"], ?_, fun d md => ⟨"atom", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib]
    · refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso]
      · simp [Contrib]
  · -- fun
    by_cases ne : ∃ v : PN t n, v.1.1 = "fun" ∧ denD (.map Y) v
    · rw [bp_true.mpr ne] at emp
      refine ⟨[.atom "fun"], ?_, fun d md => ⟨"fun", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib, ne]
    · rw [bp_false.mpr ne] at emp
      refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom]
      · simp [Contrib, ne]
  · -- list
    cases hb : mapLookup Y (.atom "bitmap") with
    | none =>
      have nsk : ¬ListSkip Y := fun ⟨b, h, _⟩ => by rw [hb] at h; cases h
      by_cases ne : ∃ v : PN t n, v.1.1 = "list" ∧ denD (.map Y) v
      · rw [bp_true.mpr ne] at emp
        refine ⟨[.atom "list"], ?_, fun d md => ⟨"list", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
            boolAtom, Term.list, getMapKeys_single, hb]
        · simp [Contrib, ne, nsk]
      · rw [bp_false.mpr ne] at emp
        refine ⟨[], ?_, by simp, fun s => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
            boolAtom, getMapKeys_single, hb]
        · simp [Contrib, ne]
    | some x' =>
      obtain ⟨b, rfl, -, -⟩ := fieldC_bitmap (sY.fields _ _ hb)
      have a2 : Erlang.erlang.«band/2» (.integer (b : Int)) (.integer 4) = .ok (.integer (Int.ofNat (b &&& 2 ^ 2))) :=
        band_nat b 4
      have n2 := ne_bit b 2
      have i2 : (if b &&& 4 = 0 then Term.atom "false" else Term.atom "true") = boolAtom (b.testBit 2) := by
        have := testBit_and_pow b 2
        cases h : b.testBit 2 <;> simp_all [boolAtom]
      cases tb : b.testBit 2
      · have nsk : ¬ListSkip Y := fun ⟨b', h, t'⟩ => by
          rw [hb] at h
          obtain rfl : b = b' := by have := Term.integer.inj (Option.some.inj h); omega
          rw [tb] at t'; cases t'
        by_cases ne : ∃ v : PN t n, v.1.1 = "list" ∧ denD (.map Y) v
        · rw [bp_true.mpr ne] at emp
          refine ⟨[.atom "list"], ?_, fun d md => ⟨"list", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
          · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
              boolAtom, Term.list, getMapKeys_single, hb, a2, i2, tb]
          · simp [Contrib, ne, nsk]
        · rw [bp_false.mpr ne] at emp
          refine ⟨[], ?_, by simp, fun s => ?_⟩
          · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
              boolAtom, getMapKeys_single, hb, a2, i2, tb]
          · simp [Contrib, ne]
      · refine ⟨[], ?_, by simp, fun s => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso,
            getMapKeys_single, hb, a2, i2, tb, boolAtom]
        · have sk : ListSkip Y := ⟨b, hb, tb⟩
          simp [Contrib, sk]
  · -- tuple
    by_cases ne : ∃ v : PN t n, v.1.1 = "tuple" ∧ denD (.map Y) v
    · rw [bp_true.mpr ne] at emp
      refine ⟨[.atom "tuple"], ?_, fun d md => ⟨"tuple", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib, ne]
    · rw [bp_false.mpr ne] at emp
      refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom]
      · simp [Contrib, ne]
  · -- map
    by_cases ne : ∃ v : PN t n, v.1.1 = "map" ∧ denD (.map Y) v
    · rw [bp_true.mpr ne] at emp
      refine ⟨[.atom "map"], ?_, fun d md => ⟨"map", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib, ne]
    · rw [bp_false.mpr ne] at emp
      refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom]
      · simp [Contrib, ne]

/-- `maps:fold/3` of the domain keys step over fields of a key type. -/
theorem dom_fold {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∀ (es : List (Term × Term)), (∀ e ∈ es, mapLookup Y e.1 = some e.2) → ∀ acc : List Term,
      ∃ out, es.foldlM (fun acc e => Lynx.Dispatcher.pure (D (m + 1))
          (.function "Elixir.Module.Types.Descr" "-to_domain_keys/1-fun-0-" 3 #[.map Y]) #[e.1, e.2, acc])
          (Term.list acc) = .ok (Term.list (out ++ acc)) ∧ (∀ d ∈ out, ∃ s ∈ domainKinds, d = .atom s) ∧
        ∀ s, .atom s ∈ out ↔ ∃ e ∈ es, ∃ name, e.1 = .atom name ∧ Contrib (t := t) (n := n) Y name e.2 s
  | [], _, acc => ⟨[], rfl, by simp, by simp⟩
  | (k, x) :: es, hes, acc => by
    have hk := hes _ List.mem_cons_self
    obtain ⟨name, -, rfl⟩ := (de_map hY).keys k (by rw [hk]; rfl)
    obtain ⟨pre, run, hpre, spre⟩ := dom_step hY hk hm acc
    obtain ⟨out, run', hout, sout⟩ := dom_fold hY hm es (fun e me => hes e (List.mem_cons_of_mem _ me)) (pre ++ acc)
    refine ⟨out ++ pre, ?_, fun d md => ?_, fun s => ?_⟩
    · simp only [List.foldlM_cons]
      rw [Erlang.program.«Elixir.Module.Types.Descr:-to_domain_keys/1-fun-0-/3».pure, run]
      simpa using run'
    · rcases List.mem_append.mp md with h | h
      · exact hout d h
      · exact hpre d h
    · rw [List.mem_append, sout, spre]
      constructor
      · rintro (⟨e, me, h⟩ | h)
        · exact ⟨e, List.mem_cons_of_mem _ me, h⟩
        · exact ⟨_, List.mem_cons_self, name, rfl, h⟩
      · rintro ⟨e, me, name', e₁, h⟩
        rcases List.mem_cons.mp me with rfl | me
        · obtain rfl : name = name' := Term.atom.inj e₁
          exact Or.inr h
        · exact Or.inl ⟨e, me, name', e₁, h⟩

theorem entry_of_lookup_entries {es : List (Term × Term)} {q x : Term} (h : mapLookup es q = some x) :
    ∃ e ∈ mapEntries es, compareExact (fuel q e.1) q e.1 = .eq ∧ e.2 = x := by
  rw [← mapLookup_mapEntries, mapLookup] at h
  cases e : (mapEntries es).find? (fun entry => decide (compareExact (fuel q entry.1) q entry.1 = .eq)) with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    exact ⟨r, List.mem_of_find?_eq_some e, this, h⟩

/-- `to_domain_keys/1` on a static key type: the kinds its fields contribute. -/
theorem dom_keys {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ ds, Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) (.map Y) = .ok (Term.list ds) ∧
      (∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) ∧
      ∀ s, .atom s ∈ ds ↔ ∃ name x, mapLookup Y (.atom name) = some x ∧ Contrib (t := t) (n := n) Y name x s := by
  obtain ⟨out, run, hout, sout⟩ := dom_fold hY hm (mapEntries Y)
    (fun e me => mapLookup_of_mem_mapEntries me) []
  refine ⟨out, ?_, hout, fun s => ?_⟩
  · rw [Elixir.Module.Types.Descr.«to_domain_keys/1».eq_def]
    simp only [getMapKeys_single, (de_map hY).static, Option.toList_none]
    simpa [Erlang.maps.«fold/3», Term.list] using run
  · rw [sout]
    constructor
    · rintro ⟨e, me, name, e₁, h⟩
      exact ⟨name, e.2, by rw [← e₁]; exact mapLookup_of_mem_mapEntries me, h⟩
    · rintro ⟨name, x, hx, h⟩
      obtain ⟨e, me, ec, rfl⟩ := entry_of_lookup_entries hx
      exact ⟨e, me, name, ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm ec)), h⟩

/-- Kinds of keys of static key types: the atom kind for negated atoms, and the other kinds of their points. -/
theorem dom_kinds {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ ds, Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) (.map Y) = .ok (Term.list ds) ∧
      (∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) ∧
      (.atom "atom" ∈ ds ↔ ∃ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map S])) ∧
      ∀ s, s ≠ "atom" → (.atom s ∈ ds ↔ ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = s) := by
  obtain ⟨ds, run, hds, sds⟩ := dom_keys hY hm
  refine ⟨ds, run, hds, ?_, fun s ns => ?_⟩
  · rw [sds]
    constructor
    · rintro ⟨name, x, hx, (⟨rfl, b, -, i, hi, -, e⟩ | ⟨rfl, -, S, rfl⟩ | ⟨-, na, e, -⟩)⟩
      · match i, hi with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind] at e
      · exact ⟨S, hx⟩
      · exact absurd e.symm na
    · rintro ⟨S, hS⟩
      exact ⟨"atom", _, hS, Or.inr (Or.inl ⟨rfl, rfl, S, rfl⟩)⟩
  · rw [sds]
    constructor
    · rintro ⟨name, x, hx, (⟨rfl, b, rfl, i, hi, hb, rfl⟩ | ⟨-, e, -⟩ | ⟨nb, -, rfl, -, v, hv, dv⟩)⟩
      · refine ⟨bPt i hi, (denD_field _).mpr ⟨_, hx, ?_⟩, rfl⟩
        simp [bPt, dn_bitmap, bitOf, hb]
      · exact absurd e ns
      · exact ⟨v, dv, by simp [ptKind, hv, nb]⟩
    · rintro ⟨v, dv, rfl⟩
      obtain ⟨x, hx, dx⟩ := (denD_field v).mp dv
      by_cases hb : v.1.1 = "bitmap"
      · rw [hb] at hx dx
        obtain ⟨b, rfl, -, -⟩ := fieldC_bitmap ((de_map hY).fields _ _ hx)
        have hi : v.1.2.1 < 8 := v.2.2.2.1 hb
        refine ⟨"bitmap", _, hx, Or.inl ⟨rfl, b, rfl, v.1.2.1, hi, ?_, by simp [ptKind, hb]⟩⟩
        simpa [dn_bitmap, bitOf] using dx
      · have pk : ptKind v = v.1.1 := by simp [ptKind, hb]
        rw [pk] at ns ⊢
        by_cases sk : v.1.1 = "list" ∧ ListSkip Y
        · obtain ⟨e, b, hb', tb⟩ := sk
          exact ⟨"bitmap", _, hb', Or.inl ⟨rfl, b, rfl, 2, by omega, tb, by rw [e]; rfl⟩⟩
        · exact ⟨v.1.1, x, hx, Or.inr (Or.inr ⟨hb, ns, rfl, sk, v, rfl, dv⟩)⟩

theorem denD_aPt {Y : List (Term × Term)} (q : Term) :
    denD (.map Y) (aPt (t := t) (n := n) q) ↔ amemV (mapLookup Y (.atom "atom")) q = Bool.true := by
  rw [denD_map]
  simp only [aPt]
  cases h : mapLookup Y (.atom "atom") <;> simp [dn_none, dn_atom, amemV]

/-- `map_split_keys_and_domains/1` on a static key type, whose unions of atoms hold atoms: the atoms of its points,
and the kinds of its other points. -/
theorem split_map {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y))
    (hU : ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map Y) =
        .ok (splitT rs neg ds) ∧ SplitOk rs neg ds ∧
      (∀ s, SplitKey rs neg ds (.atom s) ↔ denD (.map Y) (aPt (t := t) (n := n) (.atom s))) ∧
      ∀ k i, SplitKey rs neg ds (.dom k i) ↔ ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = domKind k := by
  obtain ⟨ds, rd, hds, hat, hk⟩ := dom_kinds hY hm
  have dom : ∀ rs neg k i, SplitKey rs neg ds (.dom k i) ↔ ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = domKind k :=
    fun rs neg k i => hk _ (domKind_ne_atom k)
  have st := (de_map hY).static
  cases ha : mapLookup Y (.atom "atom") with
  | none =>
    refine ⟨[], .atom "nil", ds, ?_, ⟨by simp, Or.inl rfl, hds, ?_⟩, fun s => ?_, dom _ _⟩
    · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
      simp [getMapKeys_single, st, ha, rd, splitT, Term.list]
    · rw [hat, ha]; simp
    · rw [denD_aPt, ha]; simp [SplitKey, amemV]
  | some x =>
    obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map hY).fields _ _ ha)
    cases pos
    · refine ⟨[], .map S, ds, ?_, ⟨by simp, Or.inr ⟨S, rfl⟩, hds, ?_⟩, fun s => ?_, dom _ _⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        simp [getMapKeys_single, st, ha, rd, splitT, Term.list]
      · rw [hat, ha]; simp
      · rw [denD_aPt, ha]; simp [SplitKey, amemV]
    · have hU' := hU S (by simpa using ha)
      refine ⟨(mapEntries S).map Prod.fst, .atom "nil", ds, ?_, ⟨fun r mr => ?_, Or.inl rfl, hds, ?_⟩, fun s => ?_,
        dom _ _⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        simp [getMapKeys_single, st, ha, rd, splitT, Erlang.sets.«to_list/1», Erlang.maps.«keys/1»]
      · obtain ⟨e, me, rfl⟩ := List.mem_map.mp mr
        exact hU' e.1 (by rw [mapLookup_of_mem_mapEntries me]; rfl)
      · rw [hat, ha]; simp
      · rw [denD_aPt, ha]
        simp only [SplitKey, ↓reduceIte, amemV]
        constructor
        · rintro (m | ⟨N, e, -⟩)
          · obtain ⟨e, me, he⟩ := List.mem_map.mp m
            rw [← he, mapLookup_of_mem_mapEntries me]; rfl
          · cases e
        · intro h
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
          obtain ⟨e, me, ec, -⟩ := entry_of_lookup_entries hv
          exact Or.inl (List.mem_map.mpr ⟨e, me, ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm ec))⟩)

end

end Elixir.STTDescrProofsTest.Nest
