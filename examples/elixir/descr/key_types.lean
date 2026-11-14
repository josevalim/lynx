namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Key types of atoms and kinds: the atom points of the atoms `P`, or all of them with the atom kind, and points of
the other kinds `ks`. -/
structure KeyInv (t : Term) (n : Nat) (Y : List (Term × Term)) (P : Term → Prop) (ks : List Term) : Prop where
  de : DE (level t n).E (.map Y)
  atoms : ∀ q, denD (.map Y) (aPt (t := t) (n := n) q) ↔ P q ∨ .atom "atom" ∈ ks
  kinds : ∀ v : PN t n, denD (.map Y) v → v.1.1 ≠ "atom" → .atom (ptKind v) ∈ ks
  wit : ∀ s, .atom s ∈ ks → s ≠ "atom" → ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = s

theorem KeyInv.congr {Y : List (Term × Term)} {P : Term → Prop} {ks ks' : List Term} (h : KeyInv t n Y P ks)
    (e : ∀ x, x ∈ ks ↔ x ∈ ks') : KeyInv t n Y P ks' :=
  ⟨h.de, fun q => by rw [h.atoms, e], fun v hv nv => (e _).mp (h.kinds v hv nv),
    fun s ms ns => h.wit s ((e _).mpr ms) ns⟩

/-- `kinds_type/2` unites the key types of kinds. -/
theorem kinds_type_run {m : Nat} (hm : (level t n).K + 23 ≤ m) : ∀ (kinds : List Term),
    (∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) → ∀ (Y : List (Term × Term)) (P : Term → Prop) (ks : List Term),
    KeyInv t n Y P ks → ∃ Y', Elixir.STTDescrProofsTest.«kinds_type/2» (D m) (Term.list kinds) (.map Y) = .ok (.map Y') ∧
      KeyInv t n Y' P (kinds ++ ks)
  | [], _, Y, P, ks, h => ⟨Y, by simp [Elixir.STTDescrProofsTest.«kinds_type/2»], by simpa using h⟩
  | d :: rest, hd, Y, P, ks, h => by
    obtain ⟨s, ms, rfl⟩ := hd _ List.mem_cons_self
    obtain ⟨T, rT, kT⟩ := kind_run ms hm
    obtain ⟨U, rU, dU, sU⟩ := union_map kT.de h.de hm
    have inT : ∀ q, denD (.map T) (aPt (t := t) (n := n) q) ↔ s = "atom" := fun q => by
      constructor
      · intro hq
        rcases kT.pts _ hq with ⟨e, -⟩ | ⟨ne, -⟩
        · exact e
        · exact absurd rfl ne
      · intro e; exact kT.atoms e q
    have inv : KeyInv t n U P (.atom s :: ks) := by
      refine ⟨dU, fun q => ?_, fun v hv nv => ?_, fun s' ms' ns' => ?_⟩
      · rw [sU, inT, h.atoms]
        simp only [List.mem_cons, Term.atom.injEq]
        constructor
        · rintro (e | h' | h')
          · exact Or.inr (Or.inl e.symm)
          · exact Or.inl h'
          · exact Or.inr (Or.inr h')
        · rintro (h' | e | h')
          · exact Or.inr (Or.inl h')
          · exact Or.inl e.symm
          · exact Or.inr (Or.inr h')
      · rcases (sU v).mp hv with h' | h'
        · rcases kT.pts v h' with ⟨-, e⟩ | ⟨-, pk⟩
          · exact absurd e nv
          · rw [pk]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h.kinds v h' nv)
      · rcases List.mem_cons.mp ms' with e | m'
        · obtain rfl : s' = s := Term.atom.inj e
          obtain ⟨v, hv, pv⟩ := kT.wit ns'
          exact ⟨v, (sU v).mpr (Or.inl hv), pv⟩
        · obtain ⟨v, hv, pv⟩ := h.wit s' m' ns'
          exact ⟨v, (sU v).mpr (Or.inr hv), pv⟩
    obtain ⟨Y', r', h'⟩ := kinds_type_run hm rest (fun d md => hd d (List.mem_cons_of_mem _ md)) U P _ inv
    refine ⟨Y', ?_, h'.congr fun x => ?_⟩
    · simp only [Term.list] at r' ⊢
      simp [Elixir.STTDescrProofsTest.«kinds_type/2», rT, rU, r']
    · simp only [List.mem_append, List.mem_cons, List.cons_append, or_left_comm]

theorem lookup_nil_pairs (atoms : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s) (q : Term) :
    (mapLookup (atoms.map (·, Term.nil)) q).isSome = Bool.true ↔ q ∈ atoms := by
  induction atoms with
  | nil => simp [mapLookup]
  | cons a rest ih =>
    obtain ⟨s, rfl⟩ := ha a List.mem_cons_self
    have ih := ih fun a m => ha a (List.mem_cons_of_mem _ m)
    rw [List.map_cons]
    by_cases e : compareExact (fuel q (.atom s)) q (.atom s) = .eq
    · obtain rfl := (compareExact_eq_atom _ _).mp e
      simp [mapLookup]
    · have ne : q ≠ .atom s := fun h => e ((compareExact_eq_atom _ _).mpr h)
      have hl : mapLookup ((Term.atom s, Term.nil) :: rest.map (·, Term.nil)) q = mapLookup (rest.map (·, Term.nil)) q := by
        simp [mapLookup, e]
      rw [hl, ih]
      simp [ne]

/-- `key_type/2` on atoms and kinds. -/
theorem key_type_run (atoms kinds : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s)
    (hk : ∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ Y, Elixir.STTDescrProofsTest.«key_type/2» (D m) (Term.list atoms) (Term.list kinds) = .ok (.map Y) ∧
      KeyInv t n Y (· ∈ atoms) kinds := by
  cases atoms with
  | nil =>
    have base : KeyInv t n [] (· ∈ ([] : List Term)) [] :=
      ⟨Or.inr ⟨[], rfl, fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩,
        fun q => by simp [denD_map, mapLookup, dn_none], fun v hv => by simp [denD_map, mapLookup, dn_none] at hv,
        fun s ms => by simp at ms⟩
    obtain ⟨Y, rY, hY⟩ := kinds_type_run hm kinds hk [] _ [] base
    exact ⟨Y, by simpa [Elixir.STTDescrProofsTest.«key_type/2», Elixir.Module.Types.Descr.«none/0», Term.list] using rY,
      by simpa using hY⟩
  | cons a rest =>
    let S := (a :: rest).map (·, Term.nil)
    have hS : ∀ q, (mapLookup S q).isSome = Bool.true ↔ q ∈ a :: rest := lookup_nil_pairs _ ha
    have set : Erlang.sets.elements? (.map S) = some S := by
      simp only [Erlang.sets.elements?, List.all_eq_true]
      rw [ite_eq_left_iff.mpr fun h => absurd ?_ h]
      intro e me
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp (mem_of_mem_mapEntries me)
      rfl
    have base : KeyInv t n [(.atom "atom", .tuple #[.atom "union", .map S])] (· ∈ a :: rest) [] := by
      refine ⟨single_de (by simp [names]) (Or.inr (Or.inl ⟨rfl, ⟨Bool.true, S, rfl, set⟩, a, ?_⟩)), fun q => ?_,
        fun v hv nv => absurd ((denD_single _ _ v).mp hv).1 nv, fun s ms => by simp at ms⟩
      · simp [amemV, (hS a).mpr List.mem_cons_self]
      · rw [denD_single]
        simp [aPt, dn_atom, amemV, hS q]
    obtain ⟨Y, rY, hY⟩ := kinds_type_run hm kinds hk _ _ [] base
    refine ⟨Y, ?_, by simpa using hY⟩
    have pl : Term.properList? (Term.cons a (Term.list rest)) = some (a :: rest) := Term.properList?_list (a :: rest)
    simp only [Term.list] at pl ⊢
    simp [Elixir.STTDescrProofsTest.«key_type/2», Elixir.Module.Types.Descr.«atom/1»,
      Elixir.Module.Types.Descr.«atom_new/1», Erlang.erlang.«is_list/1», Erlang.sets.«from_list/2»,
      Erlang.sets.«from_list/1», pl]
    exact rY

/-- The keys of the given atoms and kinds. -/
def KeysOf (atoms kinds : List Term) : MKey → Prop
  | .atom s => .atom s ∈ atoms ∨ .atom "atom" ∈ kinds
  | .dom k _ => .atom (domKind k) ∈ kinds

/-- `map_split_keys_and_domains/1` on the key type of atoms and kinds selects their keys. -/
theorem key_split (atoms kinds : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s)
    (hk : ∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∃ Y rs neg ds, Elixir.STTDescrProofsTest.«key_type/2» (D m) (Term.list atoms) (Term.list kinds) = .ok (.map Y) ∧
      Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) (.map Y) = .ok (splitT rs neg ds) ∧
      SplitOk rs neg ds ∧ ∀ κ, SplitKey rs neg ds κ ↔ KeysOf atoms kinds κ := by
  obtain ⟨Y, rY, hY⟩ := key_type_run (t := t) (n := n) atoms kinds ha hk (m := m) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hU : ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s := by
    intro S hS q hq
    have mem : ∀ q, (mapLookup S q).isSome = Bool.true → q ∈ atoms ∨ .atom "atom" ∈ kinds := fun q hq =>
      (hY.atoms q).mp ((denD_aPt q).mpr (by rw [hS]; simpa [amemV] using hq))
    rcases mem q hq with h | h
    · exact ha q h
    · obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
      have := (denD_aPt (t := t) (n := n) (Y := Y) (.atom c)).mp ((hY.atoms _).mpr (Or.inr h))
      rw [hS] at this
      simp [amemV, lookup_fresh' hc] at this
  obtain ⟨rs, neg, ds, rs', ok, sa, sd⟩ := split_map hY.de hU (m := k) (by omega)
  refine ⟨Y, rs, neg, ds, rY, rs', ok, fun κ => ?_⟩
  cases κ with
  | atom s => rw [sa, hY.atoms]; rfl
  | dom k' i =>
    rw [sd]
    constructor
    · rintro ⟨v, hv, pv⟩
      by_cases va : v.1.1 = "atom"
      · exact absurd (by simpa [ptKind, va] using pv.symm) (domKind_ne_atom k')
      · show .atom (domKind k') ∈ kinds
        rw [← pv]; exact hY.kinds v hv va
    · intro h
      exact hY.wit _ h (domKind_ne_atom k')

end

end Elixir.STTDescrProofsTest.Nest
