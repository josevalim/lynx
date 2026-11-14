namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- `open_map/1` of one optional key is the open literal of that field. -/
theorem open_map_opt (a : String) {v : Term} (hv : Static v) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom a, .tuple #[v, .atom "true"]]]) =
      .ok (.map [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "true"])]])]) ∧
    KeyOk (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "true"])]]) := by
  obtain ⟨k, leaf, key⟩ := leaf_new_key "open" (Or.inl rfl) [.tuple #[.atom a, .tuple #[v, .atom "true"]]]
  refine ⟨k, ?_, key⟩
  simp only [Elixir.Module.Types.Descr.«open_map/1», Elixir.Module.Types.Descr.«map_descr/2»,
    Elixir.Module.Types.Descr.«map_descr_pairs/1»]
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure,
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_atom/1», Erlang.erlang.«is_boolean/1»,
    Elixir.Module.Types.Descr.«map_descr_pair/4», split_static hv, Lynx.Except.orElse, Lynx.Except.andAlso,
    ukeysort_one, Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2»]
  simp only [Term.list] at leaf
  simp [fieldsTerm, Term.list, leaf]

theorem fieldsV_opt {a : String} {e : Term} (he : (level t n).E e) :
    FieldsV (level t n).E [(.atom a, .tuple #[e, .atom "true"])] :=
  ⟨fun x mx => by simp at mx; subst mx; exact ⟨⟨a, rfl⟩, ⟨e, Bool.true, rfl, he⟩⟩, by simp⟩

/-- Values allowed at a key: absent, or of a type. -/
def OkAt (den : Term → V → Prop) (e : Term) (o : Option V) : Prop := o = none ∨ ∃ x, o = some x ∧ den e x

/-- The maps of an open literal of one optional key. -/
theorem mt_open_opt {e : Term} (he : (level t n).E e) (a : String) (k : Int) (w : MW (level t n).V) :
    MT t n [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[e, .atom "true"])]])] w ↔
      OkAt (level t n).den e (w (.atom a)) := by
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [denMF_leaf (level t n).ef (fieldsV_opt he) (Or.inl rfl), msem_at (level t n).ef (Or.inl rfl) _ a]
  have er : eraseKey a [(.atom a, .tuple #[e, .atom "true"])] = [] := by simp [eraseKey]
  rw [er]
  simp only [fieldAt, lookup_cons_atom, ite_true, Option.getD_some, msem_open_nil, and_true]
  rw [show Term.atom "true" = boolAtom Bool.true from rfl, fieldSem_mk]
  simp [OkAt]

/-- The domains an open map of one domain kind holds: values of a type at the kind, and any value at the others. -/
def domL (d : String) (v : Term) : List (Term × Term) :=
  domainKinds.map fun s => (.atom s, if s = d then v else .atom "term")

theorem map_put_domain_one (m : Nat) (k v : Term) :
    Elixir.Module.Types.Descr.«map_put_domain/4» (D m) .nil (Term.list [k]) v v = .ok (Term.list [.tuple #[k, v]]) := by
  rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
  simp only [Term.list]
  rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
  rfl

theorem pairs_domain (m : Nat) (d : String) {v : Term} (hv : Static v) (acc : Term) :
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[Term.list [.atom d], v]) acc =
      Elixir.Module.Types.Descr.«map_descr_domain/3» (D m) (Term.list [.atom d]) v acc := by
  rcases hv with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩ <;>
    simp [Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_list/1», Term.list]

/-- The domain kinds, as the domains of open maps list them. -/
def domKeysT : Term := Term.list (domainKinds.map Term.atom)

/-- `fields_put_all_new/3` fills the other domain kinds of a domain with `term()`. -/
theorem put_all_dom {d : String} (hd : d ∈ domainKinds) (v : Term) (m : Nat) :
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (Term.list [.tuple #[.atom d, v]]) domKeysT (.atom "term") =
      .ok (fieldsTerm (domL d v)) := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def, Term.list, domKeysT,
      domainKinds, domL, fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», Erlang.lists.«map/2»,
      Erlang.lists.«map_1/2».eq_def, Erlang.erlang.«is_function/2», Elixir.Module.Types.Descr.«-fields_put_all_new/3-fun-0-/2»,
      Erlang.program.«Elixir.Module.Types.Descr:-fields_put_all_new/3-fun-0-/1».pure, atoms_cmp, Ord.compare,
      Lynx.Term.string_compare_eq, compareOfLessAndEq]


theorem domsV_domL (d : String) {v : Term} (he : (level t n).E v) : DomsV (level t n).E (domL d v) := by
  refine ⟨fun e me => ?_, ?_⟩
  · obtain ⟨s, ms, rfl⟩ := List.mem_map.mp me
    refine ⟨⟨s, rfl, ms⟩, ?_⟩
    by_cases h : s = d
    · simp [h, he]
    · simp [h, (level t n).ef.term]
  · simp only [domL, domainKinds, List.map_cons, List.map_nil]
    simp (config := { decide := true }) [atoms_cmp, Ord.compare, Lynx.Term.string_compare_eq, compareOfLessAndEq]

theorem usort_one (x : Term) : Erlang.lists.«usort/1» (Term.list [x]) = .ok (Term.list [x]) := by
  rw [Erlang.lists.«usort/1».eq_def]; rfl

theorem ukeysort_nil : Erlang.lists.«ukeysort/2» (.integer 1) .nil = .ok .nil := by
  rw [Erlang.lists.«ukeysort/2».eq_def]
  simp [Erlang.erlang.«>/2», cmp10, Erlang.erlang.«and/2»]

/-- `open_map/1` of one domain kind is the open literal of its domains. -/
theorem open_map_dom {d : String} (hd : d ∈ domainKinds) {v : Term} (hv : Static v) (he : (level t n).E v) (m : Nat) :
    ∃ k : Int, Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[Term.list [.atom d], v]]) =
      .ok (.map [(.atom "map", .tuple #[.integer k, fieldsTerm (domL d v), .nil])]) ∧
    KeyOk (.tuple #[.integer k, fieldsTerm (domL d v), .nil]) := by
  obtain ⟨k, leaf, key⟩ := leaf_new_keyM (E := (level t n).E) (Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)) []
  refine ⟨k, ?_, by simpa [Term.list] using key⟩
  have pa := put_all_dom hd v (m + 1)
  simp only [domKeysT, domainKinds, List.map_cons, List.map_nil] at pa
  simp only [Elixir.Module.Types.Descr.«open_map/1», Elixir.Module.Types.Descr.«map_descr/2»,
    Elixir.Module.Types.Descr.«map_descr_pairs/1»]
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure, pairs_domain _ d hv,
    Elixir.Module.Types.Descr.«map_descr_domain/3», split_static hv, Elixir.Module.Types.Descr.«map_put_domain/3»,
    Erlang.erlang.«is_list/1», ukeysort_nil, Lynx.Except.orElse,
    Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2»]
  rw [usort_one]
  simp only [Lynx.Except.ok_bind]
  rw [map_put_domain_one]
  simp only [Term.list] at pa leaf ⊢
  simp [pa, leaf]

theorem lookup_domL {kind : String} (hk : kind ∈ domainKinds) (d : String) (v : Term) :
    mapLookup (domL d v) (.atom kind) = some (if kind = d then v else .atom "term") := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [domL, domainKinds, lookup_cons_atom]

/-- The maps of an open literal of one domain kind. -/
theorem mt_dom {d : String} {v : Term} (he : (level t n).E v) (k : Int) (w : MW (level t n).V) :
    MT t n [(.atom "map", .tuple #[.integer k, fieldsTerm (domL d v), .nil])] w ↔
      (d = "atom" → ∀ s, OkAt (level t n).den v (w (.atom s))) ∧
        ∀ k' i, domKind k' = d → OkAt (level t n).den v (w (.dom k' i)) := by
  have g : TagV (level t n).E (fieldsTerm (domL d v)) := Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)
  have hn : ∀ x, ¬(level t n).den (.map []) x := fun x h => (level t n).ef.den_none x h
  have ts : ∀ kind ∈ domainKinds, ∀ o, TagSem (level t n).den (fieldsTerm (domL d v)) kind o ↔
      (kind = d → OkAt (level t n).den v o) := by
    intro kind mk o
    rw [tagSem_dom_iff hn, lookup_domL mk]
    by_cases e : kind = d
    · simp [e, OkAt]
    · simp only [e, ite_false, OkAt]
      cases o <;> simp [(level t n).ef.den_term]
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [show (Term.nil : Term) = fieldsTerm [] from rfl, denMF_leaf (level t n).ef ⟨by simp, by simp⟩ g]
  constructor
  · intro h
    refine ⟨fun e s => ?_, fun k' i e => ?_⟩
    · have := h.atoms s
      unfold FSem at this
      simp only [mapLookup, List.find?_nil, Option.map_none] at this
      exact (ts "atom" (by simp [domainKinds]) _).mp this e.symm
    · exact (ts _ (domKind_mem k') _).mp (h.doms k' i) e
  · rintro ⟨ha, hd'⟩
    refine ⟨fun s => ?_, fun k' i => (ts _ (domKind_mem k') _).mpr (hd' k' i)⟩
    unfold FSem
    simp only [mapLookup, List.find?_nil, Option.map_none]
    exact (ts "atom" (by simp [domainKinds]) _).mpr fun e => ha e.symm s

end

end Elixir.STTDescrProofsTest.Nest
