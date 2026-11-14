namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Maps of values in the map field of a type. -/
def MT (t : Term) (n : Nat) (X : List (Term × Term)) (w : MW (level t n).V) : Prop :=
  ∃ b, mapLookup X (.atom "map") = some b ∧ denMF (level t n).E (level t n).den b w = Bool.true

/-- Types of maps only, with some map. -/
def MOnly (t : Term) (n : Nat) (X : List (Term × Term)) : Prop :=
  (∀ v : PN t n, denD (.map X) v → v.1.1 = "map") ∧ ∃ w, MT t n X w

/-- The point of the next level of a map of values. -/
noncomputable def mpt (w : MW (level t n).V) : PN t n :=
  ⟨("map", (0, .nil, valM (level t n).E (level t n).den w)), by simp [names],
    ⟨valM_resp w, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun _ => ⟨w, rfl⟩,
      fun h => by simp at h⟩⟩

theorem denD_mpt {X : List (Term × Term)} (w : MW (level t n).V) : denD (.map X) (mpt (t := t) (n := n) w) ↔ MT t n X w := by
  rw [denD_map]
  simp only [mpt]
  cases h : mapLookup X (.atom "map") with
  | none => simp [MT, h, dn_none]
  | some b => simp [MT, h, dn_mapW (E := (level t n).E) (den := (level t n).den) (p := (0, .nil, valM _ _ w)) rfl]

theorem pt_map (v : PN t n) (h : v.1.1 = "map") :
    ∃ w, ∀ X : List (Term × Term), (denD (.map X) v ↔ MT t n X w) := by
  obtain ⟨⟨name, p⟩, mem, ok⟩ := v
  simp only at h
  subst h
  obtain ⟨w, hw⟩ := ok.2.2.2.2.1 rfl
  refine ⟨w, fun X => ?_⟩
  rw [denD_map]
  simp only
  cases hb : mapLookup X (.atom "map") with
  | none => simp [MT, hb, dn_none]
  | some b => simp [MT, hb, dn_mapW (E := (level t n).E) (den := (level t n).den) hw]

/-- A map without its map field. -/
def rmM (X : List (Term × Term)) : List (Term × Term) :=
  X.filter fun entry => compareExact (fuel (.atom "map") entry.1) (.atom "map") entry.1 != .eq

theorem lookup_rmM (X : List (Term × Term)) (name : String) :
    mapLookup (rmM X) (.atom name) = if name = "map" then none else mapLookup X (.atom name) := by
  rw [rmM, mapLookup_filter]
  by_cases h : name = "map" <;> simp [h]

theorem rest_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) :
    DE (level t n).E (.map (rmM X)) ∧ ∀ v : PN t n, denD (.map (rmM X)) v ↔ denD (.map X) v ∧ v.1.1 ≠ "map" := by
  have sX := de_map hX
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name x h => ?_⟩, fun v => ?_⟩
  · have : (mapLookup X q).isSome := by
      rw [rmM, mapLookup_filter] at h
      split at h
      · simp at h
      · exact h
    exact sX.keys q this
  · rw [lookup_rmM] at h
    split at h
    · cases h
    · exact sX.fields name x h
  · rw [denD_map, denD_map, lookup_rmM]
    by_cases h : v.1.1 = "map"
    · simp [h, dn_none]
    · simp [h]

/-- `map_fetch_key/2` on static types of the next level: types holding only maps, all of them with the key, give the
type of their values there; types holding a map without the key give `:badkey`, and others `:badmap`. -/
theorem fetch_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«map_fetch_key/2» (D m) (.map X) (.atom a) = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        (res = .atom "badkey" ∧ MOnly t n X ∧ ∃ w, MT t n X w ∧ w (.atom a) = none) ∨
        ∃ e, res = .tuple #[.atom "false", e] ∧ (level t n).E e ∧ MOnly t n X ∧
          (∀ w, MT t n X w → ∃ x, w (.atom a) = some x ∧ (level t n).den e x) ∧
          (∀ x, (level t n).den e x → ∃ w, MT t n X w ∧ w (.atom a) = some x)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_fetch_key/2».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 3))
      (.function "Elixir.Module.Types.Descr" "-map_fetch_key/2-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_fetch_key/2-fun-0-/1».pure]
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1»]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 3) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨hF, ⟨w₀, hw₀⟩, sF⟩⟩ := mstatic_fetch (level t n).ef (n := k) (by omega) hb fb a
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      obtain ⟨ty, opt, rfl, hty⟩ := hF
      have ok : MOnly t n X := only.mpr ⟨restE, w₀, hw₀⟩
      obtain ⟨eb, reb, seb⟩ := (level t n).ef.empty_pub hty
      cases opt
      · cases eb
        · refine ⟨_, ?_, Or.inr (Or.inr ⟨ty, rfl, hty, ok, fun w hw => ?_, fun x hx => ?_⟩)⟩
          · simp [key, mo, run, Lynx.Except.andAlso, reb (k + 3) (by omega), Lynx.Except.orElse, Lynx.Term.isMember,
              boolAtom]
          · have := (sF (w (.atom a))).mpr ⟨w, (mt w).mp hw, rfl⟩
            rw [fieldSem_mk] at this
            rcases this with ⟨-, h⟩ | ⟨x, hx, hd⟩
            · cases h
            · exact ⟨x, hx, hd⟩
          · obtain ⟨w, hw, e⟩ := (sF (some x)).mp ((fieldSem_mk (opt := Bool.false)).mpr (Or.inr ⟨x, rfl, hx⟩))
            exact ⟨w, (mt w).mpr hw, e⟩
        · exfalso
          have := (sF (w₀ (.atom a))).mpr ⟨w₀, hw₀, rfl⟩
          rw [fieldSem_mk] at this
          rcases this with ⟨-, h⟩ | ⟨x, -, hd⟩
          · cases h
          · exact seb.mp rfl x hd
      · refine ⟨.atom "badkey", ?_, Or.inr (Or.inl ⟨rfl, ok, ?_⟩)⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Except.orElse, Lynx.Term.isMember, boolAtom]
        · obtain ⟨w, hw, e⟩ := (sF none).mp ((fieldSem_mk (opt := Bool.true)).mpr (Or.inl ⟨rfl, rfl⟩))
          exact ⟨w, (mt w).mpr hw, e⟩
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1», boolAtom]

theorem ukeysort_one (x : Term) : Erlang.lists.«ukeysort/2» (.integer 1) (.cons x .nil) = .ok (.cons x .nil) := by
  rw [Erlang.lists.«ukeysort/2».eq_def]
  simp [Erlang.erlang.«>/2», Erlang.erlang.«and/2», Lynx.Except.guard, Lynx.Except.tryWith]
  rfl

/-- `open_map/1` of one required key is the open literal of that field. -/
theorem open_map_run (a : String) {v : Term} (hv : Static v) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom a, .tuple #[v, .atom "false"]]]) =
      .ok (.map [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "false"])]])]) ∧
    KeyOk (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "false"])]]) := by
  obtain ⟨k, leaf, key⟩ := leaf_new_key "open" (Or.inl rfl) [.tuple #[.atom a, .tuple #[v, .atom "false"]]]
  refine ⟨k, ?_, key⟩
  simp only [Elixir.Module.Types.Descr.«open_map/1», Elixir.Module.Types.Descr.«map_descr/2»,
    Elixir.Module.Types.Descr.«map_descr_pairs/1»]
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure,
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_atom/1», Erlang.erlang.«is_boolean/1»,
    Elixir.Module.Types.Descr.«map_descr_pair/4», split_static hv, Lynx.Except.orElse, Lynx.Except.andAlso,
    Erlang.erlang.«==/2», ukeysort_one, Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2»]
  simp only [Term.list] at leaf
  simp [fieldsTerm, Term.list, leaf]

/-- A map type of a single map field. -/
theorem mfused_de {x : Term} (hx : MField (level t n).E x) : DE (level t n).E (.map [(.atom "map", x)]) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
    by_cases e : compareExact (fuel q (.atom "map")) q (.atom "map") = .eq
    · exact ⟨"map", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [e] at h
  · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq] at h
    by_cases e : name = "map"
    · subst e
      simp at h
      subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hx⟩))))
    · simp [e] at h

theorem fieldsV_req {a : String} {e : Term} (he : (level t n).E e) :
    FieldsV (level t n).E [(.atom a, .tuple #[e, .atom "false"])] :=
  ⟨fun x mx => by simp at mx; subst mx; exact ⟨⟨a, rfl⟩, ⟨e, Bool.false, rfl, he⟩⟩, by simp⟩

/-- The maps of an open literal of one required key. -/
theorem mt_open_at {e : Term} (he : (level t n).E e) (a : String) (k : Int) (w : MW (level t n).V) :
    MT t n [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[e, .atom "false"])]])] w ↔
      ∃ x, w (.atom a) = some x ∧ (level t n).den e x := by
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [denMF_leaf (level t n).ef (fieldsV_req he) (Or.inl rfl), msem_at (level t n).ef (Or.inl rfl) _ a]
  have er : eraseKey a [(.atom a, .tuple #[e, .atom "false"])] = [] := by simp [eraseKey]
  rw [er]
  simp only [fieldAt, lookup_cons_atom, ite_true, Option.getD_some, msem_open_nil, and_true]
  rw [show Term.atom "false" = boolAtom Bool.false from rfl, fieldSem_mk]
  simp

/-- The top map type, as `open_map/0` builds it. -/
theorem mapTop_de : DE (level t n).E (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) :=
  mfused_de (Or.inl ⟨_, rfl⟩)

theorem mapTop_den (v : PN t n) :
    denD (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) v ↔ v.1.1 = "map" := by
  rw [denD_map]
  by_cases h : v.1.1 = "map"
  · simp [mapLookup, h, dn_map, denO_top]
  · simp [mapLookup, h, dn_none]

theorem fetch_map_term (d : Dispatcher) (a : String) :
    Elixir.Module.Types.Descr.«map_fetch_key/2» d (.atom "term") (.atom a) = .ok (.atom "badmap") := by
  rw [Elixir.Module.Types.Descr.«map_fetch_key/2».eq_def]
  rfl

end

end Elixir.STTDescrProofsTest.Nest
