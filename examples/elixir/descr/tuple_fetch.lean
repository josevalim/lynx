namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Tuples of values in the tuple field of a map. -/
def TT (t : Term) (n : Nat) (X : List (Term × Term)) (w : List (level t n).V) : Prop :=
  ∃ b, mapLookup X (.atom "tuple") = some b ∧ denTF (level t n).E (level t n).den b w = Bool.true

/-- Maps of tuple types only, with some tuple. -/
def TOnly (t : Term) (n : Nat) (X : List (Term × Term)) : Prop :=
  (∀ v : PN t n, denD (.map X) v → v.1.1 = "tuple") ∧ ∃ w, TT t n X w

/-- The point of the next level of a tuple of values. -/
noncomputable def tpt (w : List (level t n).V) : PN t n :=
  ⟨("tuple", (0, .nil, valT (level t n).E (level t n).den w)), by simp [names],
    ⟨valT_resp w, fun h => by simp at h, fun h => by simp at h, fun _ => ⟨w, rfl⟩,
      fun h => by simp at h, fun h => by simp at h⟩⟩

theorem denD_tpt {X : List (Term × Term)} (w : List (level t n).V) : denD (.map X) (tpt (t := t) (n := n) w) ↔ TT t n X w := by
  rw [denD_map]
  simp only [tpt]
  cases h : mapLookup X (.atom "tuple") with
  | none => simp [TT, h, dn_none]
  | some b => simp [TT, h, dn_tupleT (E := (level t n).E) (den := (level t n).den) (p := (0, .nil, valT _ _ w)) rfl]

theorem pt_tuple (v : PN t n) (h : v.1.1 = "tuple") :
    ∃ w, ∀ X : List (Term × Term), (denD (.map X) v ↔ TT t n X w) := by
  obtain ⟨⟨name, p⟩, mem, ok⟩ := v
  simp only at h
  subst h
  obtain ⟨w, hw⟩ := ok.2.2.2.1 rfl
  refine ⟨w, fun X => ?_⟩
  rw [denD_map]
  simp only
  cases hb : mapLookup X (.atom "tuple") with
  | none => simp [TT, hb, dn_none]
  | some b => simp [TT, hb, dn_tupleT (E := (level t n).E) (den := (level t n).den) hw]


/-- A map without its tuple field. -/
def rmT (X : List (Term × Term)) : List (Term × Term) :=
  X.filter fun entry => compareExact (fuel (.atom "tuple") entry.1) (.atom "tuple") entry.1 != .eq

theorem lookup_rmT (X : List (Term × Term)) (name : String) :
    mapLookup (rmT X) (.atom name) = if name = "tuple" then none else mapLookup X (.atom name) := by
  rw [rmT, mapLookup_filter]
  by_cases h : name = "tuple" <;> simp [h]

theorem rest_tuple {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) :
    DE (level t n).E (.map (rmT X)) ∧ ∀ v : PN t n, denD (.map (rmT X)) v ↔ denD (.map X) v ∧ v.1.1 ≠ "tuple" := by
  have sX := de_map hX
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name x h => ?_⟩, fun v => ?_⟩
  · have : (mapLookup X q).isSome := by
      rw [rmT, mapLookup_filter] at h
      split at h
      · simp at h
      · exact h
    exact sX.keys q this
  · rw [lookup_rmT] at h
    split at h
    · cases h
    · exact sX.fields name x h
  · rw [denD_map, denD_map, lookup_rmT]
    by_cases h : v.1.1 = "tuple"
    · simp [h, dn_none]
    · simp [h]

/-- `open_tuple/1` of static element types is the open tuple literal of them. -/
theorem open_tuple_run (l : List Term) (hl : ∀ e ∈ l, Static e) : ∃ k : Int,
    Elixir.Module.Types.Descr.«open_tuple/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list l])]) ∧
    KeyOk (.tuple #[.integer k, .atom "open", Term.list l]) := by
  obtain ⟨se, run⟩ := descr_fields l hl [] [] Bool.false
  obtain ⟨k, leaf, key⟩ := leaf_new_key "open" (Or.inl rfl) l
  refine ⟨k, ?_, key⟩
  have rev : Erlang.lists.«reverse/1» (Term.list l.reverse) = .ok (Term.list l) := by
    simpa using reverse1_list l.reverse
  simp only [Term.list, List.append_nil, boolAtom_false] at run
  simp_all [Elixir.Module.Types.Descr.«open_tuple/1», Elixir.Module.Types.Descr.«open_tuple/2»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_static/2»,
    Elixir.Module.Types.Descr.«tuple_new/2»]

theorem inT_rep_true (hterm : ∀ y, (level t n).den (.atom "term") y) (i : Nat) (v : List (level t n).V) :
    InT (level t n).den Bool.true (List.replicate i (.atom "term")) v ↔ v.length = i :=
  ⟨fun h => by simpa using h.closed_length, fun h => InT.terms hterm i v h.symm⟩

/-- The tuples of an open literal of top types and an element type at an index. -/
theorem tt_open_at {e : Term} (he : (level t n).E e) (i : Nat) (k : Int) (w : List (level t n).V) :
    TT t n [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list (List.replicate i (.atom "term") ++ [e])])] w ↔
      ∃ v₁ y v₂, w = v₁ ++ y :: v₂ ∧ v₁.length = i ∧ (level t n).den e y := by
  have hl : ∀ x ∈ List.replicate i (.atom "term") ++ [e], (level t n).E x := by
    intro x mx
    rcases List.mem_append.mp mx with mx | mx
    · rw [List.eq_of_mem_replicate mx]; exact (level t n).ef.term
    · simp at mx; subst mx; exact he
  simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', denTF_leaf (level t n).ef (Or.inl rfl) hl, vT_lit (level t n).ef (Or.inl rfl) hl]
  rw [show ("open" == "closed") = Bool.false from rfl, InT.mid]
  constructor
  · rintro ⟨v₁, y, v₂, rfl, h₁, hy, -⟩
    exact ⟨v₁, y, v₂, rfl, (inT_rep_true (level t n).ef.den_term i v₁).mp h₁, hy⟩
  · rintro ⟨v₁, y, v₂, rfl, len, hy⟩
    exact ⟨v₁, y, v₂, rfl, (inT_rep_true (level t n).ef.den_term i v₁).mpr len, hy, InT.open_nil v₂⟩

/-- The tuples of an open literal of top types. -/
theorem tt_open (i : Nat) (k : Int) (w : List (level t n).V) :
    TT t n [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list (List.replicate i (.atom "term"))])] w ↔
      i ≤ w.length := by
  have hl : ∀ x ∈ List.replicate i (.atom "term"), (level t n).E x := by
    intro x mx; rw [List.eq_of_mem_replicate mx]; exact (level t n).ef.term
  simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', denTF_leaf (level t n).ef (Or.inl rfl) hl, vT_lit (level t n).ef (Or.inl rfl) hl]
  exact inT_terms_iff (level t n).ef.den_term i w

/-- The top tuple type, as `tuple/0` builds it. -/
theorem tupleTop_de : DE (level t n).E (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) :=
  fused_de (l := []) (Or.inl rfl) (by simp) fun k tag l e => by
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₂
    subst e₂
    have : l = [] := by cases l <;> simp_all [Term.list]
    exact ⟨fun h => by simp at h, fun _ h => absurd this h⟩

theorem tupleTop_den (v : PN t n) :
    denD (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) v ↔ v.1.1 = "tuple" := by
  rw [denD_map]
  by_cases h : v.1.1 = "tuple"
  · simp [mapLookup, h, dn_tuple, denO_top]
  · simp [mapLookup, h, dn_none]

/-- A point of the next level outside every tuple type. -/
def bitPt : PN t n := ⟨("bitmap", (0, .nil, fun _ => Bool.false)), by simp [names],
  ⟨resp_const _, fun _ => by simp, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h⟩⟩

theorem lt_zero_false (i : Nat) : Erlang.erlang.«</2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
  have : ¬(i : Int) < 0 := by omega
  simp [Erlang.erlang.«</2», Int.compare_eq_lt, this]

/-- `tuple_fetch/2` on static types of the next level: types holding only tuples, all of them long enough, give the
type of their values at the index; types holding a shorter tuple give `:badindex`, and others `:badtuple`. -/
theorem fetch_tuple {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok res ∧
      ((res = .atom "badtuple" ∧ ¬TOnly t n X) ∨ (res = .atom "badindex" ∧ TOnly t n X ∧ ∃ w, TT t n X w ∧ w.length ≤ i) ∨
        ∃ e, res = .tuple #[.atom "false", e] ∧ (level t n).E e ∧ TOnly t n X ∧ (∀ w, TT t n X w → i < w.length) ∧
          (∀ v₁ y v₂, v₁.length = i → TT t n X (v₁ ++ y :: v₂) → (level t n).den e y) ∧
          (∀ y, (level t n).den e y → ∃ v₁ v₂, v₁.length = i ∧ TT t n X (v₁ ++ y :: v₂))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have sX := de_map hX
  have ef := (level t n).ef
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def]
  simp only [Erlang.maps.«take/2», sX.static, lt_zero_false]
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Lynx.Term.isMember]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    obtain ⟨dR, sR⟩ := rest_tuple hX
    have rE := next_empty dR (m := k + 2) (by omega)
    obtain ⟨eb, reb, seb⟩ := tuple_empty_exact (level t n).ef fb []
    have seb := seb (lh b + 1) (by omega) (safeT_nil _)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have only : TOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmT X)) v) ∧ eb = Bool.false := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        refine ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), ?_⟩
        cases eb
        · rfl
        · have := seb.mp rfl w; rw [(tt w).mp hw] at this; cases this
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), ?_⟩
        obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt seb.mpr (by simp [h₂]))
        exact ⟨w, (tt w).mpr (by simpa using hw)⟩
    have nonEmpty : Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 2)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb)) := by
      simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb]
      rw [show (List.filter (fun entry => compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst != Ordering.eq) X) = rmT X from rfl]
      simp only [Lynx.Except.ok_bind, rE, reb (k + 2) (by omega)]
      cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
        simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    by_cases ok : TOnly t n X
    · have r : (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb) = Bool.true := by
        obtain ⟨h₁, h₂⟩ := only.mp ok
        rw [bp_true.mpr h₁, h₂]; rfl
      rw [r] at nonEmpty
      obtain ⟨w₀, hw₀⟩ := ok.2
      obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ := static_fetch (level t n).ef (n := k) (by omega) hb fb
        ⟨w₀, (tt w₀).mp hw₀⟩ i
      obtain ⟨eb₂, re₂, se₂⟩ := (level t n).ef.empty_pub he
      cases o
      · have long : ∀ w, TT t n X w → i < w.length := fun w hw => by
          by_cases h : w.length ≤ i
          · exact absurd (s₂.mpr ⟨w, (tt w).mp hw, h⟩) (by simp)
          · omega
        cases eb₂
        · refine ⟨_, ?_, Or.inr (Or.inr ⟨e, rfl, he, ok, long, fun v₁ y v₂ len h => s₁ v₁ y v₂ len ((tt _).mp h),
            fun y hy => ?_⟩)⟩
          · simp [key, nonEmpty, run, re₂ (k + 2) (by omega), Lynx.Except.andAlso, Lynx.Term.isMember,
              Lynx.Except.orElse, boolAtom]
          · obtain ⟨v₁, v₂, len, h⟩ := s₃ rfl y hy
            exact ⟨v₁, v₂, len, (tt _).mpr h⟩
        · exfalso
          have lw := long w₀ hw₀
          have split : w₀ = w₀.take i ++ w₀[i] :: w₀.drop (i + 1) := by simp
          have hw' := (tt w₀).mp hw₀
          rw [split] at hw'
          exact se₂.mp rfl _ (s₁ _ _ _ (by simp; omega) hw')
      · refine ⟨.atom "badindex", ?_, Or.inr (Or.inl ⟨rfl, ok, ?_⟩)⟩
        · simp [key, nonEmpty, run, Lynx.Except.andAlso, Lynx.Term.isMember, Lynx.Except.orElse, boolAtom]
        · obtain ⟨w, hw, len⟩ := s₂.mp rfl
          exact ⟨w, (tt w).mpr hw, len⟩
    · have r : (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb) = Bool.false := by
        cases h : (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb)
        · rfl
        · simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true'] at h
          exact absurd (only.mpr h) ok
      rw [r] at nonEmpty
      refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, ok⟩⟩
      simp [key, nonEmpty, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]


theorem fetch_neg (d : Dispatcher) (a : Term) {z : Int} (h : z < 0) :
    Elixir.Module.Types.Descr.«tuple_fetch/2» d a (.integer z) = .ok (.atom "badindex") := by
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def]
  simp [Erlang.erlang.«</2», Int.compare_eq_lt, h]

theorem fetch_term (d : Dispatcher) (i : Nat) :
    Elixir.Module.Types.Descr.«tuple_fetch/2» d (.atom "term") (.integer i) = .ok (.atom "badtuple") := by
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def]
  simp

end

end Elixir.STTDescrProofsTest.Nest
