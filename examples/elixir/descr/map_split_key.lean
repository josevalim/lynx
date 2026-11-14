namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fetching keys of map types: map literals split at a key. -/

/-- Fields without a key. -/
def eraseKey (a : String) (l : List (Term × Term)) : List (Term × Term) :=
  l.filter fun e => compareExact (fuel (.atom a) e.1) (.atom a) e.1 != .eq

theorem lookup_eraseKey (a s : String) (l : List (Term × Term)) :
    mapLookup (eraseKey a l) (.atom s) = if s = a then none else mapLookup l (.atom s) := by
  rw [eraseKey, mapLookup_filter]
  by_cases h : s = a <;> simp [h]

theorem eraseKey_of_absent {a : String} {l : List (Term × Term)} (h : ∀ e ∈ l, e.1 ≠ .atom a) : eraseKey a l = l :=
  List.filter_eq_self.mpr fun e me => by
    have : ¬compareExact (fuel (.atom a) e.1) (.atom a) e.1 = .eq := fun c => h e me ((atom_compareExact_eq a e.1).mp c)
    simp [this]

section
variable {E : Term → Prop}

theorem fieldsV_eraseKey {a : String} {l : List (Term × Term)} (sl : FieldsV E l) : FieldsV E (eraseKey a l) :=
  ⟨fun e me => sl.1 e (List.mem_filter.mp me).1, sl.2.filter _⟩

/-- `orddict:take/2` on the fields of value maps. -/
theorem take_val (a : String) : ∀ {l : List (Term × Term)}, FieldsV E l → ∀ (acc : List (Term × Term)),
    Erlang.orddict.«take_1/3» (.atom a) (fieldsTerm l) (fieldsTerm acc) =
      match mapLookup l (.atom a) with
      | some f => .ok (.tuple #[f, fieldsTerm (acc.reverse ++ eraseKey a l)])
      | none => .ok (.atom "error")
  | [], _, acc => by rw [Erlang.orddict.«take_1/3».eq_def]; simp [fieldsTerm, Term.list, mapLookup]
  | (k, v) :: t, sl, acc => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have st := fieldsV_tail sl
    have hd := fieldsV_head sl
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have none : mapLookup t (.atom a) = Option.none := lookup_none fun e me eq => by
        have := cmp_lt_trans cmp (hd e me)
        rw [eq, compare_self] at this; cases this
      rw [Erlang.orddict.«take_1/3».eq_def, lookup_cons_atom, ite_eq_right ne, none]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      have absent : ∀ e ∈ t, e.1 ≠ .atom a := fun e me eq => by
        have := hd e me; rw [eq, compare_self] at this; cases this
      have er : eraseKey a ((.atom a, v) :: t) = t := by
        have := eraseKey_of_absent absent
        simp only [eraseKey, List.filter_cons] at this ⊢
        simp [this]
      rw [Erlang.orddict.«take_1/3».eq_def, lookup_cons_atom, ite_eq_left rfl, er]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», reverse_list]
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have ih := take_val a st ((.atom b, v) :: acc)
      have er : eraseKey a ((.atom b, v) :: t) = (.atom b, v) :: eraseKey a t := by
        simp [eraseKey, List.filter_cons]
        exact fun h => ne h.symm
      rw [Erlang.orddict.«take_1/3».eq_def, lookup_cons_atom, ite_eq_right ne, er]
      simp only [fieldsTerm, List.map_cons, Term.list] at ih ⊢
      simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, ih]

end

theorem eraseKey_none {a : String} {l : List (Term × Term)} (h : mapLookup l (.atom a) = none) : eraseKey a l = l :=
  List.filter_eq_self.mpr fun e me => by
    have : ¬compareExact (fuel (.atom a) e.1) (.atom a) e.1 = .eq := fun c => by
      have := (mapLookup_isSome l (.atom a)).mpr ⟨e, me, c⟩
      rw [h] at this; cases this
    simp [this]

/-- The field a map literal gives a key. -/
def fieldAt (tag : Term) (l : List (Term × Term)) (a : String) : Term := (mapLookup l (.atom a)).getD (tagField tag)

/-- A map of values without a key. -/
def eraseK {V : Type} (a : String) (w : MW V) : MW V := fun k => if k = .atom a then none else w k

/-- A map of values with a key set. -/
def setK {V : Type} (a : String) (o : Option V) (w : MW V) : MW V := fun k => if k = .atom a then o else w k

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_pop_key_bdd/3` splits a literal into the field of a key and a literal of the other fields. -/
theorem pop_val {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l) (a : String) :
    ∃ k : Int, Elixir.Module.Types.Descr.«map_pop_key_bdd/3» tag (fieldsTerm l) (.atom a) =
      .ok (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]]) ∧
      KeyOk (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) := by
  obtain ⟨k, run, key⟩ := leaf_new_keyM g ((eraseKey a l).map fun e => .tuple #[e.1, e.2])
  refine ⟨k, ?_, key⟩
  have tk := take_val a sl []
  simp only [List.reverse_nil, List.nil_append] at tk
  have tk' : Erlang.orddict.«take/2» (.atom a) (fieldsTerm l) =
      match mapLookup l (.atom a) with
      | some f => .ok (.tuple #[f, fieldsTerm (eraseKey a l)])
      | none => .ok (.atom "error") := by
    unfold Erlang.orddict.«take/2»; exact tk
  unfold Elixir.Module.Types.Descr.«map_pop_key_bdd/3»
  rw [tk']
  cases h : mapLookup l (.atom a) with
  | none =>
    rw [eraseKey_none h] at run ⊢
    simp only [Lynx.Except.ok_bind, key_tag_field g, Elixir.Module.Types.Descr.«map_new/2»]
    rw [show fieldsTerm l = Term.list (l.map fun e => .tuple #[e.1, e.2]) from rfl, run]
    simp [fieldAt, h]
  | some f =>
    simp only [Lynx.Except.ok_bind, Elixir.Module.Types.Descr.«map_new/2»]
    rw [show fieldsTerm (eraseKey a l) = Term.list ((eraseKey a l).map fun e => .tuple #[e.1, e.2]) from rfl, run]
    simp [fieldAt, h]

theorem tagSem_field (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) (o : Option V) :
    TagSem den tag "atom" o ↔ FieldSem den (tagField tag) o := by
  rcases g with rfl | rfl | ⟨dl, rfl, -⟩
  · rw [fieldSem_tag ef.mopsE ef.mdopsE ef.semR (Or.inl rfl)]; rfl
  · rw [fieldSem_tag ef.mopsE ef.mdopsE ef.semR (Or.inr rfl)]; rfl
  · rw [tagSem_dom]
    simp only [tagField, tagType_dom]

/-- A map literal holds the maps whose key holds a value of its field there, and whose other keys hold what the
literal of its other fields holds. -/
theorem msem_at (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) (l : List (Term × Term)) (a : String)
    (w : MW V) : MSem den tag l w ↔
      FieldSem den (fieldAt tag l a) (w (.atom a)) ∧ MSem den tag (eraseKey a l) (eraseK a w) := by
  constructor
  · intro h
    refine ⟨?_, ⟨fun s => ?_, fun k i => by simpa [eraseK] using h.doms k i⟩⟩
    · have := h.atoms a
      unfold FSem at this
      unfold fieldAt
      cases hl : mapLookup l (.atom a) with
      | none => rw [hl] at this; exact (tagSem_field ef g _).mp this
      | some f => rw [hl] at this; exact this
    · unfold FSem
      rw [lookup_eraseKey]
      by_cases hs : s = a
      · subst hs; simp [eraseK, tagSem_none]
      · have := h.atoms s
        unfold FSem at this
        simpa [eraseK, hs] using this
  · rintro ⟨hf, hm⟩
    refine ⟨fun s => ?_, fun k i => by simpa [eraseK] using hm.doms k i⟩
    by_cases hs : s = a
    · subst hs
      unfold FSem
      unfold fieldAt at hf
      cases hl : mapLookup l (.atom s) with
      | none => rw [hl] at hf; exact (tagSem_field ef g _).mpr hf
      | some f => rw [hl] at hf; exact hf
    · have := hm.atoms s
      unfold FSem at this ⊢
      rw [lookup_eraseKey] at this
      simpa [eraseK, hs] using this

end

end Elixir.STTDescrProofsTest.Nest
