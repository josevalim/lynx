namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-! Valid types: every field is a non-empty bitmap or an atom type. -/

/-- `min/2` on integers. -/
@[simp] theorem min_integers (a b : Int) :
    Erlang.erlang.«min/2» (.integer a) (.integer b) = .ok (.integer (min a b)) := by
  simp only [Erlang.erlang.«min/2», compare_integers]
  by_cases h : a ≤ b
  · have : (Ord.compare a b).isLE = Bool.true := Int.isLE_compare.mpr h
    simp [this, Int.min_def, h]
  · have : (Ord.compare a b).isLE = Bool.false := by
      cases e : (Ord.compare a b).isLE
      · rfl
      · exact absurd (Int.isLE_compare.mp e) h
    simp [this, Int.min_def, h]

/-- Atom types are unions (true) or negations (false) of version 2 sets of atoms. -/
abbrev AtomField (w : Term) : Prop :=
  ∃ (pos : Bool) (S : List (Term × Term)),
    w = .tuple #[.atom (if pos then "union" else "negation"), .map S] ∧
      Erlang.sets.elements? (.map S) = some S

/-- What `valid?/1` checks of a type. -/
structure Valid (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom"
  bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
  atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
  atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []

/-- Atom sets hold [] for each element, so they are version 2 sets. -/
theorem atom_keys_set (S : List (Term × Term))
    (atoms : «atom_keys?/1» (Term.list ((mapEntries S).map fun e => .tuple #[e.1, e.2])) =
      .ok Term.true) : Erlang.sets.elements? (.map S) = some S := by
  have empty : ∀ es : List (Term × Term),
      «atom_keys?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true →
      es.all (fun entry => entry.2 matches .nil) := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons e rest ih =>
      intro valid
      obtain ⟨k₀, w₀⟩ := e
      rw [«atom_keys?/1».eq_def] at valid
      split at valid
      · rename_i atom tail heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        simp [ih valid.2]
      · rename_i heq; simp at heq
      · simp at valid
  simp only [Erlang.sets.elements?]
  exact ite_eq_left (empty _ atoms)

/-- Every field of a valid type is a bitmap or an atom field. -/
theorem valid_fields (es : List (Term × Term))
    (valid : «valid_fields?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
    ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    have head : ((k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
        (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ [])) ∧
        «valid_fields?/1» (Term.list (rest.map fun e => .tuple #[e.1, e.2])) = .ok Term.true := by
      rw [«valid_fields?/1».eq_def] at valid
      split at valid
      · rename_i bits fields heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        cases w <;> simp [Erlang.erlang.«is_integer/1»] at valid
        rename_i n
        obtain ⟨⟨low, high⟩, tail⟩ := valid
        exact ⟨Or.inl ⟨rfl, n.toNat, by rw [Int.toNat_of_nonneg (by omega)], by omega, by omega⟩, tail⟩
      · rename_i set fields heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        cases set <;> simp [«atoms?/1»] at valid
        rename_i S
        refine ⟨Or.inr ⟨rfl, ⟨true, S, rfl, atom_keys_set S valid.1.1⟩, fun S' e => ?_⟩, valid.2⟩
        simp at e
        subst e
        rintro rfl
        simp [Erlang.erlang.«map_size/1»] at valid
      · rename_i set fields heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        cases set <;> simp [«atoms?/1»] at valid
        rename_i S
        exact ⟨Or.inr ⟨rfl, ⟨false, S, rfl, atom_keys_set S valid.1⟩, fun S' e => by simp at e⟩, valid.2⟩
      · rename_i heq
        simp at heq
      · simp at valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.1
    · exact ih head.2 p member

theorem lookup_found (E : List (Term × Term)) (q w : Term) (lookup : mapLookup E q = some w) :
    ∃ p ∈ E, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w := by
  simp only [mapLookup, Option.map_eq_some_iff] at lookup
  obtain ⟨p, hp, rfl⟩ := lookup
  exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, rfl⟩

theorem valid_of (X : List (Term × Term)) (valid : «valid?/1» (.map X) = .ok Term.true) : Valid X := by
  simp only [«valid?/1», Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at valid
  have each := valid_fields (mapEntries X) valid
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  refine ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?_⟩
  · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
    obtain ⟨p, mp, qp, -⟩ := entry q w lookup
    rcases each p mp with ⟨key, -⟩ | ⟨key, -⟩ <;> rw [key] at qp <;> simp at qp <;> simp [qp]
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨key, field⟩ | ⟨key, -⟩
    · exact field
    · rw [key] at qp; simp at qp
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨key, -⟩ | ⟨key, field, -⟩
    · rw [key] at qp; simp at qp
    · exact field
  · obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
    rcases each p mp with ⟨key, -⟩ | ⟨key, -, union⟩
    · rw [key] at qp; simp at qp
    · exact union S e

theorem valid_map (descr : Term) (valid : «valid?/1» descr = .ok Term.true) :
    ∃ X, descr = .map X ∧ Valid X := by
  cases descr <;> simp [«valid?/1»] at valid
  exact ⟨_, rfl, valid_of _ (by simpa [«valid?/1»] using valid)⟩
