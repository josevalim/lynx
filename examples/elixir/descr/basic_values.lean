namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Values of basic types: the bits of bitmaps, atoms, and the values of the top function, list, tuple, and
map types. -/

inductive FV where
  | bit (i : Fin 8)
  | atom (q : Term)
  | kind (k : Fin 4)

def kindName (k : Fin 4) : String :=
  match k.val with
  | 0 => "fun"
  | 1 => "list"
  | 2 => "tuple"
  | _ => "map"

theorem kindName_ne (k : Fin 4) : kindName k ≠ "bitmap" ∧ kindName k ≠ "atom" := by
  obtain ⟨k, lt⟩ := k
  simp only [kindName]
  match k, lt with
  | 0, _ | 1, _ | 2, _ | 3, _ => decide

/-- The top fields of basic types are named by kinds. -/
theorem kind_of {M : List (Term × Term)} (basic : Basic M) {name : String} (b : name ≠ "bitmap") (a : name ≠ "atom")
    (h : has M name = Bool.true) : ∃ k, kindName k = name := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  rcases basic.keys (.atom name) (by simp [hw]) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
    subst e
  · exact absurd rfl b
  · exact absurd rfl a
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The values of basic types, where the top type holds every value. -/
def denF (e : Term) (v : FV) : Prop :=
  match e with
  | .map M =>
    match v with
    | .bit i => (bits M).testBit i = Bool.true
    | .atom q => amem M q = Bool.true
    | .kind k => has M (kindName k) = Bool.true
  | _ => True

/-- Seen sets that keep the emptiness of basic types exact. -/
def SafeF (S : List (Term × Term)) : Prop := SeenOk (.map S)

theorem denF_none (v : FV) : ¬denF (.map []) v := by
  cases v <;> simp [denF, bits, amem, amemV, has, mapLookup]

/-- Basic types without values have no fields. -/
theorem basic_nil_of {M : List (Term × Term)} (basic : Basic M) (none : ∀ v, ¬denF (.map M) v) : M = [] := by
  refine basic_empty basic ?_ (fun q => ?_) fun name b a => ?_
  · have le := bits_le basic
    refine Nat.eq_of_testBit_eq fun i => ?_
    by_cases lt : i < 8
    · have := none (.bit ⟨i, lt⟩)
      simp only [denF] at this
      simpa using this
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt le (by
        have : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        omega))]
      simp
  · have := none (.atom q)
    simp only [denF] at this
    simpa using this
  · cases h : has M name with
    | false => rfl
    | true =>
      obtain ⟨k, rfl⟩ := kind_of basic b a h
      have := none (.kind k)
      simp only [denF] at this
      exact absurd h this

theorem lookup_rel {M M' : List (Term × Term)} (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) (q : Term) :
    Option.Rel (fun x y => compare (fuel x y) x y = .eq) (mapLookup M q) (mapLookup M' q) :=
  lookup_of_map_compare_eq M M' h q

theorem rel_isSome {a b : Option Term} (h : Option.Rel (fun x y => compare (fuel x y) x y = .eq) a b) : a.isSome = b.isSome := by
  cases h <;> rfl

theorem bits_resp {M M' : List (Term × Term)} (bM : Basic M) (bM' : Basic M') (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) :
    bits M = bits M' := by
  have r := lookup_rel h (.atom "bitmap")
  simp only [bits]
  cases hx : mapLookup M (.atom "bitmap") <;> cases hy : mapLookup M' (.atom "bitmap") <;> rw [hx, hy] at r <;>
    cases r <;> try rfl
  rename_i x y e
  obtain ⟨b, rfl, -⟩ := bM.bitmap x hx
  obtain ⟨b', rfl, -⟩ := bM'.bitmap y hy
  simp at e
  simp [e]

theorem amem_resp {M M' : List (Term × Term)} (bM : Basic M) (bM' : Basic M') (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq)
    (q : Term) : amem M q = amem M' q := by
  have r := lookup_rel h (.atom "atom")
  simp only [amem]
  cases hx : mapLookup M (.atom "atom") <;> cases hy : mapLookup M' (.atom "atom") <;> rw [hx, hy] at r <;>
    cases r <;> try rfl
  rename_i x y e
  obtain ⟨⟨p, S, rfl, -⟩, -⟩ := bM.atom x hx
  obtain ⟨⟨p', S', rfl, -⟩, -⟩ := bM'.atom y hy
  simp only [compare_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
    Ordering.then_eq_eq, List.compareLex_cons_cons] at e
  obtain ⟨-, et, es, -⟩ := e
  have same := rel_isSome (lookup_rel es q)
  cases p <;> cases p' <;> simp at et <;> simp [amemV, same]

theorem has_resp {M M' : List (Term × Term)} (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) (name : String) :
    has M name = has M' name :=
  rel_isSome (lookup_rel h (.atom name))

theorem denF_term (v : FV) : denF (.atom "term") v := trivial

theorem denF_inter {a b c : Term} {m : Nat} (ha : LElem a) (hb : LElem b) (hm : 2 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) (v : FV) :
    denF c v ↔ denF a v ∧ denF b v := by
  rcases ha with rfl | ⟨A, rfl, bA⟩
  · have : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.atom "term") b = .ok b := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    rw [this] at run; cases run
    simp [denF_term]
  rcases hb with rfl | ⟨B, rfl, bB⟩
  · rw [inter_term_right] at run; cases run
    simp [denF_term]
  obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, run', -, hbits, hamem, hhas⟩ := inter_basic depth A B bA bB
  rw [run'] at run; cases run
  cases v with
  | bit i => simp [denF, hbits, Nat.testBit_and]
  | atom q => simp [denF, hamem]
  | kind k => simp [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2]

theorem term_bits {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) (v : FV) :
    denF (.map T) v := by
  obtain ⟨-, hbits, hamem, hhas⟩ := term_basic term
  cases v with
  | bit i =>
    obtain ⟨i, lt⟩ := i
    simp only [denF, hbits]
    match i, lt with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
  | atom q => simp [denF, hamem]
  | kind k =>
    simp only [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2]
    obtain ⟨k, lt⟩ := k
    simp only [kindName]
    match k, lt with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl

theorem denF_diff {a b c : Term} {m : Nat} (ha : LElem a) (hb : LElem b) (hm : 2 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) (v : FV) :
    denF c v ↔ denF a v ∧ ¬denF b v := by
  rcases hb with rfl | ⟨B, rfl, bB⟩
  · rw [diff_term_right] at run; cases run
    simp [denF_term, denF_none]
  by_cases empty : B = []
  · subst empty
    have : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a (.map []) = .ok a := by
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]
    rw [this] at run; cases run
    simp [denF_none]
  obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, bA⟩
  · obtain ⟨T, term, -⟩ := unfolded_term_fields
    obtain ⟨C, run', -, hbits, hamem, hhas⟩ := diff_basic depth (.atom "term") T B (term_basic term).1 bB
      (Or.inr ⟨rfl, empty, term⟩)
    rw [run'] at run; cases run
    have all := term_bits term v
    cases v with
    | bit i => simp [denF, hbits, testBit_sub_and] at all ⊢; simp [all]
    | atom q => simp [denF, hamem] at all ⊢; simp [all]
    | kind k => simp [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2] at all ⊢; simp [all]
  · obtain ⟨C, run', -, hbits, hamem, hhas⟩ := diff_basic depth (.map A) A B bA bB (Or.inl rfl)
    rw [run'] at run; cases run
    cases v with
    | bit i => simp [denF, hbits, testBit_sub_and]
    | atom q => simp [denF, hamem]
    | kind k => simp [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2]

theorem denF_empty {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool} (ha : LElem a) (hS : SafeF S)
    (run : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v, ¬denF a v := by
  rcases ha with rfl | ⟨M, rfl, bM⟩
  · have : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.atom "term") (.map S) = .ok (boolAtom Bool.false) := by
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl
    rw [this] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    simp only [Bool.false_eq_true, false_iff]
    exact fun none => none (.bit 0) trivial
  by_cases nil : M = []
  · subst nil
    rw [empty_none_seen] at run
    have : b = Bool.true := by cases b <;> simp_all [boolAtom]
    subst this
    simp [denF_none]
  · rw [empty_basic (D m) bM hS nil] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    simp only [Bool.false_eq_true, false_iff]
    exact fun none => nil (basic_nil_of bM none)

theorem denF_resp {e e' : Term} {v : FV} (he : LElem e) (he' : LElem e') (h : compare (fuel e e') e e' = .eq) (d : denF e' v) :
    denF e v := by
  rcases he with rfl | ⟨M, rfl, bM⟩
  · exact trivial
  rcases he' with rfl | ⟨M', rfl, bM'⟩
  · simp at h
  cases v with
  | bit i => simpa [denF, bits_resp bM bM' h] using d
  | atom q => simpa [denF, amem_resp bM bM' h] using d
  | kind k => simpa [denF, has_resp h] using d

theorem flatSem : ElemSem LElem 2 FV denF SafeF :=
  ⟨denF_term, fun ha hb hm run => denF_inter ha hb hm run, fun ha hb hm run => denF_diff ha hb hm run,
    fun ha hS _ run => denF_empty ha hS run, ⟨.bit 0⟩, fun he he' h d => denF_resp he he' h d⟩

end Elixir.STTDescrProofsTest
