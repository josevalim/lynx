namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple/1` of static elements is the closed literal of them. -/
theorem tuple_run (l : List Term) (hl : ∀ e ∈ l, Static e) : ∃ k : Int,
    Elixir.Module.Types.Descr.«tuple/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", Term.list l])]) ∧
    KeyOk (.tuple #[.integer k, .atom "closed", Term.list l]) := by
  obtain ⟨se, run⟩ := descr_fields l hl [] [] Bool.false
  obtain ⟨k, leaf, key⟩ := leaf_new_key "closed" (Or.inr rfl) l
  refine ⟨k, ?_, key⟩
  have rev : Erlang.lists.«reverse/1» (Term.list l.reverse) = .ok (Term.list l) := by
    simpa using reverse1_list l.reverse
  simp only [Term.list, List.append_nil, boolAtom_false] at run
  cases l <;> simp_all [Elixir.Module.Types.Descr.«tuple/1»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_static/2»,
    Elixir.Module.Types.Descr.«tuple_new/2», Term.list]

section
variable {t : Term} {n : Nat}

/-- Closed tuples of two element types: the tuples of a value of each. -/
theorem pair_sem {a b : Term} (ha : (level t n).E a) (hb : (level t n).E b) (hsa : Static a) (hsb : Static b) :
    ∃ P, Elixir.Module.Types.Descr.«tuple/1» (Term.list [a, b]) = .ok P ∧ DE (level t n).E P ∧
      ∀ w, (∃ X, P = .map X ∧ TT t n X w) ↔ ∃ x y, w = [x, y] ∧ (level t n).den a x ∧ (level t n).den b y := by
  obtain ⟨k, run, key⟩ := tuple_run [a, b] (by simp [hsa, hsb])
  have hl : ∀ e ∈ [a, b], (level t n).E e := by simp [ha, hb]
  refine ⟨_, run, fused_de (Or.inr rfl) hl key, fun w => ?_⟩
  simp only [Term.map.injEq, exists_eq_left', TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true,
    Option.map_some, Option.some.injEq, denTF_leaf (level t n).ef (Or.inr rfl) hl, vT_lit (level t n).ef (Or.inr rfl) hl]
  match w with
  | [] => simp [InT]
  | [x] => simp [InT]
  | [x, y] => simp only [InT, and_true, List.cons.injEq]; exact ⟨fun h => ⟨x, y, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨e₁, e₂⟩, h⟩ => e₁ ▸ e₂ ▸ h⟩
  | x :: y :: z :: r => simp [InT]

end

/-- The empty list type. -/
def nilT : Term := .map [(.atom "bitmap", .integer 4)]

theorem leaf_map_new {tag : Term} (ht : tag ≠ .atom "closed") (Y : List (Term × Term)) : ∃ k : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» tag (.map Y) = .ok (.tuple #[.integer k, tag, .map Y]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons tag (.map Y))
  refine ⟨hash, ?_⟩
  unfold Elixir.Module.Types.Descr.«bdd_leaf_new/2»
  split
  · exact absurd rfl ht
  · simp [hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2», Erlang.erlang.«is_list/1»]

/-- `list/1` and `non_empty_list/1` of a static element type: the literal of lists of its values ending in the empty
list, with the empty list for `list/1`. -/
theorem list_run {e : Term} (he : Static e) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«list/1» (D m) e =
      .ok (.map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, e, nilT])]) ∧
    Elixir.Module.Types.Descr.«non_empty_list/1» (D m) e = .ok (.map [(.atom "list", .tuple #[.integer k, e, nilT])]) := by
  have ne : e ≠ .atom "closed" := by rcases he with rfl | ⟨X, rfl, -⟩ | ⟨r, -, -, rfl⟩ <;> simp
  obtain ⟨k, leaf⟩ := leaf_map_new ne [(.atom "bitmap", .integer 4)]
  have sn : Static (.map [(.atom "bitmap", .integer 4)]) := Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩)
  refine ⟨k, ?_, ?_⟩
  · simp [Elixir.Module.Types.Descr.«list/1», Elixir.Module.Types.Descr.«list_descr/3», split_static he,
      split_static sn, Elixir.Module.Types.Descr.«list_descr_static/3», Erlang.maps.«take/2», mapLookup,
      Elixir.Module.Types.Descr.«list_new/2», nilT, leaf, Lynx.Except.orElse, Erlang.erlang.«==/2»]
    by_cases h : Term.compare (Term.fuel e (.map [])) e (.map []) = .eq <;> simp [h]
  · simp [Elixir.Module.Types.Descr.«non_empty_list/1», Elixir.Module.Types.Descr.«non_empty_list/2»,
      Elixir.Module.Types.Descr.«list_descr/3», split_static he,
      split_static sn, Elixir.Module.Types.Descr.«list_descr_static/3», Erlang.maps.«take/2», mapLookup,
      Elixir.Module.Types.Descr.«list_new/2», nilT, leaf, Lynx.Except.orElse, Erlang.erlang.«==/2»]
    by_cases h : Term.compare (Term.fuel e (.map [])) e (.map []) = .eq <;> simp [h]

end Elixir.STTDescrProofsTest.Nest
