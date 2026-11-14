namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! The recursive node of the plain laws: its expansion is nil or a closed pair of a term and the node. -/

/-- The expansion literal of a node, with key `k`. -/
def litN (e : Term) (k : Int) : Term := .tuple #[.integer k, .atom "closed", Term.list [.atom "term", e]]

/-- The expansion of a node. -/
def expN (e : Term) (k : Int) : Term :=
  .map [(.atom "tuple", litN e k), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]

theorem tuple_node_run {r : List Nat} {e : Term} (h : NodeAt r e) {k : Int}
    (leaf : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list [.atom "term", e]) =
      .ok (.tuple #[.integer k, .atom "closed", Term.list [.atom "term", e]])) :
    Elixir.Module.Types.Descr.«tuple/1» (Term.list [.atom "term", e]) = .ok (.map [(.atom "tuple", litN e k)]) := by
  obtain ⟨S, rfl, -⟩ := h
  have c₁ : Term.compare (Term.fuel (Term.atom "term") (.map [])) (Term.atom "term") (.map []) ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  have c₂ : Term.compare (Term.fuel (Term.tuple ⟨[.reference r, .map S, gen]⟩) (.map [])) (Term.tuple ⟨[.reference r, .map S, gen]⟩) (.map []) ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  simp only [Term.list] at leaf ⊢
  simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₁, c₂, Elixir.Module.Types.Descr.«tuple/1»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_fields/5»,
    Elixir.Module.Types.Descr.«split_dynamic/1»,
    Elixir.Module.Types.Descr.«tuple_descr_static/2», Elixir.Module.Types.Descr.«tuple_new/2», leaf,
    Erlang.lists.«reverse/1», Term.list, litN]

/-- Nodes expand to nil or their expansion literal. -/
theorem expand_node_of {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (leaf : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list [.atom "term", e]) =
      .ok (.tuple #[.integer k, .atom "closed", Term.list [.atom "term", e]])) :
    Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k) := by
  have tup := tuple_node_run h leaf
  obtain ⟨S, rfl, hk⟩ := h
  have recur : Elixir.Module.Types.Descr.«-expand_node/1-fun-0-/2» (.map S) (.atom "t") =
      .ok (.tuple #[.reference r, .map S, gen]) := by
    obtain ⟨q, hq⟩ : ∃ q, S.find? (fun entry => decide (Term.compareExact (Term.fuel (Term.atom "t") entry.fst) (Term.atom "t") entry.fst = .eq)) =
        some (q, .tuple #[.reference r, gen]) := by
      simp only [getMapKeys, List.mapM_cons, List.mapM_nil] at hk
      cases hf : S.find? (fun entry => decide (Term.compareExact (Term.fuel (Term.atom "t") entry.fst) (Term.atom "t") entry.fst = .eq)) with
      | none => simp [hf] at hk
      | some p => obtain ⟨q, v⟩ := p; simp [hf] at hk; exact ⟨q, by rw [hk]⟩
    simp [Elixir.Module.Types.Descr.«-expand_node/1-fun-0-/2», Erlang.erlang.«map_get/2», hq,
      Elixir.Module.Types.Descr.«make_node/3»]
  have atomNil : Elixir.Module.Types.Descr.«atom/1» (Term.list [.atom "nil"]) =
      .ok (.map [(.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]) := rfl
  have run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) (.tuple #[.reference r, .map S, gen]) =
      Elixir.Module.Types.Descr.«bare_union/2» (D m)
        (.map [(.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])])
        (.map [(.atom "tuple", litN (.tuple #[.reference r, .map S, gen]) k)]) := by
    unfold Elixir.Module.Types.Descr.«expand_node/1»
    simp only [gen, D, Erlang.program.«Elixir.STTDescrProofsTest:tuple_list/1».pure, pure, Except.pure,
      Lynx.Except.ok_bind]
    simp only [Elixir.STTDescrProofsTest.«Elixir.STTDescrProofsTest:tuple_list/1», Elixir.STTDescrProofsTest.«tuple_list/1»,
      atomNil, Lynx.Except.ok_bind, Erlang.program.«Elixir.Module.Types.Descr:-expand_node/1-fun-0-/1».pure, recur,
      Elixir.Module.Types.Descr.«term/0»]
    simp only [pure, Except.pure, Lynx.Except.ok_bind]
    rw [tup]
    simp only [Lynx.Except.ok_bind, gen]
  rw [run]
  unfold Elixir.Module.Types.Descr.«bare_union/2»
  simp [expN, Erlang.erlang.«==/2», Lynx.Term.getMapKeys, Elixir.Module.Types.Descr.«symmetrical_merge/3»,
    Erlang.maps.«merge_with/3», mapEntries_singleton, mapLookup]



theorem expand_node_run {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k) := by
  obtain ⟨k, leaf⟩ := leaf_closed [.atom "term", e]
  exact ⟨k, expand_node_of h m leaf⟩

/-! Plain operations compute on the expansion of a node. -/

theorem inter_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term") :
    Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (expN e k) b := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_intersection/2».eq_def, Elixir.Module.Types.Descr.«bare_intersection/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp [run, unfold_map, expN]
  all_goals simp [run, unfold_map, expN]


theorem inter_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) (ha : a ≠ .atom "term") :
    Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_intersection/2».eq_def, Elixir.Module.Types.Descr.«bare_intersection/2».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp [run, unfold_map, expN]
  all_goals simp [run, unfold_map, expN]

theorem sub_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) :
    Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) (expN e k) b := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«subtype?/2».eq_def, Elixir.Module.Types.Descr.«subtype?/2».eq_def]
  simp [run, unfold_map, expN]

theorem sub_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) :
    Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«subtype?/2».eq_def, Elixir.Module.Types.Descr.«subtype?/2».eq_def]
  simp [run, unfold_map, expN]


theorem node_ne_none {r : List Nat} {e : Term} (h : NodeAt r e) : Term.compare (Term.fuel e (.map [])) e (.map []) ≠ .eq := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Term.compare_step]; simp [Compare.compareStep]

theorem map_ne_none {B : List (Term × Term)} (ne : B ≠ []) : Term.compare (Term.fuel (Term.map B) (.map [])) (Term.map B) (.map []) ≠ .eq := by
  obtain ⟨e, xs, rfl⟩ : ∃ e xs, B = e :: xs := by
    cases B with
    | nil => exact absurd rfl ne
    | cons e xs => exact ⟨e, xs, rfl⟩
  have pos : ∀ (l : List (Term × Term)) (p : Term × Term),
      (Compare.mapViewInsert (fun a b => compareExact (fuel a b) a b) p l).length ≠ 0 := by
    intro l p
    cases l with
    | nil => simp [Compare.mapViewInsert]
    | cons q l => simp only [Compare.mapViewInsert]; split <;> simp
  intro h
  rw [Term.compare_step] at h
  simp [Compare.compareStep, Compare.compareMapViews, Compare.mapView] at h
  have h1 := h.1
  simp only [Compare.compareOn] at h1
  have := pos (Compare.mapView (fun a b => Term.compareExact (Term.fuel a b) a b) xs) e
  have z : (Compare.mapViewInsert (fun a b => compareExact (fuel a b) a b) e (Compare.mapView (fun a b => compareExact (fuel a b) a b) xs)).length = 0 := by
    simpa [Nat.compare_eq_eq] using h1
  exact this z


theorem expN_ne_none (e : Term) (k : Int) : Term.compare (Term.fuel (expN e k) (.map [])) (expN e k) (.map []) ≠ .eq :=
  map_ne_none (by simp)

theorem diff_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) :
    Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a (expN e k) := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_difference/2».eq_def, Elixir.Module.Types.Descr.«bare_difference/2».eq_def]
  simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem upper_expN (d : Dispatcher) (e : Term) (k : Int) :
    Elixir.Module.Types.Descr.«upper_bound/1» d (expN e k) = .ok (expN e k) := by
  unfold Elixir.Module.Types.Descr.«upper_bound/1»
  simp [expN, getMapKeys_single, mapLookup]

/-- The expansion of a node is not empty: it holds nil. -/
theorem empty_expN (d : Dispatcher) (e : Term) (k : Int) (S : Term) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d (expN e k) S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [expN, getMapKeys_single, Erlang.erlang.«==/2», Erlang.erlang.«is_map_key/2», mapLookup, Term.true,
    Term.false, Lynx.Except.andAlso]

/-- A node is empty only when seen: its expansion holds nil. -/
theorem empty_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D (m + 1)) e (.map S) =
      .ok (boolAtom (S.any fun p => Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 == .eq)) := by
  obtain ⟨k, run⟩ := expand_node_run h m
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  cases hs : S.any fun p => Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 == .eq <;>
    simp [Erlang.erlang.«is_map_key/2», hs, Term.true, Term.false, Erlang.maps.«put/3», run, empty_expN, boolAtom]

theorem getMapKeys_tuple (ks : List Term) (xs : Array Term) : getMapKeys ks (.tuple xs) = [] := rfl

theorem disj_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term")
    (sb : ∀ X, b = .map X → mapLookup X (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) (expN e k) b := by
  obtain ⟨S, rfl, -⟩ := h
  have ue := upper_expN (D (m + 1)) (.tuple #[.reference r, .map S, gen]) k
  simp only [expN] at ue
  rw [Elixir.Module.Types.Descr.«disjoint?/2».eq_def, Elixir.Module.Types.Descr.«disjoint?/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp [run, unfold_map, expN, getMapKeys, ue]
  case map X =>
    have hE : mapLookup [(.atom "tuple", litN (.tuple #[.reference r, .map S, gen]) k),
        (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] (.atom "dynamic") = none := by
      simp [mapLookup]
    simp [run, unfold_map, expN, getMapKeys_single, getMapKeys_tuple, ue, sb X rfl, hE]
  all_goals simp [run, unfold_map, expN, getMapKeys, ue]


theorem disj_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) (ha : a ≠ .atom "term")
    (sa : ∀ X, a = .map X → mapLookup X (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) a (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  have ue := upper_expN (D (m + 1)) (.tuple #[.reference r, .map S, gen]) k
  simp only [expN] at ue
  have hE : mapLookup [(.atom "tuple", litN (.tuple #[.reference r, .map S, gen]) k),
      (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] (.atom "dynamic") = none := by
    simp [mapLookup]
  rw [Elixir.Module.Types.Descr.«disjoint?/2».eq_def, Elixir.Module.Types.Descr.«disjoint?/2».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp [run, unfold_map, expN, getMapKeys, ue]
  case map X => simp [run, unfold_map, expN, getMapKeys_single, getMapKeys_tuple, ue, sa X rfl, hE]
  all_goals simp [run, unfold_map, expN, getMapKeys, ue]

theorem tail_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) :
    Elixir.Module.Types.Descr.«list_tail_unfold/1» (D (m + 1)) e = .ok (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«list_tail_unfold/1».eq_def]
  simp [run, unfold_map, expN, Erlang.maps.«remove/2»]


/-! The emptiness of BDDs of the expansion literal: their elements are nodes, which hold nil, so they are not
empty unless seen. -/

/-- Whether a seen set holds the id of the node `r`. -/
def idIn (r : List Nat) (S : List (Term × Term)) : Bool := S.any fun p => Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 == .eq

theorem els_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D (m + 2)) (Term.list [.atom "term", e]) (.map S) =
      .ok (boolAtom (idIn r S)) := by
  have e₁ : Elixir.Module.Types.Descr.«empty_seen?/2» (D (m + 1)) (.atom "term") (.map S) = .ok (.atom "false") := by
    unfold Elixir.Module.Types.Descr.«empty_seen?/2»; rfl
  have e₂ := empty_node h m S
  simp [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», Erlang.lists.«any/2», Erlang.erlang.«is_function/2»,
    D, Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure,
    Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2», e₁, Term.list]
  rw [Erlang.lists.«any_1/2».eq_def]
  simp [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure,
    Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2», e₂]
  rw [Erlang.lists.«any_1/2».eq_def]
  simp only [idIn]
  cases hi : S.any (fun p => Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 == .eq) <;> simp [boolAtom] <;> rfl


theorem walk_leaf_node {r : List Nat} {e : Term} (h : NodeAt r e) (k : Int) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (m + 2)) (.tuple #[.atom "open", .nil]) .nil (litN e k) (.map S) =
      .ok (boolAtom (idIn r S)) := by
  have els := els_node h m S
  simp only [Term.list] at els
  cases hb : idIn r S <;> rw [hb] at els <;>
    simp [litN, Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4», els,
      Term.list, boolAtom]

theorem walk_pos_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (m + 2))
      (.tuple #[.atom "closed", Term.list [.atom "term", e]]) .nil (.atom "bdd_top") (.map S) =
      .ok (boolAtom (idIn r S)) := by
  have els := els_node h m S
  cases hb : idIn r S <;> rw [hb] at els <;>
    simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4», els,
      Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, boolAtom]

theorem walk_neg_node (e : Term) (k : Int) (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) (.cons (litN e k) .nil)
      (.atom "bdd_top") S = .ok (.atom "false") := by
  simp [litN, Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil, Erlang.erlang.«==/2»,
    Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«/=/2», Lynx.Except.andAlso]


theorem tuple_walk_top (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil (.atom "bdd_top") S =
      .ok (.atom "false") := by
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]

theorem tuple_walk_bot (d : Dispatcher) (pos negs S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d pos negs (.atom "bdd_bot") S = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»]

/-- The top or empty BDD. -/
def bt (b : Bool) : Term := if b then .atom "bdd_top" else .atom "bdd_bot"

theorem walk_node_node {r : List Nat} {e : Term} (h : NodeAt r e) (k j : Int) (m : Nat) (S : List (Term × Term))
    (c u d : Bool) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (m + 2)) (.tuple #[.atom "open", .nil]) .nil
      (.tuple #[.integer j, litN e k, bt c, bt u, bt d]) (.map S) = .ok (boolAtom ((!c || idIn r S) && !u && !d)) := by
  have pt := walk_pos_node h m S
  have nt := walk_neg_node e k (D (m + 2)) (.map S)
  have tt := tuple_walk_top (D (m + 2)) (.map S)
  rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
  simp only [litN] at nt pt ⊢
  cases hb : idIn r S <;> rw [hb] at pt <;> cases c <;> cases u <;> cases d <;>
    simp [bt, tuple_walk_bot, pt, nt, tt, Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2», Term.list, boolAtom]

theorem diff_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term")
    (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) (expN e k) b := by
  have ne := node_ne_none h
  obtain ⟨S, rfl, -⟩ := h
  have tne : Term.compare (Term.fuel (Term.tuple #[.reference r, .map S, gen]) (.atom "term")) (Term.tuple #[.reference r, .map S, gen]) (.atom "term") ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  have ene : Term.compare (Term.fuel (expN (.tuple #[.reference r, .map S, gen]) k) (.atom "term")) (expN (.tuple #[.reference r, .map S, gen]) k) (.atom "term") ≠ .eq := by
    simp only [expN]; rw [Term.compare_step]; simp [Compare.compareStep]
  rw [Elixir.Module.Types.Descr.«bare_difference/2».eq_def, Elixir.Module.Types.Descr.«bare_difference/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem union_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term")
    (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) (expN e k) b := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def, Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem union_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) (ha : a ≠ .atom "term")
    (none : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) a (expN e k) := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def, Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

/-! The nodes the laws accept share the expansion literal of `t`, so BDDs of expansion literals hold a single
literal. -/

/-- The key of the expansion literal of the node `t`. -/
def keyOf (t : Term) : Int :=
  match Erlang.erlang.«phash2/1» (Term.list [.atom "term", t]) with
  | .ok (.integer h) => 268435456 + h - 288230376151711744
  | _ => 0

theorem leaf_isT {t e : Term} (h : IsT t e) :
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list [.atom "term", e]) =
      .ok (.tuple #[.integer (keyOf t), .atom "closed", Term.list [.atom "term", e]]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (Term.list [.atom "term", t])
  have hk := h.hash
  rw [hrun] at hk
  simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hk, keyOf, hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2»,
    Erlang.erlang.«is_list/1», bsl27, Term.list, Erlang.erlang.«length/1», Erlang.erlang.«-/2_integers»] <;> decide

/-- Accepted nodes expand with the key of `t`. -/
theorem expand_isT {t e : Term} (h : IsT t e) (m : Nat) :
    Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e (keyOf t)) :=
  expand_node_of h.node m (leaf_isT h)

theorem lit_compare {t e e' : Term} (h₁ : IsT t e) (h₂ : IsT t e') (k : Int) :
    compare (fuel (litN e k) (litN e' k)) (litN e k) (litN e' k) = .eq := by
  have ce := compare_eq_of_compareExact_eq _ _ (isT_exact h₁ h₂)
  simp only [litN, Term.list]
  rw [Term.compare_step]
  simp [Compare.compareStep, List.compareLex_cons_cons, Ordering.then_eq_eq]
  rw [Term.compare_step]
  simp [Compare.compareStep]
  rw [Term.compare_step]
  simp [Compare.compareStep, ce, List.compareLex]

/-- The expansion literals of accepted nodes, with the key of `t`. -/
def PureLit (t l : Term) : Prop := ∃ e, IsT t e ∧ l = litN e (keyOf t)

theorem pureLit_not {t : Term} : ∀ l, PureLit t l → ¬IsTop l := by
  rintro l ⟨e, -, rfl⟩ ⟨k, h⟩
  simp [litN, Term.list] at h

theorem pure_inter {t x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_intersection/2» x y = .ok w ∧
      (kept (.atom "tuple", w) = Bool.true → OField (PureLit t) w) := by
  obtain ⟨w, run, k, -⟩ := open_inter_spec pureLit_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
    tuple_inter_shape.2.2 (.atom "tuple") fx fy
  exact ⟨w, run, fun kw => (k kw).1⟩

theorem pure_union {t x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok w ∧ OField (PureLit t) w := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl, Or.inl ⟨k, rfl⟩⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · refine ⟨_, ?_, Or.inl ⟨k, rfl⟩⟩
    have nx := not_top_of_ok wx pureLit_not
    unfold Elixir.Module.Types.Descr.«tuple_union/2»
    split
    · exact (nx _ rfl).elim
    · rename_i e; simp at e; subst e; rfl
    · rename_i h₁ h₂; exact (h₂ _ rfl).elim
  obtain ⟨r, hr, okr, -⟩ := union_ok wx wy
  exact ⟨r, by rw [tuple_union_bdd (not_top_of_ok wx pureLit_not) (not_top_of_ok wy pureLit_not), hr],
    Or.inr (okr _ wx wy)⟩

theorem pure_diff {t x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧
      (kept (.atom "tuple", w) = Bool.true → OField (PureLit t) w) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl,
      fun k => by simp [kept] at k⟩
  have ny := not_top_of_ok wy pureLit_not
  have special : ¬∃ k, y = .tuple #[k, .atom "closed", .nil] := by
    rintro ⟨k, rfl⟩
    unfold Bdd at wy
    split at wy <;> simp_all [PureLit, litN, Term.list]
    obtain ⟨e, -, -, h⟩ := wy
    cases h
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_top]
    · refine ⟨_, ?_, fun _ => Or.inl ⟨kt, rfl⟩⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    · obtain ⟨w, run, keep, -⟩ := neg_ok wy
      refine ⟨w, ?_, fun _ => Or.inr (keep _ wy)⟩
      rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
    · obtain ⟨w, run, keep, -⟩ := neg_ok wy
      refine ⟨w, ?_, fun _ => Or.inr (keep _ wy)⟩
      rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
  · obtain ⟨w, run, keep, -⟩ := diff_ok wx wy
    exact ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx pureLit_not) ny (fun ⟨_, h⟩ => special h), run],
      fun _ => Or.inr (keep _ wx wy)⟩

theorem pure_child {t lit c : Term} (hl : PureLit t lit) (wc : Bdd (fun s => PureLit t s ∧ compare (fuel lit s) lit s = .lt) c) :
    c = .atom "bdd_top" ∨ c = .atom "bdd_bot" := by
  obtain ⟨e, he, rfl⟩ := hl
  have no : ∀ s, PureLit t s → compare (fuel (litN e (keyOf t)) s) (litN e (keyOf t)) s ≠ .lt := by
    rintro s ⟨e', he', rfl⟩ h
    rw [lit_compare he he'] at h; cases h
  rcases wc.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, l, c', u, d, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · obtain ⟨p, q⟩ := Bdd.leaf_iff.mp wc
    exact absurd q (no _ p)
  · unfold Bdd at wc
    obtain ⟨-, ⟨p, q⟩, -⟩ := wc
    exact absurd q (no _ p)

/-- BDDs of expansion literals: the constants, a literal, or a node of a literal over constants. -/
theorem pure_shape {t x : Term} (wx : Bdd (PureLit t) x) :
    x = .atom "bdd_top" ∨ x = .atom "bdd_bot" ∨ (∃ e, IsT t e ∧ x = litN e (keyOf t)) ∨
      ∃ (j : Int) (e : Term) (c u d : Bool), IsT t e ∧
        x = .tuple #[.integer j, litN e (keyOf t), bt c, bt u, bt d] := by
  have btc : ∀ y : Term, y = .atom "bdd_top" ∨ y = .atom "bdd_bot" → ∃ b, y = bt b := by
    rintro y (rfl | rfl)
    · exact ⟨Bool.true, rfl⟩
    · exact ⟨Bool.false, rfl⟩
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · obtain ⟨e, he, h⟩ := Bdd.leaf_iff.mp wx
    exact Or.inr (Or.inr (Or.inl ⟨e, he, h⟩))
  · unfold Bdd at wx
    obtain ⟨-, hl, wc, wu, wd⟩ := wx
    obtain ⟨cb, rfl⟩ := btc c (pure_child hl wc)
    obtain ⟨ub, rfl⟩ := btc u (pure_child hl wu)
    obtain ⟨db, rfl⟩ := btc d (pure_child hl wd)
    obtain ⟨e, he, rfl⟩ := hl
    exact Or.inr (Or.inr (Or.inr ⟨h, e, cb, ub, db, he, rfl⟩))

theorem tuple_walk_top_leaf (d : Dispatcher) (k : Int) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil
      (.tuple #[.integer k, .atom "open", .nil]) S = .ok (.atom "false") := by
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
    Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil, Erlang.erlang.«>=/2»]

/-- The emptiness of the tuple field of a node expansion is decided, whatever was seen. -/
theorem pure_tuple_empty {t x : Term} (fx : OField (PureLit t) x) (S : List (Term × Term)) :
    ∃ b, ∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom b) := by
  by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 == .eq) = Bool.true
  · refine ⟨Bool.true, fun m _ => ?_⟩
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true, boolAtom]
  have fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 == .eq) = Bool.false := by
    simpa using seen
  obtain ⟨S', put⟩ : ∃ S', Erlang.maps.«put/3» (.cons (.atom "tuple") x) (.atom "true") (.map S) = .ok (.map S') :=
    ⟨_, by simp [Erlang.maps.«put/3»]; rfl⟩
  have walk : ∀ m, Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) (.tuple #[.atom "open", .nil]) .nil x (.map S') := by
    intro m
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, put]
  have two : ∀ m, 2 ≤ m → ∃ m', m = m' + 2 := fun m hm => ⟨m - 2, by omega⟩
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨Bool.false, fun m _ => by rw [walk]; exact tuple_walk_top_leaf _ _ _⟩
  rcases pure_shape wx with rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · exact ⟨Bool.false, fun m _ => by rw [walk]; exact tuple_walk_top _ _⟩
  · exact ⟨Bool.true, fun m _ => by rw [walk]; exact tuple_walk_bot _ _ _ _⟩
  · exact ⟨idIn (refOf t) S', fun m hm => by
      obtain ⟨m', rfl⟩ := two m hm; rw [walk]; exact walk_leaf_node he.node _ m' S'⟩
  · exact ⟨(!c || idIn (refOf t) S') && !u && !d, fun m hm => by
      obtain ⟨m', rfl⟩ := two m hm; rw [walk]; exact walk_node_node he.node _ _ m' S' c u d⟩

/-! Node expansions and their combinations with basic types: plain operations keep them, and their emptiness is
decided. -/

/-- Fields of node expansions and their combinations with basic types: basic fields, or a tuple field of
expansion literals. -/
def FieldP (t : Term) (name : String) (w : Term) : Prop := FieldOk name w ∨ (name = "tuple" ∧ OField (PureLit t) w)

/-- Maps of fields of node expansions. -/
structure PureMap (t : Term) (M : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup M q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
    q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map"
  fields : ∀ name w, mapLookup M (.atom name) = some w → FieldP t name w

theorem PureMap.static {t : Term} {M : List (Term × Term)} (p : PureMap t M) :
    mapLookup M (.atom "dynamic") = Option.none := by
  cases h : mapLookup M (.atom "dynamic") with
  | none => rfl
  | some w => rcases p.keys _ (by rw [h]; rfl) with e | e | e | e | e | e <;> simp at e

theorem PureMap.atomKey {t : Term} {M : List (Term × Term)} (p : PureMap t M) {q w : Term}
    (h : mapLookup M q = some w) : ∃ name, q = .atom name := by
  rcases p.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem Basic.pure {t : Term} {M : List (Term × Term)} (b : Basic M) : PureMap t M :=
  ⟨b.keys, fun _ _ h => Or.inl (b.field h)⟩

theorem fieldP_tuple {t w : Term} (h : FieldP t "tuple" w) : OField (PureLit t) w := by
  rcases h with f | ⟨-, f⟩
  · rcases f with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · simp at e
    · simp at e
    · simp [topValue] at tv; subst tv; exact Or.inl ⟨_, rfl⟩
  · exact f

theorem fieldP_other {t w : Term} {name : String} (h : FieldP t name w) (nt : name ≠ "tuple") : FieldOk name w := by
  rcases h with f | ⟨e, -⟩
  · exact f
  · exact absurd e nt

theorem interP (t : Term) (name : String) (x y : Term) (hx : FieldP t name x) (hy : FieldP t name y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → FieldP t name r) := by
  by_cases nt : name = "tuple"
  · subst nt
    obtain ⟨w, run, k⟩ := pure_inter (fieldP_tuple hx) (fieldP_tuple hy)
    exact ⟨w, fun d => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => Or.inr ⟨rfl, k kw⟩⟩
  · obtain ⟨r, run, ok, -⟩ := inter_key name x y (fieldP_other hx nt) (fieldP_other hy nt)
    exact ⟨r, run, fun kw => Or.inl (ok kw)⟩

theorem diffP (t : Term) (name : String) (x y : Term) (hx : FieldP t name x) (hy : FieldP t name y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → FieldP t name r) := by
  by_cases nt : name = "tuple"
  · subst nt
    obtain ⟨w, run, k⟩ := pure_diff (fieldP_tuple hx) (fieldP_tuple hy)
    exact ⟨w, fun d => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => Or.inr ⟨rfl, k kw⟩⟩
  · obtain ⟨r, run, ok, -⟩ := diff_key name x y (fieldP_other hx nt) (fieldP_other hy nt)
    exact ⟨r, run, fun kw => Or.inl (ok kw)⟩

theorem unionP (t : Term) (name : String) (x y : Term) (hx : FieldP t name x) (hy : FieldP t name y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y = .ok r) ∧ FieldP t name r := by
  by_cases nt : name = "tuple"
  · subst nt
    obtain ⟨w, run, k⟩ := pure_union (fieldP_tuple hx) (fieldP_tuple hy)
    exact ⟨w, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr ⟨rfl, k⟩⟩
  · obtain ⟨r, run, ok⟩ := fieldok_union name (fieldP_other hx nt) (fieldP_other hy nt)
    exact ⟨r, run, Or.inl ok⟩

theorem inter_pure (t : Term) (A B : List (Term × Term)) (bA : PureMap t A) (bB : PureMap t B) :
    ∃ C, (∀ m, 0 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.map A) (.map B) =
      .ok (.map C)) ∧ PureMap t C := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (D 0) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have ik := fun name x y (hx : mapLookup A (.atom name) = some x) (hy : mapLookup B (.atom name) = some y) =>
    interP t name x y (bA.fields _ _ hx) (bB.fields _ _ hy)
  have gval : ∀ name x y r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom name) x y = .ok r) →
      g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  obtain ⟨I, C, run, lookI, lookC⟩ := inter_uniform 0 A B bA.static bB.static g (by
    intro q x y hx hy m _
    obtain ⟨name, key⟩ := bA.atomKey hx
    subst key
    obtain ⟨r, run, -⟩ := ik name x y hx hy
    rw [run, gval _ _ _ _ run])
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup A (.atom name), mapLookup B (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    intro name
    rw [lookC, find_atom, lookI, find_atom]
    cases mapLookup A (.atom name) <;> cases hR : mapLookup B (.atom name) <;> simp [hR]
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have hI := find_isSome I q hit
      rw [lookI] at hI
      split at hI
      · rename_i e' hit'
        exact find_isSome A q hit'
      · simp at hI
    · simp at some
  refine ⟨C, run, ⟨fun q h => bA.keys q (keys q h), fun name w h => ?_⟩⟩
  rw [look] at h
  cases hx : mapLookup A (.atom name) <;> cases hy : mapLookup B (.atom name) <;> rw [hx, hy] at h <;>
    try simp at h
  rename_i x y
  obtain ⟨r, run, ok⟩ := ik name x y hx hy
  simp only [gval _ _ _ _ run] at h
  obtain ⟨k, rfl⟩ := h
  exact ok k


/-- Folding the difference of maps of fields of node expansions gives such a map. -/
theorem fold_pure (t : Term) (A B C : List (Term × Term)) (bA : PureMap t A) (g : Term → Term → Term → Term)
    (lookC : ∀ q, mapLookup C q =
      match (mapEntries B).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | some e => (mapLookup A e.1).bind fun v₁ =>
          if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else Option.none
      | none => mapLookup A q)
    (dk : ∀ name x y, mapLookup A (.atom name) = some x → mapLookup B (.atom name) = some y →
      kept (.atom name, g (.atom name) x y) = Bool.true → FieldP t name (g (.atom name) x y)) :
    PureMap t C := by
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup B (.atom name) with
      | some y => (mapLookup A (.atom name)).bind fun x =>
          if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | none => mapLookup A (.atom name) := by
    intro name
    rw [lookC, find_atom]
    cases mapLookup B (.atom name) <;> rfl
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have same : compareExact (fuel q e.1) q e.1 = .eq := by simpa using List.find?_some hit
      rw [mapLookup_congr same]
      cases h : mapLookup A e.1 <;> simp_all
    · exact some
  refine ⟨fun q h => bA.keys q (keys q h), fun name w h => ?_⟩
  rw [look] at h
  cases hy : mapLookup B (.atom name) with
  | none => rw [hy] at h; exact bA.fields _ _ h
  | some y =>
    rw [hy] at h
    cases hx : mapLookup A (.atom name) with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Option.bind_some] at h
      split at h
      · rename_i k; cases h; exact dk name x y hx hy k
      · cases h

theorem diff_pure (t : Term) (left : Term) (A B : List (Term × Term)) (bA : PureMap t A) (bB : PureMap t B)
    (hleft : left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧
      Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) :
    ∃ C, (∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) left (.map B) = .ok (.map C)) ∧
      PureMap t C := by
  by_cases emptyB : B = []
  · subst emptyB
    rcases hleft with rfl | ⟨-, ne, -⟩
    rotate_left
    · exact absurd rfl ne
    refine ⟨A, fun m _ => ?_, bA⟩
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2»]
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (D 0) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have gval : ∀ name x y r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y = .ok r) →
      g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  have fold := fun depth => difference_fold depth (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries B) A (mapEntries_distinct B) (by
      intro e member v₁ found
      have hy := mapLookup_of_mem_mapEntries member
      obtain ⟨name, key⟩ := bA.atomKey found
      rw [key] at found hy ⊢
      obtain ⟨r, run, -⟩ := diffP t name v₁ e.2 (bA.fields _ _ found) (bB.fields _ _ hy)
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure, run, gval _ _ _ _ run])
  obtain ⟨C, -, lookC, eqC⟩ := fold 0
  refine ⟨C, fun m hm => ?_, fold_pure t A B C bA g lookC fun name x y hx hy k => by
    obtain ⟨r, run, ok⟩ := diffP t name x y (bA.fields _ _ hx) (bB.fields _ _ hy)
    rw [gval _ _ _ _ run] at k ⊢; exact ok k⟩
  obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 2 := ⟨m - 2, by omega⟩
  obtain ⟨C', fold', -, eq'⟩ := fold depth
  rw [eqC, ← eq']
  rcases hleft with rfl | ⟨rfl, -, term⟩
  · unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map bA.static, static_map bB.static, emptyB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3»]
    simpa using fold'
  · unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map bB.static, emptyB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3», term]
    simpa using fold'

theorem union_pure (t : Term) (A B : List (Term × Term)) (bA : PureMap t A) (bB : PureMap t B) :
    ∃ U, (∀ m, 1 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B) = .ok (.map U)) ∧
      PureMap t U := by
  let g : Term → Term → Term → Term := fun q x y =>
    match Elixir.Module.Types.Descr.«bare_union/3» (D 1) q x y with | .ok w => w | .error _ => .nil
  have gval : ∀ name x y r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y =
      .ok r) → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h 0]
  have atomKey : ∀ {X : List (Term × Term)}, PureMap t X → ∀ {q w : Term}, mapLookup X q = some w →
      ∃ name, q = .atom name := fun bX q w h => by
    rcases bX.keys q (by rw [h]; rfl) with e | e | e | e | e | e <;> exact ⟨_, e⟩
  have calls : ∀ q x y, mapLookup A q = some x → mapLookup B q = some y → ∀ m, 1 ≤ m →
      Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y = .ok (g q x y) := by
    intro q x y hx hy m hm
    obtain ⟨name, rfl⟩ := atomKey bA hx
    obtain ⟨r, run, -⟩ := unionP t name x y (bA.fields _ _ hx) (bB.fields _ _ hy)
    obtain ⟨n, rfl, -⟩ := succ_of_le hm
    rw [run, gval _ _ _ _ run]
  obtain ⟨U, run, look⟩ := union_uniform 1 A B bA.static bB.static (fun q h => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h; exact atomKey bB hw) g calls
  refine ⟨U, run, ⟨fun q h => ?_, fun name w h => ?_⟩⟩
  · cases hb : mapLookup B q with
    | none => rw [(look q).1 hb] at h; exact bA.keys q h
    | some y => exact bB.keys q (by simp [hb])
  · cases hb : mapLookup B (.atom name) with
    | none => rw [(look _).1 hb] at h; exact bA.fields _ _ h
    | some y =>
      cases ha : mapLookup A (.atom name) with
      | none => rw [(look _).2.1 y hb ha] at h; rw [← Option.some.inj h]; exact bB.fields _ _ hb
      | some x =>
        rw [(look _).2.2 x y ha hb] at h
        rw [← Option.some.inj h]
        obtain ⟨r, run, ok⟩ := unionP t name x y (bA.fields _ _ ha) (bB.fields _ _ hb)
        rw [gval _ _ _ _ run]
        exact ok


theorem empty_pure {t : Term} {M : List (Term × Term)} (pM : PureMap t M) (S : List (Term × Term)) :
    ∃ b, ∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.map M) (.map S) = .ok (boolAtom b) := by
  by_cases nonempty : M = []
  · subst nonempty
    exact ⟨Bool.true, fun m _ => by simpa [boolAtom] using empty_none_seen (D m) (.map S)⟩
  obtain ⟨tb, ht⟩ : ∃ tb, ∀ m, 2 ≤ m → ∀ x, mapLookup M (.atom "tuple") = some x →
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom tb) := by
    cases hx : mapLookup M (.atom "tuple") with
    | none => exact ⟨Bool.false, fun m _ x h => by cases h⟩
    | some x =>
      obtain ⟨b, hb⟩ := pure_tuple_empty (fieldP_tuple (pM.fields _ _ hx)) S
      exact ⟨b, fun m hm x' h => by cases h; exact hb m hm⟩
  obtain ⟨mb, hm⟩ := map_top_bool S
  have static : mapLookup M (.atom "dynamic") = Option.none := pM.static
  have top : ∀ name, name ≠ "bitmap" → name ≠ "atom" → name ≠ "tuple" → ∀ w, mapLookup M (.atom name) = some w →
      topValue name = some w := fun name n₁ n₂ n₃ w h => by
    rcases fieldP_other (pM.fields _ _ h) n₃ with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · exact absurd e n₁
    · exact absurd e n₂
    · exact tv
  have mapV := top "map" (by decide) (by decide) (by decide)
  have listV := top "list" (by decide) (by decide) (by decide)
  have funV := top "fun" (by decide) (by decide) (by decide)
  simp only [topValue] at mapV listV funV
  refine ⟨!(mapLookup M (.atom "atom")).isSome && !(mapLookup M (.atom "bitmap")).isSome &&
    (!(mapLookup M (.atom "tuple")).isSome || tb) && (!(mapLookup M (.atom "map")).isSome || mb) &&
    !(mapLookup M (.atom "list")).isSome && !(mapLookup M (.atom "fun")).isSome, fun m hm' => ?_⟩
  have nL := list_top_nonempty (D m) (.map S)
  have nF := fun_top_nonempty (D m) (.map S)
  have mB := hm (D m)
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
  cases ha : mapLookup M (.atom "atom") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso, boolAtom]
  | none =>
  cases hb : mapLookup M (.atom "bitmap") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  | none =>
  have ab : ∀ x y : Bool,
      Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (boolAtom y)) Bool.true = .ok (boolAtom (x && y)) := by
    intro x y; cases x <;> cases y <;> rfl
  have abT : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "true")) Bool.true = .ok (boolAtom x) := by
    intro x; cases x <;> rfl
  have abF : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "false")) Bool.true = .ok (.atom "false") := by
    intro x; cases x <;> rfl
  have bt : boolAtom Bool.true = .atom "true" := rfl
  have bf : boolAtom Bool.false = .atom "false" := rfl
  have val : ∀ {key : String} {v : Term}, (∀ w, mapLookup M (.atom key) = some w → some v = some w) →
      mapLookup M (.atom key) = Option.none ∨ mapLookup M (.atom key) = some v := by
    intro key v h
    cases e : mapLookup M (.atom key) with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (by rw [Option.some.inj (h w e)])
  have tupleV : mapLookup M (.atom "tuple") = Option.none ∨ ∃ x, mapLookup M (.atom "tuple") = some x ∧
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom tb) := by
    cases hx : mapLookup M (.atom "tuple") with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl, ht m hm' x hx⟩
  rcases tupleV with htu | ⟨x, htu, tB⟩ <;> rcases val mapV with hma | hma <;>
    rcases val listV with hl | hl <;> rcases val funV with hf | hf <;>
    simp [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», abT, abF, bt, bf, ha, hb, htu, hma, hl, hf,
      mB, nL, nF]
  all_goals first
    | (cases tb <;> cases mb <;> simp [tB, boolAtom, Lynx.Except.andAlso] <;> rfl)
    | (apply nonempty
       apply nil_of_lookup_none
       intro q
       cases h : mapLookup M q with
       | none => rfl
       | some w =>
         rcases pM.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)

/-- The node `t`, its expansion, and their combinations with basic types. -/
def Pure (t a : Term) : Prop := a = .atom "term" ∨ IsT t a ∨ ∃ M, a = .map M ∧ PureMap t M

theorem expN_pure {t e : Term} (he : IsT t e) : PureMap t
    [(.atom "tuple", litN e (keyOf t)), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] := by
  refine ⟨fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?] at h
    by_cases t₁ : Term.compareExact (Term.fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₁)))))
    · by_cases t₂ : Term.compareExact (Term.fuel q (.atom "atom")) q (.atom "atom") = .eq
      · exact Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₂))
      · simp [t₁, t₂] at h
  · by_cases t₁ : name = "tuple"
    · subst t₁
      simp [mapLookup] at h
      subst h
      exact Or.inr ⟨rfl, Or.inr (Bdd.leaf_iff.mpr ⟨e, he, rfl⟩)⟩
    · by_cases t₂ : name = "atom"
      · subst t₂
        simp [mapLookup] at h
        subst h
        exact Or.inl (Or.inr (Or.inl ⟨rfl, ⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil", by
          simp [amemV, mapLookup]⟩))
      · simp [mapLookup, t₁, t₂] at h

theorem node_ne_term {t e : Term} (he : IsT t e) : e ≠ .atom "term" := by
  obtain ⟨S, rfl, -⟩ := he.node; simp

theorem expN_ne_term (e : Term) (k : Int) : expN e k ≠ .atom "term" := by simp [expN]

theorem pure_none (t : Term) : Pure t (.map []) :=
  Or.inr (Or.inr ⟨[], rfl, ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩⟩)

/-- Intersections of maps of the class, with nodes replaced by their expansions. -/
theorem pure_inter_maps {t : Term} {a b : Term} (ha : IsT t a ∨ ∃ A, a = .map A ∧ PureMap t A)
    (hb : IsT t b ∨ ∃ B, b = .map B ∧ PureMap t B) :
    ∃ C, (∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok (.map C)) ∧ PureMap t C := by
  obtain ⟨A, pA, ea⟩ : ∃ A, PureMap t A ∧ ∀ m b, b ≠ .atom "term" →
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) b := by
    rcases ha with ha | ⟨A, rfl, pA⟩
    · exact ⟨_, expN_pure ha, fun m b hb => inter_node_l ha.node m (expand_isT ha m) b hb⟩
    · exact ⟨A, pA, fun _ _ _ => rfl⟩
  obtain ⟨B, pB, eb⟩ : ∃ B, PureMap t B ∧ ∀ m, b ≠ .atom "term" ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) b =
        Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) (.map B) := by
    rcases hb with hb | ⟨B, rfl, pB⟩
    · exact ⟨_, expN_pure hb, fun m => ⟨node_ne_term hb, inter_node_r hb.node m (expand_isT hb m) _ (by simp)⟩⟩
    · exact ⟨B, pB, fun _ => ⟨by simp, rfl⟩⟩
  obtain ⟨C, run, pC⟩ := inter_pure t A B pA pB
  refine ⟨C, fun m hm => ?_, pC⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [ea m b (eb m).1, (eb m).2, run _ (by omega)]

theorem pureOk (t : Term) : ElemOk (Pure t) 2 := by
  refine ⟨Or.inl rfl, fun {a b} ha hb => ?_, fun {a} ha S => ?_, pure_none t, by decide⟩
  · rcases ha with rfl | ha'
    · exact ⟨b, hb, fun _ _ => by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl⟩
    rcases hb with rfl | hb'
    · exact ⟨a, Or.inr ha', fun m _ => inter_term_right _ _⟩
    obtain ⟨C, run, pC⟩ := pure_inter_maps ha' hb'
    exact ⟨_, Or.inr (Or.inr ⟨C, rfl, pC⟩), run⟩
  · rcases ha with rfl | ha | ⟨M, rfl, pM⟩
    · exact ⟨Bool.false, fun m _ => by rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl⟩
    · exact ⟨_, fun m hm => by
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact empty_node ha.node m S⟩
    · exact empty_pure pM S

theorem pureDiff (t : Term) : ElemDiff (Pure t) 2 := by
  refine ⟨fun {a b} ha hb => ?_⟩
  rcases hb with rfl | hb'
  · exact ⟨_, pure_none t, fun m _ => diff_term_right _ _⟩
  -- The right type as a map.
  obtain ⟨B, pB, eb⟩ : ∃ B, PureMap t B ∧ ∀ m a,
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a (.map B) := by
    rcases hb' with hb | ⟨B, rfl, pB⟩
    · exact ⟨_, expN_pure hb, fun m a => diff_node_r hb.node m (expand_isT hb m) a⟩
    · exact ⟨B, pB, fun _ _ => rfl⟩
  have succ : ∀ m, 2 ≤ m → ∃ m', m = m' + 1 ∧ 1 ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  -- The left type as a map, or the result as the left type.
  have mapCase : ∀ {left : Term} (A : List (Term × Term)), PureMap t A →
      (left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧ Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) →
      ∃ c, Pure t c ∧ ∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) left (.map B) = .ok c :=
    fun A pA hl => let ⟨C, run, pC⟩ := diff_pure t _ A B pA pB hl; ⟨_, Or.inr (Or.inr ⟨C, rfl, pC⟩), run⟩
  obtain ⟨c, hc, run⟩ : ∃ c, Pure t c ∧ ∀ m, 2 ≤ m →
      Elixir.Module.Types.Descr.«bare_difference/2» (D m) a (.map B) = .ok c := by
    by_cases empty : B = []
    · subst empty
      refine ⟨a, ha, fun m _ => ?_⟩
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Erlang.erlang.«==/2»]
    rcases ha with rfl | ha | ⟨A, rfl, pA⟩
    · obtain ⟨T, term, -⟩ := unfolded_term_fields
      exact mapCase T (Basic.pure (term_basic term).1) (Or.inr ⟨rfl, empty, term⟩)
    · obtain ⟨c, hc, run⟩ := mapCase _ (expN_pure ha) (Or.inl rfl)
      refine ⟨c, hc, fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ m hm
      rw [diff_node_l ha.node m' (expand_isT ha m') (.map B) (by simp) (map_ne_none empty)]
      exact run _ (by omega)
    · exact mapCase A pA (Or.inl rfl)
  exact ⟨c, hc, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m hm; rw [eb]; exact run _ hm⟩

theorem union_any_term (d : Dispatcher) (a : Term) :
    Elixir.Module.Types.Descr.«bare_union/2» d a (.atom "term") = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»; split <;> simp_all

theorem empty_any_node {t e : Term} (he : IsT t e) (m : Nat) :
    Elixir.Module.Types.Descr.«empty?/1» (D (m + 1)) e = .ok (.atom "false") := by
  obtain ⟨S, rfl, -⟩ := he.node
  have := empty_node he.node m []
  unfold Elixir.Module.Types.Descr.«empty?/1»
  simpa [boolAtom] using this

/-- The maps of the class, with nodes replaced by their expansions, for `subtype?/2` and `disjoint?/2`. -/
def PureC (t a : Term) : Prop := a = .atom "term" ∨ ∃ M, a = .map M ∧ PureMap t M

theorem pure_sub_disj (t : Term) :
    (∀ {a b}, PureC t a → PureC t b → BoolAt 2 (fun m => Elixir.Module.Types.Descr.«subtype?/2» (D m) a b)) ∧
      (∀ {a b}, PureC t a → PureC t b → BoolAt (2 + 6) (fun m => Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b)) := by
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  exact class_sub_disj (PureC t) (FieldP t) (PureMap t) 2 (fun ha => ha) ⟨T, term, Basic.pure (term_basic term).1⟩
    (fun bA => bA.static) (fun bA => bA.keys) (fun bA _ _ h => bA.fields _ _ h)
    (fun name x y hx hy => by
      obtain ⟨r, run, ok⟩ := diffP t name x y hx hy
      exact ⟨r, fun m _ => run _, ok⟩)
    (fun name x y hx hy => by
      obtain ⟨r, run, ok⟩ := interP t name x y hx hy
      exact ⟨r, fun m _ => run _, ok⟩)
    (fun name x hx => by
      by_cases nt : name = "tuple"
      · subst nt
        obtain ⟨b, hb⟩ := pure_tuple_empty (fieldP_tuple hx) []
        exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using hb m hm⟩
      · exact ⟨Bool.false, fun m _ => fieldok_empty (D m) name (fieldP_other hx nt)⟩)
    (fun {a} ha => by
      rcases ha with rfl | ⟨A, rfl, pA⟩
      · exact ⟨Bool.false, fun m _ => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; rfl⟩
      · obtain ⟨b, hb⟩ := empty_pure pA []
        exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; exact hb m hm⟩)

theorem disj_term_l (d : Dispatcher) (b : Term) :
    Elixir.Module.Types.Descr.«disjoint?/2» d (.atom "term") b = Elixir.Module.Types.Descr.«empty?/1» d b := by
  unfold Elixir.Module.Types.Descr.«disjoint?/2»; rfl

theorem disj_term_r (d : Dispatcher) (a : Term) :
    Elixir.Module.Types.Descr.«disjoint?/2» d a (.atom "term") = Elixir.Module.Types.Descr.«empty?/1» d a := by
  unfold Elixir.Module.Types.Descr.«disjoint?/2»; split <;> simp_all

theorem pureFun (t : Term) : ElemFun (Pure t) 8 := by
  obtain ⟨sub, disj⟩ := pure_sub_disj t
  have succ : ∀ m, 2 ≤ m → ∃ m', m = m' + 1 ∧ 1 ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  have expC : ∀ {e}, IsT t e → PureC t (expN e (keyOf t)) := fun he => Or.inr ⟨_, rfl, expN_pure he⟩
  refine ⟨fun {a} ha => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_⟩
  · rcases ha with rfl | ha | ⟨A, rfl, pA⟩
    · exact Or.inl rfl
    · obtain ⟨S, rfl, -⟩ := ha.node; exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
    · exact Or.inr (Or.inl ⟨A, rfl, pA.static⟩)
  · -- Unions.
    rcases ha with rfl | ha' | ⟨A, rfl, pA⟩
    · exact ⟨_, Or.inl rfl, fun m _ => union_term_l _ _⟩
    rotate_left
    · rcases hb with rfl | hb' | ⟨B, rfl, pB⟩
      · exact ⟨_, Or.inl rfl, fun m _ => union_any_term _ _⟩
      · by_cases none : A = []
        · subst none
          refine ⟨b, Or.inr (Or.inl hb'), fun m _ => ?_⟩
          obtain ⟨S, rfl, -⟩ := hb'.node
          unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
        obtain ⟨U, run, pU⟩ := union_pure t A _ pA (expN_pure hb')
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => by
          obtain ⟨m', rfl, -⟩ := succ m (by omega)
          rw [union_node_r hb'.node m' (expand_isT hb' m') _ (by simp) (map_ne_none none)]; exact run _ (by omega)⟩
      · obtain ⟨U, run, pU⟩ := union_pure t A B pA pB
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => run m (by omega)⟩
    · rcases hb with rfl | hb' | ⟨B, rfl, pB⟩
      · exact ⟨_, Or.inl rfl, fun m _ => union_any_term _ _⟩
      · obtain ⟨U, run, pU⟩ := union_pure t _ _ (expN_pure ha') (expN_pure hb')
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => by
          obtain ⟨m', rfl, -⟩ := succ m (by omega)
          rw [union_node_l ha'.node m' (expand_isT ha' m') _ (node_ne_term hb') (node_ne_none hb'.node),
            union_node_r hb'.node m' (expand_isT hb' m') _ (expN_ne_term _ _) (expN_ne_none _ _)]
          exact run _ (by omega)⟩
      · by_cases none : B = []
        · subst none
          refine ⟨a, Or.inr (Or.inl ha'), fun m _ => ?_⟩
          have := node_ne_none ha'.node
          obtain ⟨S, rfl, -⟩ := ha'.node
          unfold Elixir.Module.Types.Descr.«bare_union/2»; simp_all [Erlang.erlang.«==/2»]
        obtain ⟨U, run, pU⟩ := union_pure t _ B (expN_pure ha') pB
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => by
          obtain ⟨m', rfl, -⟩ := succ m (by omega)
          rw [union_node_l ha'.node m' (expand_isT ha' m') _ (by simp) (map_ne_none none)]
          exact run _ (by omega)⟩
  · -- Inclusions: nodes behave as their expansions.
    obtain ⟨A', cA, ea⟩ : ∃ A', PureC t A' ∧ ∀ m' b, Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A' b := by
      rcases ha with rfl | ha | ⟨A, rfl, pA⟩
      · exact ⟨_, Or.inl rfl, fun _ _ => rfl⟩
      · exact ⟨_, expC ha, fun m' b => sub_node_l ha.node m' (expand_isT ha m') b⟩
      · exact ⟨_, Or.inr ⟨A, rfl, pA⟩, fun _ _ => rfl⟩
    obtain ⟨B', cB, eb⟩ : ∃ B', PureC t B' ∧ ∀ m' a, Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a B' := by
      rcases hb with rfl | hb | ⟨B, rfl, pB⟩
      · exact ⟨_, Or.inl rfl, fun _ _ => rfl⟩
      · exact ⟨_, expC hb, fun m' a => sub_node_r hb.node m' (expand_isT hb m') a⟩
      · exact ⟨_, Or.inr ⟨B, rfl, pB⟩, fun _ _ => rfl⟩
    obtain ⟨s, hs⟩ := sub cA cB
    exact ⟨s, fun m hm => by
      obtain ⟨m', rfl, -⟩ := succ m (by omega); dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩
  · -- Disjointness: the top type checks emptiness, and nodes behave as their expansions otherwise.
    have emptyOf : ∀ {a}, Pure t a → BoolAt 8 (fun m => Elixir.Module.Types.Descr.«empty?/1» (D m) a) := by
      intro a ha
      rcases ha with rfl | ha | ⟨A, rfl, pA⟩
      · exact ⟨Bool.false, fun m _ => by unfold Elixir.Module.Types.Descr.«empty?/1»; rfl⟩
      · exact ⟨Bool.false, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m (by omega); exact empty_any_node ha m'⟩
      · obtain ⟨b, hb⟩ := empty_pure pA []
        exact ⟨b, fun m hm => by unfold Elixir.Module.Types.Descr.«empty?/1»; exact hb m (by omega)⟩
    by_cases bt : b = .atom "term"
    · subst bt
      obtain ⟨s, hs⟩ := emptyOf ha
      exact ⟨s, fun m hm => by dsimp only; rw [disj_term_r]; exact hs m hm⟩
    by_cases at' : a = .atom "term"
    · subst at'
      obtain ⟨s, hs⟩ := emptyOf hb
      exact ⟨s, fun m hm => by dsimp only; rw [disj_term_l]; exact hs m hm⟩
    have stat : ∀ {x}, Pure t x → ∀ X, x = .map X → mapLookup X (.atom "dynamic") = none := by
      intro x hx X e
      rcases hx with rfl | hx | ⟨A, rfl, pA⟩
      · cases e
      · obtain ⟨S, rfl, -⟩ := hx.node; cases e
      · cases e; exact pA.static
    obtain ⟨A', cA, sA, nt, ea⟩ : ∃ A', PureC t A' ∧ (∀ X, A' = .map X → mapLookup X (.atom "dynamic") = none) ∧
        A' ≠ .atom "term" ∧ ∀ m', Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) a b =
          Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A' b := by
      rcases ha with rfl | ha | ⟨A, rfl, pA⟩
      · exact absurd rfl at'
      · exact ⟨_, expC ha, fun X e => by simp [expN] at e; subst e; simp [mapLookup], expN_ne_term _ _,
          fun m' => disj_node_l ha.node m' (expand_isT ha m') b bt (stat hb)⟩
      · exact ⟨_, Or.inr ⟨A, rfl, pA⟩, fun X e => by cases e; exact pA.static, by simp, fun _ => rfl⟩
    obtain ⟨B', cB, eb⟩ : ∃ B', PureC t B' ∧ ∀ m', Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A' b =
        Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A' B' := by
      rcases hb with rfl | hb | ⟨B, rfl, pB⟩
      · exact absurd rfl bt
      · exact ⟨_, expC hb, fun m' => disj_node_r hb.node m' (expand_isT hb m') A' nt sA⟩
      · exact ⟨_, Or.inr ⟨B, rfl, pB⟩, fun _ => rfl⟩
    obtain ⟨s, hs⟩ := disj cA cB
    exact ⟨s, fun m hm => by
      obtain ⟨m', rfl, -⟩ := succ m (by omega); dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩

section
variable {t : Term} {C : Term → Prop} {K : Nat}

/-! Classes with the node: operations on the node compute on its expansion, which the class holds. -/

/-- A class of maps with the node `t`. -/
def WithNode (t : Term) (C : Term → Prop) (a : Term) : Prop := C a ∨ IsT t a

theorem addOk (_hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ X, a = .map X)
    (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (ops : ElemOk C K) : ElemOk (WithNode t C) (K + 1) := by
  have succ : ∀ m, K + 1 ≤ m → ∃ m', m = m' + 1 ∧ K ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  -- The left and right types as types of the class.
  refine ⟨Or.inl ops.term, fun {a b} ha hb => ?_, fun {a} ha S => ?_, Or.inl ops.none, by omega⟩
  · by_cases bt : b = .atom "term"
    · subst bt; exact ⟨a, ha, fun m _ => inter_term_right _ _⟩
    by_cases at' : a = .atom "term"
    · subst at'; exact ⟨b, hb, fun m _ => by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl⟩
    obtain ⟨A, cA, nA, ea⟩ : ∃ A, C A ∧ A ≠ .atom "term" ∧ ∀ m, Elixir.Module.Types.Descr.«bare_intersection/2»
        (D (m + 1)) a b = Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A b := by
      rcases ha with ha | ha
      · exact ⟨a, ha, at', fun _ => rfl⟩
      · exact ⟨_, hexp ha, expN_ne_term _ _, fun m => inter_node_l ha.node m (expand_isT ha m) b bt⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m, Elixir.Module.Types.Descr.«bare_intersection/2»
        (D (m + 1)) A b = Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ => rfl⟩
      · exact ⟨_, hexp hb, fun m => inter_node_r hb.node m (expand_isT hb m) A nA⟩
    obtain ⟨c, hc, run⟩ := ops.inter cA cB
    exact ⟨c, Or.inl hc, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; rw [ea, eb]; exact run _ (by omega)⟩
  · rcases ha with ha | ha
    · obtain ⟨b, run⟩ := ops.empty ha S
      exact ⟨b, fun m hm => run m (by omega)⟩
    · exact ⟨_, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m hm; exact empty_node ha.node m' S⟩

theorem diff_none (d : Dispatcher) (a b : Term) (bt : b ≠ .atom "term") (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a b = .ok a := by
  rw [Elixir.Module.Types.Descr.«bare_difference/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) bt
    · simp_all [Erlang.erlang.«==/2»]
  all_goals simp_all [Erlang.erlang.«==/2»]

theorem addDiff (_hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ X, a = .map X)
    (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (hnone : C (.map [])) (dops : ElemDiff C K) :
    ElemDiff (WithNode t C) (K + 1) := by
  have succ : ∀ m, K + 1 ≤ m → ∃ m', m = m' + 1 ∧ K ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  refine ⟨fun {a b} ha hb => ?_⟩
  by_cases bt : b = .atom "term"
  · subst bt; exact ⟨_, Or.inl hnone, fun m _ => diff_term_right _ _⟩
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · exact ⟨a, ha, fun m _ => diff_none _ a b bt none⟩
  obtain ⟨B, cB, nB, sB, eb⟩ : ∃ B, C B ∧ B ≠ .atom "term" ∧ ¬Term.compare (Term.fuel B (.map [])) B (.map []) = .eq ∧
      ∀ m a, Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a B := by
    rcases hb with hb | hb
    · exact ⟨b, hb, bt, none, fun _ _ => rfl⟩
    · exact ⟨_, hexp hb, expN_ne_term _ _, expN_ne_none _ _, fun m a => diff_node_r hb.node m (expand_isT hb m) a⟩
  obtain ⟨A, cA, ea⟩ : ∃ A, C A ∧ ∀ m, Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a B =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) A B := by
    rcases ha with ha | ha
    · exact ⟨a, ha, fun _ => rfl⟩
    · exact ⟨_, hexp ha, fun m => diff_node_l ha.node m (expand_isT ha m) B nB sB⟩
  obtain ⟨c, hc, run⟩ := dops.diff cA cB
  exact ⟨c, Or.inl hc, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; rw [eb, ea]; exact run _ (by omega)⟩

theorem union_none (d : Dispatcher) (a b : Term) (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (none : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) : Elixir.Module.Types.Descr.«bare_union/2» d a b = .ok b := by
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem union_none_r (d : Dispatcher) (a b : Term) (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (na : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_union/2» d a b = .ok a := by
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem addFun (hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = none)
    (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (ops : ElemOk C K) (fops : ElemFun C K) :
    ElemFun (WithNode t C) (K + 1) := by
  have succ : ∀ m, K + 1 ≤ m → ∃ m', m = m' + 1 ∧ K ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  have static : ∀ {x}, WithNode t C x → ∀ X, x = .map X → mapLookup X (.atom "dynamic") = none := by
    intro x hx X e
    rcases hx with hx | hx
    · rcases hC hx with rfl | ⟨Y, rfl, sY⟩
      · cases e
      · cases e; exact sY
    · obtain ⟨S, rfl, -⟩ := hx.node; cases e
  refine ⟨fun {a} ha => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_⟩
  · rcases ha with ha | ha
    · exact fops.static ha
    · obtain ⟨S, rfl, -⟩ := ha.node; exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
  · -- Unions.
    by_cases at' : a = .atom "term"
    · subst at'; exact ⟨_, Or.inl ops.term, fun m _ => union_term_l _ _⟩
    by_cases bt : b = .atom "term"
    · subst bt; exact ⟨_, Or.inl ops.term, fun m _ => union_any_term _ _⟩
    by_cases na : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq
    · exact ⟨b, hb, fun m _ => union_none _ a b at' bt na⟩
    by_cases nb : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
    · exact ⟨a, ha, fun m _ => union_none_r _ a b at' bt na nb⟩
    obtain ⟨A, cA, nA, sA, ea⟩ : ∃ A, C A ∧ A ≠ .atom "term" ∧ ¬Term.compare (Term.fuel A (.map [])) A (.map []) = .eq ∧
        ∀ m, Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) a b =
          Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) A b := by
      rcases ha with ha | ha
      · exact ⟨a, ha, at', na, fun _ => rfl⟩
      · exact ⟨_, hexp ha, expN_ne_term _ _, expN_ne_none _ _,
          fun m => union_node_l ha.node m (expand_isT ha m) b bt nb⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m, Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) A b =
        Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) A B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ => rfl⟩
      · exact ⟨_, hexp hb, fun m => union_node_r hb.node m (expand_isT hb m) A nA sA⟩
    obtain ⟨c, hc, run⟩ := fops.union cA cB
    exact ⟨c, Or.inl hc, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; rw [ea, eb]; exact run _ (by omega)⟩
  · -- Inclusions.
    obtain ⟨A, cA, ea⟩ : ∃ A, C A ∧ ∀ m b, Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) A b := by
      rcases ha with ha | ha
      · exact ⟨a, ha, fun _ _ => rfl⟩
      · exact ⟨_, hexp ha, fun m b => sub_node_l ha.node m (expand_isT ha m) b⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m a, Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ _ => rfl⟩
      · exact ⟨_, hexp hb, fun m a => sub_node_r hb.node m (expand_isT hb m) a⟩
    obtain ⟨s, hs⟩ := fops.sub cA cB
    exact ⟨s, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩
  · -- Disjointness: nodes are not empty, and behave as their expansions otherwise.
    have nodeEmpty : ∀ {e}, IsT t e → BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«empty?/1» (D m) e) :=
      fun he => ⟨Bool.false, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m hm; exact empty_any_node he m'⟩
    by_cases bt : b = .atom "term"
    · subst bt
      rcases ha with ha | ha
      · exact (fops.disj ha ops.term).mono (by omega)
      · obtain ⟨s, hs⟩ := nodeEmpty ha
        exact ⟨s, fun m hm => by dsimp only; rw [disj_term_r]; exact hs m hm⟩
    by_cases at' : a = .atom "term"
    · subst at'
      rcases hb with hb | hb
      · exact (fops.disj ops.term hb).mono (by omega)
      · obtain ⟨s, hs⟩ := nodeEmpty hb
        exact ⟨s, fun m hm => by dsimp only; rw [disj_term_l]; exact hs m hm⟩
    obtain ⟨A, cA, nA, sA, ea⟩ : ∃ A, C A ∧ A ≠ .atom "term" ∧
        (∀ X, A = .map X → mapLookup X (.atom "dynamic") = none) ∧
        ∀ m, Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) a b =
          Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) A b := by
      rcases ha with ha' | ha'
      · exact ⟨a, ha', at', static (Or.inl ha'), fun _ => rfl⟩
      · exact ⟨_, hexp ha', expN_ne_term _ _, fun X e => by simp [expN] at e; subst e; simp [mapLookup],
          fun m => disj_node_l ha'.node m (expand_isT ha' m) b bt (static hb)⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m, Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) A b =
        Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) A B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ => rfl⟩
      · exact ⟨_, hexp hb, fun m => disj_node_r hb.node m (expand_isT hb m) A nA sA⟩
    obtain ⟨s, hs⟩ := fops.disj cA cB
    exact ⟨s, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩

end

theorem PureMap.noList {t : Term} {M : List (Term × Term)} (p : PureMap t M) : PureMap t (noList M) := by
  refine ⟨fun q h => p.keys q (by rw [← noList_lookup M q h]; exact h), fun name w h => ?_⟩
  have := noList_lookup M (.atom name) (by rw [h]; rfl)
  rw [this] at h
  exact p.fields _ _ h

theorem pureTail (t : Term) : TailOk (Pure t) := by
  intro e he
  rcases he with rfl | he | ⟨M, rfl, pM⟩
  · obtain ⟨T, run, bT⟩ := tail_term
    exact ⟨.map T, fun m _ => run (D m), Or.inr (Or.inr ⟨T, rfl, Basic.pure bT⟩)⟩
  · exact ⟨_, fun m hm => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact tail_node he.node m' (expand_isT he m'), Or.inr (Or.inr ⟨_, rfl, expN_pure he⟩)⟩
  · exact ⟨_, fun m _ => tail_map (D m) M, Or.inr (Or.inr ⟨_, rfl, pM.noList⟩)⟩

theorem addTail {t : Term} {C : Term → Prop} (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (tail : TailOk C) :
    TailOk (WithNode t C) := by
  intro e he
  rcases he with he | he
  · obtain ⟨e', run, he'⟩ := tail e he
    exact ⟨e', run, Or.inl he'⟩
  · exact ⟨_, fun m hm => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact tail_node he.node m' (expand_isT he m'), Or.inl (hexp he)⟩

/-- The expansion of a node nests its elements. -/
theorem expN_nest {E : Term → Prop} (hterm : E (.atom "term")) {e : Term} (he : E e) (k : Int) :
    NestC E (expN e k) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?] at h
    by_cases t₁ : Term.compareExact (Term.fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₁)))))
    · by_cases t₂ : Term.compareExact (Term.fuel q (.atom "atom")) q (.atom "atom") = .eq
      · exact Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₂))
      · simp [t₁, t₂] at h
  · by_cases t₁ : name = "tuple"
    · subst t₁
      simp [mapLookup] at h
      subst h
      refine Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Bdd.leaf_iff.mpr ⟨⟨k, "closed", [.atom "term", e], rfl, Or.inr rfl,
        fun x mx => ?_⟩, fun ⟨_, h⟩ => by simp [Term.list] at h⟩)⟩))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mx
      rcases mx with rfl | rfl
      · exact hterm
      · exact he
    · by_cases t₂ : name = "atom"
      · subst t₂
        simp [mapLookup] at h
        subst h
        exact Or.inl ⟨by decide, by decide, by decide, by decide, Or.inr (Or.inl ⟨rfl,
          ⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil",
          by simp [amemV, mapLookup]⟩)⟩
      · simp [mapLookup, t₁, t₂] at h

/-- Nested element types of a depth with the recursive node `t`, closed under intersection and difference: at
depth 0, they nest the node, its expansion, and their combinations with basic types. -/
def Closed (t : Term) : Nat → Term → Prop
  | 0 => WithNode t (NestC (Pure t))
  | d + 1 => WithNode t (NestC (Closed t d))

theorem closed_node {t e : Term} (he : IsT t e) : ∀ d, Closed t d e
  | 0 => Or.inr he
  | _ + 1 => Or.inr he

/-- Adding the node to nested types of elements holding it. -/
theorem nest_node {t : Term} {E : Term → Prop} {K : Nat} (hterm : E (.atom "term")) (hnode : ∀ {e}, IsT t e → E e)
    (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (hnone : E (.map [])) (tail : TailOk E) :
    ElemOk (WithNode t (NestC E)) (K + 15) ∧ ElemDiff (WithNode t (NestC E)) (K + 15) ∧
      ElemFun (WithNode t (NestC E)) (K + 15) ∧ WithNode t (NestC E) (.map []) ∧ TailOk (WithNode t (NestC E)) := by
  have hC : ∀ {a}, NestC E a → a = .atom "term" ∨ ∃ X, a = .map X := fun {a} ha => by
    rcases ha with rfl | ⟨X, rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, rfl⟩
  have hS : ∀ {a}, NestC E a → a = .atom "term" ∨ ∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = none :=
    fun {a} ha => by
      rcases ha with rfl | ⟨X, rfl, v⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, rfl, v.static⟩
  have hexp : ∀ {e}, IsT t e → NestC E (expN e (keyOf t)) := fun he => expN_nest hterm (hnode he) _
  have n₁ := (nestOk ops dops fops hnone tail).mono (show K + 8 ≤ K + 14 by omega)
  have n₂ := (nestDiff hterm K).mono (show K + 3 ≤ K + 14 by omega)
  have n₃ := nestFun ops dops fops hnone tail
  exact ⟨addOk hC hexp n₁, addDiff hC hexp nest_none n₂, addFun hS hexp n₁ n₃, Or.inl nest_none,
    addTail hexp (tail_nest hterm)⟩

theorem closed_ok (t : Term) : ∀ d, ElemOk (Closed t d) (23 + 15 * d) ∧ ElemDiff (Closed t d) (23 + 15 * d) ∧
    ElemFun (Closed t d) (23 + 15 * d) ∧ Closed t d (.map []) ∧ TailOk (Closed t d)
  | 0 => nest_node (Or.inl rfl) (fun he => Or.inr (Or.inl he)) ((pureOk t).mono (by omega))
      ((pureDiff t).mono (by omega)) (pureFun t) (pure_none t) (pureTail t)
  | d + 1 => by
    obtain ⟨ops, dops, fops, hnone, tail⟩ := closed_ok t d
    have := nest_node ops.term (fun he => closed_node he d) ops dops fops hnone tail
    rw [show 23 + 15 * (d + 1) = 23 + 15 * d + 15 by omega]
    exact this

theorem OField.mono {ok ok' : Term → Prop} (h : ∀ t, ok t → ok' t) {x : Term} (f : OField ok x) : OField ok' x := by
  rcases f with top | b
  · exact Or.inl top
  · exact Or.inr (b.mono h)

theorem FField.mono {E E' : Term → Prop} (h : ∀ t, E t → E' t) {w : Term} (f : FField E w) : FField E' w := by
  obtain ⟨p, R, rfl, b⟩ := f
  exact ⟨p, R, rfl, fun q v hv => (b q v hv).mono fun t ⟨n, e, k, args, ret, ht, len, ha, hr⟩ =>
    ⟨n, e, k, args, ret, ht, len, fun a ma => h a (ha a ma), h ret hr⟩⟩

/-- The nested types of the specification are closed nested types. -/
theorem nest_closed (t : Term) : ∀ d e, Nest t d e → Closed t d e
  | 0, _, h => by
    rcases h with h | h
    · rcases elem_lelem h with rfl | ⟨M, rfl, bM⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨M, rfl, Basic.nest (Or.inl rfl) bM⟩)
    · exact Or.inr h
  | d + 1, _, h => by
    rcases h with h | h
    rotate_left
    · exact Or.inr h
    rcases h with rfl | ⟨X, rfl, v⟩
    · exact Or.inl (Or.inl rfl)
    refine Or.inl (Or.inr ⟨X, rfl, ⟨v.keys, fun name w h => ?_⟩⟩)
    rcases v.keys (.atom name) (by rw [h]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨by decide, by decide, by decide, by decide, Or.inl ⟨rfl, v.bitmap w h⟩⟩
    · obtain ⟨p, S, rfl, set⟩ := v.atom w h
      refine Or.inl ⟨by decide, by decide, by decide, by decide, Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, ?_⟩)⟩
      exact atom_nonempty p S fun hp => v.atomUnion S (by subst hp; simpa using h)
    · exact Or.inr (Or.inl ⟨rfl, (v.funs w h).mono (nest_closed t d)⟩)
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))
      rcases v.lists w h with ⟨k, rfl⟩ | b
      · exact Bdd.leaf_iff.mpr ⟨k, _, _, rfl, (closed_ok t d).1.term, (closed_ok t d).1.term⟩
      · exact b.mono fun x ok => by
          obtain ⟨-, k, a, b, rfl, ha, hb⟩ := ok
          exact ⟨k, a, b, rfl, nest_closed t d a ha, nest_closed t d b hb⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, OField.mono (fun x ok => ok.mono (nest_closed t d)) (v.tuples w h)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, OField.mono (fun x ok => ok.mono (nest_closed t d)) (v.maps w h)⟩)))

/-! The law. -/

theorem Negatable.sem {X : List (Term × Term)} (v : Negatable E X) : Sem E X := by
  refine ⟨fun q h => ?_, fun name x hx => ?_⟩
  · rcases v.keys q h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
  · rcases v.keys (.atom name) (by simp [hx]) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨rfl, v.bitmap x hx⟩
    · obtain ⟨p, S, rfl, set⟩ := v.atom x hx
      refine Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, atom_nonempty p S fun hp => v.atomUnion S ?_⟩)
      subst hp
      simpa using hx
    · obtain ⟨pos, R, rfl⟩ := v.funs x hx
      exact Or.inr (Or.inr (Or.inl ⟨rfl, pos, R, rfl, fun q w h => v.arities _ hx _ R rfl q w h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (v.lists x hx).list⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, v.tuples x hx⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, v.maps x hx⟩))))

theorem negation_none_term (δ : Nat) : Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map []) = .ok (.atom "term") := by
  simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2»]

theorem equal_self (δ : Nat) (x : Term) : Elixir.Module.Types.Descr.«equal?/2» (D (δ + 100)) x x = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«equal?/2», Erlang.erlang.«==/2», Std.ReflCmp.compare_self, Lynx.Except.orElse,
    Term.true]

/-- De Morgan's law for any two types of bitmaps, atoms, functions, lists, tuples, and maps. -/
theorem de_morgan_union_law (δ : Nat) (ops : ElemOk E K) (dops : ElemDiff E K) (hK : K ≤ δ + 90) (L R : List (Term × Term)) (vL : Negatable E L) (vR : Negatable E R) :
    (do
      let u ← Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map L) (.map R)
      let a ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) u
      let nl ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map L)
      let nr ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map R)
      let b ← Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) nl nr
      Elixir.Module.Types.Descr.«equal?/2» (D (δ + 100)) a b) = .ok (.atom "true") := by
  by_cases eL : L = [] <;> by_cases eR : R = []
  · subst eL eR
    have union : Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map []) (.map []) = .ok (.map []) := by
      unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
    have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.atom "term") (.atom "term") =
        .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    simp [union, negation_none_term, inter, equal_self]
  · subst eL
    obtain ⟨N, neg, -⟩ := sem_neg δ ops.term R vR.sem eR
    have union : Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map []) (.map R) = .ok (.map R) := by
      unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
    have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.atom "term") (.map N) = .ok (.map N) := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    simp [union, neg, negation_none_term, inter, equal_self]
  · subst eR
    obtain ⟨N, neg, -⟩ := sem_neg δ ops.term L vL.sem eL
    have union : Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map L) (.map []) = .ok (.map L) := by
      unfold Elixir.Module.Types.Descr.«bare_union/2»
      cases L with
      | nil => exact absurd rfl eL
      | cons e rest => simp [Erlang.erlang.«==/2»]
    have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.map N) (.atom "term") = .ok (.map N) := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    simp [union, neg, negation_none_term, inter, equal_self]
  · obtain ⟨U, A, NL, NR, B, union, negU, negL, negR, inter, sub₁, sub₂⟩ := de_morgan_sem δ ops dops hK L R vL.sem vR.sem eL eR
    simp only [union, negU, negL, negR, inter, Lynx.Except.ok_bind]
    by_cases c : Term.compare (Term.fuel (.map A) (.map B)) (.map A) (.map B) = .eq <;>
      simp [Elixir.Module.Types.Descr.«equal?/2», sub₁, sub₂, Lynx.Except.orElse, Lynx.Except.andAlso,
        Erlang.erlang.«==/2», c, Term.true, Term.false]

end Elixir.STTDescrProofsTest
