namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! The top type in the negation and De Morgan laws of the plain operations. -/

/-- Intersecting the empty type with a map of fields keeps no field. -/
theorem symmetrical_none_left (d : Dispatcher) (X : List (Term × Term)) :
    Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map []) (.map X)
      (.function "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) = .ok (.map []) := by
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup d "Elixir.Module.Types.Descr"
    "bare_intersection" #[] [] X (fun _ _ _ => .nil) (by intro e me; simp at me)
  obtain rfl : I = [] := nil_of_lookup_none I fun q => by rw [lookI]; simp
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup d "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] [] kept (by intro e member; simp at member)
  obtain rfl : out = [] := nil_of_lookup_none out fun q => by rw [lookO]; simp
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [runI, runO]

theorem intersection_none_left (depth : Nat) (X : List (Term × Term))
    (static : mapLookup X (.atom "dynamic") = Option.none) :
    Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map []) (.map X) = .ok (.map []) := by
  have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, static, absent, symmetrical_none_left]

theorem negation_term_none (d : Dispatcher) :
    Elixir.Module.Types.Descr.«bare_negation/1» d (.atom "term") = .ok (.map []) := by
  simp [Elixir.Module.Types.Descr.«bare_negation/1»]

/-- The negation of a negatable type, or of the top type, is a static map of fields. -/
theorem negation_static (δ : Nat) {t : Term} {n : Nat} (_hn : 23 + 15 * n ≤ δ + 90) {a : Term}
    (ha : a = .atom "term" ∨ ∃ X, a = .map X ∧ Negatable (Nest t n) X) :
    (∃ N, Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) a = .ok (.map N) ∧
      mapLookup N (.atom "dynamic") = Option.none) ∨
    Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) a = .ok (.atom "term") := by
  obtain ⟨ops, -, -, -, -⟩ := closed_ok t n
  rcases ha with rfl | ⟨X, rfl, v⟩
  · exact Or.inl ⟨[], negation_term_none _, rfl⟩
  by_cases e : X = []
  · subst e; exact Or.inr (negation_none_term δ)
  obtain ⟨N, neg, sN, -⟩ := sem_neg δ ops.term X (v.mono (nest_closed t n)).sem e
  exact Or.inl ⟨N, neg, sN.static⟩

/-- De Morgan's law for any two negatable types or top types. -/
theorem de_morgan_union_any (δ : Nat) {t : Term} {n : Nat} (hn : 23 + 15 * n ≤ δ + 90) {l r : Term}
    (hl : l = .atom "term" ∨ ∃ L, l = .map L ∧ Negatable (Nest t n) L)
    (hr : r = .atom "term" ∨ ∃ R, r = .map R ∧ Negatable (Nest t n) R) :
    (do
      let u ← Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) l r
      let a ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) u
      let nl ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) l
      let nr ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) r
      let b ← Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) nl nr
      Elixir.Module.Types.Descr.«equal?/2» (D (δ + 100)) a b) = .ok (.atom "true") := by
  rcases hl with rfl | ⟨L, rfl, vL⟩
  · rcases negation_static δ hn hr with ⟨N, neg, sN⟩ | neg
    · simp [union_term_l, negation_term_none, neg, intersection_none_left (δ + 99) N sN, equal_self]
    · simp [union_term_l, negation_term_none, neg, inter_term_right, equal_self]
  rcases hr with rfl | ⟨R, rfl, vR⟩
  · rcases negation_static δ hn (Or.inr ⟨L, rfl, vL⟩) with ⟨N, neg, sN⟩ | neg
    · simp [union_term_r, negation_term_none, neg, intersection_none_static (δ + 99) N sN, equal_self]
    · simp [union_term_r, negation_term_none, neg, inter_term_left, equal_self]
  obtain ⟨ops, dops, -, -, -⟩ := closed_ok t n
  exact de_morgan_union_law δ ops dops (by omega) L R (vL.mono (nest_closed t n)) (vR.mono (nest_closed t n))

end Elixir.STTDescrProofsTest
