namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! `subtype?/2` is sound on basic types: a `true` answer means inclusion. -/

/-- A walk over the fields of a type that answers `true` checked each field. -/
theorem iterator_sound (d : Dispatcher) (B : List (Term × Term)) :
    ∀ es : List (Term × Term),
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» d it (.map B) (.map [])) =
        .ok (.atom "true") → ∀ e ∈ es, KeySub d B e.1 e.2 := by
  intro es
  induction es with
  | nil => intro _ e m; simp at m
  | cons e rest ih =>
    intro h e' m
    simp only [List.map, Term.list, Erlang.maps.«next/1», Lynx.Except.ok_bind] at h
    rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def] at h
    simp only [Lynx.Except.andAlso_eq_true] at h
    obtain ⟨here, tail⟩ := h
    rcases List.mem_cons.mp m with rfl | m
    · cases hB : mapLookup B e'.1 with
      | none =>
        simp [getMapKeys_single, hB] at here
        exact Or.inr ⟨hB, here⟩
      | some y =>
        simp only [getMapKeys_single, hB, Option.toList_some] at here
        cases hw : Elixir.Module.Types.Descr.«bare_difference/3» d e'.1 e'.2 y with
        | error x => simp [hw] at here
        | ok w =>
          simp only [hw, Lynx.Except.ok_bind, Lynx.Except.orElse_eq_true] at here
          refine Or.inl ⟨y, w, hB, hw, ?_⟩
          rcases here with h | ⟨-, h⟩
          · by_cases h₀ : w = .integer 0
            · exact Or.inl h₀
            · by_cases h₁ : w = .atom "bdd_bot"
              · exact Or.inr (Or.inl h₁)
              · simp [isMember, h₀, h₁] at h
          · exact Or.inr (Or.inr h)
    · exact ih tail e' m

theorem lookup_entry {A : List (Term × Term)} {q x : Term} (h : mapLookup A q = some x) :
    ∃ e ∈ mapEntries A, compareExact (fuel q e.1) q e.1 = .eq ∧ e.2 = x := by
  rw [← mapLookup_mapEntries] at h
  simp only [mapLookup, Option.map_eq_some_iff] at h
  obtain ⟨e, hit, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some hit, by simpa using List.find?_some hit, rfl⟩

end Elixir.STTDescrProofsTest
