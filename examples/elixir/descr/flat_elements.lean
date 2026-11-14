namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Flat element types: the bottom nesting level, whose values are bits, atoms, and the kinds of other values. -/

/-- Maps of size one hold a single key, up to exact equality. -/
theorem size_one_keys {A : List (Term × Term)} (h : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    {q q' x x' : Term} (hx : mapLookup A q = some x) (hx' : mapLookup A q' = some x') : compareExact (fuel q q') q q' = .eq := by
  simp only [Erlang.erlang.«map_size/1», Except.ok.injEq, Term.integer.injEq] at h
  have mem : ∀ {q x}, mapLookup A q = some x → ∃ e ∈ A, compareExact (fuel q e.1) q e.1 = .eq := by
    intro q x hq
    simp only [mapLookup, Option.map_eq_some_iff] at hq
    obtain ⟨e, he, -⟩ := hq
    exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩
  obtain ⟨e, me, qe⟩ := mem hx
  obtain ⟨e', me', qe'⟩ := mem hx'
  cases A with
  | nil => simp at me
  | cons e₀ rest =>
    simp only [List.map_cons, List.eraseDupsBy_cons, List.length_cons] at h
    have none : List.filter (fun b => decide ((compareExact (fuel b e₀.1) b e₀.1 == .eq) = Bool.false)) (rest.map Prod.fst) = [] := by
      cases hf : List.filter (fun b => decide ((compareExact (fuel b e₀.1) b e₀.1 == .eq) = Bool.false)) (rest.map Prod.fst) with
      | nil => rfl
      | cons a as =>
        exfalso
        rw [hf, List.eraseDupsBy_cons] at h
        simp at h
        omega
    have all : ∀ f ∈ e₀ :: rest, compareExact (fuel f.1 e₀.1) f.1 e₀.1 = .eq := by
      intro f mf
      rcases List.mem_cons.mp mf with rfl | mf
      · simp
      · have := List.filter_eq_nil_iff.mp none f.1 (List.mem_map.mpr ⟨f, mf, rfl⟩)
        simpa using this
    exact Lynx.Term.compareExact_eq_trans (Lynx.Term.compareExact_eq_trans qe (all e me))
      (Lynx.Term.compareExact_eq_symm (Lynx.Term.compareExact_eq_trans qe' (all e' me')))

theorem lh_top61 : lh (.tuple #[.integer 61102469, .atom "open", .nil]) = 0 := lh_leaf_top _

theorem safeF_of {N : Nat} {S : List (Term × Term)} (h : SafeN N S) : SafeF S := by
  refine ⟨S, rfl, fun e me kind hit => ?_⟩
  obtain ⟨k, b, e₁, one, -⟩ := h e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
  rw [lh_top61] at this
  omega

end Elixir.STTDescrProofsTest.Nest
