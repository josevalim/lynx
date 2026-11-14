/-! Map fields. -/

/-- Atom keys are found exactly. -/
theorem find_atom (X : List (Term × Term)) (name : String) :
    (mapEntries X).find? (fun p => decide (compareExact (fuel (.atom name) p.1) (.atom name) p.1 = .eq)) =
      (mapLookup X (.atom name)).map fun v => (.atom name, v) := by
  rw [← mapLookup_mapEntries]
  simp only [mapLookup]
  cases hit : (mapEntries X).find? (fun p => decide (compareExact (fuel (.atom name) p.1) (.atom name) p.1 = .eq)) with
  | none => rfl
  | some p =>
    have same : compareExact (fuel (.atom name) p.1) (.atom name) p.1 = .eq := by simpa using List.find?_some hit
    have key : p.1 = .atom name := (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm same)
    obtain ⟨k₀, v₀⟩ := p
    simp only at key
    subst key
    rfl

/-! Unions. -/

/-- The union of two atom types holds the atoms of either. -/
theorem atom_union (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
    (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
    (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
    ∃ (p : Bool) (E : List (Term × Term)),
      Elixir.Module.Types.Descr.«atom_union/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
        .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
      Erlang.sets.elements? (.map E) = some E ∧
      ∀ q, (p == (mapLookup E q).isSome) =
        ((p₁ == (mapLookup S₁ q).isSome) || (p₂ == (mapLookup S₂ q).isSome)) := by
  cases p₁ <;> cases p₂
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
    refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
    refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
    refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
    refine ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl

