/-! Intersections. -/

/-- Unions of atoms are dropped when empty. -/
theorem union_or_empty (E : List (Term × Term)) :
    (∃ s : Nat, s ≠ 0 ∧ Erlang.sets.«size/1» (.map E) = .ok (.integer s)) ∨
      (Erlang.sets.«size/1» (.map E) = .ok (.integer 0) ∧ ∀ q, mapLookup E q = none) := by
  cases h : ((E.map Prod.fst).eraseDupsBy (fun a b => compareExact (fuel a b) a b == .eq)).length with
  | zero =>
    have empty : Erlang.sets.«size/1» (.map E) = .ok (.integer 0) := by simp [Erlang.sets.«size/1», h]
    exact Or.inr ⟨empty, fun q => Erlang.sets.size_empty E q empty⟩
  | succ s => exact Or.inl ⟨s + 1, by omega, by simp [Erlang.sets.«size/1», h]⟩

/-- The intersection of two atom types holds the atoms of both, and is `0` when empty. -/
theorem atom_intersection (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
    (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
    (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
    (∃ (p : Bool) (E : List (Term × Term)),
      Elixir.Module.Types.Descr.«atom_intersection/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
        .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
      Erlang.sets.elements? (.map E) = some E ∧
      -- Intersections are unions unless both types are negations, and are not empty.
      p = (p₁ || p₂) ∧ (p = Bool.true → E ≠ []) ∧
      ∀ q, (p == (mapLookup E q).isSome) =
        ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome))) ∨
    (Elixir.Module.Types.Descr.«atom_intersection/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .ok (.integer 0) ∧
      ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) := by
  cases p₁ <;> cases p₂
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
    refine Or.inl ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE,
      Erlang.erlang.«==/2»], setE, rfl, fun negated => Bool.noConfusion negated, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp

/-- The intersection keeps the fields that are neither `0` nor `bdd_bot`. -/
def kept (entry : Term × Term) : Bool :=
  !decide (compareExact (fuel entry.2 (.integer 0)) entry.2 (.integer 0) = .eq) &&
    !decide (compareExact (fuel entry.2 (.atom "bdd_bot")) entry.2 (.atom "bdd_bot") = .eq)

theorem keep_field (key value : Term) :
    Elixir.Module.Types.Descr.«-symmetrical_intersection/3-fun-0-/2» key value =
      .ok (if kept (key, value) then Term.true else Term.false) := by
  by_cases zero : compareExact (fuel value (.integer 0)) value (.integer 0) = .eq <;>
    by_cases bot : compareExact (fuel value (.atom "bdd_bot")) value (.atom "bdd_bot") = .eq <;>
    simp [Elixir.Module.Types.Descr.«-symmetrical_intersection/3-fun-0-/2», kept, Erlang.erlang.«=:=/2»,
      Erlang.erlang.«=/=/2», zero, bot, Term.true, Term.false]

