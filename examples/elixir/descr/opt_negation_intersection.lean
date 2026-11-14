open BddProofs

theorem any_key (X : List (Term × Term)) (name : String) :
    (X.any fun e => compareExact (fuel (.atom name) e.1) (.atom name) e.1 == .eq) = (mapLookup X (.atom name)).isSome := by
  rw [Bool.eq_iff_iff, mapLookup_isSome]
  simp

theorem Valid.absent {V : List (Term × Term)} (valid : Valid V) (name : String) (nb : name ≠ "bitmap")
    (na : name ≠ "atom") : mapLookup V (.atom name) = Option.none := by
  cases h : mapLookup V (.atom name) with
  | none => rfl
  | some w =>
    rcases valid.keys (.atom name) (by rw [h]; rfl) with e | e
    · cases e; exact absurd rfl nb
    · cases e; exact absurd rfl na

theorem Valid.negatable {V : List (Term × Term)} (valid : Valid V) : Negatable E V := by
  refine ⟨fun q h => ?_, valid.bitmap, valid.atom, valid.atomUnion, fun w h => ?_, fun w h => ?_, fun w h => ?_,
    fun w h => ?_, fun w h => ?_⟩
  · rcases valid.keys q h with rfl | rfl <;> simp
  · simp [valid.absent "fun" (by decide) (by decide)] at h
  · simp [valid.absent "fun" (by decide) (by decide)] at h
  · simp [valid.absent "list" (by decide) (by decide)] at h
  · simp [valid.absent "tuple" (by decide) (by decide)] at h
  · simp [valid.absent "map" (by decide) (by decide)] at h

theorem difference_term_term (d : Dispatcher) (x S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» d x (.atom "term") S = .ok (.map []) := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  rfl

theorem difference_term_none (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» d (.atom "term") (.map []) S = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  simp [Erlang.erlang.«==/2»]

end Elixir.STTDescrProofsTest
