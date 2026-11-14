/-- Maps without visible keys hold no entries. -/
theorem nil_of_lookup_none (entries : List (Term × Term))
    (none : ∀ q, mapLookup entries q = Option.none) : entries = [] := by
  cases entries with
  | nil => rfl
  | cons entry rest =>
    have := none entry.1
    simp [mapLookup] at this

/-- Intersecting a map of fields with the empty type keeps no field. -/
theorem symmetrical_none (d : Dispatcher) (X : List (Term × Term)) :
    Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map X) (.map [])
      (.function "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) = .ok (.map []) := by
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup d "Elixir.Module.Types.Descr"
    "bare_intersection" #[] X [] (fun _ _ _ => .nil) (by intro e _ y hy; simp [mapLookup] at hy)
  obtain rfl : I = [] := nil_of_lookup_none I fun q => by
    rw [lookI]
    cases (mapEntries X).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) <;> simp [mapLookup]
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup d "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] [] kept (by intro e member; simp at member)
  obtain rfl : out = [] := nil_of_lookup_none out fun q => by rw [lookO]; simp
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [runI, runO]

/-- The intersection of a static type with the empty type is empty, whatever its fields hold. -/
theorem intersection_none_static (depth : Nat) (X : List (Term × Term))
    (static : mapLookup X (.atom "dynamic") = Option.none) :
    Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map X) (.map []) = .ok (.map []) := by
  have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, static, absent, symmetrical_none]

/-- The intersection of a gradual type with the empty type is empty, when its dynamic
part is the top type or a map of fields. -/
theorem intersection_none_dynamic (depth : Nat) (X : List (Term × Term)) (Dy : Term)
    (dynamic : mapLookup X (.atom "dynamic") = some Dy)
    (inner : Dy = .atom "term" ∨ ∃ Y, Dy = .map Y) :
    Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map X) (.map []) = .ok (.map []) := by
  have part : Elixir.Module.Types.Descr.«bare_intersection/3»
      (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom "dynamic") Dy (.map []) =
        .ok (.integer 0) := by
    simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]
    unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»
    rcases inner with rfl | ⟨Y, rfl⟩
    · simp [Erlang.erlang.«==/2»]
    · simp [symmetrical_none, Erlang.erlang.«==/2»]
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
    "bare_intersection" #[] X [(.atom "dynamic", .map [])] (fun _ _ _ => .integer 0) (by
      intro e me y hy
      simp [mapLookup] at hy
      obtain ⟨key, rfl⟩ := hy
      have hx := mapLookup_of_mem_mapEntries me
      rw [key, dynamic] at hx
      cases hx
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, key, part])
  have zero : ∀ e ∈ mapEntries I, e.2 = .integer 0 := by
    intro e me
    have hx := mapLookup_of_mem_mapEntries me
    rw [lookI] at hx
    split at hx
    · simp at hx
      exact hx.2.symm
    · cases hx
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  obtain rfl : out = [] := nil_of_lookup_none out fun q => by
    rw [lookO]
    cases found : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rfl
    | some e => simp [kept, zero e (List.mem_of_find?_eq_some found)]
  have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, dynamic, absent, Erlang.maps.«put/3»]
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [runI, runO]

/-- The empty type is empty. -/
theorem empty_none (d : Dispatcher) :
    Elixir.Module.Types.Descr.«empty?/1» d (.map []) = .ok Term.true := by
  simp only [Elixir.Module.Types.Descr.«empty?/1»]
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [getMapKeys_single, mapLookup, Erlang.erlang.«==/2», Term.true]

