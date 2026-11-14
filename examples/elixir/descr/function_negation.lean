/-- Function types are unions (true) or negations (false) of maps from arities to BDDs. -/
abbrev FunField (w : Term) : Prop :=
  ∃ (pos : Bool) (R : List (Term × Term)), w = .tuple #[.atom (if pos then "union" else "negation"), .map R]

/-- A BDD without its own copy is bottom. -/
theorem bdd_difference_self (b : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/2» b b = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_difference/2»
  simp [Erlang.erlang.«=:=/2»]

/-- Each step of `fun_repr_difference/2` removes an arity whose BDD the accumulator holds as is. -/
theorem repr_step (acc : List (Term × Term)) (key bdd : Term)
    (same : ∀ v, mapLookup acc key = some v → v = bdd) :
    ∃ next, Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3» key bdd (.map acc) = .ok (.map next) ∧
      (∀ q, compareExact (fuel q key) q key ≠ .eq → mapLookup next q = mapLookup acc q) ∧
      (∀ q, compareExact (fuel q key) q key = .eq → mapLookup next q = Option.none) := by
  unfold Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3»
  cases found : mapLookup acc key with
  | none =>
    refine ⟨acc, by simp [getMapKeys_single, found], fun q _ => rfl, fun q eq => ?_⟩
    rw [mapLookup_congr eq]; exact found
  | some v =>
    obtain rfl := same v found
    refine ⟨acc.filter fun e => compareExact (fuel key e.1) key e.1 != .eq, ?_, fun q ne => ?_, fun q eq => ?_⟩
    · simp [getMapKeys_single, found, bdd_difference_self, isMember, Erlang.maps.«remove/2»]
    · rw [mapLookup_filter]; simp [ne]
    · rw [mapLookup_filter]; simp [eq]

/-- Folding `fun_repr_difference/2` over arities whose BDDs the accumulator holds as is
removes them. -/
theorem repr_fold (n : Nat) (es acc : List (Term × Term))
    (distinct : es.Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq))
    (same : ∀ e ∈ es, ∀ v, mapLookup acc e.1 = some v → v = e.2) :
    ∃ M, es.foldlM (fun acc entry =>
        (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table n)
          (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
          #[entry.1, entry.2, acc] : Except Exception Term)) (.map acc) = .ok (.map M) ∧
      ∀ q, mapLookup M q =
        match es.find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some _ => Option.none
        | none => mapLookup acc q := by
  induction es generalizing acc with
  | nil => exact ⟨acc, rfl, fun q => rfl⟩
  | cons e rest ih =>
    have apart := List.pairwise_cons.mp distinct
    obtain ⟨next, run₁, other, gone⟩ := repr_step acc e.1 e.2 (same e (List.mem_cons_self ..))
    have step : (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table n)
        (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
        #[e.1, e.2, .map acc] : Except Exception Term) = .ok (.map next) := by
      rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_difference/2-fun-0-/3».pure, run₁]
    obtain ⟨M, run, look⟩ := ih next apart.2 (by
      intro e' member v found
      rw [other e'.1 (fun s => apart.1 e' member (Lynx.Term.compareExact_eq_symm s))] at found
      exact same e' (List.mem_cons_of_mem _ member) v found)
    refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_⟩
    rw [look q]
    by_cases s : compareExact (fuel q e.1) q e.1 = .eq
    · have absent : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) = Option.none := by
        rw [List.find?_eq_none]
        intro p member hit
        exact apart.1 p member
          (Lynx.Term.compareExact_eq_trans (Lynx.Term.compareExact_eq_symm s) (of_decide_eq_true hit))
      simp only [absent, List.find?_cons, s, decide_true]
      exact gone q s
    · simp only [List.find?_cons, s, decide_false]
      cases rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) with
      | none => exact other q s
      | some _ => rfl

/-- The difference of a map of arities to BDDs with a map of the same lookups is empty. -/
theorem repr_cancel (n : Nat) (R M : List (Term × Term)) (lookups : ∀ q, mapLookup M q = mapLookup R q) :
    Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
      (.map R) (.map M) = .ok (.map []) := by
  obtain ⟨D, run, look⟩ := repr_fold n (mapEntries M) R (mapEntries_distinct M) (by
    intro e member v found
    rw [← lookups, mapLookup_of_mem_mapEntries member] at found
    exact (Option.some.inj found).symm)
  obtain rfl : D = [] := nil_of_lookup_none D fun q => by
    rw [look q]
    cases hit : (mapEntries M).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | some _ => rfl
    | none =>
      have : mapLookup (mapEntries M) q = Option.none := by simp [mapLookup, hit]
      rw [mapLookup_mapEntries, lookups] at this
      exact this
  simp only [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
  simpa using run

/-- A function type does not intersect its negation. -/
theorem fun_negation (n : Nat) (w : Term) (field : FunField w) :
    ∃ y, Elixir.Module.Types.Descr.«fun_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
        (.tuple #[.atom "negation", .map []]) w = .ok y ∧
      (y = .integer 0 ∨ ∀ m, Elixir.Module.Types.Descr.«fun_intersection/2»
        (Dispatcher.ofTable Erlang.program.fun_table m) w y = .ok (.integer 0)) := by
  obtain ⟨pos, R, rfl⟩ := field
  cases pos with
  | true =>
    obtain ⟨out, merge, look⟩ := Erlang.maps.merge_with_lookup (Dispatcher.ofTable Erlang.program.fun_table n)
      "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] R (fun _ _ _ => .nil)
      (by intro e _ v found; simp [mapLookup] at found)
    have same : ∀ q, mapLookup out q = mapLookup R q := by
      intro q
      rw [look q, ← mapLookup_mapEntries R]
      simp only [mapLookup]
      cases (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) <;> simp
    refine ⟨.tuple #[.atom "negation", .map out], ?_, Or.inr fun m => ?_⟩
    · simp [Elixir.Module.Types.Descr.«fun_difference/2», Elixir.Module.Types.Descr.«fun_repr_union/2»,
        Elixir.Module.Types.Descr.«symmetrical_merge/3», merge, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · simp [Elixir.Module.Types.Descr.«fun_intersection/2», repr_cancel m R out same, Erlang.erlang.«==/2»,
        Erlang.erlang.«map_size/1», Lynx.Except.andAlso]
  | false =>
    have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
        (.map R) (.map []) = .ok (.map R) := by
      simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
    by_cases empty : ((R.map Prod.fst).eraseDupsBy (fun a b => compareExact (fuel a b) a b == .eq)).length = 0
    · refine ⟨.integer 0, ?_, Or.inl rfl⟩
      simp [Elixir.Module.Types.Descr.«fun_difference/2», keep, Erlang.erlang.«==/2»,
        Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
    · refine ⟨.tuple #[.atom "union", .map R], ?_, Or.inr fun m => ?_⟩
      · simp [Elixir.Module.Types.Descr.«fun_difference/2», keep, Erlang.erlang.«==/2»,
          Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
      · simp [Elixir.Module.Types.Descr.«fun_intersection/2», repr_cancel m R R (fun _ => rfl),
          Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]
