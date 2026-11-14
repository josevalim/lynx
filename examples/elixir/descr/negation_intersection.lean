/-- Symmetrical intersections whose common fields intersect to what remains of a type and its negation. -/
theorem symmetrical_gone (depth : Nat) (name : String) (captures : Array Term) (L R : List (Term × Term))
    (g : Term → Term → Term → Term)
    (common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        (.function "Elixir.Module.Types.Descr" name 3 captures) #[q, x, y] = .ok (g q x y) ∧
      (kept (q, g q x y) = Bool.true → Gone K q (g q x y))) :
    ∃ I, Elixir.Module.Types.Descr.«symmetrical_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
      (.map L) (.map R) (.function "Elixir.Module.Types.Descr" name 3 captures) = .ok (.map I) ∧
      ∀ q w, mapLookup I q = some w → Gone K q w := by
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
    name captures L R g (fun e member y hy => (common e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy).1)
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure,
        keep_field])
  refine ⟨out, ?_, fun q w hw => ?_⟩
  · unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  rw [lookO q] at hw
  cases hit : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
  | none => simp [hit] at hw
  | some e =>
    rw [hit] at hw
    have qe : compareExact (fuel q e.1) q e.1 = .eq := by simpa using List.find?_some hit
    have inI : mapLookup I e.1 = some e.2 :=
      mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hit)
    rw [lookI e.1] at inI
    cases hL : (mapEntries L).find? (fun f => decide (compareExact (fuel e.1 f.1) e.1 f.1 = .eq)) with
    | none => simp [hL] at inI
    | some f =>
      rw [hL] at inI
      obtain ⟨y, hy, value⟩ := Option.map_eq_some_iff.mp inI
      have hx := mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hL)
      have ef : compareExact (fuel e.1 f.1) e.1 f.1 = .eq := by simpa using List.find?_some hL
      have keep : kept e = kept (f.1, g f.1 f.2 y) := by rw [value]; rfl
      by_cases k : kept e = Bool.true
      · simp [k] at hw
        subst hw
        have gone := (common f.1 f.2 y hx hy).2 (by rw [← keep]; exact k)
        rw [value] at gone
        exact gone.congr (Lynx.Term.compareExact_eq_trans qe ef)
      · simp [k] at hw

/-- Intersections keep at most an unsatisfiable list BDD when every common bitmap is
disjoint, every common atom field holds no atom, function types cancel out, and list
types are negations of each other. -/
theorem intersection_disjoint (depth : Nat) (L R : List (Term × Term)) (validL : Negatable E L)
    (staticR : mapLookup R (.atom "dynamic") = Option.none)
    (bitmaps : ∀ (b₁ : Nat) w, mapLookup L (.atom "bitmap") = some (.integer b₁) →
      mapLookup R (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0)
    (atoms : ∀ x y, mapLookup L (.atom "atom") = some x → mapLookup R (.atom "atom") = some y →
      ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
        x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
        y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
        Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
        (p₁ || p₂) = Bool.true ∧
        ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false)
    (funs : ∀ x y, mapLookup L (.atom "fun") = some x → mapLookup R (.atom "fun") = some y →
      Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table depth) x y =
        .ok (.integer 0))
    (lists : ∀ x y, mapLookup L (.atom "list") = some x → mapLookup R (.atom "list") = some y →
      Bdd ListOk x ∧ Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x)
    (tuples : ∀ x y, mapLookup L (.atom "tuple") = some x → mapLookup R (.atom "tuple") = some y →
      TupleCancel K x y)
    (maps : ∀ x y, mapLookup L (.atom "map") = some x → mapLookup R (.atom "map") = some y →
      MapCancel K x y) :
    ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map I) ∧
      ∀ q w, mapLookup I q = some w → Gone K q w := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
      k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  -- Each common field intersects to a value the filter drops.
  have common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
        q x y = .ok (g q x y) ∧
        (kept (q, g q x y) = Bool.true → Gone K q (g q x y)) := by
    intro q x y hx hy
    rcases validL.keys q (by simp [hx]) with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hx
      obtain ⟨b₂, rfl, disjoint⟩ := bitmaps b₁ y hx hy
      simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», Erlang.erlang.«band/2», kept, disjoint]
    · obtain ⟨p₁, S₁, p₂, S₂, rfl, rfl, set₁, set₂, union, none⟩ := atoms x y hx hy
      rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, -, tag, nonempty, mE⟩ | ⟨hE, -⟩
      · exfalso
        have positive : p = Bool.true := by rw [tag, union]
        apply nonempty positive
        apply nil_of_lookup_none
        intro q
        have := mE q
        rw [none q, positive] at this
        cases h : mapLookup E q with
        | none => rfl
        | some _ => simp [h] at this
      · simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE, kept]
    · simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», funs x y hx hy, kept]
    · obtain ⟨wx, wy, sem⟩ := lists x y hx hy
      obtain ⟨r, run, keep, semr⟩ := inter_ok wx wy
      have value : g (.atom "list") x y = r := by
        simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», list_intersection_bdd wx wy, run]
      refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», list_intersection_bdd wx wy, run, value],
        fun _ => Or.inl ⟨rfl, value ▸ keep _ wx wy, fun ρ resp => ?_⟩⟩
      rw [value, semr ρ resp, sem ρ resp]
      cases eval ρ x <;> rfl
    · obtain ⟨r, run, empty⟩ := tuples x y hx hy
      have value : g (.atom "tuple") x y = r := by
        simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», run]
      refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run, value], fun k => ?_⟩
      rw [value] at k ⊢
      exact Or.inr (Or.inl ⟨rfl, empty k⟩)
    · obtain ⟨r, run, empty⟩ := maps x y hx hy
      have value : g (.atom "map") x y = r := by
        simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», run]
      refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run, value], fun k => ?_⟩
      rw [value] at k ⊢
      exact Or.inr (Or.inr ⟨rfl, empty k⟩)
  obtain ⟨I, run, only⟩ := symmetrical_gone depth "bare_intersection" #[] L R g fun q x y hx hy =>
    ⟨by rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure]; exact (common q x y hx hy).1,
      (common q x y hx hy).2⟩
  refine ⟨I, ?_, only⟩
  have absent : mapLookup R (.atom "dynamic") = Option.none := staticR
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, validL.static, absent, run]

/-- The top type holds every bitmap and the negations of no atoms and of no functions. -/
theorem unfolded_term_fields : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    mapLookup T (.atom "bitmap") = some (.integer 255) ∧
    mapLookup T (.atom "atom") = some (.tuple #[.atom "negation", .map []]) ∧
    mapLookup T (.atom "fun") = some (.tuple #[.atom "negation", .map []]) ∧
    mapLookup T (.atom "dynamic") = Option.none :=
  ⟨_, rfl, by simp [mapLookup], by simp [mapLookup], by simp [mapLookup], by simp [mapLookup]⟩

theorem negation_fields (ops : ElemOk E K) (depth : Nat) (X : List (Term × Term)) (valid : Negatable E X)
    (nonempty : X ≠ []) :
    ∃ N, Elixir.Module.Types.Descr.«bare_negation/1»
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map X) = .ok (.map N) ∧
      mapLookup N (.atom "dynamic") = Option.none ∧
      (∀ (b₁ : Nat) w, mapLookup X (.atom "bitmap") = some (.integer b₁) →
        mapLookup N (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0) ∧
      (∀ x y, mapLookup X (.atom "atom") = some x → mapLookup N (.atom "atom") = some y →
        ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
          x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
          y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
          Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
          (p₁ || p₂) = Bool.true ∧
          ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) ∧
      (∀ x y, mapLookup X (.atom "fun") = some x → mapLookup N (.atom "fun") = some y → ∀ m,
        Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table m) x y =
          .ok (.integer 0)) ∧
      (∀ x y, mapLookup X (.atom "list") = some x → mapLookup N (.atom "list") = some y →
        Bdd ListOk x ∧ Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x) ∧
      (∀ x y, mapLookup X (.atom "tuple") = some x → mapLookup N (.atom "tuple") = some y →
        TupleCancel K x y) ∧
      (∀ x y, mapLookup X (.atom "map") = some x → mapLookup N (.atom "map") = some y →
        MapCancel K x y) ∧
      (∀ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) → ∀ name t,
        mapLookup T (.atom name) = some t →
        (mapLookup X (.atom name) = Option.none → mapLookup N (.atom name) = some t) ∧
        ∀ x w, mapLookup X (.atom name) = some x →
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            (.atom name) t x = .ok w →
          mapLookup N (.atom name) = if kept (.atom name, w) then some w else Option.none) := by
  obtain ⟨T, term, termBitmap, termAtom, termFun, termDynamic⟩ := unfolded_term_fields
  have termTuple : mapLookup T (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  have termMap : mapLookup T (.atom "map") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  have termList : mapLookup T (.atom "list") =
      some (.tuple #[.integer 46675407, .atom "term", .atom "term"]) := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
      k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have noAtoms : Erlang.sets.elements? (.map []) = some [] := by simp [Erlang.sets.elements?]
  obtain ⟨N, fold, lookN, -⟩ := difference_fold depth (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries X) T (mapEntries_distinct X) (by
    intro e member v₁ found
    have hy := mapLookup_of_mem_mapEntries member
    rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure]
    rcases valid.keys e.1 (by simp [hy]) with key | key | key | key | key | key <;> rw [key] at found hy ⊢
    · rw [termBitmap] at found
      cases found
      obtain ⟨b, value, -⟩ := valid.bitmap e.2 hy
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», value]
    · rw [termAtom] at found
      cases found
      obtain ⟨p, S, value, set⟩ := valid.atom e.2 hy
      rw [value]
      rcases atom_difference false [] p S noAtoms set with ⟨_, _, hE, -⟩ | ⟨hE, -⟩ <;>
        simp only [Bool.false_eq_true, ite_false] at hE <;>
        simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
    · rw [termFun] at found
      cases found
      obtain ⟨y, run, -⟩ := fun_negation depth e.2 (valid.funs e.2 hy)
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    · rw [termList] at found
      cases found
      rcases list_negation 46675407 e.2 (valid.lists e.2 hy).list with run | ⟨-, y, run, -⟩ <;>
        simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    · rw [termTuple] at found
      cases found
      obtain ⟨y, run, -⟩ := tuple_cancel ops e.2 (valid.tuples e.2 hy)
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    · rw [termMap] at found
      cases found
      obtain ⟨y, run, -⟩ := map_cancel ops e.2 (valid.maps e.2 hy)
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run])
  have run : Elixir.Module.Types.Descr.«bare_negation/1»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map X) = .ok (.map N) := by
    simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map valid.static, nonempty]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», nonempty, term, Erlang.maps.«fold/3»]
    simpa using fold
  refine ⟨N, run, ?_, fun b₁ w hX hN => ?_, fun x y hX hN => ?_, fun x y hX hN m => ?_, fun x y hX hN => ?_,
    fun x y hX hN => ?_, fun x y hX hN => ?_, fun T' term' name t hT => ?_⟩
  · rw [lookN, find_atom, valid.static]
    exact termDynamic
  · rw [lookN, find_atom, hX] at hN
    have le : 255 &&& b₁ ≤ 255 := Nat.and_le_left
    have value : g (.atom "bitmap") (.integer 255) (.integer b₁) = .integer ↑(255 - (255 &&& b₁)) := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]
      omega
    simp only [Option.map_some, termBitmap, Option.bind_some, value] at hN
    refine ⟨255 - (255 &&& b₁), ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
    · split at hN <;> simp_all
    · simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
      cases b₁.testBit i <;> simp
  · obtain ⟨pR, SR, rfl, setR⟩ := valid.atom x hX
    rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termAtom, Option.bind_some] at hN
    rcases atom_difference false [] pR SR noAtoms setR with ⟨p, E, hE, setE, tag, -, mE⟩ | ⟨hE, -⟩ <;>
      simp only [Bool.false_eq_true, ite_false] at hE
    · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
          (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) =
          .tuple #[.atom (if p then "union" else "negation"), .map E] := by
        simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
      have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) =
          Bool.true := by
        simp [kept]
      simp only [value, keep, ite_true, Option.some.injEq] at hN
      refine ⟨pR, SR, p, E, rfl, hN.symm, setR, setE, by rw [tag]; cases pR <;> rfl, fun q => ?_⟩
      rw [mE q]
      cases (mapLookup SR q).isSome <;> cases pR <;> simp [mapLookup]
    · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
          (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) = .integer 0 := by
        simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
      have drop : kept (.atom "atom", .integer 0) = Bool.false := by simp [kept]
      simp [value, drop] at hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termFun, Option.bind_some] at hN
    obtain ⟨w, negation, either⟩ := fun_negation depth x (valid.funs x hX)
    have value : g (.atom "fun") (.tuple #[.atom "negation", .map []]) x = w := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», negation]
    rw [value] at hN
    rcases either with rfl | all
    · simp [kept] at hN
    · split at hN
      · cases hN; exact all m
      · cases hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termList, Option.bind_some] at hN
    rcases list_negation 46675407 x (valid.lists x hX).list with run | ⟨wx, w, run, wy, sem⟩
    · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x =
          .atom "bdd_bot" := by
        simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
      simp [value, kept] at hN
    · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x = w := by
        simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
      rw [value] at hN
      split at hN
      · cases hN; exact ⟨wx, wy, sem⟩
      · cases hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termTuple, Option.bind_some] at hN
    obtain ⟨w, run, cancel⟩ := tuple_cancel ops x (valid.tuples x hX)
    have value : g (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    rw [value] at hN
    split at hN
    · rename_i k; cases hN; exact cancel k
    · cases hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termMap, Option.bind_some] at hN
    obtain ⟨w, run, cancel⟩ := map_cancel ops x (valid.maps x hX)
    have value : g (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    rw [value] at hN
    split at hN
    · rename_i k; cases hN; exact cancel k
    · cases hN
  · rw [term] at term'
    cases term'
    refine ⟨fun hX => ?_, fun x w hX run => ?_⟩
    · rw [lookN, find_atom, hX]
      exact hT
    · rw [lookN, find_atom, hX]
      have value : g (.atom name) t x = w := by simp [g, run]
      simp only [Option.map_some, hT, Option.bind_some, value]
