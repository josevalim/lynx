namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-- A field of the left type whose difference with the right type is empty. -/
def Covered (d : Dispatcher) (U : List (Term × Term)) (q t : Term) : Prop :=
  ∃ u w, mapLookup U q = some u ∧ Elixir.Module.Types.Descr.«bare_difference/3» d q t u = .ok w ∧
    (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
      Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))

theorem iterator_covered (d : Dispatcher) (U : List (Term × Term)) :
    ∀ es : List (Term × Term), (∀ e ∈ es, Covered d U e.1 e.2) →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» d it (.map U) (.map [])) =
        .ok (.atom "true") := by
  intro es
  induction es with
  | nil =>
    intro _
    simp [Term.list, Erlang.maps.«next/1»]
    unfold Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3»
    rfl
  | cons e rest ih =>
    intro all
    obtain ⟨u, w, hu, run, empty⟩ := all e (by simp)
    have tail := ih (fun e' m => all e' (by simp [m]))
    simp only [List.map, Term.list] at tail ⊢
    simp only [Erlang.maps.«next/1», Lynx.Except.ok_bind]
    rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, hu, run]
    rcases empty with h | h | h
    · simpa [h] using tail
    · simpa [h] using tail
    · refine ⟨?_, tail⟩
      by_cases h₀ : w = .integer 0
      · simp [h₀]
      · by_cases h₁ : w = .atom "bdd_bot"
        · simp [h₁]
        · right
          simp [h₀, h₁, h]

/-- The top type is a subtype of static types covering each of its fields. -/
theorem subtype_term (d : Dispatcher) (T U : List (Term × Term))
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    (static : mapLookup U (.atom "dynamic") = Option.none)
    (covered : ∀ e ∈ mapEntries T, Covered d U e.1 e.2) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.atom "term") (.map U) = .ok (.atom "true") := by
  have walk := iterator_covered d U (mapEntries T) covered
  have staticT : mapLookup T (.atom "dynamic") = Option.none := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  unfold Elixir.Module.Types.Descr.«subtype?/2»
  simp [term, unfold_map, Erlang.erlang.«is_map_key/2», static, staticT, any_key, Lynx.Except.andAlso,
    Erlang.erlang.«/=/2»]
  unfold Elixir.Module.Types.Descr.«subtype_static?/2»
  by_cases same : compareExact (fuel (.map U) (.map T)) (.map U) (.map T) = .eq
  · simp [Erlang.erlang.«=:=/2», same]
  · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, staticT, Erlang.maps.«iterator/1»]
    exact walk

/-- The difference of a field of the top type with a field type is empty. -/
def CoveredVal (d : Dispatcher) (q t u : Term) : Prop :=
  ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» d q t u = .ok w ∧
    (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
      Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))

/-- What a field type and its negation unite into covers the field of the top type. -/
def KeyOk (dn du dc : Dispatcher) (q t x : Term) : Prop :=
  ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» dn q t x = .ok w ∧
    (kept (q, w) = Bool.false → CoveredVal dc q t x) ∧
    (kept (q, w) = Bool.true → ∃ u, Elixir.Module.Types.Descr.«bare_union/3» du q x w = .ok u ∧ CoveredVal dc q t u)

theorem bitmap_absent (dc : Dispatcher) : CoveredVal dc (.atom "bitmap") (.integer 255) (.integer 255) :=
  ⟨.integer 0, by simp [Elixir.Module.Types.Descr.«bare_difference/3»]; rfl, Or.inl rfl⟩

theorem bitmap_key (dn du dc : Dispatcher) (b : Nat) (le : b ≤ 255) :
    KeyOk dn du dc (.atom "bitmap") (.integer 255) (.integer b) := by
  have band : (255 : Nat) &&& b = b := by
    rw [Nat.and_comm]
    have := Nat.and_two_pow_sub_one_eq_mod b 8
    simp at this
    omega
  refine ⟨.integer ↑(255 - b), ?_, fun k => ?_, fun _ => ?_⟩
  · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]
    omega
  · refine ⟨.integer ↑(255 - b), ?_, ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]; omega
    · simp [kept] at k; left; simp [k]
  · refine ⟨.integer 255, ?_, .integer 0, ?_, Or.inl rfl⟩
    · have disjoint : b &&& (255 - b) = 0 := Nat.eq_of_testBit_eq fun i => by
        rw [← band]; simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
        cases b.testBit i <;> simp
      have := add_eq_or b (255 - b) disjoint
      simp [Elixir.Module.Types.Descr.«bare_union/3», Erlang.erlang.«bor/2»]
      omega
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]

theorem no_atoms : Erlang.sets.elements? (.map []) = some [] := by simp [Erlang.sets.elements?]

/-- Sets without members are empty. -/
theorem set_none {left right : Term} {f : Term → Term → Except Exception Term} {E : List (Term × Term)}
    (run : f left right = .ok (.map E)) (none : ∀ q, (mapLookup E q).isSome = Bool.false) :
    f left right = .ok (.map []) := by
  rw [run, nil_of_lookup_none E fun q => by simpa using none q]

theorem atom_absent (dc : Dispatcher) :
    CoveredVal dc (.atom "atom") (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "negation", .map []]) := by
  obtain ⟨E, hE, -, m⟩ := Erlang.sets.subtract_member _ _ _ _ no_atoms no_atoms
  have run := set_none hE fun q => by rw [m]; simp [mapLookup]
  refine ⟨.integer 0, ?_, Or.inl rfl⟩
  simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», run,
    Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.sets.«size/1»]

theorem atom_key (dn du dc : Dispatcher) (p : Bool) (S : List (Term × Term))
    (set : Erlang.sets.elements? (.map S) = some S) :
    KeyOk dn du dc (.atom "atom") (.tuple #[.atom "negation", .map []])
      (.tuple #[.atom (if p then "union" else "negation"), .map S]) := by
  cases p
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set no_atoms
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine ⟨.tuple #[.atom "union", .map E], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, size, nonzero]
      · obtain ⟨F, hF, -, mF⟩ := Erlang.sets.subtract_member _ _ _ _ set setE
        have run := set_none hF fun q => by rw [mF, m]; simp [mapLookup]
        exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«atom_union/2», run],
          atom_absent dc⟩
    · refine ⟨.integer 0, ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, size]
      · obtain rfl : S = [] := nil_of_lookup_none S fun q => by
          have := m q
          rw [empty q] at this
          simpa [mapLookup] using this
        exact atom_absent dc
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ no_atoms set
    refine ⟨.tuple #[.atom "negation", .map E], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
        Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · obtain ⟨F, hF, -, mF⟩ := Erlang.sets.subtract_member _ _ _ _ setE set
      have run := set_none hF fun q => by rw [mF, m]; simp [mapLookup]
      exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«atom_union/2», run],
        atom_absent dc⟩

theorem loop_ne_nil (f : Term → Term → Bool) :
    ∀ (l : List Term) (a : Term) (acc : List Term), List.eraseDupsBy.loop f l (a :: acc) ≠ [] := by
  intro l
  induction l with
  | nil => intro a acc; simp [List.eraseDupsBy.loop]
  | cons x xs ih =>
    intro a acc
    simp only [List.eraseDupsBy.loop]
    split
    · exact ih a acc
    · exact ih x (a :: acc)

theorem fun_absent (n : Nat) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "fun") (.tuple #[.atom "negation", .map []])
      (.tuple #[.atom "negation", .map []]) := by
  have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
      (.map []) (.map []) = .ok (.map []) := by
    simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
  refine ⟨.integer 0, ?_, Or.inl rfl⟩
  simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
    Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]

theorem fun_key (n m k : Nat) (x : Term) (field : FunField x) :
    KeyOk (Dispatcher.ofTable Erlang.program.fun_table n) (Dispatcher.ofTable Erlang.program.fun_table m)
      (Dispatcher.ofTable Erlang.program.fun_table k) (.atom "fun") (.tuple #[.atom "negation", .map []]) x := by
  obtain ⟨pos, R, rfl⟩ := field
  cases pos with
  | true =>
    obtain ⟨out, merge, look⟩ := Erlang.maps.merge_with_lookup (Dispatcher.ofTable Erlang.program.fun_table n)
      "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] R (fun _ _ _ => .nil)
      (by intro e _ v found; simp [mapLookup] at found)
    have same : ∀ q, mapLookup R q = mapLookup out q := by
      intro q
      rw [look q, ← mapLookup_mapEntries R]
      simp only [mapLookup]
      cases (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) <;> simp
    refine ⟨.tuple #[.atom "negation", .map out], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2»,
        Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», merge,
        Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2»,
        repr_cancel m out R same], fun_absent k⟩
  | false =>
    have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
        (.map R) (.map []) = .ok (.map R) := by
      simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
    by_cases empty : ((R.map Prod.fst).eraseDupsBy (fun a b => compareExact (fuel a b) a b == .eq)).length = 0
    · refine ⟨.integer 0, ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
          Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
      · obtain rfl : R = [] := by
          cases R with
          | nil => rfl
          | cons e rest =>
            simp [List.eraseDupsBy, List.eraseDupsBy.loop] at empty
            exact (loop_ne_nil _ _ _ [] empty).elim
        exact fun_absent k
    · refine ⟨.tuple #[.atom "union", .map R], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
          Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
      · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2»,
          repr_cancel m R R (fun _ => rfl)], fun_absent k⟩

theorem list_absent (dc : Dispatcher) (k : Int) :
    CoveredVal dc (.atom "list") (.tuple #[.integer k, .atom "term", .atom "term"])
      (.tuple #[.integer k, .atom "term", .atom "term"]) :=
  ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
    Or.inr (Or.inl rfl)⟩

/-- The difference of all lists with a list BDD of other literals is its negation. -/
theorem list_difference_bdd (k : Int) {x : Term} (wx : Bdd ListOk x) :
    Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer k, .atom "term", .atom "term"]) x =
      Elixir.Module.Types.Descr.«bdd_negation/1» x := by
  have nt := not_top_leaf wx
  unfold Elixir.Module.Types.Descr.«list_difference/2»
  split
  · exact (nt _ rfl).elim
  · rfl
  · next h₁ h₂ => first | exact (h₁ _ rfl).elim | exact (h₁ _ _ rfl).elim | exact absurd rfl (h₁ _) | simp_all

theorem list_key (dn du dc : Dispatcher) (k : Int) (x : Term) (field : ListField x) :
    KeyOk dn du dc (.atom "list") (.tuple #[.integer k, .atom "term", .atom "term"]) x := by
  rcases field with ⟨k', rfl⟩ | wx
  · refine ⟨.atom "bdd_bot", ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»]
    · exact ⟨.atom "bdd_bot", by
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
        Or.inr (Or.inl rfl)⟩
  obtain ⟨w, run, keep, sem⟩ := neg_ok wx
  have diff : Elixir.Module.Types.Descr.«bare_difference/3» dn (.atom "list")
      (.tuple #[.integer k, .atom "term", .atom "term"]) x = .ok w := by
    simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wx, run]
  have ww := keep _ wx
  refine ⟨w, diff, fun kw => ⟨w, by
      simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wx, run], ?_⟩, fun _ => ?_⟩
  · simp [kept] at kw
    by_cases e : w = .integer 0
    · exact Or.inl e
    · exact Or.inr (Or.inl (kw e))
  obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
  have wu := keepU _ wx ww
  have unionRun : Elixir.Module.Types.Descr.«list_union/2» x w = Elixir.Module.Types.Descr.«bdd_union/2» x w := by
    have nx := not_top_leaf wx
    have nw := not_top_leaf ww
    unfold Elixir.Module.Types.Descr.«list_union/2»
    split
    · exact (nx _ rfl).elim
    · exact (nw _ rfl).elim
    · rfl
  obtain ⟨w', runW, keepW, semW⟩ := neg_ok wu
  refine ⟨u, by simp [Elixir.Module.Types.Descr.«bare_union/3», unionRun, runU], w', ?_, Or.inr (Or.inr ?_)⟩
  · simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wu, runW]
  · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
    exact list_empty_unsat dc (keepW _ wu) (fun ρ resp => by
      rw [semW ρ resp, semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl) []

theorem remove_atom_leaf (s : String) (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_remove/2» (.atom s) (.tuple #[k, x, y]) = .ok (.atom s) := by
  unfold Elixir.Module.Types.Descr.«bdd_remove/2»
  unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
  simp [Erlang.erlang.«=:=/2»]

theorem union_bot_leaf (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_bot") (.tuple #[k, x, y]) = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2»]

theorem union_leaf_bot (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2»]

theorem union_two_leaves {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (lt : Term.compare (Term.fuel a b) a b = .lt) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_union/2» a b =
      .ok (.tuple #[.integer h, a, .atom "bdd_top", b, .atom "bdd_bot"]) := by
  have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
  have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
  have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
  have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
  have same : ¬compareExact (fuel a b) a b = .eq := fun e => by
    rw [compare_eq_of_compareExact_eq _ _ e] at lt; cases lt
  have same' : ¬compareExact (fuel b a) b a = .eq := fun e => same (Lynx.Term.compareExact_eq_symm e)
  obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt wa ha hb lt
  rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, rfl⟩ := la; simp at e
  obtain ⟨h₁, node⟩ := node_new a (.atom "bdd_top") b (.atom "bdd_bot") la (Bdd.top (ok := fun _ => True))
    wb (Bdd.bot (ok := fun _ => True))
  refine ⟨h₁, ?_⟩
  obtain ⟨_, _, _, rfl⟩ := la
  obtain ⟨_, _, _, rfl⟩ := lb
  conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2», run, remove_atom_leaf, union_bot_leaf, node, same']

theorem union_two_leaves_gt {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (gt : Term.compare (Term.fuel a b) a b = .gt) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_union/2» a b =
      .ok (.tuple #[.integer h, b, .atom "bdd_top", a, .atom "bdd_bot"]) := by
  have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
  have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
  have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
  have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
  have same : ¬compareExact (fuel a b) a b = .eq := fun e => by
    rw [compare_eq_of_compareExact_eq _ _ e] at gt; cases gt
  have same' : ¬compareExact (fuel b a) b a = .eq := fun e => same (Lynx.Term.compareExact_eq_symm e)
  obtain ⟨h₀, c, u, d, run, split⟩ := compare_gt wb ha hb gt
  rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, rfl⟩ := lb; simp at e
  obtain ⟨h₁, node⟩ := node_new b (.atom "bdd_top") a (.atom "bdd_bot") lb (Bdd.top (ok := fun _ => True))
    wa (Bdd.bot (ok := fun _ => True))
  refine ⟨h₁, ?_⟩
  obtain ⟨_, _, _, rfl⟩ := la
  obtain ⟨_, _, _, rfl⟩ := lb
  conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2», run, remove_atom_leaf, union_leaf_bot, node, same']

theorem inter_bot_any (b : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_bot") b = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  by_cases e : compareExact (fuel b (.atom "bdd_bot")) b (.atom "bdd_bot") = .eq
  · simp [Erlang.erlang.«=:=/2», e]
  · simp [Erlang.erlang.«=:=/2», e]
    split <;> simp_all

theorem inter_top_any (b : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_top") b = .ok b := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  by_cases e : compareExact (fuel b (.atom "bdd_top")) b (.atom "bdd_top") = .eq
  · have := (compareExact_eq_atom _ _).mp e; subst this; simp [Erlang.erlang.«=:=/2»]
  · simp [Erlang.erlang.«=:=/2», e]

/-- The negation of the union of two leaves negates each in turn. -/
theorem neg_union_leaves {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (lt : Term.compare (Term.fuel a b) a b = .lt) (h : Int) :
    ∃ h₁ h₂ : Int, Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, a, .atom "bdd_top", b, .atom "bdd_bot"]) =
      .ok (.tuple #[.integer h₁, a, .atom "bdd_bot", .atom "bdd_bot",
        .tuple #[.integer h₂, b, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]]) := by
  obtain ⟨hA, nodeA⟩ := node_new a (.atom "bdd_bot") (.atom "bdd_bot") (.atom "bdd_top") la
    (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
  obtain ⟨hB, nodeB⟩ := node_new b (.atom "bdd_bot") (.atom "bdd_bot") (.atom "bdd_top") lb
    (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
  let nB : Term := .tuple #[.integer hB, b, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]
  have wnB : Bdd (fun _ => True) nB := by
    obtain ⟨_, _, _, rfl⟩ := lb
    simp [nB, Bdd, IsLeaf]
  have wnA : Bdd (fun _ => True) (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) := by
    obtain ⟨_, _, _, rfl⟩ := la
    simp [Bdd, IsLeaf]
  obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt (b := nB) wnA (by simp [head]) (by simp [nB, head]) lt
  rcases split with ⟨_, e⟩ | ⟨e, -⟩
  · simp at e
    obtain ⟨-, rfl, rfl, rfl⟩ := e
    obtain ⟨h₃, node3⟩ := node_new a (.atom "bdd_bot") (.atom "bdd_bot") nB la
      (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) wnB
    refine ⟨h₃, hB, ?_⟩
    have notSame : ¬compareExact (fuel nB (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"])) nB (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) = .eq := by
      intro e
      obtain ⟨_, _, _, _, _, e', b₁, -⟩ := tuple5_exact e
      simp at e'
      obtain ⟨-, rfl, -⟩ := e'
      rw [compare_eq_of_compareExact_eq _ _ (Lynx.Term.compareExact_eq_symm b₁)] at lt
      cases lt
    have inter : Elixir.Module.Types.Descr.«bdd_intersection/2»
        (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) nB =
          .ok (.tuple #[.integer h₃, a, .atom "bdd_bot", .atom "bdd_bot", nB]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [nB, Erlang.erlang.«=:=/2», notSame, run, inter_bot_any, inter_top_any, node3]
    have negTop : Elixir.Module.Types.Descr.«bdd_negation/1» (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_negation/1»; rfl
    have negBot : Elixir.Module.Types.Descr.«bdd_negation/1» (.atom "bdd_bot") = .ok (.atom "bdd_top") := by
      unfold Elixir.Module.Types.Descr.«bdd_negation/1»; rfl
    have negB : Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok nB := by
      obtain ⟨_, _, _, rfl⟩ := lb
      unfold Elixir.Module.Types.Descr.«bdd_negation/1»
      simpa using nodeB
    conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
    simp [negTop, negBot, nodeA, negB, inter, Erlang.erlang.«=:=/2», nB]
  · obtain ⟨_, _, _, rfl⟩ := la
    simp at e

theorem elements_term (d : Dispatcher) (acc tag negs S e : Term) (he : e = .nil ∨ e = Term.list [.atom "term"]) :
    Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d acc tag e (Term.list [.atom "term"]) negs S =
      .ok (.atom "true") := by
  have inter : Elixir.Module.Types.Descr.«bare_intersection/2» d (.atom "term") (.atom "term") = .ok (.atom "term") := by
    unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
  have diff : Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") (.atom "term") = .ok (.map []) := by
    unfold Elixir.Module.Types.Descr.«bare_difference/2»; rfl
  have seenTerm : Elixir.Module.Types.Descr.«empty_seen?/2» d (.atom "term") S = .ok (.atom "false") := by
    unfold Elixir.Module.Types.Descr.«empty_seen?/2»; rfl
  have seenNone : Elixir.Module.Types.Descr.«empty_seen?/2» d (.map []) S = .ok (.atom "true") := by
    unfold Elixir.Module.Types.Descr.«empty_seen?/2»
    simp [getMapKeys, Erlang.erlang.«==/2»]
  rcases he with rfl | rfl <;>
  · rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]
    simp [Term.list, inter, diff, seenTerm, seenNone, isMember]
    rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]
    rfl

theorem elements_nil (d : Dispatcher) (acc tag e negs S : Term) :
    Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d acc tag e .nil negs S = .ok (.atom "true") := by
  rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]; rfl

theorem cmp10 : Ord.compare (1 : Int) 0 = .gt := by decide
theorem cmp01 : Ord.compare (0 : Int) 1 = .lt := by decide
theorem cmp11 : Ord.compare (1 : Int) 1 = .eq := by decide

theorem dup_zero : Erlang.lists.«duplicate/2» (.integer 0) (.atom "term") = .ok .nil := by
  simp [Erlang.lists.«duplicate/2», Erlang.erlang.«>=/2», Erlang.erlang.«and/2»]
  rw [Erlang.lists.«duplicate/3».eq_def]
  simp

theorem dup_one : Erlang.lists.«duplicate/2» (.integer 1) (.atom "term") = .ok (Term.list [.atom "term"]) := by
  simp [Erlang.lists.«duplicate/2», Erlang.erlang.«>=/2», Erlang.erlang.«and/2», cmp10]
  rw [Erlang.lists.«duplicate/3».eq_def]
  simp
  rw [Erlang.lists.«duplicate/3».eq_def]
  simp [Term.list]

theorem fill_zero : Elixir.Module.Types.Descr.«tuple_fill/2» .nil (.integer 0) = .ok .nil := by
  simp [Elixir.Module.Types.Descr.«tuple_fill/2», Erlang.erlang.«length/1», Erlang.erlang.«</2»,
    dup_zero, Erlang.erlang.«++/2»]

theorem fill_one : Elixir.Module.Types.Descr.«tuple_fill/2» .nil (.integer 1) = .ok (Term.list [.atom "term"]) := by
  simp [Elixir.Module.Types.Descr.«tuple_fill/2», Erlang.erlang.«length/1», Erlang.erlang.«</2»,
    dup_one, Erlang.erlang.«++/2», cmp10]

theorem line_lt (d : Dispatcher) (k H : Int) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open") .nil
      (.cons (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]])
        (.cons (.tuple #[.integer k, .atom "closed", .nil]) .nil)) S = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«length/1», Lynx.Except.orElse,
    Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2»,
    elements_term d _ _ _ S _ (Or.inl rfl), Elixir.Module.Types.Descr.«tuple_empty_arity?/7»,
    Elixir.Module.Types.Descr.«tuple_empty_sizes?/5», fill_zero, cmp01,
    elements_nil]

theorem line_gt (d : Dispatcher) (k H : Int) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open") .nil
      (.cons (.tuple #[.integer k, .atom "closed", .nil])
        (.cons (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) .nil)) S = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«length/1», Lynx.Except.orElse,
    Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», elements_nil,
    Elixir.Module.Types.Descr.«tuple_empty_arity?/7»,
    Elixir.Module.Types.Descr.«tuple_empty_sizes?/5», fill_one,
    elements_nil, elements_term d _ _ _ S _ (Or.inr rfl)]

theorem any_nil (d : Dispatcher) (m n : String) (caps : Array Term) :
    Erlang.lists.«any/2» d (.function m n 1 caps) .nil = .ok (.atom "false") := by
  simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2»]

theorem special_lt (d : Dispatcher) (h₁ h₂ k H : Int) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» d
      (.tuple #[.integer h₁, .tuple #[.integer k, .atom "closed", .nil], .atom "bdd_bot", .atom "bdd_bot",
        .tuple #[.integer h₂, .tuple #[.integer H, .atom "open", Term.list [.atom "term"]], .atom "bdd_bot",
          .atom "bdd_bot", .atom "bdd_top"]]) (.map []) = .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.false,
    Erlang.maps.«put/3»]
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
    Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]
  rw [line_lt]; rfl

theorem special_gt (d : Dispatcher) (h₁ h₂ k H : Int) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» d
      (.tuple #[.integer h₁, .tuple #[.integer H, .atom "open", Term.list [.atom "term"]], .atom "bdd_bot", .atom "bdd_bot",
        .tuple #[.integer h₂, .tuple #[.integer k, .atom "closed", .nil], .atom "bdd_bot",
          .atom "bdd_bot", .atom "bdd_top"]]) (.map []) = .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.false,
    Erlang.maps.«put/3»]
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
    Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]
  rw [line_gt]; rfl

theorem dropped {q w : Term} (k : kept (q, w) = Bool.false) : w = .integer 0 ∨ w = .atom "bdd_bot" := by
  simp [kept] at k
  by_cases e : w = .integer 0
  · exact Or.inl e
  · exact Or.inr (k e)

/-- The difference of all tuples with a tautology of tuple literals is empty. -/
theorem tuple_taut (ops : ElemOk E K) {m : Nat} (hm : K + 1 ≤ m) {u : Term} (wu : Bdd (TupleOk E) u) (taut : ∀ ρ, Resp ρ → eval ρ u = Bool.true) :
    CoveredVal (D m) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) u := by
  rcases wu.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, d, e, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
    simp [Elixir.Module.Types.Descr.«bare_difference/3»]
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    simp [diff_leaf_top]
  · have := taut _ (resp_const Bool.false); simp at this
  · have := taut _ (resp_const Bool.false); simp [eval] at this
  · obtain ⟨w, run, keep, sem⟩ := neg_ok wu
    refine ⟨w, ?_, Or.inr (Or.inr ?_)⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [run]
    · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
      exact tuple_empty_unsat ops (keep _ wu) (fun _ h => h.1) (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) m [] hm

theorem tuple_union_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«tuple_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
  unfold Elixir.Module.Types.Descr.«tuple_union/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem tuple_absent (n : Nat) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer 61102469, .atom "open", .nil]) :=
  ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»],
    Or.inr (Or.inl rfl)⟩

/-- A tuple BDD that is neither bottom, top, nor `{}` has its negation as difference. -/
theorem tuple_key_neg (ops : ElemOk E K) (dn du : Dispatcher) {m : Nat} (hm : K + 1 ≤ m) (x : Term) (wx : Bdd (TupleOk E) x)
    (run : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x =
      Elixir.Module.Types.Descr.«bdd_negation/1» x) :
    KeyOk dn du (D m) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
  have notTop := not_top_of_ok wx fun t h => h.2
  obtain ⟨w, neg, keep, sem⟩ := neg_ok wx
  have ww := keep _ wx
  have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w := by
    intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», run, neg]
  refine ⟨w, diff _, fun kw => ⟨w, diff _, ?_⟩, fun _ => ?_⟩
  · rcases dropped kw with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
  have wu := keepU _ wx ww
  refine ⟨u, ?_, tuple_taut ops hm wu fun ρ resp => ?_⟩
  · simp [Elixir.Module.Types.Descr.«bare_union/3», tuple_union_bdd notTop (not_top_of_ok ww fun t h => h.2), runU]
  · rw [semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl

theorem tuple_key (ops : ElemOk E K) (dn du : Dispatcher) {m : Nat} (hm : K + 1 ≤ m) (x : Term) (field : TupleField E x) :
    KeyOk dn du (D m) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
  rcases field with ⟨k, rfl⟩ | wx
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by
      intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
      intro d
      simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_top]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«tuple_union/2»],
        tuple_absent _⟩
  · obtain ⟨⟨k', tag, ls, e, tags, elems⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
    simp at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    by_cases special : tag = "closed" ∧ ls = []
    · obtain ⟨rfl, rfl⟩ := special
      obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
      let W : Term := .tuple #[.integer ((1 <<< 27) + hash), .atom "open", Term.list [.atom "term"]]
      have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
          (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "closed", Term.list []]) =
            .ok W := by
        intro d
        simp [Elixir.Module.Types.Descr.«bare_difference/3»]
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
          Elixir.Module.Types.Descr.«bdd_leaf_key/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«length/1», Erlang.erlang.«bsl/2», W]
        rfl
      refine ⟨W, diff _, fun k => by simp [kept, W] at k, fun _ => ?_⟩
      have lX : IsLeaf (.tuple #[.integer k, .atom "closed", Term.list []]) := ⟨_, _, _, rfl⟩
      have lW : IsLeaf W := ⟨_, _, _, rfl⟩
      have unionRun : ∀ u, Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k, .atom "closed", Term.list []]) W = .ok u →
          Elixir.Module.Types.Descr.«bare_union/3» du (.atom "tuple") (.tuple #[.integer k, .atom "closed", Term.list []]) W =
            .ok u := by
        intro u run
        simp [Elixir.Module.Types.Descr.«bare_union/3»]
        rw [tuple_union_bdd notTop (by intro k e; simp [W] at e)]
        exact run
      by_cases order : k ≤ (1 <<< 27) + hash
      · have lt : Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", Term.list []]) W) (.tuple #[.integer k, .atom "closed", Term.list []]) W = .lt := by
          have ca : Term.compare (Term.fuel (Term.atom "closed") (.atom "open")) (Term.atom "closed") (.atom "open") = .lt := by cbv
          simp [W, compare_tuple, List.compareLex_cons_cons, ca]
          have order' : k ≤ 134217728 + (hash : Int) := by simpa using order
          rcases Int.lt_or_eq_of_le order' with o | o
          · simp [Int.compare_eq_lt.mpr o]
          · rw [o]; simp
        obtain ⟨h, run⟩ := union_two_leaves lX lW lt
        obtain ⟨h₁, h₂, neg⟩ := neg_union_leaves lX lW lt h
        refine ⟨_, unionRun _ run, .tuple #[.integer h₁, (.tuple #[.integer k, .atom "closed", Term.list []]), .atom "bdd_bot", .atom "bdd_bot",
          .tuple #[.integer h₂, W, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]], ?_, Or.inr (Or.inr ?_)⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [neg]
        · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
          exact special_lt _ _ _ _ _
      · have lt : Term.compare (Term.fuel W (.tuple #[.integer k, .atom "closed", Term.list []])) W (.tuple #[.integer k, .atom "closed", Term.list []]) = .lt := by
          have o : 134217728 + (hash : Int) < k := by simp at order; omega
          simp [W, compare_tuple, List.compareLex_cons_cons, Int.compare_eq_lt.mpr o]
        have gt : Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", Term.list []]) W) (.tuple #[.integer k, .atom "closed", Term.list []]) W = .gt := by
          rw [Lynx.Term.compare_gt_iff_lt]; exact lt
        obtain ⟨h, run⟩ := union_two_leaves_gt lX lW gt
        obtain ⟨h₁, h₂, neg⟩ := neg_union_leaves lW lX lt h
        refine ⟨_, unionRun _ run, .tuple #[.integer h₁, W, .atom "bdd_bot", .atom "bdd_bot",
          .tuple #[.integer h₂, (.tuple #[.integer k, .atom "closed", Term.list []]), .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]], ?_, Or.inr (Or.inr ?_)⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [neg]
        · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
          exact special_gt _ _ _ _ _
    · have notSpecial : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠
          .tuple #[k₁, .atom "closed", .nil] := by
        intro k₁ e
        simp at e
        apply special
        refine ⟨e.2.1, ?_⟩
        cases ls <;> simp_all [Term.list]
      refine tuple_key_neg ops dn du hm _ wx ?_
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split
      · next _ _ e =>
        exfalso
        simp at e
        obtain ⟨-, rfl, hl⟩ := e
        exact notTopX ⟨_, by rw [hl]⟩
      · next _ _ e => exact (notSpecial _ e).elim
      · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; rfl
      · next h₁ => exact (h₁ _ _ rfl rfl).elim
  · refine tuple_key_neg ops dn du hm _ wx ?_
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    simp

theorem map_taut (ops : ElemOk E K) {m : Nat} (hm : K + 2 ≤ m) {u : Term} (wu : Bdd (MapOk E) u) (taut : ∀ ρ, Resp ρ → eval ρ u = Bool.true) :
    CoveredVal (D m) (.atom "map")
      (.tuple #[.integer 61102469, .atom "open", .nil]) u := by
  rcases wu.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, d, e, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
    simp [Elixir.Module.Types.Descr.«bare_difference/3»]
    unfold Elixir.Module.Types.Descr.«map_difference/2»
    simp [diff_leaf_top]
  · have := taut _ (resp_const Bool.false); simp at this
  · have := taut _ (resp_const Bool.false); simp [eval] at this
  · obtain ⟨w, run, keep, sem⟩ := neg_ok wu
    refine ⟨w, ?_, Or.inr (Or.inr ?_)⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [run]
    · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
      exact map_empty_unsat ops (keep _ wu) (fun _ h => h.1) (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) m [] hm

theorem map_union_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«map_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
  unfold Elixir.Module.Types.Descr.«map_union/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem map_absent (n : Nat) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "map")
      (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer 61102469, .atom "open", .nil]) :=
  ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»],
    Or.inr (Or.inl rfl)⟩

theorem map_key (ops : ElemOk E K) (dn du : Dispatcher) {m : Nat} (hm : K + 2 ≤ m) (x : Term) (field : MapField E x) :
    KeyOk dn du (D m) (.atom "map")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
  rcases field with ⟨k, rfl⟩ | wx
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by
      intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  have neg : (∃ h lit c u d, x = .tuple #[.integer h, lit, c, u, d]) ∨ (∃ k x₁ y₁, x = .tuple #[.integer k, x₁, y₁]) →
      KeyOk dn du (D m) (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
    intro shape
    obtain ⟨w, neg, keep, sem⟩ := neg_ok wx
    have ww := keep _ wx
    have run : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x =
        .ok w := by
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      rcases shape with ⟨h, lit, c, u, d, rfl⟩ | ⟨k, x₁, y₁, rfl⟩
      · simp [neg]
      · split
        · next _ _ e => exact (notTop _ e).elim
        · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact neg
        · next h₁ => exact (h₁ _ _ rfl rfl).elim
    have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w := by
      intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», run]
    refine ⟨w, diff _, fun kw => ⟨w, diff _, ?_⟩, fun _ => ?_⟩
    · rcases dropped kw with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
    have wu := keepU _ wx ww
    refine ⟨u, ?_, map_taut ops hm wu fun ρ resp => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_union/3», map_union_bdd notTop (not_top_of_ok ww fun t h => h.2), runU]
    · rw [semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
      intro d
      simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_top]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_bot]
    · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«map_union/2»],
        map_absent _⟩
  · exact neg (Or.inr ⟨_, _, _, rfl⟩)
  · exact neg (Or.inl ⟨_, _, _, _, _, rfl⟩)

/-- Unions of static types merge their fields, uniting those in both. -/
theorem union_lookup (depth : Nat) (L R : List (Term × Term))
    (staticL : mapLookup L (.atom "dynamic") = Option.none) (staticR : mapLookup R (.atom "dynamic") = Option.none)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ u, Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) q x y = .ok u) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        (.map L) (.map R) = .ok (.map U) ∧
      ∀ name, (mapLookup R (.atom name) = Option.none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
        (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = Option.none →
          mapLookup U (.atom name) = some y) ∧
        (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
          Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y =
            .ok u → mapLookup U (.atom name) = some u) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
      q x y = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  obtain ⟨U, run, look⟩ : ∃ U, Elixir.Module.Types.Descr.«bare_union/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map U) ∧
      ∀ name, mapLookup U (.atom name) =
        match mapLookup R (.atom name) with
        | some y => some (match mapLookup L (.atom name) with | some x => g (.atom name) x y | none => y)
        | none => mapLookup L (.atom name) := by
    unfold Elixir.Module.Types.Descr.«bare_union/2»
    simp [getMapKeys_single, Erlang.erlang.«==/2», staticL, staticR]
    by_cases emptyL : L = []
    · subst emptyL
      refine ⟨R, by simp, fun name => ?_⟩
      cases mapLookup R (.atom name) <;> simp [mapLookup]
    by_cases emptyR : R = []
    · subst emptyR
      exact ⟨L, by simp [emptyL], fun name => by simp [mapLookup]⟩
    simp only [emptyL, emptyR]
    unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
    obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr" "bare_union" #[] L R g (by
        intro e me x hx
        have hy := mapLookup_of_mem_mapEntries me
        obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
        rw [Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure, ru, value _ _ _ _ ru])
    refine ⟨out, by simpa using run, fun name => ?_⟩
    rw [look, find_atom]
    cases mapLookup R (.atom name) <;> rfl
  refine ⟨U, run, fun name => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩⟩
  · rw [look, hR]
  · rw [look, hR, hL]
  · rw [look, hR, hL]; simp only [value _ _ _ _ ru]

theorem term_keys {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {q t : Term} (hT : mapLookup T q = some t) :
    (q = .atom "bitmap" ∧ t = .integer 255) ∨ (q = .atom "atom" ∧ t = .tuple #[.atom "negation", .map []]) ∨
      (q = .atom "fun" ∧ t = .tuple #[.atom "negation", .map []]) ∨
      (q = .atom "list" ∧ t = .tuple #[.integer 46675407, .atom "term", .atom "term"]) ∨
      (q = .atom "tuple" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) ∨
      (q = .atom "map" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) := by
  simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at term
  cases term
  simp only [mapLookup, List.find?] at hT
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  · simp at hT

/-- Each field of the top type is covered by what a field type and its negation unite into. -/
theorem key_ok (δ : Nat) (ops : ElemOk E K) (hK : K ≤ δ + 90) (X : List (Term × Term)) (valid : Negatable E X) {T : List (Term × Term)}
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) {q t x : Term}
    (hT : mapLookup T q = some t) (hX : mapLookup X q = some x) :
    KeyOk (Dispatcher.ofTable Erlang.program.fun_table (δ + 98)) (Dispatcher.ofTable Erlang.program.fun_table (δ + 99))
      (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) q t x := by
  rcases term_keys term hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨b, rfl, -, le⟩ := valid.bitmap x hX
    exact bitmap_key _ _ _ b le
  · obtain ⟨p, S, rfl, set⟩ := valid.atom x hX
    exact atom_key _ _ _ p S set
  · exact fun_key (δ + 98) (δ + 99) (δ + 100) x (valid.funs x hX)
  · exact list_key _ _ _ _ x (valid.lists x hX).list
  · exact tuple_key ops _ _ (by omega) x (valid.tuples x hX)
  · exact map_key ops _ _ (by omega) x (valid.maps x hX)

/-- Fields of the top type are covered by themselves. -/
theorem key_absent (δ : Nat) {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {q t : Term} (hT : mapLookup T q = some t) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) q t t := by
  rcases term_keys term hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact bitmap_absent _
  · exact atom_absent _
  · exact fun_absent _
  · exact list_absent _ _
  · exact tuple_absent _
  · exact map_absent _

theorem atom_key_of {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {q t : Term} (hT : mapLookup T q = some t) : ∃ name, q = .atom name := by
  rcases term_keys term hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨_, rfl⟩

/-- A type united with its negation covers the top type. -/
theorem union_negation_covers (δ : Nat) (ops : ElemOk E K) (hK : K ≤ δ + 90) (X : List (Term × Term)) (valid : Negatable E X)
    (nonempty : X ≠ []) :
    ∃ N U, Elixir.Module.Types.Descr.«bare_negation/1» (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) =
        .ok (.map N) ∧
      Elixir.Module.Types.Descr.«bare_union/2» (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.map N) =
        .ok (.map U) ∧ mapLookup U (.atom "dynamic") = Option.none ∧
      Elixir.Module.Types.Descr.«subtype?/2» (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.atom "term")
        (.map U) = .ok (.atom "true") := by
  obtain ⟨N, negation, staticN, -, -, -, -, -, -, lookups⟩ := negation_fields ops (δ + 98) X valid nonempty
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  have inT : ∀ q x, mapLookup X q = some x → ∃ t, mapLookup T q = some t := by
    intro q x hX
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    rcases valid.keys q (by simp [hX]) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mapLookup]
  obtain ⟨U, union, lookU⟩ := union_lookup (δ + 99) X N valid.static staticN (by
    intro q x y hX hN
    obtain ⟨t, hT⟩ := inT q x hX
    obtain ⟨name, rfl⟩ := atom_key_of term hT
    obtain ⟨w, run, -, keep⟩ := key_ok δ ops hK X valid term hT hX
    have look := (lookups T term name t hT).2 x w hX run
    rw [hN] at look
    by_cases k : kept (.atom name, w) = Bool.true
    · simp only [k, ite_true, Option.some.injEq] at look
      obtain ⟨u, ru, -⟩ := keep k
      exact ⟨u, look ▸ ru⟩
    · simp [k] at look)
  have staticU : mapLookup U (.atom "dynamic") = Option.none := by
    rw [(lookU "dynamic").1 staticN]
    exact valid.static
  refine ⟨N, U, negation, union, staticU, subtype_term _ T U term staticU fun e member => ?_⟩
  have hT := mapLookup_of_mem_mapEntries member
  obtain ⟨name, key⟩ := atom_key_of term hT
  rw [key] at hT ⊢
  cases hX : mapLookup X (.atom name) with
  | none =>
    have hN := (lookups T term name e.2 hT).1 hX
    obtain ⟨w, run, empty⟩ := key_absent δ term hT
    exact ⟨e.2, w, (lookU name).2.1 _ hN hX, run, empty⟩
  | some x =>
    obtain ⟨w, run, drop, keep⟩ := key_ok δ ops hK X valid term hT hX
    have look := (lookups T term name e.2 hT).2 x w hX run
    by_cases k : kept (.atom name, w) = Bool.true
    · obtain ⟨u, ru, w', rw', empty⟩ := keep k
      simp only [k, ite_true] at look
      exact ⟨u, w', (lookU name).2.2 x w u hX look ru, rw', empty⟩
    · simp only [k, Bool.false_eq_true, ite_false] at look
      obtain ⟨w', rw', empty⟩ := drop (by simpa using k)
      exact ⟨x, w', by rw [(lookU name).1 look, hX], rw', empty⟩

end Elixir.STTDescrProofsTest
