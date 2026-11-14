/-! Differences. -/

/-- The difference updates the fields of the left type that the right type also has,
dropping them when they become `0` or `bdd_bot`. -/
def differenceStep (g : Term → Term → Term → Term) (acc : List (Term × Term)) (entry : Term × Term) :
    List (Term × Term) :=
  match mapLookup acc entry.1 with
  | some v₁ =>
    if kept (entry.1, g entry.1 v₁ entry.2) then (entry.1, g entry.1 v₁ entry.2) :: acc
    else acc.filter fun e => compareExact (fuel entry.1 e.1) entry.1 e.1 != .eq
  | none => acc

theorem member_dropped (key w : Term) :
    isMember w [.integer 0, .atom "bdd_bot"] = if kept (key, w) then .atom "false" else .atom "true" := by
  by_cases zero : compareExact (fuel w (.integer 0)) w (.integer 0) = .eq <;>
    by_cases bot : compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") = .eq <;>
    simp [isMember, kept, zero, bot]

theorem difference_step (depth : Nat) (fn : Term) (g : Term → Term → Term → Term) (acc : List (Term × Term))
    (key v₂ : Term)
    (calls : ∀ v₁, mapLookup acc key = some v₁ →
      Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[key, v₁, v₂] =
        .ok (g key v₁ v₂)) :
    Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        fn key v₂ (.map acc) = .ok (.map (differenceStep g acc (key, v₂))) := by
  unfold Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4»
  cases found : mapLookup acc key with
  | none => simp [getMapKeys_single, found, differenceStep]
  | some v₁ =>
    simp only [getMapKeys_single, found, Option.toList_some,
      calls v₁ found, Lynx.Except.ok_bind, member_dropped key, differenceStep]
    obtain ⟨e, member, same⟩ := (mapLookup_isSome acc key).mp (by simp [found])
    by_cases keep : kept (key, g key v₁ v₂) <;> simp [keep, Erlang.erlang.«is_map/1», Erlang.maps.«update/3»,
      Erlang.maps.«remove/2»]
    exact ⟨e.1, ⟨e.2, member⟩, same⟩

theorem step_other (g : Term → Term → Term → Term) (acc : List (Term × Term)) (e : Term × Term) (q : Term)
    (other : compareExact (fuel q e.1) q e.1 ≠ .eq) : mapLookup (differenceStep g acc e) q = mapLookup acc q := by
  unfold differenceStep
  cases mapLookup acc e.1 with
  | none => rfl
  | some v₁ =>
    by_cases keep : kept (e.1, g e.1 v₁ e.2)
    · simp [keep, mapLookup, other]
    · simp only [keep, Bool.false_eq_true, ite_false]
      rw [mapLookup_filter]
      simp [other]

theorem step_same (g : Term → Term → Term → Term) (acc : List (Term × Term)) (e : Term × Term) (q : Term)
    (same : compareExact (fuel q e.1) q e.1 = .eq) :
    mapLookup (differenceStep g acc e) q = (mapLookup acc e.1).bind fun v₁ =>
      if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none := by
  unfold differenceStep
  cases found : mapLookup acc e.1 with
  | none => simp only [Option.bind_none]; rw [mapLookup_congr same, found]
  | some v₁ =>
    by_cases keep : kept (e.1, g e.1 v₁ e.2)
    · simp [keep, mapLookup, same]
    · simp only [keep, Bool.false_eq_true, ite_false, Option.bind_some]
      rw [mapLookup_filter]
      simp [same]

/-- Folding the difference over the entries of the right type. -/
theorem difference_fold (depth : Nat) (fn : Term) (g : Term → Term → Term → Term) (es acc : List (Term × Term))
    (distinct : es.Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq))
    (calls : ∀ e ∈ es, ∀ v₁, mapLookup acc e.1 = some v₁ →
      Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[e.1, v₁, e.2] =
        .ok (g e.1 v₁ e.2)) :
    ∃ M, es.foldlM (fun acc entry =>
        (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
          (.function "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3
          #[fn]) #[entry.1, entry.2, acc] : Except Exception Term))
        (.map acc) = .ok (.map M) ∧
      (∀ q, mapLookup M q =
        match es.find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => (mapLookup acc e.1).bind fun v₁ =>
            if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none
        | none => mapLookup acc q) ∧ M = es.foldl (differenceStep g) acc := by
  induction es generalizing acc with
  | nil => exact ⟨acc, rfl, fun q => rfl, rfl⟩
  | cons e rest ih =>
    have apart := List.pairwise_cons.mp distinct
    have step : (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
        (.function "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3
          #[fn]) #[e.1, e.2, .map acc] : Except Exception Term) =
        .ok (.map (differenceStep g acc e)) := by
      rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-dynamic_difference/3-fun-0-/3».pure,
        difference_step depth fn g acc e.1 e.2 (calls e (List.mem_cons_self ..))]
    obtain ⟨M, run, look, explicit⟩ := ih (differenceStep g acc e) apart.2 (by
      intro e' member v₁ found
      rw [step_other g acc e e'.1 (fun same => apart.1 e' member (Lynx.Term.compareExact_eq_symm same))] at found
      exact calls e' (List.mem_cons_of_mem _ member) v₁ found)
    refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_,
      by rw [explicit]; rfl⟩
    rw [look q]
    by_cases same : compareExact (fuel q e.1) q e.1 = .eq
    · have absent : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) = none := by
        rw [List.find?_eq_none]
        intro p member hit
        exact apart.1 p member
          (Lynx.Term.compareExact_eq_trans (Lynx.Term.compareExact_eq_symm same) (of_decide_eq_true hit))
      simp only [absent, List.find?_cons, same, decide_true]
      exact step_same g acc e q same
    · simp only [List.find?_cons, same, decide_false]
      cases hit : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) with
      | none => exact step_other g acc e q same
      | some e' =>
        have qe' : compareExact (fuel q e'.1) q e'.1 = .eq := by simpa using List.find?_some hit
        have other : compareExact (fuel e'.1 e.1) e'.1 e.1 ≠ .eq := fun same' =>
          same (Lynx.Term.compareExact_eq_trans qe' same')
        simp only
        rw [step_other g acc e e'.1 other]

/-! Bitmap differences remove the bits of the right bitmap. -/

theorem add_eq_or (x y : Nat) (disjoint : x &&& y = 0) : x + y = x ||| y := by
  let w := x + y + 1
  have small (n : Nat) (h : n ≤ x + y) : n < 2 ^ w :=
    Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega))
  have bv : BitVec.ofNat w x &&& BitVec.ofNat w y = 0#w := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (small x (by omega)), Nat.mod_eq_of_lt (small y (by omega)), disjoint]
  have := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ bv)
  simp only [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (small x (by omega)), Nat.mod_eq_of_lt (small y (by omega)),
    Nat.mod_eq_of_lt (small (x + y) (by omega))] at this
  exact this

theorem testBit_sub_and (a b i : Nat) :
    (a - (a &&& b)).testBit i = (a.testBit i && !b.testBit i) := by
  have disjoint : (a ^^^ (a &&& b)) &&& (a &&& b) = 0 := Nat.eq_of_testBit_eq fun j => by
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases a.testBit j <;> cases b.testBit j <;> rfl
  have whole : (a ^^^ (a &&& b)) ||| (a &&& b) = a := Nat.eq_of_testBit_eq fun j => by
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
    cases a.testBit j <;> cases b.testBit j <;> rfl
  have split := add_eq_or _ _ disjoint
  rw [whole] at split
  rw [show a - (a &&& b) = a ^^^ (a &&& b) by omega]
  simp only [Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

/-- The difference of two atom types holds the atoms of the first only, and is `0` when empty. -/
theorem atom_difference (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
    (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
    (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
    (∃ (p : Bool) (E : List (Term × Term)),
      Elixir.Module.Types.Descr.«atom_difference/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
        .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
      Erlang.sets.elements? (.map E) = some E ∧
      -- Differences are unions unless a negation removes a union.
      p = (p₁ || !p₂) ∧ (p = Bool.true → E ≠ []) ∧
      ∀ q, (p == (mapLookup E q).isSome) =
        ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome))) ∨
    (Elixir.Module.Types.Descr.«atom_difference/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .ok (.integer 0) ∧
      ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome)) = Bool.false) := by
  cases p₁ <;> cases p₂
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
    refine Or.inl ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE,
      Erlang.erlang.«==/2»], setE, rfl, fun negated => Bool.noConfusion negated, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp

theorem unfold_map (d : Dispatcher) (entries : List (Term × Term)) :
    Elixir.Module.Types.Descr.«unfold/1» d (.map entries) = .ok (.map entries) := by
  rw [Elixir.Module.Types.Descr.«unfold/1».eq_def]; rfl

theorem static_map {X : List (Term × Term)} (static : mapLookup X (.atom "dynamic") = none) :
    Erlang.erlang.«is_map_key/2» (.atom "dynamic") (.map X) = .ok (.atom "false") := by
  have absent : X.any (fun entry => compareExact (fuel (.atom "dynamic") entry.1) (.atom "dynamic") entry.1 == .eq) = Bool.false := by
    rw [Bool.eq_false_iff]
    intro present
    obtain ⟨entry, member, same⟩ := List.any_eq_true.mp present
    have := (mapLookup_isSome X (.atom "dynamic")).mpr ⟨entry, member, by simpa using same⟩
    rw [static] at this
    cases this
  simp [Erlang.erlang.«is_map_key/2», absent, Term.false]

