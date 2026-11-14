namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- The type of a single atom, as `atom/1` builds it. -/
def atomT (s : String) : Term := .map [(.atom "atom", .tuple #[.atom "union", .map [(.atom s, .nil)]])]

theorem atom_one (s : String) : Elixir.Module.Types.Descr.«atom/1» (Term.list [.atom s]) = .ok (atomT s) := by
  have pl : Term.properList? (Term.cons (.atom s) .nil) = some [.atom s] := Term.properList?_list [.atom s]
  simp [Elixir.Module.Types.Descr.«atom/1», Elixir.Module.Types.Descr.«atom_new/1», Erlang.erlang.«is_list/1»,
    Erlang.sets.«from_list/2», Erlang.sets.«from_list/1», atomT, Term.list, pl]

section
variable {t : Term} {n : Nat}

theorem atomT_de (s : String) : DE (level t n).E (atomT s) :=
  single_de (by simp [names]) (Or.inr (Or.inl ⟨rfl, ⟨Bool.true, _, rfl, by simp [Erlang.sets.elements?]⟩, .atom s,
    by simp [amemV, mapLookup]⟩))

theorem atomT_static (s : String) : Static (atomT s) := Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩)

theorem atomT_den (s : String) (v : PN t n) : denD (atomT s) v ↔ v.1.1 = "atom" ∧ v.1.2.2.1 = .atom s := by
  rw [atomT, denD_single]
  simp [dn_atom, amemV, mapLookup]

/-- Pairs of an atom key and the values at that key of the maps of lines. -/
def AtomPair (t : Term) (n : Nat) (lines : List Term) (s : String) (p : PN t (n + 1)) : Prop :=
  ∃ w : List (level t (n + 1)).V, (∀ X, denD (.map X) p ↔ TT t (n + 1) X w) ∧
    ∃ k x, w = [k, x] ∧ (level t (n + 1)).den (atomT s) k ∧ ∃ L ∈ lines, LongM (level t (n + 1)).den L s (some x)

end

section
variable {t : Term} {n : Nat}

/-- Seen keys: atoms mapped to `[]`. -/
def SeenOk (S : List (Term × Term)) : Prop := ∀ e ∈ S, ∃ s, e = (.atom s, .nil)

/-- Accumulated pairs: those of an initial type, and of the atom keys seen. -/
def AccOk (t : Term) (n : Nat) (lines : List Term) (acc₀ : Term) (S : List (Term × Term)) (acc : Term) : Prop :=
  DE (level t (n + 1)).E acc ∧ ∀ p, denD acc p ↔ denD acc₀ p ∨ ∃ s, (Term.atom s, Term.nil) ∈ S ∧ AtomPair t n lines s p

theorem seen_lookup {S : List (Term × Term)} (hS : SeenOk S) (s : String) :
    (mapLookup S (.atom s)).isSome = Bool.true ↔ (Term.atom s, Term.nil) ∈ S := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    rw [mapLookup] at hv
    cases e : S.find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
    | none => rw [e] at hv; cases hv
    | some r =>
      have mr := List.mem_of_find?_eq_some e
      have := List.find?_some e
      simp only [decide_eq_true_eq] at this
      obtain ⟨s', rfl⟩ := hS r mr
      have : s = s' := by simpa using this
      subst this
      exact mr
  · intro h
    rw [mapLookup]
    cases e : S.find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
    | none => exact absurd (List.find?_eq_none.mp e _ h) (by simp)
    | some r => simp

/-- One field of `map_to_list_static/3`: a new atom key adds the pairs of its values in the maps of the lines. -/
theorem fetch_step {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) {acc₀ : Term}
    {S : List (Term × Term)} (hS : SeenOk S) {acc : Term} (ha : AccOk t n lines acc₀ S acc) (s : String) {f : Term}
    (hf : FieldValue (level t (n + 1)).E f) :
    ∃ S' acc', Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5» (D (M + 3)) (Term.list lines) mtlF (.atom s) f
        (.tuple #[.map S, acc]) = .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ (Term.atom s, Term.nil) ∈ S' ∧
      (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' := by
  obtain ⟨ty, o, rfl, -⟩ := hf
  by_cases seen : (mapLookup S (.atom s)).isSome = Bool.true
  · refine ⟨S, acc, ?_, hS, (seen_lookup hS s).mp seen, fun e me => me, ha⟩
    simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5», Erlang.erlang.«is_map_key/2», any_key, seen,
      Lynx.Term.isMember, Term.true]
  obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch (level t (n + 1)).ef (n := M) (by rw [level_K] at hM ⊢; omega) s lines hl
  obtain ⟨vt, hvt, ⟨o', rfl⟩, svt⟩ := fieldValue_den (den := (level t (n + 1)).den) hF
  have vals : ∀ x, (level t (n + 1)).den vt x ↔ ∃ L ∈ lines, LongM (level t (n + 1)).den L s (some x) :=
    fun x => (svt x).trans (sF _)
  have hS' : SeenOk ((.atom s, .nil) :: S) := fun e me => (List.mem_cons.mp me).elim (fun h => ⟨s, h⟩) (hS e)
  obtain ⟨eb, reb, seb⟩ := (level t (n + 1)).ef.empty_pub hvt
  cases eb
  · obtain ⟨P, rP, dP, sP⟩ := mtl_pair (t := t) (n := n + 1) (e_succ (atomT_de s)) hvt (atomT_static s)
      ((level t (n + 1)).ef.static hvt) (M + 3)
    obtain ⟨c, hc, rc, sc⟩ := (ef_next t (n + 1)).opt_union [] ha.1 dP (m := M + 3) (by omega)
    refine ⟨(.atom s, .nil) :: S, c, ?_, hS', List.mem_cons_self, fun e me => List.mem_cons_of_mem _ me, hc, fun p => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5», Erlang.erlang.«is_map_key/2», any_key, seen,
        Lynx.Term.isMember, Term.false, rF, Erlang.maps.«put/3», reb (M + 3) (by rw [level_K] at hM ⊢; omega), boolAtom,
        Elixir.Module.Types.Descr.«opt_union/2»]
      rw [atom_one]
      simp [rP, rc]
    · have pe : PairPt t (n + 1) (atomT s) vt p ↔ AtomPair t n lines s p := by
        simp only [PairPt, AtomPair, vals]
      rw [sc, ha.2, sP, pe]
      simp only [List.mem_cons, Prod.mk.injEq, Term.atom.injEq, and_true]
      constructor
      · rintro ((h | ⟨s', m', h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨s', Or.inr m', h⟩
        · exact Or.inr ⟨s, Or.inl rfl, h⟩
      · rintro (h | ⟨s', e | m', h⟩)
        · exact Or.inl (Or.inl h)
        · subst e; exact Or.inr h
        · exact Or.inl (Or.inr ⟨s', m', h⟩)
  · refine ⟨(.atom s, .nil) :: S, acc, ?_, hS', List.mem_cons_self, fun e me => List.mem_cons_of_mem _ me, ha.1,
      fun p => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5», Erlang.erlang.«is_map_key/2», any_key, seen,
        Lynx.Term.isMember, Term.false, rF, Erlang.maps.«put/3», reb (M + 3) (by rw [level_K] at hM ⊢; omega), boolAtom]
    · rw [ha.2]
      have none : ¬AtomPair t n lines s p := fun ⟨_, _, _, x, _, _, h⟩ => seb.mp rfl x ((vals x).mpr h)
      simp only [List.mem_cons, Prod.mk.injEq, Term.atom.injEq, and_true]
      constructor
      · rintro (h | ⟨s', m', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s', Or.inr m', h⟩
      · rintro (h | ⟨s', e | m', h⟩)
        · exact Or.inl h
        · subst e; exact absurd h none
        · exact Or.inr ⟨s', m', h⟩

end

section
variable {t : Term} {n : Nat}

/-- `orddict:fold/3` of `map_to_list_static/3` over the fields of a literal. -/
theorem fetch_fold {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) (acc₀ : Term) :
    ∀ (l : List (Term × Term)), FieldsV (level t (n + 1)).E l → ∀ (S : List (Term × Term)) (acc : Term), SeenOk S →
      AccOk t n lines acc₀ S acc → ∃ S' acc', Erlang.orddict.«fold/3» (D (M + 4))
        (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-2-" 3 #[Term.list lines, mtlF])
        (.tuple #[.map S, acc]) (fieldsTerm l) = .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧
        (∀ s ∈ keyStrs l, (Term.atom s, Term.nil) ∈ S') ∧ (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc'
  | [], _, S, acc, hS, ha => ⟨S, acc, by rw [Erlang.orddict.«fold/3».eq_def]; simp [fieldsTerm, Term.list,
      Erlang.erlang.«is_function/2»], hS, by simp [keyStrs], fun e me => me, ha⟩
  | (k, f) :: rest, sl, S, acc, hS, ha => by
    obtain ⟨⟨s, rfl⟩, hf⟩ := sl.1 _ List.mem_cons_self
    obtain ⟨S₁, a₁, r₁, hS₁, m₁, sub₁, ha₁⟩ := fetch_step hM lines hl hS ha s hf
    obtain ⟨S₂, a₂, r₂, hS₂, m₂, sub₂, ha₂⟩ := fetch_fold hM lines hl acc₀ rest (fieldsV_tail sl) S₁ a₁ hS₁ ha₁
    refine ⟨S₂, a₂, ?_, hS₂, fun s' ms' => ?_, fun e me => sub₂ e (sub₁ e me), ha₂⟩
    · rw [Erlang.orddict.«fold/3».eq_def]
      simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-2-/3».pure, r₁, r₂]
    · simp only [keyStrs, List.filterMap_cons, List.mem_cons] at ms'
      rcases ms' with rfl | ms'
      · exact sub₂ _ m₁
      · exact m₂ s' ms'

/-- Literals whose field keys are all seen. -/
def SeenNamed (S : List (Term × Term)) (t : Term) : Prop :=
  ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    ∀ s ∈ keyStrs l, (Term.atom s, Term.nil) ∈ S

theorem seenNamed_mono {a b : List (Term × Term)} (h : ∀ e ∈ a, e ∈ b) {t : Term} (ht : SeenNamed a t) :
    SeenNamed b t :=
  fun k tag l e s ms => h _ (ht k tag l e s ms)

theorem fetch_leaf {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) (acc₀ : Term)
    {lit : Term} (hlit : MapLitV (level t (n + 1)).E lit) (S : List (Term × Term)) (acc : Term) (hS : SeenOk S)
    (ha : AccOk t n lines acc₀ S acc) :
    ∃ S' acc', Lynx.Dispatcher.pure (D (M + 5))
        (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF])
        #[lit, .tuple #[.map S, acc]] = .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ SeenNamed S' lit ∧
      (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' := by
  obtain ⟨k, tag, l, rfl, -, sl⟩ := hlit
  obtain ⟨S', a', run, hS', named, sub, ha'⟩ := fetch_fold hM lines hl acc₀ l sl S acc hS ha
  refine ⟨S', a', ?_, hS', fun k' tag' l' e s ms => ?_, sub, ha'⟩
  · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-3-/2».pure]
    simpa [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-3-/4»] using run
  · obtain ⟨-, -, e₃⟩ := tuple3_inj e
    rw [← fieldsTerm_inj e₃] at ms
    exact named s ms

/-- `bdd_reduce/3` of `map_to_list_static/3` over a map BDD sees all its field keys. -/
theorem fetch_reduce {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) (acc₀ : Term)
    {b : Term} (wb : Bdd (MLit (level t (n + 1)).E) b) :
    ∀ (S : List (Term × Term)) (acc : Term), SeenOk S → AccOk t n lines acc₀ S acc →
      ∃ S' acc', Elixir.Module.Types.Descr.«bdd_reduce/3» (D (M + 5)) b (.tuple #[.map S, acc])
          (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF]) =
          .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' ∧
        Bdd (fun u => MLit (level t (n + 1)).E u ∧ SeenNamed S' u) b := by
  refine Bdd.induction (P := fun ok b => (∀ u, ok u → MLit (level t (n + 1)).E u) →
      ∀ (S : List (Term × Term)) (acc : Term), SeenOk S → AccOk t n lines acc₀ S acc →
      ∃ S' acc', Elixir.Module.Types.Descr.«bdd_reduce/3» (D (M + 5)) b (.tuple #[.map S, acc])
          (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF]) =
          .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' ∧
        Bdd (fun u => ok u ∧ SeenNamed S' u) b)
    ?_ ?_ ?_ ?_ (MLit (level t (n + 1)).E) b wb (fun _ h => h)
  · intro ok _ S acc hS ha
    exact ⟨S, acc, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, hS, fun e me => me, ha, by simp [Bdd]⟩
  · intro ok _ S acc hS ha
    exact ⟨S, acc, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, hS, fun e me => me, ha, by simp [Bdd]⟩
  · intro ok k x y okl lit S acc hS ha
    obtain ⟨S', a', run, hS', named, sub, ha'⟩ := fetch_leaf hM lines hl acc₀ (lit _ okl).1 S acc hS ha
    exact ⟨S', a', by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simpa using run, hS', sub, ha',
      Bdd.leaf_iff.mpr ⟨okl, named⟩⟩
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits S acc hS ha
    have lits' : ∀ u, Above ok lit u → MLit (level t (n + 1)).E u := fun u hu => lits u hu.1
    obtain ⟨S₀, a₀, r₀, h₀, n₀, s₀, ha₀⟩ := fetch_leaf hM lines hl acc₀ (lits _ okl).1 S acc hS ha
    obtain ⟨S₁, a₁, r₁, h₁, s₁, ha₁, k₁⟩ := ic lits' S₀ a₀ h₀ ha₀
    obtain ⟨S₂, a₂, r₂, h₂, s₂, ha₂, k₂⟩ := iu lits' S₁ a₁ h₁ ha₁
    obtain ⟨S₃, a₃, r₃, h₃, s₃, ha₃, k₃⟩ := id lits' S₂ a₂ h₂ ha₂
    have t₀ : ∀ e ∈ S₀, e ∈ S₃ := fun e me => s₃ e (s₂ e (s₁ e me))
    refine ⟨S₃, a₃, ?_, h₃, fun e me => t₀ e (s₀ e me), ha₃, ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]
      simp [r₀, r₁, r₂, r₃]
    · have lift : ∀ (S' : List (Term × Term)), (∀ e ∈ S', e ∈ S₃) →
          ∀ u, (Above ok lit u ∧ SeenNamed S' u) → Above (fun u => ok u ∧ SeenNamed S₃ u) lit u :=
        fun S' sub u ⟨⟨o, lt⟩, nt⟩ => ⟨⟨o, seenNamed_mono sub nt⟩, lt⟩
      exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, seenNamed_mono t₀ n₀⟩,
        k₁.mono (lift S₁ fun e me => s₃ e (s₂ e me)), k₂.mono (lift S₂ fun e me => s₃ e me),
        k₃.mono (lift S₃ fun e me => me)⟩

end

end Elixir.STTDescrProofsTest.Nest
