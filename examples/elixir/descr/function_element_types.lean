namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Function types of element types: arrows between element types, whose points are functions. -/

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- Literals of the BDD of the arity `q`: arrows with that many arguments, for arities that are natural numbers. -/
def FunArityN (E : Term → Prop) (q t : Term) : Prop := ∃ n : Nat, q = .integer n ∧ FunLit E n t

/-- Arities: maps whose keys are natural numbers. -/
def NatKeys (R : List (Term × Term)) : Prop := ∀ q, (mapLookup R q).isSome → ∃ n : Nat, q = .integer n

/-- Function types of element types: unions of some arities, or negations, of maps from arities to BDDs of arrows. -/
def FunA (E : Term → Prop) (x : Term) : Prop :=
  ∃ (pos : Bool) (R : List (Term × Term)), x = .tuple #[.atom (if pos then "union" else "negation"), .map R] ∧
    (pos = Bool.true → R ≠ []) ∧ AllBddP (FunArityN E) R ∧ NatKeys R

/-- Points of function types of element types: an arity and the valuation of arrows a function of that arity
induces. -/
def FVal (E : Term → Prop) (den : Term → V → Prop) (a : Term) (ρ : Term → Bool) : Prop :=
  ∃ (n : Nat) (g : List (FunSem.Row V)), a = .integer n ∧ (∀ r ∈ g, FunSem.ValidRow n r) ∧ ρ = valF E den g

theorem fVal_wit : ∃ a ρ, Resp ρ ∧ FVal E den a ρ :=
  ⟨.integer 0, valF E den [], valF_resp [], 0, [], rfl, by simp, rfl⟩

theorem FunA.funF {x : Term} (h : FunA E x) : FunF x :=
  let ⟨p, R, e, _, b, _⟩ := h
  ⟨p, R, e, fun q v h => (b q v h).mono fun _ _ => trivial⟩

theorem funA_top : FunA E funTopT :=
  ⟨Bool.false, [], rfl, by simp, fun q v h => by simp [mapLookup] at h, fun q h => by simp [mapLookup] at h⟩

theorem funLit_mono {E' : Term → Prop} (h : ∀ a, E a → E' a) {n : Int} {t : Term} (ht : FunLit E n t) :
    FunLit E' n t :=
  let ⟨k, args, ret, e, len, ha, hr⟩ := ht
  ⟨k, args, ret, e, len, fun a ma => h a (ha a ma), h ret hr⟩

/-! Heights of function literals and BDDs. -/

theorem lh_flit (k : Int) (args : List Term) (ret : Term) :
    lh (.tuple #[.integer k, Term.list args, ret]) = max (lh (Term.list args)) (lh ret) + 1 := by
  refine lh_leaf _ _ _ ?_ ?_ ?_ ?_
  · rintro ⟨h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨-, h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨r, a, h, -⟩; cases h

theorem flit_node_lh (h k : Int) (args : List Term) (ret c u d : Term) :
    lh (.tuple #[.integer h, .tuple #[.integer k, Term.list args, ret], c, u, d]) =
      max (lh (.tuple #[.integer k, Term.list args, ret])) (max (lh c) (max (lh u) (lh d))) := by
  refine lh_node_lit _ _ _ _ _ _ _ ?_ ?_ ?_
  · rintro ⟨h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨-, h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨r, a, h, -⟩; cases h

theorem lh_list_le : ∀ (l : List Term) {M : Nat}, (∀ a ∈ l, lh a ≤ M) → lh (Term.list l) ≤ M
  | [], _, _ => by simp [Term.list, lh]
  | a :: l, M, h => by
    simp only [Term.list, lh]
    have := lh_list_le l fun b mb => h b (List.mem_cons_of_mem _ mb)
    have := h a List.mem_cons_self
    omega

theorem le_lh_list : ∀ {l : List Term} {a : Term}, a ∈ l → lh a ≤ lh (Term.list l)
  | b :: l, a, m => by
    simp only [Term.list, lh]
    rcases List.mem_cons.mp m with rfl | m
    · omega
    · have := le_lh_list m; omega

/-- Function literals. -/
def FShape (t : Term) : Prop := ∃ (k : Int) (args : List Term) (ret : Term), t = .tuple #[.integer k, Term.list args, ret]

theorem FunLit.shape {n : Int} {t : Term} (h : FunLit E n t) : FShape t :=
  let ⟨k, args, ret, e, _⟩ := h
  ⟨k, args, ret, e⟩

/-- Literals of function BDDs are no higher than the BDD. -/
theorem fbdd_lh_le {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (lits : ∀ t, ok t → FShape t) :
    ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x := by
  revert lits
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → FShape t) → ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _ _ _; exact Bdd.top
  · intro _ _ _ _; exact Bdd.bot
  · intro ok k x y okl _ M le
    exact Bdd.leaf_iff.mpr ⟨okl, le⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd lits M le
    obtain ⟨k', args, ret, rfl⟩ := lits _ okl
    rw [flit_node_lh] at le
    have hlit : lh (.tuple #[.integer k', Term.list args, ret]) ≤ M := by omega
    have hc' : lh c ≤ M ∧ lh u ≤ M ∧ lh d ≤ M := by omega
    have lits' : ∀ t, Above ok (.tuple #[.integer k', Term.list args, ret]) t → FShape t := fun t ht => lits t ht.1
    obtain ⟨isLeaf, -⟩ := Bdd.node_iff.mp (show Bdd ok (.tuple #[.integer h, .tuple #[.integer k', Term.list args, ret], c, u, d])
      from Bdd.node_iff.mpr ⟨⟨_, _, _, rfl⟩, okl, hc, hu, hd⟩)
    refine Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, hlit⟩, ?_, ?_, ?_⟩
    · exact (ic lits' M hc'.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (iu lits' M hc'.2.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (idd lits' M hc'.2.2).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩

/-- Function BDDs whose literals are below a positive height are below it. -/
theorem fbdd_lh_bound {ok : Term → Prop} {r : Term} (wr : Bdd ok r) {M : Nat}
    (lits : ∀ t, ok t → FShape t ∧ lh t ≤ M) (top : 1 ≤ M) : lh r ≤ M := by
  revert lits top
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → FShape t ∧ lh t ≤ M) → 1 ≤ M → lh r ≤ M)
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ top; simpa [lh] using top
  · intro _ _ top; simpa [lh] using top
  · intro ok k x y okl lits _
    exact (lits _ okl).2
  · intro ok h lit c u d leaf okl _ _ _ ic iu idd lits one
    obtain ⟨⟨k', args, ret, rfl⟩, le⟩ := lits _ okl
    have lits' : ∀ t, Above ok (.tuple #[.integer k', Term.list args, ret]) t → FShape t ∧ lh t ≤ M :=
      fun t ht => lits t ht.1
    have hc := ic lits' one
    have hu := iu lits' one
    have hd := idd lits' one
    rw [flit_node_lh]
    omega

/-- Function BDDs have a height. -/
theorem fbdd_pos {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (lits : ∀ t, ok t → FShape t) :
    1 ≤ lh r := by
  revert lits
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → FShape t) → 1 ≤ lh r) ?_ ?_ ?_ ?_ ok r wr
  · intro _ _; simp [lh]
  · intro _ _; simp [lh]
  · intro ok k x y okl lits
    obtain ⟨k', args, ret, e⟩ := lits _ okl
    rw [e, lh_flit]; omega
  · intro ok h lit c u d leaf okl _ _ _ _ _ _ lits
    obtain ⟨k', args, ret, rfl⟩ := lits _ okl
    rw [flit_node_lh, lh_flit]; omega

/-! Plain operations on function types of element types. -/

/-- Literals of arity `q` below the height `L`. -/
abbrev FunArityL (E : Term → Prop) (L : Nat) (q t : Term) : Prop := FunArityN E q t ∧ lh t ≤ L

theorem lh_tag (p : Bool) (M : List (Term × Term)) :
    lh (.tuple #[.atom (if p then "union" else "negation"), .map M]) = lh (.map M) := by
  have : lh (.atom (if p then "union" else "negation")) = 0 := by cases p <;> simp [lh]
  simp [lh, this]

theorem lh_union (M : List (Term × Term)) : lh (.tuple #[.atom "union", .map M]) = lh (.map M) := lh_tag Bool.true M
theorem lh_negation (M : List (Term × Term)) : lh (.tuple #[.atom "negation", .map M]) = lh (.map M) :=
  lh_tag Bool.false M

theorem funArity_shape {q t : Term} (h : FunArityN E q t) : FShape t :=
  let ⟨_, _, lit⟩ := h
  FunLit.shape lit

theorem lookup_lh {R : List (Term × Term)} {q v : Term} (h : mapLookup R q = some v) : lh v ≤ lh (.map R) := by
  obtain ⟨e, me, -, rfl⟩ := lookup_entry h
  exact le_lh_map me

/-- Maps of BDDs of literals below a positive height are below it. -/
theorem allBdd_lh {R : List (Term × Term)} {L : Nat} (b : AllBddP (FunArityL E L) R) (one : 1 ≤ L) :
    lh (.map R) ≤ L :=
  lh_map_le.mpr fun _e me =>
    fbdd_lh_bound (b _ _ (mapLookup_of_mem_mapEntries me)) (fun _t ht => ⟨funArity_shape ht.1, ht.2⟩) one

theorem allBdd_bound {R : List (Term × Term)} (b : AllBddP (FunArityN E) R) {L : Nat} (le : lh (.map R) ≤ L) :
    AllBddP (FunArityL E L) R := fun q v h =>
  fbdd_lh_le (b q v h) (fun _ ht => funArity_shape ht) L (by have := lookup_lh h; omega)

theorem allBdd_unbound {R : List (Term × Term)} {L : Nat} (b : AllBddP (FunArityL E L) R) : AllBddP (FunArityN E) R :=
  fun q v h => (b q v h).mono fun _ ht => ht.1

/-- Function types of element types of height zero are the top function type. -/
theorem funA_lh0 {x : Term} (fx : FunA E x) (h : lh x = 0) : x = funTopT := by
  obtain ⟨p, R, rfl, ne, b, -⟩ := fx
  rw [lh_tag] at h
  have nil : R = [] := by
    cases R with
    | nil => rfl
    | cons e rest =>
      exfalso
      have hl : mapLookup (e :: rest) e.1 = some e.2 := by simp [mapLookup]
      have := lookup_lh hl
      have := fbdd_pos (b _ _ hl) (fun _ ht => funArity_shape ht)
      omega
  subst nil
  cases p
  · rfl
  · exact absurd rfl (ne rfl)

theorem funA_ne {R : List (Term × Term)} (h : R ≠ []) : ∃ a, (mapLookup R a).isSome := by
  cases R with
  | nil => exact absurd rfl h
  | cons e rest => exact ⟨e.1, by simp [mapLookup]⟩

theorem ne_of_some {M : List (Term × Term)} {a : Term} (h : (mapLookup M a).isSome) : M ≠ [] := by
  rintro rfl; simp [mapLookup] at h

/-- Function results whose unions have no arities become `0`. -/
theorem funA_result {pos : Bool} {M : List (Term × Term)} {L : Nat} (bM : AllBddP (FunArityL E L) M) (kM : NatKeys M)
    (one : 1 ≤ L)
    (e : Nat → Except Exception Term)
    (h₁ : pos = Bool.false → ∀ n, e n = .ok (.tuple #[.atom "negation", .map M]))
    (h₂ : pos = Bool.true → M = [] → ∀ n, e n = .ok (.integer 0))
    (h₃ : pos = Bool.true → M ≠ [] → ∀ n, e n = .ok (.tuple #[.atom "union", .map M])) :
    ∃ r, (∀ n, e n = .ok r) ∧ (kept (.atom "fun", r) = Bool.true → FunA E r ∧ lh r ≤ L) := by
  cases pos
  · exact ⟨_, h₁ rfl, fun _ => ⟨⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, kM⟩, by
      rw [lh_negation]; exact allBdd_lh bM one⟩⟩
  · by_cases hM : M = []
    · exact ⟨_, h₂ rfl hM, fun k => by simp [kept] at k⟩
    · exact ⟨_, h₃ rfl hM, fun _ => ⟨⟨Bool.true, M, rfl, fun _ => hM, allBdd_unbound bM, kM⟩, by
        rw [lh_union]; exact allBdd_lh bM one⟩⟩

theorem funA_bounded {x : Term} (fx : FunA E x) {L : Nat} (le : lh x ≤ L) :
    ∃ (p : Bool) (R : List (Term × Term)), x = .tuple #[.atom (if p then "union" else "negation"), .map R] ∧
      (p = Bool.true → R ≠ []) ∧ AllBddP (FunArityL E L) R ∧ NatKeys R := by
  obtain ⟨p, R, rfl, ne, b, k⟩ := fx
  rw [lh_tag] at le
  exact ⟨p, R, rfl, ne, allBdd_bound b le, k⟩

theorem natKeys_of {M R : List (Term × Term)} (k : NatKeys R) (h : ∀ a, (mapLookup M a).isSome → (mapLookup R a).isSome) :
    NatKeys M := fun q hq => k q (h q hq)

theorem natKeys_or {M R₁ R₂ : List (Term × Term)} (k₁ : NatKeys R₁) (k₂ : NatKeys R₂)
    (h : ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome ∨ (mapLookup R₂ a).isSome) : NatKeys M :=
  fun q hq => (h q hq).elim (k₁ q) (k₂ q)

theorem funA_union {x y : Term} (fx : FunA E x) (fy : FunA E y) :
    ∃ w, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom "fun") x y = .ok w) ∧ FunA E w ∧
      lh w ≤ max (lh x) (lh y) := by
  by_cases z : max (lh x) (lh y) = 0
  · rw [funA_lh0 fx (by omega), funA_lh0 fy (by omega)]
    exact ⟨funTopT, fun n => fun_top_union n, funA_top, by rw [lh_funTop]; omega⟩
  have one : 1 ≤ max (lh x) (lh y) := by omega
  obtain ⟨p₁, R₁, rfl, n₁, b₁, k₁⟩ := funA_bounded fx (Nat.le_max_left _ (lh y))
  obtain ⟨p₂, R₂, rfl, n₂, b₂, k₂⟩ := funA_bounded fy (Nat.le_max_right (lh (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])) _)
  generalize max (lh (Term.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁]))
    (lh (Term.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂])) = L at one b₁ b₂ ⊢
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, keys⟩ := repr_inter_uniform b₁ b₂
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, natKeys_of k₁ keys⟩, by rw [lh_tag]; exact allBdd_lh bM one⟩
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₁ b₂
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, natKeys_of k₁ keys⟩, by rw [lh_tag]; exact allBdd_lh bM one⟩
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₂ b₁
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, natKeys_of k₂ keys⟩, by rw [lh_tag]; exact allBdd_lh bM one⟩
  · obtain ⟨M, bM, run, keys, keys'⟩ := repr_union_uniform b₁ b₂
    obtain ⟨a, ha⟩ := funA_ne (n₁ rfl)
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.true, M, rfl, fun _ => ne_of_some (keys a ha), allBdd_unbound bM, natKeys_or k₁ k₂ keys'⟩,
      by rw [lh_tag]; exact allBdd_lh bM one⟩

theorem funA_inter {x y : Term} (fx : FunA E x) (fy : FunA E y) :
    ∃ w, (∀ n, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom "fun") x y = .ok w) ∧
      (kept (.atom "fun", w) = Bool.true → FunA E w ∧ lh w ≤ max (lh x) (lh y)) := by
  by_cases z : max (lh x) (lh y) = 0
  · rw [funA_lh0 fx (by omega), funA_lh0 fy (by omega)]
    exact ⟨funTopT, fun n => fun_top_inter n, fun _ => ⟨funA_top, by rw [lh_funTop]; omega⟩⟩
  have one : 1 ≤ max (lh x) (lh y) := by omega
  obtain ⟨p₁, R₁, rfl, n₁, b₁, k₁⟩ := funA_bounded fx (Nat.le_max_left _ (lh y))
  obtain ⟨p₂, R₂, rfl, n₂, b₂, k₂⟩ := funA_bounded fy (Nat.le_max_right (lh (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])) _)
  generalize max (lh (Term.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁]))
    (lh (Term.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂])) = L at one b₁ b₂ ⊢
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, -, keys⟩ := repr_union_uniform b₁ b₂
    refine funA_result (pos := Bool.false) bM (natKeys_or k₁ k₂ keys) one _ (fun _ n => ?_) (fun h => by cases h) (fun h => by cases h)
    simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
      Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₂ b₁
    refine funA_result (pos := Bool.true) bM (natKeys_of k₂ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, keys⟩ := repr_inter_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]

theorem funA_diff {x y : Term} (fx : FunA E x) (fy : FunA E y) :
    ∃ w, (∀ n, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun") x y = .ok w) ∧
      (kept (.atom "fun", w) = Bool.true → FunA E w ∧ lh w ≤ max (lh x) (lh y)) := by
  by_cases z : max (lh x) (lh y) = 0
  · rw [funA_lh0 fx (by omega), funA_lh0 fy (by omega)]
    exact ⟨.integer 0, fun n => fun_top_diff (n + 1), fun k => by simp [kept] at k⟩
  have one : 1 ≤ max (lh x) (lh y) := by omega
  obtain ⟨p₁, R₁, rfl, n₁, b₁, k₁⟩ := funA_bounded fx (Nat.le_max_left _ (lh y))
  obtain ⟨p₂, R₂, rfl, n₂, b₂, k₂⟩ := funA_bounded fy (Nat.le_max_right (lh (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])) _)
  generalize max (lh (Term.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁]))
    (lh (Term.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂])) = L at one b₁ b₂ ⊢
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₂ b₁
    refine funA_result (pos := Bool.true) bM (natKeys_of k₂ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, -, keys⟩ := repr_union_uniform b₁ b₂
    refine funA_result (pos := Bool.false) bM (natKeys_or k₁ k₂ keys) one _ (fun _ n => ?_) (fun h => by cases h) (fun h => by cases h)
    simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
      Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · obtain ⟨M, bM, run, keys⟩ := repr_inter_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]

/-- Literals of arity `n` of the function BDD `b`, whose types are below `b`. -/
abbrev LitB (E : Term → Prop) (b : Term) (n : Nat) (t : Term) : Prop := FunLit (EB E (lh b)) n t

theorem litB_of {q b : Term} (wb : Bdd (FunArityN E q) b) {n : Nat} (hq : q = .integer n) : Bdd (LitB E b n) b := by
  refine (fbdd_lh_le wb (fun _ ht => funArity_shape ht) (lh b) (Nat.le_refl _)).mono fun t ⟨⟨n', e', lit⟩, le⟩ => ?_
  rw [hq] at e'
  simp only [Term.integer.injEq] at e'
  obtain rfl : n' = n := by omega
  obtain ⟨k, args, ret, rfl, len, ha, hr⟩ := lit
  rw [lh_flit] at le
  refine ⟨k, args, ret, rfl, len, fun a ma => ⟨ha a ma, ?_⟩, hr, ?_⟩
  · have := le_lh_list ma; omega
  · omega

/-- Function types of element types below a height are nested function types of element types below it. -/
theorem funA_ffield {x : Term} (fx : FunA E x) {N : Nat} (h : lh x < N) : FField (EB E N) x := by
  obtain ⟨p, R, rfl, -, bR, kR⟩ := fx
  refine ⟨p, R, rfl, fun q v hv => ?_⟩
  obtain ⟨n, hn⟩ := kR q (by rw [hv]; rfl)
  have le : lh v ≤ lh (.tuple #[.atom (if p then "union" else "negation"), .map R]) := by
    rw [lh_tag]; exact lookup_lh hv
  exact (litB_of (bR q v hv) hn).mono fun t ht =>
    ⟨n, hn, funLit_mono (fun a ha => ⟨ha.1, by have := ha.2; omega⟩) ht⟩


/-- The element types of the next level, below a height. -/
theorem descr_nest (ef : EF nd E V den tl K) {X : List (Term × Term)}
    (sX : DescrC (FunA E) (TField E) (LF E) (MField E) X) {N : Nat} (h : lh (.map X) < N) : NestFields (EB E N) X := by
  refine ⟨fun q hq => ?_, fun name w hw => ?_⟩
  · obtain ⟨name, m, rfl⟩ := sX.keys q hq
    simp [names] at m
    rcases m with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · have le := lh_field_le hw
    rcases sX.fields name w hw with ⟨rfl, b⟩ | ⟨rfl, a⟩ | ⟨rfl, f⟩ | ⟨rfl, l⟩ | ⟨rfl, t⟩ | ⟨rfl, m⟩
    · exact Or.inl ⟨by simp, by simp, by simp, by simp, Or.inl ⟨rfl, b⟩⟩
    · exact Or.inl ⟨by simp, by simp, by simp, by simp, Or.inr (Or.inl ⟨rfl, a⟩)⟩
    · exact Or.inr (Or.inl ⟨rfl, funA_ffield f (by omega)⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lf_nest ef l (by omega) (by omega)⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, tfield_nest t (by omega)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, mfield_nest m (by omega)⟩)))

end

end Elixir.STTDescrProofsTest.Nest
