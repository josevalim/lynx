namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple emptiness is exact under seen sets of higher BDDs. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem lh_atom {s : String} (h : s ≠ "bdd_top") (h' : s ≠ "bdd_bot") : lh (.atom s) = 0 := by
  unfold lh; split <;> simp_all

theorem lh_list_mem : ∀ {l : List Term} {e : Term}, e ∈ l → lh e ≤ lh (Term.list l)
  | x :: l, e, h => by
    rw [Term.list, lh]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := lh_list_mem h; omega

/-- Expansion literals of recursive nodes, `{_, closed, [term(), node]}`. -/
def ExpLit (t : Term) : Prop :=
  ∃ (k : Int) (r : List Nat) (a : List (Term × Term)) (b : Term),
    t = .tuple #[.integer k, .atom "closed", Term.list [.atom "term", .tuple #[.reference r, .map a, b]]]

/-- Whether the elements of a tuple literal are those of an expansion literal. -/
def ExpEls (tag : String) (l : List Term) : Prop :=
  tag = "closed" ∧ ∃ (r : List Nat) (a : List (Term × Term)) (b : Term), l = [.atom "term", .tuple #[.reference r, .map a, b]]

theorem lh_lit {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (top : ¬(tag = "open" ∧ l = [])) (ne : ¬ExpEls tag l) :
    lh (.tuple #[.integer k, .atom tag, Term.list l]) = lh (Term.list l) + 1 := by
  rw [show (#[.integer k, .atom tag, Term.list l] : Array Term) = ⟨[.integer k, .atom tag, Term.list l]⟩ from rfl,
    lh_leaf _ _ _ (fun ⟨h₁, h₂⟩ => top ⟨by simpa using h₁, list_eq_nil.mp h₂⟩)
      (fun ⟨_, _, h⟩ => by cases l <;> simp [Term.list] at h) ?_ (by simp),
    lh_atom (by rintro rfl; simp at g) (by rintro rfl; simp at g)]
  · omega
  · rintro ⟨h, r, a, b, e⟩
    simp only [Term.atom.injEq] at h
    match l, e with
    | [x, y], e =>
      simp only [Term.list, Term.cons.injEq] at e
      obtain ⟨rfl, rfl, -⟩ := e
      exact ne ⟨h, r, a, b, rfl⟩

theorem lh_lit_exp {k : Int} {tag : String} {l : List Term} (ex : ExpEls tag l) :
    1 ≤ lh (.tuple #[.integer k, .atom tag, Term.list l]) ∧ ∀ e ∈ l, lh e ≤ lh (.tuple #[.integer k, .atom tag, Term.list l]) := by
  obtain ⟨rfl, r, a, b, rfl⟩ := ex
  have e : lh (.tuple #[.integer k, .atom "closed", Term.list [.atom "term", .tuple #[.reference r, .map a, b]]]) =
      lh (.tuple ⟨[.reference r, .map a, b]⟩) := lh_nodeLit
  rw [e, lh_node_term]
  refine ⟨by omega, fun x mx => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at mx
  rcases mx with rfl | rfl
  · simp [lh]
  · rw [show (#[.reference r, .map a, b] : Array Term) = ⟨[.reference r, .map a, b]⟩ from rfl, lh_node_term]
    exact Nat.le_refl _

theorem tlit_lh {t : Term} (h : TLit E t) : 1 ≤ lh t ∧ ∀ (k : Int) (tag : String) (l : List Term),
    t = .tuple #[.integer k, .atom tag, Term.list l] → ∀ e ∈ l, lh e ≤ lh t ∧ (lh e < lh t ∨ ExpLit t) := by
  obtain ⟨⟨⟨k, tag, l, rfl, g, -⟩, nt⟩, -⟩ := h
  have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [h₁, h₂]⟩
  by_cases ex : ExpEls tag l
  · obtain ⟨one, els⟩ := lh_lit_exp (k := k) ex
    refine ⟨one, fun k' tag' l' e x mx => ?_⟩
    obtain ⟨-, -, e₃⟩ := tuple3_inj e
    have := list_inj e₃
    subst this
    refine ⟨els x mx, Or.inr ?_⟩
    obtain ⟨rfl, r, a, b, rfl⟩ := ex
    exact ⟨k, r, a, b, rfl⟩
  refine ⟨by rw [lh_lit g top ex]; omega, fun k' tag' l' e => ?_⟩
  obtain ⟨-, -, e₃⟩ := tuple3_inj e
  have := list_inj e₃
  subst this
  intro x mx
  have := lh_list_mem mx
  rw [lh_lit g top ex]; omega

theorem tlit_node_lh {h k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (top : ¬(tag = "open" ∧ l = [])) (c u d : Term) :
    lh (.tuple #[.integer h, .tuple #[.integer k, .atom tag, Term.list l], c, u, d]) =
      max (lh (.tuple #[.integer k, .atom tag, Term.list l])) (max (lh c) (max (lh u) (lh d))) :=
  lh_node_lit (.integer h) (.integer k) (.atom tag) (Term.list l) c u d
    (fun ⟨h₁, h₂⟩ => top ⟨by simpa using h₁, list_eq_nil.mp h₂⟩)
    (fun ⟨_, e, _⟩ => by rcases g with rfl | rfl <;> simp at e) (by simp)

/-- Literals of tuple BDDs are no higher than the BDD. -/
theorem bdd_lh_le {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (lits : ∀ t, ok t → TLit E t) :
    ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x := by
  revert lits
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → TLit E t) → ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _ _ _; exact Bdd.top
  · intro _ _ _ _; exact Bdd.bot
  · intro ok k x y okl _ M le
    exact Bdd.leaf_iff.mpr ⟨okl, le⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd lits M le
    obtain ⟨k, a, b, rfl⟩ := leaf
    have tl := lits _ okl
    obtain ⟨⟨⟨k', tag, l, e, g, -⟩, nt⟩, -⟩ := tl
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [h₁, h₂]⟩
    rw [tlit_node_lh (h := h) g top c u d] at le
    have hlit : lh (.tuple #[.integer k, .atom tag, Term.list l]) ≤ M := by omega
    have hc' : lh c ≤ M ∧ lh u ≤ M ∧ lh d ≤ M := by omega
    have lits' : ∀ t, Above ok (.tuple #[.integer k, .atom tag, Term.list l]) t → TLit E t := fun t ht => lits t ht.1
    refine Bdd.node_iff.mpr ⟨⟨k, _, _, rfl⟩, ⟨okl, hlit⟩, ?_, ?_, ?_⟩
    · exact (ic lits' M hc'.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (iu lits' M hc'.2.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (idd lits' M hc'.2.2).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩

theorem EF.opsU (ef : EF nd E V den tl K) : ElemOk E K :=
  ⟨ef.term, fun ha hb => let ⟨c, hc, run, _⟩ := ef.inter ha hb; ⟨c, hc, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha; ⟨b, run⟩, ef.none, ef.pos⟩

theorem EF.dopsU (ef : EF nd E V den tl K) : ElemDiff E K :=
  ⟨fun ha hb => let ⟨c, hc, run, _⟩ := ef.diff ha hb; ⟨c, hc, run⟩⟩

/-- Types below the seen BDDs are not seen. -/
theorem not_seen {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {x : Term} (hx : lh x < N) (kind : String) :
    S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom kind) x) e.1) (.cons (.atom kind) x) e.1 == .eq) = Bool.false := by
  simp only [List.any_eq_false, beq_iff_eq]
  intro e me hit
  obtain ⟨kind', b, e₁, one, hb⟩ := hS e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
  omega

/-- Seeing a BDD with literals keeps the seen set safe below it. -/
theorem safe_put {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {x : Term} (hx : lh x < N) (one : 1 ≤ lh x)
    (kind : String) : SafeN (lh x) ((.cons (.atom kind) x, .atom "true") :: S) := by
  intro e me
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨.atom kind, x, rfl, one, Nat.le_refl _⟩
  · obtain ⟨kind', b, e₁, one', hb⟩ := hS e me
    exact ⟨kind', b, e₁, one', by omega⟩

theorem not_seenT {N : Nat} {S : List (Term × Term)} (hS : SafeT N S) {x : Term} (hx : lh x < N) (kind : String) :
    S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom kind) x) e.1) (.cons (.atom kind) x) e.1 == .eq) = Bool.false := by
  simp only [List.any_eq_false, beq_iff_eq]
  intro e me hit
  obtain ⟨h, b, e₁, one, hb⟩ := hS e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  rcases hb with hb | ⟨⟨i, rfl⟩, -⟩
  · have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
    omega
  · simp at hit

theorem safe_putT {N : Nat} {S : List (Term × Term)} (hS : SafeT N S) {x : Term} (hx : lh x < N) (one : 1 ≤ lh x)
    (kind : String) : SafeN (lh x) ((.cons (.atom kind) x, .atom "true") :: S) := by
  intro e me
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨.atom kind, x, rfl, one, Nat.le_refl _⟩
  · obtain ⟨h, b, e₁, one', hb⟩ := hS e me
    exact ⟨h, b, e₁, one', by omega⟩

theorem tuple_empty_step {d : Dispatcher} {x : Term} {S : List (Term × Term)}
    (fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 == .eq) = Bool.false) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» d x (.map S) =
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil x
        (.map ((.cons (.atom "tuple") x, .atom "true") :: S)) := by
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]

theorem tlit_bdd_lh {x : Term} (wx : Bdd (TLit E) x) (nt : x ≠ .atom "bdd_top") (nb : x ≠ .atom "bdd_bot") :
    1 ≤ lh x := by
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact absurd rfl nt
  · exact absurd rfl nb
  · exact (tlit_lh (Bdd.leaf_iff.mp wx)).1
  · obtain ⟨⟨k, a, b, rfl⟩, okl, -⟩ := Bdd.node_iff.mp wx
    have := (tlit_lh okl).1
    obtain ⟨⟨⟨k', tag, l, e, g, -⟩, nt'⟩, -⟩ := okl
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.integer.injEq] at e₁
    subst e₁ e₂ e₃
    have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt' ⟨_, by rw [h₁, h₂]⟩
    rw [tlit_node_lh (h := h) g top c u d]
    omega

/-- Element types that combine the node with types of height zero. -/
abbrev EC (nd : Term) (E : Term → Prop) (a : Term) : Prop := E a ∧ Combo nd a

theorem combo_term (nd : Term) : Combo nd (.atom "term") := Or.inl rfl

theorem combo_none (nd : Term) : Combo nd (.map []) :=
  Or.inr (Or.inr ⟨[], rfl, fun w h => by simp [mapLookup] at h, fun _ w _ h => by simp [mapLookup] at h⟩)

theorem EF.ops1 (ef : EF nd E V den tl K) : ElemOk (EC nd E) K := by
  refine ⟨⟨ef.term, combo_term nd⟩, fun ha hb => ?_, fun ha S => ?_, ⟨ef.none, combo_none nd⟩, ef.pos⟩
  · obtain ⟨c, hc, run, -, -⟩ := ef.inter ha.1 hb.1
    exact ⟨c, ⟨hc, ef.cinter ha.1 hb.1 ha.2 hb.2 (Nat.le_refl _) (run K (Nat.le_refl _))⟩, run⟩
  · obtain ⟨b, run, -⟩ := ef.empty S ha.1
    exact ⟨b, run⟩

theorem EF.dops1 (ef : EF nd E V den tl K) : ElemDiff (EC nd E) K := by
  refine ⟨fun ha hb => ?_⟩
  obtain ⟨c, hc, run, -, -⟩ := ef.diff ha.1 hb.1
  exact ⟨c, ⟨hc, ef.cdiff ha.1 hb.1 ha.2 hb.2 (Nat.le_refl _) (run K (Nat.le_refl _))⟩, run⟩

theorem EF.sem1 (ef : EF nd E V den tl K) : ElemSem (EC nd E) K V den (Safe1 nd) where
  term := ef.den_term
  inter := fun ha hb hm run v => ef.semR.inter ha.1 hb.1 hm run v
  diff := fun ha hb hm run v => ef.semR.diff ha.1 hb.1 hm run v
  empty := fun ha hS hm run => ef.cempty ha.1 ha.2 hS hm run
  inhabited := ef.inhabited
  resp := fun he he' h d => ef.resp he.1 he'.1 h d

/-- The node holds values: its expansion holds nil. -/
theorem EF.node_inh (ef : EF nd E V den tl K) {e : Term} (he : E e) (ht : IsT nd e) : ∃ w, den e w := by
  obtain ⟨b, run, ex⟩ := ef.empty [] he
  obtain ⟨m, hm⟩ : ∃ m, K = m + 1 := ⟨K - 1, by have := ef.pos; omega⟩
  have r := run (m + 1) (by omega)
  rw [empty_node ht.node m] at r
  have : b = Bool.false := by cases b <;> simp_all [boolAtom]
  subst this
  have h := ex (lh e + 1) (Nat.lt_succ_self _) (safeN_nil _)
  exact Classical.byContradiction fun hn => absurd (h.mpr fun w hw => hn ⟨w, hw⟩) (by decide)

theorem litN_el {e : Term} {k : Int} (ht : TLit E (litN e k)) : E e := by
  obtain ⟨⟨⟨k', tag, l, eq, -, el⟩, -⟩, -⟩ := ht
  obtain ⟨-, -, e₃⟩ := tuple3_inj eq
  have := list_inj e₃
  exact el e (by rw [← this]; simp)

/-- Values of the expansion literal of the node, and values outside it. -/
theorem EF.litN_vals (ef : EF nd E V den tl K) {e : Term} (he : E e) (ht : IsT nd e) (k : Int) :
    (∃ v, valT E den v (litN e k) = Bool.true) ∧ ∃ v, valT E den v (litN e k) = Bool.false := by
  have hl : ∀ x ∈ [Term.atom "term", e], E x := by
    intro x mx; simp at mx; rcases mx with rfl | rfl; exact ef.term; exact he
  obtain ⟨w₁, hw₁⟩ := ef.node_inh he ht
  obtain ⟨w₀⟩ := ef.inhabited
  refine ⟨⟨[w₀, w₁], (vT_lit ef (Or.inr rfl) hl).mpr ?_⟩, ⟨[], ?_⟩⟩
  · simp [InT, ef.den_term, hw₁]
  · cases h : valT E den [] (litN e k)
    · rfl
    · have := (vT_lit ef (Or.inr rfl) hl).mp h
      simp [InT] at this

/-- A walk over a tuple BDD with literals over element types `C` decides the emptiness of the BDD. -/
theorem walk_exact {C : Term → Prop} {Safe : List (Term × Term) → Prop} (ef : EF nd E V den tl K)
    (ops : ElemOk C K) (dops : ElemDiff C K) (sem : ElemSem C K V den Safe) {x : Term} (wx : Bdd (TLit E) x)
    {M : Nat} (le : lh x ≤ M) (okLit : ∀ t, (TLit E t ∧ lh t ≤ M) → TupleOk C t) {S' : List (Term × Term)}
    (hS' : Safe S') {b : Bool}
    (run : Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (K + 1)) (.tuple #[.atom "open", .nil]) .nil x
      (.map S') = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v, denTF E den x v = Bool.false := by
  have wx' := bdd_lh_le wx (fun _ h => h) M le
  have agree : ∀ v, eval (valT C den v) x = eval (valT E den v) x := fun v =>
    eval_ext wx' fun t ht => by
      have h₁ := valT_iff sem (okLit t ht).1 (v := v)
      have h₂ := valT_iff ef.semR ht.1.1.1 (v := v)
      cases e₁ : valT C den v t <;> cases e₂ : valT E den v t <;> simp_all
  have pos : TuplePos C (.tuple #[.atom "open", .nil]) := ⟨"open", [], rfl, Or.inl rfl, by simp⟩
  constructor
  · intro hbt v
    subst hbt
    cases e : denTF E den x v
    · rfl
    · exfalso
      have f := tuple_bdd_false ops dops sem (Nat.le_refl _) _ hS' wx' okLit _ [] pos (by simp) v
        ⟨"open", [], rfl, InT.open_nil v⟩ (by simp) (by rw [agree, ← denTF_bdd wx]; exact e)
      simp only [Term.list] at f
      rw [f] at run
      simp [boolAtom] at run
  · intro unsat
    have t := tuple_bdd_val ops dops sem (Nat.le_refl _) _ hS' wx' okLit _ [] pos (by simp)
      fun v _ _ => by rw [agree, ← denTF_bdd wx]; exact unsat v
    simp only [Term.list] at t
    rw [t] at run
    cases b <;> simp_all [boolAtom]

theorem lh_explit {t : Term} (ex : ExpLit t) : lh t = 1 := by
  obtain ⟨k, r, a, b, rfl⟩ := ex
  simp only [Term.list]
  rw [show (#[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple #[.reference r, .map a, b]) .nil)] :
      Array Term) = ⟨[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩
      from rfl, lh_nodeLit]
  exact lh_node_term

/-- Tuple literals of element types: their elements are below them, or are the node and `term()`. -/
theorem tlit_els (ef : EF nd E V den tl K) {t : Term} (ht : TLit E t) {k : Int} {tag : String} {l : List Term}
    (e : t = .tuple #[.integer k, .atom tag, Term.list l]) {x : Term} (mx : x ∈ l) :
    E x ∧ (lh x < lh t ∨ (lh t = 1 ∧ (x = .atom "term" ∨ IsT nd x))) := by
  have hx : E x := by
    obtain ⟨⟨⟨k', tag', l', e', -, el⟩, -⟩, -⟩ := ht
    rw [e'] at e
    obtain ⟨-, -, e₃⟩ := tuple3_inj e
    exact el x (list_inj e₃ ▸ mx)
  refine ⟨hx, ?_⟩
  rcases ((tlit_lh ht).2 k tag l e x mx).2 with lt | ex
  · exact Or.inl lt
  · refine Or.inr ⟨lh_explit ex, ?_⟩
    obtain ⟨k', r, a, b, rfl⟩ := ex
    obtain ⟨-, -, e₃⟩ := tuple3_inj e
    have := list_inj e₃
    subst this
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at mx
    rcases mx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (ef.node hx ⟨r, a, b, rfl⟩)

/-- Literals of element types exactly equal to an expansion literal of `nd` are expansion literals of `nd`. -/
theorem lit_of_exact (ef : EF nd E V den tl K) {l l' : Term} (hl : PureLit nd l) (hl' : TLit E l')
    (ex : compareExact (fuel l l') l l' = .eq) : PureLit nd l' := by
  obtain ⟨e₀, h₀, rfl⟩ := hl
  obtain ⟨⟨⟨k, tag, l, rfl, -, el⟩, -⟩, -⟩ := hl'
  obtain ⟨S, he₀, -⟩ := h₀.node
  simp only [litN, Term.list, compareExact_tuple, List.size_toArray, List.length_cons, List.length_nil,
    Std.ReflCmp.compare_self, Ordering.then_eq_eq, true_and, List.compareLex_cons_cons, List.compareLex_nil_nil,
    and_true] at ex
  obtain ⟨ek, et, el'⟩ := ex
  have hk := (int_exact ek).mp rfl
  have ht := (atom_exact et).mp rfl
  simp only [Term.integer.injEq, Term.atom.injEq] at hk ht
  subst hk ht
  obtain ⟨y₁, r₁, e₁, ey₁, er₁⟩ := cons_exact el'
  obtain ⟨y₂, r₂, e₂, ey₂, er₂⟩ := cons_exact er₁
  have := (nil_exact er₂).mp rfl
  subst this
  have := (atom_exact ey₁).mp rfl
  subst this
  have ll : l = [.atom "term", y₂] := list_inj (by rw [e₁, e₂])
  subst ll
  subst he₀
  obtain ⟨ys, rfl, ex⟩ := tuple_exact ey₂
  obtain ⟨ys⟩ := ys
  match ys, ex with
  | [r', m', g'], ex =>
    have rr := (reference_compareExact_eq _ _).mp ex.1
    obtain ⟨S', rfl⟩ := map_exact ex.2.1
    subst rr
    exact ⟨_, ef.node (el _ (by simp)) ⟨_, _, _, rfl⟩, rfl⟩

/-- Pure tuple fields are exactly equal only to pure tuple fields, among tuple fields of element types. -/
theorem pure_of_exact (ef : EF nd E V den tl K) {p x : Term} (fp : OField (PureLit nd) p) (wx : Bdd (TLit E) x)
    (e : compareExact (fuel p x) p x = .eq) : Bdd (PureLit nd) x := by
  rcases pure_cases fp with ⟨k, rfl⟩ | rfl | rfl | ⟨e₀, h₀, rfl⟩ | ⟨j, e₀, c, u, d, h₀, rfl⟩
  · obtain ⟨a', b', c', rfl, ea, eb, ec⟩ := exact_tuple3 (Lynx.Term.compareExact_eq_symm e)
    have := (atom_exact eb).mpr rfl
    have := (nil_exact ec).mpr rfl
    have := (int_exact ea).mpr rfl
    subst_vars
    exact absurd ⟨_, rfl⟩ (Bdd.leaf_iff.mp wx).1.2
  · have := (atom_exact (Lynx.Term.compareExact_eq_symm e)).mpr rfl
    subst this; exact Bdd.top
  · have := (atom_exact (Lynx.Term.compareExact_eq_symm e)).mpr rfl
    subst this; exact Bdd.bot
  · rcases wx.shape with rfl | rfl | ⟨k', a', b', rfl⟩ | ⟨hh, lit, c', u', d', rfl⟩
    · simp [litN] at e
    · simp [litN] at e
    rotate_left
    · simp [litN, Term.list, compareExact_tuple] at e
    exact Bdd.leaf_iff.mpr (lit_of_exact ef ⟨e₀, h₀, rfl⟩ (Bdd.leaf_iff.mp wx) e)
  · rcases wx.shape with rfl | rfl | ⟨k', a', b', rfl⟩ | ⟨hh, lit, c', u', d', rfl⟩
    · simp at e
    · simp at e
    · simp [compareExact_tuple] at e
    obtain ⟨isLeaf, okl, -, -, -⟩ := Bdd.node_iff.mp wx
    simp only [compareExact_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
      Ordering.then_eq_eq, true_and, List.compareLex_cons_cons, List.compareLex_nil_nil,
      and_true] at e
    obtain ⟨-, el, ec, eu, ed⟩ := e
    have btE : ∀ (b : Bool) {y : Term}, compareExact (fuel (bt b) y) (bt b) y = .eq → y = bt b := by
      intro b y h; cases b <;> exact (atom_exact h).mp rfl
    rw [btE c ec, btE u eu, btE d ed]
    have btB : ∀ (ok : Term → Prop) (b : Bool), Bdd ok (bt b) := by
      intro ok b; cases b
      · exact Bdd.bot
      · exact Bdd.top
    exact Bdd.node_iff.mpr ⟨isLeaf, lit_of_exact ef ⟨e₀, h₀, rfl⟩ okl el, btB _ _, btB _ _, btB _ _⟩

/-- Tuple types decide their emptiness exactly, when the seen BDDs are higher than them, or, keyed by an arity,
as high. -/
theorem tuple_empty_exact (ef : EF nd E V den tl K) {x : Term} (fx : TField E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeT N S → (b = Bool.true ↔ ∀ v, denTF E den x v = Bool.false) := by
  have field : TupleField E x := fx.imp id fun w => w.mono fun _ h => h.1
  obtain ⟨b, hb⟩ := tuple_total ef.opsU ef.dopsU S field
  refine ⟨b, hb, fun N hx hS => ?_⟩
  have step := tuple_empty_step (d := D (K + 1)) (not_seenT hS hx "tuple")
  have run := hb (K + 1) (Nat.le_refl _)
  dsimp only at run
  rw [step] at run
  rcases fx with ⟨k, rfl⟩ | wx
  · rw [tuple_walk_top_leaf] at run
    have : b = Bool.false := by
      cases b
      · rfl
      · simp [boolAtom] at run
    subst this
    exact ⟨fun h => absurd h (by decide), fun h => absurd (h []) (by rw [denTF_top]; simp)⟩
  by_cases top : x = .atom "bdd_top"
  · subst top
    rw [tuple_walk_top] at run
    have : b = Bool.false := by
      cases b
      · rfl
      · simp [boolAtom] at run
    subst this
    exact ⟨fun h => absurd h (by decide), fun h => absurd (h []) (by rw [denTF_bdd wx]; simp)⟩
  by_cases bot : x = .atom "bdd_bot"
  · subst bot
    rw [tuple_walk_bot] at run
    have : b = Bool.true := by
      cases b
      · simp [boolAtom] at run
      · rfl
    subst this
    exact ⟨fun _ v => by rw [denTF_bdd wx]; rfl, fun _ => rfl⟩
  have one := tlit_bdd_lh wx top bot
  by_cases pure : Bdd (PureLit nd) x
  · have noid := safeN_noid (safe_putT hS hx one "tuple") (refOf nd)
    obtain ⟨m', hm'⟩ : ∃ m', K + 1 = m' + 2 := ⟨K - 1, by have := ef.pos; omega⟩
    rw [hm'] at run
    rcases pure_shape pure with rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
    · exact absurd rfl top
    · exact absurd rfl bot
    · rw [walk_leaf_node he.node _ m', noid] at run
      have : b = Bool.false := by
        simp only [boolAtom] at run
        cases b <;> simp at run ⊢
      subst this
      obtain ⟨⟨v, hv⟩, -⟩ := ef.litN_vals (litN_el (Bdd.leaf_iff.mp wx)) he (keyOf nd)
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      have := h v
      rw [denTF_bdd wx, show eval (valT E den v) (litN e (keyOf nd)) = valT E den v (litN e (keyOf nd)) by
        simp [litN, Term.list, eval_leaf], hv] at this
      cases this
    · rw [walk_node_node he.node _ _ m', noid] at run
      have hb' : b = (!c && !u && !d) := by
        simp only [boolAtom] at run
        cases b <;> cases c <;> cases u <;> cases d <;> simp at run ⊢
      subst hb'
      obtain ⟨isLeaf, okl, -⟩ := Bdd.node_iff.mp wx
      obtain ⟨⟨v₁, h₁⟩, ⟨v₀, h₀⟩⟩ := ef.litN_vals (litN_el okl) he (keyOf nd)
      have ev : ∀ v, denTF E den (.tuple #[.integer j, litN e (keyOf nd), bt c, bt u, bt d]) v =
          (valT E den v (litN e (keyOf nd)) && c || u || (!valT E den v (litN e (keyOf nd)) && d)) := by
        intro v
        rw [denTF_bdd wx]
        cases c <;> cases u <;> cases d <;> simp [eval, bt]
      constructor
      · intro h v
        rw [ev]
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        obtain ⟨⟨hc, hu⟩, hd⟩ := h
        subst hc hu hd
        simp
      · intro h
        have a₁ := h v₁
        have a₀ := h v₀
        rw [ev, h₁] at a₁
        rw [ev, h₀] at a₀
        cases c <;> cases u <;> cases d <;> simp at a₁ a₀ ⊢
  by_cases two : 2 ≤ lh x
  · refine walk_exact ef (ef.ops (lh x) (by omega)) (ef.dops (lh x)) (ef.sem (lh x)) wx (Nat.le_refl _)
      (fun t ⟨ht, le⟩ => ?_) (safe_putT hS hx one "tuple") run
    obtain ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ := ht
    refine ⟨⟨k, tag, l, rfl, g, fun e me => ?_⟩, nt⟩
    obtain ⟨he, lt | ⟨l1, -⟩⟩ := tlit_els ef ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ rfl me
    · exact ⟨he, by omega⟩
    · have := ((tlit_lh ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩).2 k tag l rfl e me).1
      exact ⟨he, by omega⟩
  · have l1 : lh x = 1 := by omega
    have hS1 : Safe1 nd ((.cons (.atom "tuple") x, .atom "true") :: S) := by
      refine ⟨by have := safe_putT hS hx one "tuple"; rwa [l1] at this, fun e me p fp hit => ?_⟩
      rcases List.mem_cons.mp me with rfl | me
      · rw [compareExact_cons, Ordering.then_eq_eq] at hit
        exact pure (pure_of_exact ef fp wx hit.2)
      · obtain ⟨h', b', e₁, -, hb'⟩ := hS e me
        rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
        rcases hb' with hb' | ⟨⟨i, rfl⟩, -⟩
        · have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
          have := pure_le fp
          omega
        · simp at hit
    refine walk_exact ef ef.ops1 ef.dops1 ef.sem1 wx (Nat.le_of_eq l1) (fun t ⟨ht, le⟩ => ?_) hS1 run
    obtain ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ := ht
    refine ⟨⟨k, tag, l, rfl, g, fun e me => ?_⟩, nt⟩
    obtain ⟨he, lt | ⟨-, c⟩⟩ := tlit_els ef ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ rfl me
    · exact ⟨he, ef.low he (by omega)⟩
    · rcases c with rfl | c
      · exact ⟨he, combo_term nd⟩
      · exact ⟨he, Or.inr (Or.inl c)⟩

end Elixir.STTDescrProofsTest.Nest
