namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! List types of element types: their emptiness is exact on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Lists of values: non-empty, whose tail is not a non-empty list. -/
def ListVal (tl : V → Prop) (v : LV V) : Prop := v.xs ≠ [] ∧ ¬tl v.last

/-- Element types of the whole class, with operations at every call depth from `K`. -/
theorem EF.opsE (ef : EF nd E V den tl K) : ElemOk E K :=
  ⟨ef.term, fun ha hb => let ⟨c, hc, run, _⟩ := ef.inter ha hb; ⟨c, hc, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha; ⟨b, run⟩, ef.none, ef.pos⟩

theorem EF.dopsE (ef : EF nd E V den tl K) : ElemDiff E K :=
  ⟨fun ha hb => let ⟨c, hc, run, _⟩ := ef.diff ha hb; ⟨c, hc, run⟩⟩

theorem EF.tailE (ef : EF nd E V den tl K) : TailOk E := fun _ he =>
  let ⟨e', run, he', _⟩ := ef.tail he
  ⟨e', run, he'⟩

theorem EF.shape (ef : EF nd E V den tl K) {a : Term} (ha : E a) :
    a = .atom "term" ∨ (∃ X, a = .map X) ∨ IsNode a := by
  rcases ef.static ha with rfl | ⟨X, rfl, -⟩ | hn₀
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨X, rfl⟩)
  · exact Or.inr (Or.inr hn₀)

theorem nl_lh_leaf {k : Int} {a b : Term} (hb : b = .atom "term" ∨ (∃ X, b = .map X) ∨ IsNode b)
    (nt : ¬(k = 46675407 ∧ a = .atom "term" ∧ b = .atom "term")) :
    lh (.tuple #[.integer k, a, b]) = max (lh a) (lh b) + 1 :=
  lh_leaf _ _ _ (fun h => by rcases hb with rfl | ⟨X, rfl⟩ | ⟨r, st, g, rfl⟩ <;> simp at h)
    (fun ⟨e, ea, eb⟩ => nt ⟨by simpa using e, ea, eb⟩)
    (by rintro ⟨-, r, x, y, rfl⟩; rcases hb with h | ⟨X, h⟩ | ⟨r', st, g, h⟩ <;> simp at h) (by simp)

theorem nl_lh_node {h k : Int} {a b c u d : Term} (ha : a = .atom "term" ∨ (∃ X, a = .map X) ∨ IsNode a) :
    lh (.tuple #[.integer h, .tuple #[.integer k, a, b], c, u, d]) =
      max (max (lh a) (lh b) + 1) (max (lh c) (max (lh u) (lh d))) :=
  lh_node _ _ _ _ _ _ _ (by rcases ha with rfl | ⟨X, rfl⟩ | ⟨r, st, g, rfl⟩ <;> simp [litZ])

theorem nl_lh_node_le {h k : Int} {a b c u d : Term} :
    lh (.tuple #[.integer h, .tuple #[.integer k, a, b], c, u, d]) ≤
      max (max (lh a) (lh b) + 1) (max (lh c) (max (lh u) (lh d))) := by
  cases hz : litZ a b
  · exact Nat.le_of_eq (lh_node _ _ _ _ _ _ _ hz)
  · rw [show (#[.integer h, .tuple #[.integer k, a, b], c, u, d] : Array Term) =
      ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩ from rfl, lh_node_z _ _ _ _ _ _ _ hz]
    unfold litZ at hz
    split at hz
    · rw [lh_nodeLit]; simp only [lh]; omega
    · cases hz

/-- The literals of a list BDD below some height have elements below that height. -/
theorem nl_lits_bound (ef : EF nd E V den tl K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → LLit E t) → ∀ N, 1 ≤ N → lh r ≤ N → Bdd (fun t => ok t ∧ LLit (EB E N) t) r := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → LLit E t) → ∀ N, 1 ≤ N → lh r ≤ N →
    Bdd (fun t => ok t ∧ LLit (EB E N) t) r) ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ _ _ _; exact Bdd.top
  · intro _ _ _ _ _; exact Bdd.bot
  · intro ok k x y okl lits N one le
    obtain ⟨k', a, b, e, ha, hb⟩ := lits _ okl
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    refine Bdd.leaf_iff.mpr ⟨okl, k, x, y, rfl, ⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
    all_goals
      by_cases top : k = 46675407 ∧ x = .atom "term" ∧ y = .atom "term"
      · obtain ⟨-, e₁, e₂⟩ := top; subst e₁ e₂; simp [lh]; omega
      · rw [nl_lh_leaf (ef.shape hb) top] at le; omega
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits N one le
    obtain ⟨k', a, b, rfl, ha, hb⟩ := lits _ okl
    rw [nl_lh_node (ef.shape ha)] at le
    have lift : ∀ x, (fun t => Above ok (.tuple #[.integer k', a, b]) t ∧ LLit (EB E N) t) x →
        Above (fun t => ok t ∧ LLit (EB E N) t) (.tuple #[.integer k', a, b]) x :=
      fun x hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
    have lits' : ∀ t, Above ok (.tuple #[.integer k', a, b]) t → LLit E t := fun t ht => lits t ht.1
    refine Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, k', a, b, rfl, ⟨ha, by omega⟩, ⟨hb, by omega⟩⟩,
      (ic lits' N one (by omega)).mono lift, (iu lits' N one (by omega)).mono lift,
      (id lits' N one (by omega)).mono lift⟩

/-- Seen sets of higher BDDs never hold a BDD. -/
theorem nl_fresh {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {r : Term} (hr : lh r < N) (kind : String) :
    S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom kind) r) e.1) (.cons (.atom kind) r) e.1 == .eq) = Bool.false := by
  cases h : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom kind) r) e.1) (.cons (.atom kind) r) e.1 == .eq)
  · rfl
  · exfalso
    obtain ⟨e, me, hit⟩ := List.any_eq_true.mp h
    obtain ⟨k, b, e₁, -, hb⟩ := hS e me
    rw [e₁] at hit
    simp only [beq_iff_eq, compareExact_cons, Ordering.then_eq_eq] at hit
    have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
    omega

theorem nl_safe_put {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {r : Term} (hr : lh r < N) (one : 1 ≤ lh r)
    (kind : String) : SafeN (lh r) ((.cons (.atom kind) r, .atom "true") :: S) := by
  intro e me
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨.atom kind, r, rfl, one, Nat.le_refl _⟩
  · obtain ⟨k, b, e₁, one', hb⟩ := hS e me
    exact ⟨k, b, e₁, one', by omega⟩

/-- Valuations of list literals do not depend on how far below the element types are. -/
theorem nl_valL_eq (ef : EF nd E V den tl K) {N : Nat} (v : LV V) {t : Term} (ht : LLit (EB E N) t) :
    valL (EB E N) den v t = valL E den v t := by
  obtain ⟨k, a, b, rfl, ha, hb⟩ := ht
  apply Bool.eq_iff_iff.mpr
  rw [valL_iff (ef.sem N) ⟨k, a, b, rfl, ha, hb⟩, valL_iff ef.semR ⟨k, a, b, rfl, ha.1, hb.1⟩]

theorem nl_safeF_put {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) (r : Term)
    (nt : compareExact (fuel (.tuple #[.integer 61102469, .atom "open", .nil]) r) (.tuple #[.integer 61102469, .atom "open", .nil]) r ≠ .eq) (kind : String) :
    SafeF ((.cons (.atom kind) r, .atom "true") :: S) := by
  obtain ⟨L, e, all⟩ := safeF_of hS
  simp only [Term.map.injEq] at e
  subst e
  refine ⟨_, rfl, fun e me k hit => ?_⟩
  rcases List.mem_cons.mp me with rfl | me
  · rw [compareExact_cons, Ordering.then_eq_eq] at hit
    exact nt hit.2
  · exact all e me k hit

/-- `list_empty?/2` decides exactly whether list types of element types hold lists of values. -/
theorem nl_list_empty (ef : EF nd E V den tl K) {x : Term} (wx : Bdd (LLit E) x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m → Elixir.Module.Types.Descr.«list_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ v, ListVal tl v → eval (valL E den v) x = Bool.false) := by
  obtain ⟨b, hb⟩ := list_total ef.opsE ef.dopsE ef.tailE S wx
  refine ⟨b, hb, fun N hN hS => ?_⟩
  obtain ⟨x₀⟩ := ef.inhabited
  obtain ⟨y₀, hy₀⟩ := ef.tl_witness
  have v₀ : ListVal tl ⟨[x₀], y₀⟩ := ⟨by simp, hy₀⟩
  have fresh := nl_fresh hS hN "list"
  have run := hb (K + 2) (Nat.le_refl _)
  dsimp only at run
  by_cases top : x = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  · subst top
    have : b = Bool.false := by
      unfold Elixir.Module.Types.Descr.«list_empty?/2» at run
      cases b <;> simp_all [boolAtom]
    subst this
    simp only [Bool.false_eq_true, false_iff]
    intro all
    have := all _ v₀
    rw [eval_leaf, (valL_iff ef.semR ⟨_, _, _, rfl, ef.term, ef.term⟩).mpr
      (llitSem_iff.mpr ⟨fun x _ => ef.den_term x, ef.den_term _⟩)] at this
    cases this
  by_cases one : 1 ≤ lh x
  · have wb := (nl_lits_bound ef wx (fun _ h => h) (lh x) one (Nat.le_refl _)).mono fun _ h => h.2
    have safe := nl_safe_put hS hN one "list"
    have agree : ∀ v, eval (valL (EB E (lh x)) den v) x = eval (valL E den v) x := fun v =>
      eval_ext wb fun t ht => nl_valL_eq ef v ht
    constructor
    · intro e v lv
      subst e
      rw [← agree v]
      exact nl_list_sound (ef.ops _ one) (ef.dops _) (ef.sem _) (ef.tsem _) (Nat.le_refl _) wb S fresh safe
        (by simpa [boolAtom] using run) v lv.1 lv.2
    · intro unsat
      have := list_empty_val (ef.ops _ one) (ef.dops _) (ef.sem _) (ef.tsem _) (Nat.le_refl _) wb S
        (fun S' put => by
          simp only [Erlang.maps.«put/3», Except.ok.injEq, Term.map.injEq] at put
          subst put; exact safe)
        fun v ne nl => by rw [agree v]; exact unsat v ⟨ne, nl⟩
      rw [run] at this
      cases b <;> simp_all [boolAtom]
  · have shape : x = .atom "bdd_top" ∨ x = .atom "bdd_bot" := by
      rcases wx.shape with h | h | ⟨k, a, c, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        obtain ⟨k', a', c', e, -, hc⟩ := Bdd.leaf_iff.mp wx
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
        subst e₂ e₃
        have nt : ¬(k = 46675407 ∧ a = .atom "term" ∧ c = .atom "term") := fun ⟨e, e₁, e₂⟩ => by
          subst e e₁ e₂; exact top rfl
        rw [nl_lh_leaf (ef.shape hc) nt] at one
        omega
      · exfalso
        obtain ⟨-, okl, -⟩ := Bdd.node_iff.mp wx
        obtain ⟨k', a', c', rfl, ha', -⟩ := okl
        rw [nl_lh_node (ef.shape ha')] at one
        omega
    rcases shape with rfl | rfl
    · have : b = Bool.false := by
        cases b
        · rfl
        · exfalso
          have fl := nl_list_sound lelemOk lelemDiff flatSem tailF (m := K + 4) (by omega) (Bdd.top (ok := LLit LElem))
            S fresh (nl_safeF_put hS _ (by simp) "list") (by simpa [boolAtom] using hb (K + 4) (by omega))
            ⟨[.bit 0], .bit 0⟩ (by simp) (by simp [tlF])
          simp at fl
      subst this
      simp only [Bool.false_eq_true, false_iff]
      intro all
      have := all _ v₀
      simp at this
    · have := list_empty_unsat (D (K + 2)) (Bdd.bot (ok := LLit E)) (fun _ _ => by simp) S
      rw [run] at this
      have : b = Bool.true := by cases b <;> simp_all [boolAtom]
      subst this
      simp

end Elixir.STTDescrProofsTest.Nest
