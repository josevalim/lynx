namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! List fields of element types: plain unions, intersections, and differences on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- List fields: ordered BDDs of list literals of element types, top literals included. -/
abbrev LF (E : Term → Prop) (x : Term) : Prop := Bdd (LLit E) x

/-- The lists of values of a list field. -/
noncomputable def dL (E : Term → Prop) (den : Term → V → Prop) (x : Term) (v : LV V) : Bool := eval (valL E den v) x

theorem nl_top_val (ef : EF nd E V den tl K) (k : Int) (v : LV V) :
    valL E den v (.tuple #[.integer k, .atom "term", .atom "term"]) = Bool.true :=
  (valL_iff ef.semR ⟨k, _, _, rfl, ef.term, ef.term⟩).mpr
    (llitSem_iff.mpr ⟨fun x _ => ef.den_term x, ef.den_term _⟩)

theorem nl_denL (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (v : LV V) :
    denL x (valL E den v) = dL E den x v := by
  unfold denL dL
  cases h : isListTop x
  · rfl
  · obtain ⟨k, rfl⟩ := (listTop_iff x).mp h
    obtain ⟨k, rfl⟩ := leaf_int wx
    rw [eval_leaf, nl_top_val ef]; rfl

/-- List fields that compare equal hold the same lists. -/
theorem nl_dL_resp {x x' : Term} (wx : LF E x) (e : Term.compare (Term.fuel x x') x x' = .eq) (v : LV V) :
    dL E den x v = dL E den x' v :=
  eval_congr_cmp wx (valL_resp v) e

theorem nl_listVal_exists (ef : EF nd E V den tl K) : ∃ v : LV V, ListVal tl v := by
  obtain ⟨x₀⟩ := ef.inhabited
  obtain ⟨y₀, hy₀⟩ := ef.tl_witness
  exact ⟨⟨[x₀], y₀⟩, by simp, hy₀⟩

/-- The literal of a list leaf, as a height. -/
def litH : Term → Nat
  | .tuple ⟨[_, a, b]⟩ => max (lh a) (lh b) + 1
  | _ => 0

theorem litH_eq (k a b : Term) : litH (.tuple #[k, a, b]) = max (lh a) (lh b) + 1 := rfl

theorem lh_le_litH (k x y : Term) : lh (.tuple #[k, x, y]) ≤ litH (.tuple #[k, x, y]) := by
  rw [litH_eq]
  by_cases ho : x = .atom "open" ∧ y = .nil
  · obtain ⟨rfl, rfl⟩ := ho
    rw [show lh (.tuple #[k, .atom "open", .nil]) = 0 from lh_leaf_top k]; omega
  by_cases ht : k = .integer 46675407 ∧ x = .atom "term" ∧ y = .atom "term"
  · obtain ⟨rfl, rfl, rfl⟩ := ht
    rw [show lh (.tuple #[.integer 46675407, .atom "term", .atom "term"]) = 0 from lh_leaf_list]; omega
  by_cases hr : ∃ r a, k = .reference r ∧ x = .map a
  · obtain ⟨r, a, rfl, rfl⟩ := hr
    rw [show (#[.reference r, .map a, y] : Array Term) = ⟨[.reference r, .map a, y]⟩ from rfl, lh_node_term]
    omega
  by_cases hn : NodeLit k x y
  · obtain ⟨rfl, r, a, b, rfl⟩ := hn
    rw [show (#[k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)] : Array Term) =
      ⟨[k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩ from rfl, lh_nodeLit]
    simp only [lh]; omega
  · rw [show lh (.tuple #[k, x, y]) = max (lh x) (lh y) + 1 from lh_leaf k x y ho ht hn hr]; exact Nat.le_refl _

/-- BDDs whose literals are below a height are below it, when that height covers the top and empty BDDs. -/
theorem nl_lh_le {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    ∀ M, (r = .atom "bdd_top" ∨ r = .atom "bdd_bot" → 1 ≤ M) → (∀ t, ok t → litH t ≤ M) → lh r ≤ M := by
  refine Bdd.induction (P := fun ok r => ∀ M, (r = .atom "bdd_top" ∨ r = .atom "bdd_bot" → 1 ≤ M) →
    (∀ t, ok t → litH t ≤ M) → lh r ≤ M) ?_ ?_ ?_ ?_ ok r wr
  · intro _ M top _; simp [lh]; exact top (Or.inl rfl)
  · intro _ M top _; simp [lh]; exact top (Or.inr rfl)
  · intro ok k x y okl M _ h
    exact Nat.le_trans (lh_le_litH _ _ _) (h _ okl)
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id M _ hM
    obtain ⟨k, a, b, rfl⟩ := isLeaf
    have hl := hM _ okl
    rw [litH_eq] at hl
    have below : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → litH t ≤ M := fun t ht => hM t ht.1
    have one : ∀ z : Term, z = .atom "bdd_top" ∨ z = .atom "bdd_bot" → 1 ≤ M := fun _ _ => by omega
    have := ic M (one c) below
    have := iu M (one u) below
    have := id M (one d) below
    refine Nat.le_trans nl_lh_node_le ?_
    omega

/-- The literals of a list field are below its height, and the top list leaf is at height one. -/
theorem nl_lit_le (ef : EF nd E V den tl K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → LLit E t) → ∀ M, lh r ≤ M →
      (r = .tuple #[.integer 46675407, .atom "term", .atom "term"] → 1 ≤ M) →
      Bdd (fun t => ok t ∧ litH t ≤ M) r := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → LLit E t) → ∀ M, lh r ≤ M →
      (r = .tuple #[.integer 46675407, .atom "term", .atom "term"] → 1 ≤ M) →
      Bdd (fun t => ok t ∧ litH t ≤ M) r) ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ _ _ _; exact Bdd.top
  · intro _ _ _ _ _; exact Bdd.bot
  · intro ok k x y okl lits M le top
    refine Bdd.leaf_iff.mpr ⟨okl, ?_⟩
    obtain ⟨k', a, b, e, ha, hb⟩ := lits _ okl
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    rw [litH_eq]
    by_cases t : k = 46675407 ∧ x = .atom "term" ∧ y = .atom "term"
    · obtain ⟨rfl, rfl, rfl⟩ := t
      have := top rfl
      simp [lh]; omega
    · rw [nl_lh_leaf (ef.shape hb) t] at le; exact le
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits M le _
    obtain ⟨k, a, b, rfl⟩ := isLeaf
    obtain ⟨k₀, a₀, b₀, e₀, ha₀, -⟩ := lits _ okl
    obtain ⟨-, e₂, -⟩ := tuple3_inj e₀
    subst e₂
    rw [nl_lh_node (ef.shape ha₀)] at le
    have lits' : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → LLit E t := fun t ht => lits t ht.1
    have lift : ∀ x, (fun t => Above ok (.tuple #[.integer k, a, b]) t ∧ litH t ≤ M) x →
        Above (fun t => ok t ∧ litH t ≤ M) (.tuple #[.integer k, a, b]) x :=
      fun x hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
    refine Bdd.node_iff.mpr ⟨⟨k, a, b, rfl⟩, ⟨okl, by rw [litH_eq]; omega⟩,
      (ic lits' M (by omega) fun _ => by omega).mono lift, (iu lits' M (by omega) fun _ => by omega).mono lift,
      (id lits' M (by omega) fun _ => by omega).mono lift⟩

/-! Clauses of the plain list operations. -/

abbrev NoTopL (x : Term) : Prop := ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"]

theorem nl_union_eq {x y : Term} (nx : NoTopL x) (ny : NoTopL y) :
    Elixir.Module.Types.Descr.«list_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_union/2»
  split
  · exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · rfl

theorem nl_inter_eq {x y : Term} (nx : NoTopL x) (ny : NoTopL y) :
    Elixir.Module.Types.Descr.«list_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_intersection/2»
  split
  · exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · rfl

theorem nl_diff_eq {x y : Term} (nx : NoTopL x) :
    Elixir.Module.Types.Descr.«list_difference/2» x y = Elixir.Module.Types.Descr.«bdd_difference/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_difference/2»
  split
  · exact (nx _ rfl).elim
  · exact (nx _ rfl).elim
  · rfl

theorem nl_diff_top_eq {k y : Term} (ny : NoTopL y) :
    Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[k, .atom "term", .atom "term"]) y =
      Elixir.Module.Types.Descr.«bdd_negation/1» y := by
  unfold Elixir.Module.Types.Descr.«list_difference/2»
  split
  · exact (ny _ rfl).elim
  · rfl
  · rename_i h₁ h₂; exact (h₁ _ rfl).elim

theorem nl_top_dL (ef : EF nd E V den tl K) {k : Term} (w : LF E (.tuple #[k, .atom "term", .atom "term"])) (v : LV V) :
    dL E den (.tuple #[k, .atom "term", .atom "term"]) v = Bool.true := by
  obtain ⟨k, rfl⟩ := leaf_int w
  rw [dL, eval_leaf, nl_top_val ef]

/-- Literals of list fields that are not a top leaf are below their height. -/
theorem nl_lits_le (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (nx : NoTopL x) {M : Nat} (le : lh x ≤ M) :
    Bdd (fun t => LLit E t ∧ litH t ≤ M) x :=
  nl_lit_le ef wx (fun _ h => h) M le fun e => absurd e (nx _)

/-- List fields other than top list leaves have a height. -/
theorem nl_lh_pos (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (nx : NoTopL x) : 1 ≤ lh x := by
  refine Classical.byContradiction fun h0' => ?_
  have h0 : lh x = 0 := by omega
  rcases wx.shape with h | h | ⟨k, a, c, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · subst h; simp [lh] at h0
  · subst h; simp [lh] at h0
  · exfalso
    obtain ⟨k', a', c', e, -, hc⟩ := Bdd.leaf_iff.mp wx
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    have nt : ¬(k = 46675407 ∧ a = .atom "term" ∧ c = .atom "term") := fun ⟨_, e₁, e₂⟩ => by
      subst e₁ e₂; exact nx _ rfl
    rw [nl_lh_leaf (ef.shape hc) nt] at h0
    omega
  · exfalso
    obtain ⟨-, okl, -⟩ := Bdd.node_iff.mp wx
    obtain ⟨k', a', c', rfl, ha', -⟩ := okl
    rw [nl_lh_node (ef.shape ha')] at h0
    omega

theorem nl_dL_bot (v : LV V) : dL E den (.atom "bdd_bot") v = Bool.false := by simp [dL]

/-- Plain unions of list fields hold the lists of either. -/
theorem nl_bare_union (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "list") x y = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v || dL E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    refine ⟨_, fun d => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«list_union/2»],
      wx, fun v => by rw [nl_top_dL ef wx]; rfl, Nat.le_max_left _ _⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    have nx : NoTopL x := fun k e => tx ⟨k, e⟩
    refine ⟨_, fun d => ?_, wy, fun v => by rw [nl_top_dL ef wy]; simp, Nat.le_max_right _ _⟩
    simp only [Elixir.Module.Types.Descr.«bare_union/3»]
    unfold Elixir.Module.Types.Descr.«list_union/2»
    split
    · exact (nx _ rfl).elim
    · rename_i heq; obtain ⟨rfl, -, -⟩ := tuple3_inj heq; rfl
    · rename_i h; exact (h _ rfl).elim
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  have ny : NoTopL y := fun k e => ty ⟨k, e⟩
  obtain ⟨r, run, keep, sem⟩ := union_ok wx wy
  refine ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_union/3»]; rw [nl_union_eq nx ny, run],
    keep _ wx wy, fun v => sem _ (valL_resp v), ?_⟩
  have := nl_lh_pos ef wx nx
  exact nl_lh_le (keep _ (nl_lits_le ef wx nx (Nat.le_max_left _ _)) (nl_lits_le ef wy ny (Nat.le_max_right _ _)))
    _ (fun _ => by omega) fun t h => h.2

/-- Plain intersections of list fields hold the lists of both. -/
theorem nl_bare_inter (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "list") x y = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v && dL E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    refine ⟨y, fun d => by
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«list_intersection/2»],
      wy, fun v => by rw [nl_top_dL ef wx]; rfl, Nat.le_max_right _ _⟩
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    refine ⟨x, fun d => ?_, wx, fun v => by rw [nl_top_dL ef wy]; simp, Nat.le_max_left _ _⟩
    simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]
    unfold Elixir.Module.Types.Descr.«list_intersection/2»
    split
    · exact (nx _ rfl).elim
    · rfl
    · rename_i h; exact (h _ rfl).elim
  have ny : NoTopL y := fun k e => ty ⟨k, e⟩
  obtain ⟨r, run, keep, sem⟩ := inter_ok wx wy
  refine ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]; rw [nl_inter_eq nx ny, run],
    keep _ wx wy, fun v => sem _ (valL_resp v), ?_⟩
  have := nl_lh_pos ef wx nx
  exact nl_lh_le (keep _ (nl_lits_le ef wx nx (Nat.le_max_left _ _)) (nl_lits_le ef wy ny (Nat.le_max_right _ _)))
    _ (fun _ => by omega) fun t h => h.2

/-- Plain differences of list fields hold the lists of the first and not the second. Their non-empty results are
below the inputs' height. -/
theorem nl_bare_diff (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "list") x y = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v && !dL E den y v)) ∧
      (r ≠ .atom "bdd_bot" → lh r ≤ max (lh x) (lh y)) := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
    · obtain ⟨k', rfl⟩ := ty
      exact ⟨.atom "bdd_bot", fun d => by
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
        Bdd.bot, fun v => by rw [nl_top_dL ef wx, nl_top_dL ef wy]; rfl, fun nb => absurd rfl nb⟩
    have ny : NoTopL y := fun k e => ty ⟨k, e⟩
    obtain ⟨r, run, keep, sem⟩ := neg_ok wy
    have one := nl_lh_pos ef wy ny
    exact ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_difference/3»]; rw [nl_diff_top_eq ny, run],
      keep _ wy, fun v => by rw [nl_top_dL ef wx, dL, sem _ (valL_resp v)]; rfl,
      fun _ => Nat.le_trans (nl_lh_le (keep _ (nl_lits_le ef wy ny (Nat.le_refl _))) _ (fun _ => one)
        fun t h => h.2) (Nat.le_max_right _ _)⟩
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  obtain ⟨r, run, keep, sem⟩ := diff_ok wx wy
  have one := nl_lh_pos ef wx nx
  exact ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_difference/3»]; rw [nl_diff_eq nx, run],
    keep _ wx wy, fun v => sem _ (valL_resp v), fun _ => nl_lh_le (keep _ (nl_lits_le ef wx nx (Nat.le_max_left (lh x) (lh y)))
      (nl_lit_le ef wy (fun _ h => h) _ (Nat.le_max_right _ _) fun _ => by omega)) _ (fun _ => by omega) fun t h => h.2⟩

end Elixir.STTDescrProofsTest.Nest
