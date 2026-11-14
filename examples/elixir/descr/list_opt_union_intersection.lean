namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized unions and intersections of list fields on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `empty?/1` decides the emptiness of element types. -/
theorem nl_empty1 (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t : Term} (ht : E t) :
    ∃ b, Elixir.Module.Types.Descr.«empty?/1» (D m) t = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ v, ¬den t v) := by
  obtain ⟨b, run, exact⟩ := ef.empty [] ht
  have iff := exact (lh t + 1) (Nat.lt_succ_self _) (safeN_nil _)
  refine ⟨b, ?_, iff⟩
  rcases ef.static ht with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩
  · have : b = Bool.false := by
      cases b
      · rfl
      · exact absurd (ef.den_term (Classical.choice ef.inhabited)) (iff.mp rfl _)
    subst this
    rfl
  · simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm
  · simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm

theorem nl_leaf_new (ef : EF nd E V den tl K) {a b : Term} (ha : E a) (hb : E b) :
    ∃ k : Int, Elixir.Module.Types.Descr.«bdd_leaf_new/2» a b = .ok (.tuple #[.integer k, a, b]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons a b)
  rcases ef.static ha with rfl | ⟨A, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩ <;>
    rcases ef.static hb with rfl | ⟨B, rfl, -⟩ | ⟨r₁, st₁, g₁, rfl⟩
  all_goals
    exact ⟨hash, by
      simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», Elixir.Module.Types.Descr.«bdd_leaf_key/2», hrun,
        Erlang.erlang.«is_list/1»]⟩

theorem nl_llit_val (ef : EF nd E V den tl K) {k : Int} {a b : Term} (ha : E a) (hb : E b) (v : LV V) :
    valL E den v (.tuple #[.integer k, a, b]) = Bool.true ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last :=
  (valL_iff ef.semR ⟨k, a, b, rfl, ha, hb⟩).trans llitSem_iff

/-- Optimized intersections of list literals hold the lists of both. -/
theorem nl_leaf_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {k₁ k₂ : Int} {a₁ b₁ a₂ b₂ : Term}
    (ha₁ : E a₁) (hb₁ : E b₁) (ha₂ : E a₂) (hb₂ : E b₂) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3» (D m) (.tuple #[.integer k₁, a₁, b₁])
        (.tuple #[.integer k₂, a₂, b₂]) (.map S) = .ok r ∧ LF E r ∧
      ∀ v : LV V, v.xs ≠ [] → dL E den r v =
        (dL E den (.tuple #[.integer k₁, a₁, b₁]) v && dL E den (.tuple #[.integer k₂, a₂, b₂]) v) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  obtain ⟨a, ea, ra, sa⟩ := ef.opt_inter S ha₁ ha₂ hn
  obtain ⟨b, eb, rb, sb⟩ := ef.opt_inter S hb₁ hb₂ hn
  obtain ⟨xa, runa, iffa⟩ := nl_empty1 ef (m := n + 1) (by omega) ea
  obtain ⟨xb, runb, iffb⟩ := nl_empty1 ef (m := n + 1) (by omega) eb
  obtain ⟨k, leaf⟩ := nl_leaf_new ef ea eb
  have both : ∀ v : LV V, (dL E den (.tuple #[.integer k₁, a₁, b₁]) v && dL E den (.tuple #[.integer k₂, a₂, b₂]) v) =
      Bool.true ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last := by
    intro v
    simp only [dL, eval_leaf, Bool.and_eq_true, nl_llit_val ef ha₁ hb₁, nl_llit_val ef ha₂ hb₂, sa, sb]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩; exact ⟨fun x mx => ⟨h₁ x mx, h₃ x mx⟩, h₂, h₄⟩
    · rintro ⟨h₁, h₂, h₄⟩; exact ⟨⟨fun x mx => (h₁ x mx).1, h₂⟩, fun x mx => (h₁ x mx).2, h₄⟩
  have unfold : Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3» (D (n + 1)) (.tuple #[.integer k₁, a₁, b₁])
      (.tuple #[.integer k₂, a₂, b₂]) (.map S) =
      if xa then .ok (.atom "bdd_bot") else if xb then .ok (.atom "bdd_bot")
      else .ok (.tuple #[.integer k, a, b]) := by
    unfold Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3»
    have fa : Lynx.Dispatcher.pure (D (n + 1))
        (.function "Elixir.Module.Types.Descr" "-opt_list_leaf_intersection/3-fun-0-" 2 #[.map S]) #[a₁, a₂] = .ok a := by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_list_leaf_intersection/3-fun-0-/2».pure]
      simpa [Elixir.Module.Types.Descr.«-opt_list_leaf_intersection/3-fun-0-/3»] using ra
    have fb : Lynx.Dispatcher.pure (D (n + 1))
        (.function "Elixir.Module.Types.Descr" "-opt_list_leaf_intersection/3-fun-0-" 2 #[.map S]) #[b₁, b₂] = .ok b := by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_list_leaf_intersection/3-fun-0-/2».pure]
      simpa [Elixir.Module.Types.Descr.«-opt_list_leaf_intersection/3-fun-0-/3»] using rb
    cases xa <;> cases xb <;>
      simp [Elixir.Module.Types.Descr.«non_empty_intersection!/3», fa, fb, runa, runb, isMember,
        boolAtom, Lynx.Except.tryWith, Lynx.Exception.classTerm, Lynx.Exception.reason, leaf]
  rw [unfold]
  cases xa
  · cases xb
    · refine ⟨_, rfl, Bdd.leaf_iff.mpr ⟨k, a, b, rfl, ea, eb⟩, fun v _ => ?_⟩
      have e : dL E den (.tuple #[.integer k, a, b]) v = Bool.true ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last := by
        rw [dL, eval_leaf]; exact nl_llit_val ef ea eb v
      exact Bool.eq_iff_iff.mpr (e.trans (both v).symm)
    · refine ⟨_, rfl, Bdd.bot, fun v _ => ?_⟩
      refine Bool.eq_iff_iff.mpr ⟨fun h => by simp [dL] at h, fun h => ?_⟩
      exact absurd ((both v).mp h).2 ((iffb.mp rfl) v.last)
  · refine ⟨_, rfl, Bdd.bot, fun v ne => ?_⟩
    refine Bool.eq_iff_iff.mpr ⟨fun h => by simp [dL] at h, fun h => ?_⟩
    obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil v.xs ne
    exact absurd (((both v).mp h).1 x mx) ((iffa.mp rfl) x)

theorem nl_oi_top_l {d : Dispatcher} {k y S : Term} :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k, .atom "term", .atom "term"]) y S = .ok y := by
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»; rfl

theorem nl_oi_top_r {d : Dispatcher} {x k S : Term} (nx : NoTopL x) :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d x (.tuple #[k, .atom "term", .atom "term"]) S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
  split
  all_goals first
    | rfl
    | exact (nx _ rfl).elim
    | (rename_i h; exact (h _ rfl).elim)
    | (rename_i h _; exact (h _ rfl).elim)
    | (exfalso; simp_all)

theorem nl_oi_plain {d : Dispatcher} {x y S : Term} (nx : NoTopL x) (ny : NoTopL y)
    (nl : ¬((∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b])) :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d x y S = Elixir.Module.Types.Descr.«list_intersection/2» x y := by
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := by
    rintro a b c rfl e
    obtain ⟨_, _, _, rfl, -⟩ := exact_tuple3 e
    exact nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
  split
  · exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · simp only [leaf_guard]
    split
    · rw [ite_eq_right (ne _ _ _ rfl)]
      split
      · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
      · rfl
    · split
      · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
      · rfl

/-- Exactly equal list leaves intersect to the first. -/
theorem nl_oi_same {d : Dispatcher} {S k a b y : Term} (nx : NoTopL (.tuple #[k, a, b])) (ny : NoTopL y)
    (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k, a, b]) y S = .ok (.tuple #[k, a, b]) := by
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
  split
  · rename_i heq; obtain ⟨-, rfl, rfl⟩ := tuple3_eq heq; exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · simp only [leaf_guard]
    rw [ite_eq_left (by simpa using e)]
    rfl

theorem nl_oi_leaves {d : Dispatcher} {S k₁ a₁ b₁ k₂ a₂ b₂ : Term}
    (nx : NoTopL (.tuple #[k₁, a₁, b₁])) (ny : NoTopL (.tuple #[k₂, a₂, b₂]))
    (ne : compareExact (fuel (.tuple #[k₂, a₂, b₂]) (.tuple #[k₁, a₁, b₁])) (.tuple #[k₂, a₂, b₂]) (.tuple #[k₁, a₁, b₁]) ≠ .eq) :
    (Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_intersection") (.tuple #[k₁, a₁, b₁])
        (.tuple #[k₂, a₂, b₂]) = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k₁, a₁, b₁]) (.tuple #[k₂, a₂, b₂]) S =
        Elixir.Module.Types.Descr.«list_intersection/2» (.tuple #[k₁, a₁, b₁]) (.tuple #[k₂, a₂, b₂])) ∧
    (∀ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_intersection") (.tuple #[k₁, a₁, b₁])
        (.tuple #[k₂, a₂, b₂]) = .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k₁, a₁, b₁]) (.tuple #[k₂, a₂, b₂]) S =
        Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3» d (.tuple #[k₁, a₁, b₁])
          (.tuple #[k₂, a₂, b₂]) S') := by
  constructor <;> intros <;>
  · unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
    split
    all_goals try (simp only [leaf_guard]; rw [ite_eq_right (by simpa using ne)])
    all_goals first
      | (exfalso; rename_i heq; obtain ⟨-, rfl, rfl⟩ := heq; first | exact nx _ rfl | exact ny _ rfl)
      | (exfalso; rename_i heq h; obtain ⟨-, rfl, rfl⟩ := heq; first | exact nx _ rfl | exact ny _ rfl)
      | (exfalso; rename_i h heq; obtain ⟨-, rfl, rfl⟩ := heq; first | exact nx _ rfl | exact ny _ rfl)
      | (next h => exact (h _ _ _ _ _ _ rfl rfl).elim)
      | simp_all

/-- Optimized intersections of list fields hold the lists of both. -/
theorem nl_opt_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {x y : Term} (wx : LF E x) (wy : LF E y)
    (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom "list") x y (.map S) = .ok r ∧ LF E r ∧
      ∀ v, ListVal tl v → dL E den r v = (dL E den x v && dL E den y v) := by
  simp only [Elixir.Module.Types.Descr.«opt_intersection/4»]
  have plain : Elixir.Module.Types.Descr.«opt_list_intersection/3» (D m) x y (.map S) =
      Elixir.Module.Types.Descr.«list_intersection/2» x y → ∃ r,
      Elixir.Module.Types.Descr.«opt_list_intersection/3» (D m) x y (.map S) = .ok r ∧ LF E r ∧
      ∀ v, ListVal tl v → dL E den r v = (dL E den x v && dL E den y v) := by
    intro e
    obtain ⟨r, run, wr, sem, -⟩ := nl_bare_inter ef wx wy
    exact ⟨r, by rw [e]; simpa [Elixir.Module.Types.Descr.«bare_intersection/3»] using run (D m), wr,
      fun v _ => sem v⟩
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    exact ⟨y, nl_oi_top_l, wy, fun v _ => by rw [nl_top_dL ef wx]; rfl⟩
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    exact ⟨x, nl_oi_top_r nx, wx, fun v _ => by rw [nl_top_dL ef wy]; simp⟩
  have ny : NoTopL y := fun k e => ty ⟨k, e⟩
  by_cases leaves : (∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b]
  · obtain ⟨⟨k₁, a₁, b₁, rfl⟩, ⟨k₂, a₂, b₂, rfl⟩⟩ := leaves
    obtain ⟨k₁, rfl⟩ := leaf_int wx
    obtain ⟨k₂, rfl⟩ := leaf_int wy
    obtain ⟨k₁', a₁', b₁', e₁, ha₁, hb₁⟩ := Bdd.leaf_iff.mp wx
    obtain ⟨-, e₁₂, e₁₃⟩ := tuple3_inj e₁
    subst e₁₂ e₁₃
    obtain ⟨k₂', a₂', b₂', e₂, ha₂, hb₂⟩ := Bdd.leaf_iff.mp wy
    obtain ⟨-, e₂₂, e₂₃⟩ := tuple3_inj e₂
    subst e₂₂ e₂₃
    by_cases same : compareExact (fuel (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁])) (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁]) = .eq
    · exact ⟨_, nl_oi_same nx ny same, wx, fun v _ => by
        simp only [dL, eval_exact wx (valL_resp v) same, Bool.and_self]⟩
    rcases opt_bdd_seen_map S (.atom "list_intersection") (.tuple #[.integer k₁, a₁, b₁])
      (.tuple #[.integer k₂, a₂, b₂]) with seen | ⟨S', ok⟩
    · exact plain ((nl_oi_leaves nx ny same).1 seen)
    · obtain ⟨r, run, wr, sem⟩ := nl_leaf_inter ef hm ha₁ hb₁ ha₂ hb₂ S'
      exact ⟨r, by rw [(nl_oi_leaves nx ny same).2 _ ok, run], wr, fun v lv => sem v lv.1⟩
  · exact plain (nl_oi_plain nx ny leaves)

/-- Optimized unions of list fields are plain unions. -/
theorem nl_opt_union (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d S, Elixir.Module.Types.Descr.«opt_union/4» d (.atom "list") x y S = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v || dL E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, wr, sem, le⟩ := nl_bare_union ef wx wy
  refine ⟨r, fun d S => ?_, wr, sem, le⟩
  simpa [Elixir.Module.Types.Descr.«opt_union/4», Elixir.Module.Types.Descr.«bare_union/3»] using run d

end Elixir.STTDescrProofsTest.Nest
