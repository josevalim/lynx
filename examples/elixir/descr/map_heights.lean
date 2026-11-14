namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Plain operations on map types keep literal heights. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- BDDs of map literals below a positive height are below it. -/
theorem mbdd_lh_bound {ok : Term → Prop} {r : Term} (wr : Bdd ok r) {M : Nat}
    (lits : ∀ t, ok t → MLit E t ∧ lh t ≤ M) (top : 1 ≤ M) : lh r ≤ M := by
  revert lits top
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MLit E t ∧ lh t ≤ M) → 1 ≤ M → lh r ≤ M)
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ top; simpa [lh] using top
  · intro _ _ top; simpa [lh] using top
  · intro ok k x y okl lits _
    exact (lits _ okl).2
  · intro ok h lit c u d leaf okl _ _ _ ic iu idd lits _
    obtain ⟨k, a, b, rfl⟩ := leaf
    have ⟨tl', le⟩ := lits _ okl
    have lits' : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → MLit E t ∧ lh t ≤ M := fun t ht => lits t ht.1
    have hc := ic lits' (by omega)
    have hu := iu lits' (by omega)
    have hd := idd lits' (by omega)
    have hl := mlit_lh_eq tl'
    have hn := lh_node (.integer h) (.integer k) a b c u d (mlit_litZ tl')
    change lh (.tuple ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩) ≤ M
    omega

theorem mfield_mono {x : Term} (wx : Bdd (MLit E) x) {M : Nat} (le : lh x ≤ M) :
    Bdd (fun t => MLit E t ∧ lh t ≤ M) x :=
  (mbdd_lh_le wx (fun _ h => h) M le).mono fun _ h => h

/-- BDDs of map literals have a height. -/
theorem mbdd_pos {x : Term} (wx : Bdd (MLit E) x) : 1 ≤ lh x := by
  by_cases t : x = .atom "bdd_top"
  · subst t; simp [lh]
  by_cases b : x = .atom "bdd_bot"
  · subst b; simp [lh]
  · exact mbdd_lh wx t b

theorem mlh_top_leaf (k : Term) : lh (.tuple #[k, .atom "open", .nil]) = 0 := lh_leaf_top k

/-- Plain unions of map types. -/
theorem map_union_lh {x y : Term} (hx : MField E x) (hy : MField E y) :
    ∃ r, Elixir.Module.Types.Descr.«map_union/2» x y = .ok r ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w || denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, fr, sem⟩ := map_union_field (den := den) hx hy
  refine ⟨r, run, fr, sem, ?_⟩
  rcases hx with ⟨k, rfl⟩ | wx
  · have e : Elixir.Module.Types.Descr.«map_union/2» (.tuple #[.integer k, .atom "open", .nil]) y =
        .ok (.tuple #[.integer k, .atom "open", .nil]) := by unfold Elixir.Module.Types.Descr.«map_union/2»; rfl
    rw [e] at run; cases run; rw [mlh_top_leaf]; omega
  rcases hy with ⟨k, rfl⟩ | wy
  · have nx := not_top_of_ok wx mlit_not
    have e : Elixir.Module.Types.Descr.«map_union/2» x (.tuple #[.integer k, .atom "open", .nil]) =
        .ok (.tuple #[.integer k, .atom "open", .nil]) := by
      unfold Elixir.Module.Types.Descr.«map_union/2»
      split
      · exact (nx _ rfl).elim
      · rename_i e; simp at e; subst e; rfl
      · rename_i h; exact (h _ rfl).elim
    rw [e] at run; cases run; rw [mlh_top_leaf]; omega
  obtain ⟨r', hr, okr, semr⟩ := union_ok wx wy
  rw [map_union_bdd (not_top_of_ok wx mlit_not) (not_top_of_ok wy mlit_not), hr] at run
  cases run
  exact mbdd_lh_bound (okr _ (mfield_mono wx (Nat.le_max_left _ _)) (mfield_mono wy (Nat.le_max_right _ _)))
    (fun _ h => h) (by have := mbdd_pos wx; omega)

/-- Plain intersections of map types. -/
theorem map_inter_lh {x y : Term} (hx : MField E x) (hy : MField E y) :
    ∃ r, Elixir.Module.Types.Descr.«map_intersection/2» x y = .ok r ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w && denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«map_intersection/2»; rfl, hy, fun w => by simp [denMF_top],
      by omega⟩
  have nx := not_top_of_ok wx mlit_not
  rcases hy with ⟨k, rfl⟩ | wy
  · refine ⟨x, ?_, Or.inr wx, fun w => by simp [denMF_top], by omega⟩
    unfold Elixir.Module.Types.Descr.«map_intersection/2»
    split
    · exact (nx _ rfl).elim
    · simp_all
    · rename_i h₁ h₂; exact (h₂ _ rfl).elim
  · obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [map_intersection_bdd nx (not_top_of_ok wy mlit_not), hr], Or.inr wr, fun w => ?_, ?_⟩
    · rw [denMF_bdd wr, denMF_bdd wx, denMF_bdd wy, semr _ (valM_resp w)]
    · exact mbdd_lh_bound (okr _ (mfield_mono wx (Nat.le_max_left _ _)) (mfield_mono wy (Nat.le_max_right _ _)))
        (fun _ h => h) (by have := mbdd_pos wx; omega)

/-- Plain differences of map types: non-empty results keep heights. -/
theorem map_diff_lh {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ w, Elixir.Module.Types.Descr.«map_difference/2» x y = .ok w ∧ MField E w ∧
      (∀ v, denMF E den w v = (denMF E den x v && !denMF E den y v)) ∧
      (w ≠ .atom "bdd_bot" → lh w ≤ max (lh x) (lh y)) := by
  obtain ⟨w₀, run₀, fw₀, sem₀⟩ := map_diff_val (den := den) fx fy
  refine ⟨w₀, run₀, fw₀, sem₀, fun nb => ?_⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · have : w₀ = .atom "bdd_bot" := by
      have e : Elixir.Module.Types.Descr.«map_difference/2» x (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl
      rw [e] at run₀; cases run₀; rfl
    exact absurd this nb
  have ny := not_top_of_ok wy mlit_not
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · have e : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
        unfold Elixir.Module.Types.Descr.«map_difference/2»; simp [diff_leaf_top]
      rw [e] at run₀; cases run₀; exact absurd rfl nb
    · have e : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.atom "bdd_bot") = .ok (.tuple #[.integer kt, .atom "open", .nil]) := by
        unfold Elixir.Module.Types.Descr.«map_difference/2»; simp [diff_leaf_bot]
      rw [e] at run₀; cases run₀; omega
    all_goals
      obtain ⟨w, run, keep, sem⟩ := neg_ok wy
      rw [map_difference_neg ny _ rfl, run] at run₀
      cases run₀
      exact mbdd_lh_bound (keep _ (mfield_mono wy (Nat.le_max_right _ _))) (fun _ h => h)
        (by have := mbdd_lh wy (by simp) (by simp); omega)
  · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
    rw [map_difference_bdd (not_top_of_ok wx mlit_not) ny, run] at run₀
    cases run₀
    exact mbdd_lh_bound (keep _ (mfield_mono wx (Nat.le_max_left _ _)) (mfield_mono wy (Nat.le_max_right _ _)))
      (fun _ h => h) (by have := mbdd_pos wx; omega)

end Elixir.STTDescrProofsTest.Nest
