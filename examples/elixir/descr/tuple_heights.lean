namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Plain operations on tuple types keep literal heights. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- BDDs of tuple literals below a positive height are below it. -/
theorem bdd_lh_bound {ok : Term → Prop} {r : Term} (wr : Bdd ok r) {M : Nat}
    (lits : ∀ t, ok t → TLit E t ∧ lh t ≤ M) (top : 1 ≤ M) : lh r ≤ M := by
  revert lits top
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TLit E t ∧ lh t ≤ M) → 1 ≤ M → lh r ≤ M)
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ top; simpa [lh] using top
  · intro _ _ top; simpa [lh] using top
  · intro ok k x y okl lits _
    exact (lits _ okl).2
  · intro ok h lit c u d leaf okl _ _ _ ic iu idd lits one
    obtain ⟨k, a, b, rfl⟩ := leaf
    have ⟨tl', le⟩ := lits _ okl
    obtain ⟨⟨⟨k', tag, l, e, g, -⟩, nt⟩, -⟩ := tl'
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [h₁, h₂]⟩
    have lits' : ∀ t, Above ok (.tuple #[.integer k, .atom tag, Term.list l]) t → TLit E t ∧ lh t ≤ M :=
      fun t ht => lits t ht.1
    have hc := ic lits' one
    have hu := iu lits' one
    have hd := idd lits' one
    rw [tlit_node_lh (h := h) g top c u d]
    omega

theorem tfield_mono {x : Term} (wx : Bdd (TLit E) x) {M : Nat} (le : lh x ≤ M) :
    Bdd (fun t => TLit E t ∧ lh t ≤ M) x :=
  (bdd_lh_le wx (fun _ h => h) M le).mono fun _ h => h

/-- BDDs of tuple literals have a height. -/
theorem tbdd_pos {x : Term} (wx : Bdd (TLit E) x) : 1 ≤ lh x := by
  by_cases t : x = .atom "bdd_top"
  · subst t; simp [lh]
  by_cases b : x = .atom "bdd_bot"
  · subst b; simp [lh]
  · exact tlit_bdd_lh wx t b

theorem lh_top_leaf (k : Term) : lh (.tuple #[k, .atom "open", .nil]) = 0 := lh_leaf_top k

/-- Plain unions of tuple types. -/
theorem tuple_union_lh {x y : Term} (hx : TField E x) (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok r ∧ TField E r ∧
      (∀ v, denTF E den r v = (denTF E den x v || denTF E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl, Or.inl ⟨k, rfl⟩,
      fun v => by simp [denTF_top], by rw [lh_top_leaf]; omega⟩
  rcases hy with ⟨k, rfl⟩ | wy
  · exact ⟨_, tuple_union_right (not_top_of_ok wx tlit_not) _, Or.inl ⟨k, rfl⟩, fun v => by simp [denTF_top],
      by rw [lh_top_leaf]; omega⟩
  obtain ⟨r, hr, okr, semr⟩ := union_ok wx wy
  have wr := okr _ wx wy
  refine ⟨r, by rw [tuple_union_bdd (not_top_of_ok wx tlit_not) (not_top_of_ok wy tlit_not), hr],
    Or.inr wr, fun v => ?_, ?_⟩
  · rw [denTF_bdd wr, denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]
  · exact bdd_lh_bound (okr _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
      (fun _ h => h) (by have := tbdd_pos wx; omega)

/-- Plain intersections of tuple types. -/
theorem tuple_inter_lh {x y : Term} (hx : TField E x) (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_intersection/2» x y = .ok r ∧ TField E r ∧
      (∀ v, denTF E den r v = (denTF E den x v && denTF E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«tuple_intersection/2»; rfl, hy, fun v => by simp [denTF_top],
      by omega⟩
  have nx := not_top_of_ok wx tlit_not
  rcases hy with ⟨k, rfl⟩ | wy
  · refine ⟨x, ?_, Or.inr wx, fun v => by simp [denTF_top], by omega⟩
    unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
    split
    · exact (nx _ rfl).elim
    · simp_all
    · rename_i h₁ h₂; exact (h₂ _ rfl).elim
  · obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [tuple_intersection_bdd nx (not_top_of_ok wy tlit_not), hr], Or.inr wr, fun v => ?_, ?_⟩
    · rw [denTF_bdd wr, denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]
    · exact bdd_lh_bound (okr _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
        (fun _ h => h) (by have := tbdd_pos wx; omega)

theorem lh_closed_nil (k : Int) : lh (.tuple #[.integer k, .atom "closed", .nil]) = 1 := by
  simp [lh]

theorem lh_open_term (k : Int) : lh (.tuple #[.integer k, .atom "open", Term.list [.atom "term"]]) = 1 := by
  have := lh_lit (k := k) (tag := "open") (l := [.atom "term"]) (Or.inl rfl) (by simp) (by simp [ExpEls])
  rw [this]
  simp [Term.list, lh]

/-- Plain differences of tuple types: non-empty results keep heights. -/
theorem tuple_diff_lh (ef : EF nd E V den tl K) {x y : Term} (fx : TField E x) (fy : TField E y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧ TField E w ∧
      (∀ v, denTF E den w v = (denTF E den x v && !denTF E den y v)) ∧
      (w ≠ .atom "bdd_bot" → lh w ≤ max (lh x) (lh y)) := by
  obtain ⟨w₀, run₀, fw₀, sem₀⟩ := tuple_diff_val ef fx fy
  refine ⟨w₀, run₀, fw₀, sem₀, fun nb => ?_⟩
  -- the bound, by the cases of the difference
  rcases fy with ⟨k, rfl⟩ | wy
  · have : w₀ = .atom "bdd_bot" := by
      have e : Elixir.Module.Types.Descr.«tuple_difference/2» x (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl
      rw [e] at run₀; cases run₀; rfl
    exact absurd this nb
  have ny := not_top_of_ok wy tlit_not
  by_cases special : ∃ k, y = .tuple #[k, .atom "closed", .nil]
  · obtain ⟨k, rfl⟩ := special
    obtain ⟨k, rfl⟩ := leaf_int wy
    rcases fx with ⟨kt, rfl⟩ | wx
    · obtain ⟨h, run, -⟩ := leaf_new_key "open" (Or.inl rfl) [.atom "term"]
      have e : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.tuple #[.integer k, .atom "closed", .nil]) = .ok (.tuple #[.integer h, .atom "open", Term.list [.atom "term"]]) := by
        simp [Elixir.Module.Types.Descr.«tuple_difference/2», Erlang.erlang.«==/2», run]
      rw [e] at run₀; cases run₀
      rw [lh_open_term, lh_closed_nil]; omega
    · by_cases openLeaf : ∃ kx e, x = .tuple #[kx, .atom "open", e]
      · obtain ⟨kx, e, rfl⟩ := openLeaf
        have ne : e ≠ .nil := fun h => not_top_of_ok wx tlit_not _ (by rw [h])
        have e' : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[kx, .atom "open", e])
            (.tuple #[.integer k, .atom "closed", .nil]) = .ok (.tuple #[kx, .atom "open", e]) := by
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          cases e <;> simp_all [Erlang.erlang.«==/2»]
        rw [e'] at run₀; cases run₀; omega
      · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
        rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨h, _⟩ => openLeaf h), run] at run₀
        cases run₀
        exact bdd_lh_bound (keep _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
          (fun _ h => h) (by rw [lh_closed_nil]; omega)
  · rcases fx with ⟨kt, rfl⟩ | wx
    · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · have e : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
            (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»; simp [diff_leaf_top]
        rw [e] at run₀; cases run₀; exact absurd rfl nb
      · have e : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
            (.atom "bdd_bot") = .ok (.tuple #[.integer kt, .atom "open", .nil]) := by
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»; simp [diff_leaf_bot]
        rw [e] at run₀; cases run₀; omega
      all_goals
        obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run] at run₀
        cases run₀
        exact bdd_lh_bound (keep _ (tfield_mono wy (Nat.le_max_right _ _))) (fun _ h => h)
          (by have := tlit_bdd_lh wy (by simp) (by simp); omega)
    · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
      rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨_, h⟩ => special h), run] at run₀
      cases run₀
      exact bdd_lh_bound (keep _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
        (fun _ h => h) (by have := tbdd_pos wx; omega)

end Elixir.STTDescrProofsTest.Nest
