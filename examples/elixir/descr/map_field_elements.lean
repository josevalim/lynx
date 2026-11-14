namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Map fields of element types: what the descr level needs of them. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Map fields that compare equal hold the same maps. -/
theorem denMF_resp {x x' : Term} (fx : MField E x) (fx' : MField E x') (e : Term.compare (Term.fuel x x') x x' = .eq) (w : MW V) :
    denMF E den x w = denMF E den x' w := by
  rcases fx with ⟨k, rfl⟩ | wx
  · rcases fx' with ⟨k', rfl⟩ | wx'
    · rw [denMF_top, denMF_top]
    · exfalso
      obtain ⟨ys, rfl, ex⟩ : ∃ ys : Array Term, x' = .tuple ys ∧ True := by
        cases x' <;> rw [Term.compare_step] at e <;> simp [Compare.compareStep] at e
        exact ⟨_, rfl, trivial⟩
      rw [compare_tuple] at e
      obtain ⟨l⟩ := ys
      simp only [Ordering.then_eq_eq] at e
      match l, e with
      | [a, b, c], e =>
        simp only [List.compareLex_cons_cons, Ordering.then_eq_eq] at e
        obtain ⟨-, eb, ec, -⟩ := e.2
        obtain rfl := (compare_eq_atom b "open").mp (Lynx.Term.compare_eq_symm eb)
        obtain rfl := (compare_eq_nil c).mp (Lynx.Term.compare_eq_symm ec)
        exact not_top_of_ok wx' mlit_not a rfl
      | [], e => simp at e
      | [_], e => simp at e
      | [_, _], e => simp at e
      | _ :: _ :: _ :: _ :: _, e => simp at e
  · rcases fx' with ⟨k', rfl⟩ | wx'
    · exfalso
      obtain ⟨ys, rfl, -⟩ : ∃ ys : Array Term, x = .tuple ys ∧ True := by
        cases x <;> rw [Term.compare_step] at e <;> simp [Compare.compareStep] at e
        exact ⟨_, rfl, trivial⟩
      rw [compare_tuple] at e
      obtain ⟨l⟩ := ys
      simp only [Ordering.then_eq_eq] at e
      match l, e with
      | [a, b, c], e =>
        simp only [List.compareLex_cons_cons, Ordering.then_eq_eq] at e
        obtain ⟨-, eb, ec, -⟩ := e.2
        obtain rfl := (compare_eq_atom b "open").mp eb
        obtain rfl := (compare_eq_nil c).mp ec
        exact not_top_of_ok wx mlit_not a rfl
      | [], e => simp at e
      | [_], e => simp at e
      | [_, _], e => simp at e
      | _ :: _ :: _ :: _ :: _, e => simp at e
    · rw [denMF_bdd wx, denMF_bdd wx']
      exact eval_congr_cmp wx (valM_resp w) e

/-! Field-level deliverables for maps. -/

/-- F3: plain unions of map fields. -/
theorem map_field_union {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "map") x y = .ok r) ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w || denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, fr, sem, le⟩ := map_union_lh (den := den) fx fy
  exact ⟨r, fun d => by simpa [Elixir.Module.Types.Descr.«bare_union/3»] using run, fr, sem, le⟩

/-- F3: plain intersections of map fields. -/
theorem map_field_inter {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "map") x y = .ok r) ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w && denMF E den y w)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, fr, sem, le⟩ := map_inter_lh (den := den) fx fy
  exact ⟨r, fun d => by simpa [Elixir.Module.Types.Descr.«bare_intersection/3»] using run, fr, sem, le⟩

/-- F3: plain differences of map fields. -/
theorem map_field_diff {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map") x y = .ok r) ∧ MField E r ∧
      (∀ w, denMF E den r w = (denMF E den x w && !denMF E den y w)) ∧
      (r ≠ .atom "bdd_bot" → lh r ≤ max (lh x) (lh y)) := by
  obtain ⟨r, run, fr, sem, le⟩ := map_diff_lh (den := den) fx fy
  exact ⟨r, fun d => by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, fr, sem, le⟩

/-- F4: optimized unions of map fields. -/
theorem map_field_opt_union (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_union/4» (D m) (.atom "map") x y (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w || denMF E den y w) := by
  obtain ⟨r, run, fr, sem⟩ := opt_map_union_sem ef hm fx fy S
  exact ⟨r, by simpa [Elixir.Module.Types.Descr.«opt_union/4»] using run, fr, sem⟩

/-- F4: optimized intersections of map fields. -/
theorem map_field_opt_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom "map") x y (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
  obtain ⟨r, run, fr, sem⟩ := opt_map_inter_val ef hm fx fy S
  exact ⟨r, by simpa [Elixir.Module.Types.Descr.«opt_intersection/4»] using run, fr, sem⟩

/-- F4: optimized differences of map fields; dropped results have no maps. -/
theorem map_field_opt_diff (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom "map") x y (.map S) = .ok r ∧
      (kept (.atom "map", r) = Bool.true → MField E r ∧ ∀ w, denMF E den r w = (denMF E den x w && !denMF E den y w)) ∧
      (kept (.atom "map", r) = Bool.false → ∀ w, (denMF E den x w && !denMF E den y w) = Bool.false) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  obtain ⟨r, run, k, d⟩ := opt_map_diff_val ef hn fx fy S
  exact ⟨r, by simpa [Elixir.Module.Types.Descr.«opt_difference/4»] using run, k, d⟩

/-- F5: map fields decide their emptiness exactly, when the seen BDDs are higher than them. -/
theorem map_field_empty (ef : EF nd E V den tl K) {x : Term} (fx : MField E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
        Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "map") x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) := by
  obtain ⟨b, run, sem⟩ := map_empty_exact ef fx S
  exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m hm, sem⟩

end Elixir.STTDescrProofsTest.Nest
