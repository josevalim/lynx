namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Unions of gradual types. -/

section
variable {L : Level}

theorem bare_union_op {n : Nat} (hm : L.K + 12 ≤ n) :
    UnionOp L (D (n + 1)) "Elixir.Module.Types.Descr" "bare_union" #[]
      (Elixir.Module.Types.Descr.«bare_union/3» (D n)) where
  call := fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure n q v₁ v₂
  spec := fun _ _ _ fx fy =>
    let ⟨u, ru, fu, su, _⟩ := fieldC_union (tks L) (tfc L) (by omega) fx fy; ⟨u, ru, fu, su⟩

theorem opt_union_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    UnionOp L (D (n + 1)) "Elixir.Module.Types.Descr" "-opt_union/3-anonymous-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_union/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_union/3-anonymous-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_union (tks L) (tfc L) (by omega) fx fy S

theorem opt_union_dyn_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    UnionOp L (D (n + 1)) "Elixir.Module.Types.Descr" "-opt_union/4-fun-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_union/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_union/4-fun-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_union (tks L) (tfc L) (by omega) fx fy S

theorem bare_union_dyn (d : Dispatcher) (x y : Term) :
    Elixir.Module.Types.Descr.«bare_union/3» d (.atom "dynamic") x y =
      Elixir.Module.Types.Descr.«dynamic_union/3» d x y (.function "Elixir.Module.Types.Descr" "bare_union" 3 #[]) := by
  unfold Elixir.Module.Types.Descr.«bare_union/3»; rfl

theorem opt_union_dyn (d : Dispatcher) (x y S : Term) :
    Elixir.Module.Types.Descr.«opt_union/4» d (.atom "dynamic") x y S =
      Elixir.Module.Types.Descr.«dynamic_union/3» d x y (.function "Elixir.Module.Types.Descr" "-opt_union/4-fun-0-" 3 #[S]) := by
  unfold Elixir.Module.Types.Descr.«opt_union/4»; rfl

theorem union_run_grad (d : Dispatcher) {X Y : List (Term × Term)} (nX : X ≠ []) (nY : Y ≠ [])
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.map X) (.map Y) =
      Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map (alignT X)) (.map (alignT Y))
        (.function "Elixir.Module.Types.Descr" "bare_union" 3 #[]) := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, Erlang.erlang.«==/2», hX, hY, nX, nY, Erlang.maps.«put/3», alignT]

theorem opt_union_run_grad (d : Dispatcher) {X Y : List (Term × Term)} (S : Term) (nX : X ≠ []) (nY : Y ≠ [])
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«opt_union/3» d (.map X) (.map Y) S =
      Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map (alignT X)) (.map (alignT Y))
        (.function "Elixir.Module.Types.Descr" "-opt_union/3-anonymous-0-" 3 #[S]) := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, Erlang.erlang.«==/2», hX, hY, nX, nY, Erlang.maps.«put/3», alignT]

theorem GC.shape {a : Term} (ha : GC L a) : a = .atom "term" ∨ ∃ X, a = .map X := by
  rcases ha with (h | ⟨X, rfl, -⟩) | ⟨X, -, rfl, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨X, rfl⟩
  · exact Or.inr ⟨X, rfl⟩

theorem GC.static {X : List (Term × Term)} (hX : GC L (.map X)) (st : mapLookup X (.atom "dynamic") = none) :
    TC L (.map X) := by
  rcases hX with h | ⟨X', Dy, e, hD, -⟩
  · exact h
  · simp only [Term.map.injEq] at e; subst e; rw [st] at hD; cases hD

theorem upper_term : upper (.atom "term") = .atom "term" := rfl

theorem upper_nil : upper (.map []) = .map [] := rfl

/-- Unions hold the points of either type, at both bounds. -/
def USem (L : Level) (a b c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ denD a v ∨ denD b v) ∧ ∀ v : TP L, denD (upper c) v ↔ denD (upper a) v ∨ denD (upper b) v

theorem usem_term_l (a : Term) : USem L (.atom "term") a (.atom "term") :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem usem_term_r (a : Term) : USem L a (.atom "term") (.atom "term") :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem usem_nil_l (a : Term) : USem L (.map []) a a :=
  ⟨fun v => by simp [denD_nil], fun v => by simp [upper_nil, denD_nil]⟩

theorem usem_nil_r (a : Term) : USem L a (.map []) a :=
  ⟨fun v => by simp [denD_nil], fun v => by simp [upper_nil, denD_nil]⟩

theorem usem_tc {a b c : Term} (ha : TC L a) (hb : TC L b) (hc : TC L c)
    (sem : ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v) : USem L a b c :=
  ⟨sem, by rw [upper_tc ha, upper_tc hb, upper_tc hc]; exact sem⟩

theorem union_nil_l (d : Dispatcher) (Y : List (Term × Term)) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.map []) (.map Y) = .ok (.map Y) := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]

theorem union_nil_r (d : Dispatcher) (X : List (Term × Term)) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.map X) (.map []) = .ok (.map X) := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»
  by_cases h : X = [] <;> simp [Erlang.erlang.«==/2», h]

theorem opt_union_nil_l (d : Dispatcher) (Y : List (Term × Term)) (S : Term) :
    Elixir.Module.Types.Descr.«opt_union/3» d (.map []) (.map Y) S = .ok (.map Y) := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»; simp [Erlang.erlang.«==/2»]

theorem opt_union_nil_r (d : Dispatcher) (X : List (Term × Term)) (S : Term) :
    Elixir.Module.Types.Descr.«opt_union/3» d (.map X) (.map []) S = .ok (.map X) := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»
  by_cases h : X = [] <;> simp [Erlang.erlang.«==/2», h]

theorem dyn_isSome {X : List (Term × Term)} (st : ¬TC L (.map X)) (hX : GC L (.map X)) :
    (mapLookup X (.atom "dynamic")).isSome := by
  cases h : mapLookup X (.atom "dynamic")
  · exact absurd (hX.static h) st
  · rfl

theorem gc_union {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧ USem L a b c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, GC.tc tc_term, union_term_l _ _, usem_term_l _⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_term, union_term_r _ _, usem_term_r _⟩
  by_cases nX : X = []
  · subst nX; exact ⟨_, hb, union_nil_l _ _, usem_nil_l _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨_, ha, union_nil_r _ _, usem_nil_r _⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_union st.1 st.2 (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, usem_tc st.1 st.2 hc sem⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, lo, up, -⟩ := merge_aligned (bare_union_op (n := k + 1) (by omega))
    (bare_union_op (n := k) (by omega)) (bare_union_dyn _) ha hb
  exact ⟨c, hc, (union_run_grad _ nX nY g).trans run, lo, up⟩

theorem gc_opt_union {a b : Term} (ha : GC L a) (hb : GC L b) (S : List (Term × Term)) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧ USem L a b c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, GC.tc tc_term, opt_union_term_left _ _ _, usem_term_l _⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_term, opt_union_term_r _ _ _, usem_term_r _⟩
  by_cases nX : X = []
  · subst nX; exact ⟨_, hb, opt_union_nil_l _ _ _, usem_nil_l _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨_, ha, opt_union_nil_r _ _ _, usem_nil_r _⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_opt_union st.1 st.2 S (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, usem_tc st.1 st.2 hc sem⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, lo, up, -⟩ := merge_aligned (opt_union_op (n := k + 1) (by omega) S)
    (opt_union_dyn_op (n := k) (by omega) S) (fun x y => opt_union_dyn _ x y _) ha hb
  exact ⟨c, hc, (opt_union_run_grad _ _ nX nY g).trans run, lo, up⟩

end

end Elixir.STTDescrProofsTest.Nest
