namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Differences of gradual types. -/

section
variable {L : Level}

/-- Field operations a difference removes fields with: they keep the points of the first field outside the second. -/
structure DiffOp (L : Level) (n : Nat) (fn : Term) (f : Term → Term → Term → Except Exception Term) : Prop where
  call : ∀ q v₁ v₂, (D (n + 1)).pure fn #[q, v₁, v₂] = f q v₁ v₂
  spec : ∀ name x y, FC L name x → FC L name y → ∃ w, f (.atom name) x y = .ok w ∧
    (kept (.atom name, w) = Bool.true → FC L name w) ∧
    ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)

/-- Differences of static parts. -/
theorem dyn_diff_tc {n : Nat} {fn : Term} {f : Term → Term → Term → Except Exception Term} (op : DiffOp L n fn f)
    {a b : Term} (ha : TC L a) (hb : TC L b) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) a b fn = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · have c : Term.compare (Term.fuel (.atom "term") (.map [])) (.atom "term") (.map []) ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    refine ⟨_, tc_nil, ?_, fun v => by simp [denD_nil, denD_term]⟩
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», c]
  by_cases nB : B = []
  · subst nB
    refine ⟨a, ha, ?_, fun v => by simp [denD_nil]⟩
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2»]
  have left : ∃ A, DC L A ∧ (∀ v : TP L, denD a v ↔ denD (.map A) v) ∧
      Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) a (.map B) fn =
        Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) (.map A) (.map B) fn := by
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · obtain ⟨T, term, sT, -, all⟩ := termT L
      refine ⟨T, sT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩, ?_⟩
      unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
      simp [Erlang.erlang.«==/2», nB, term]
    · exact ⟨A, sA, fun v => Iff.rfl, rfl⟩
  obtain ⟨A, sA, eA, rA⟩ := left
  obtain ⟨O, fold, sO, dO, -⟩ := diff_gen (slh := False) n fn f sA sB op.call
    (fun k x y fx fy => let ⟨w, rw', kw, sw⟩ := op.spec k x y fx fy; ⟨w, rw', fun h => ⟨kw h, False.elim⟩, sw⟩)
  refine ⟨_, Or.inr ⟨O, rfl, sO⟩, ?_, fun v => ?_⟩
  · rw [rA]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», nB, Erlang.maps.«fold/3»]
    simpa using fold
  · rw [eA]
    simp only [denD_map, dO _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- The static part of a type, as `pop_dynamic/1` takes it. -/
def lower (a : Term) : Term :=
  match a with
  | .map X => .map (rmDyn X)
  | _ => a

theorem GC.low_tc {a : Term} (ha : GC L a) : TC L (lower a) := by
  rcases ha with (rfl | ⟨X, rfl, sX⟩) | ⟨X, -, rfl, -, -, sX, -⟩
  · exact tc_term
  · exact Or.inr ⟨_, rfl, by rw [rmDyn_static sX.static]; exact sX⟩
  · exact Or.inr ⟨_, rfl, sX⟩

theorem denD_lower (a : Term) (v : TP L) : denD (lower a) v ↔ denD a v := by
  cases a <;> simp [lower, denD_rmDyn]

theorem pop_dyn (Y : List (Term × Term)) :
    Elixir.Map.«pop/3» (.map Y) (.atom "dynamic") (.map Y) = .ok (.tuple #[upper (.map Y), lower (.map Y)]) := by
  cases h : mapLookup Y (.atom "dynamic") <;>
    simp [Elixir.Map.«pop/3», Erlang.maps.«take/2», h, upper, lower, rmDyn]
  rw [← rmDyn, rmDyn_static h]

/-- Differences with a gradual type subtract the upper bound from the static part, and the static part from the
upper bound. -/
theorem diff_run_grad (d : Dispatcher) {a : Term} {Y : List (Term × Term)} (nY : Y ≠ [])
    (ha : a = .atom "term" ∨ ∃ X, a = .map X)
    (g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map Y) = (do
      let dp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (upper a) (lower (.map Y))
        (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
      let sp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (lower a) (upper (.map Y))
        (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
      Elixir.Module.Types.Descr.«put_dynamic/2» sp dp) := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  rcases ha with rfl | ⟨X, rfl⟩
  · cases hY : mapLookup Y (.atom "dynamic") <;> simp [hY] at g
    simp [Erlang.erlang.«==/2», nY, unfold_map, hY, Erlang.erlang.«is_map_key/2», any_key, pop_dyn]
    rfl
  · have c : Term.compare (Term.fuel (.map X) (.atom "term")) (.map X) (.atom "term") ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    have gr : ((mapLookup X (.atom "dynamic")).isSome || (mapLookup Y (.atom "dynamic")).isSome) = Bool.true := by
      rcases g with ⟨X', e, h⟩ | h
      · simp only [Term.map.injEq] at e; subst e; simp [h]
      · simp [h]
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp [hX, hY] at gr <;>
      simp [Erlang.erlang.«==/2», nY, c, unfold_map, hX, hY, Erlang.erlang.«is_map_key/2», any_key,
        pop_dyn, Lynx.Except.orElse]

theorem opt_diff_run_grad (d : Dispatcher) {a : Term} {Y : List (Term × Term)} (S : Term) (nY : Y ≠ [])
    (ha : a = .atom "term" ∨ ∃ X, a = .map X)
    (g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«opt_difference/3» d a (.map Y) S = (do
      let dp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (upper a) (lower (.map Y))
        (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-1-" 3 #[S])
      let sp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (lower a) (upper (.map Y))
        (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-2-" 3 #[S])
      Elixir.Module.Types.Descr.«put_dynamic/2» sp dp) := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  rcases ha with rfl | ⟨X, rfl⟩
  · cases hY : mapLookup Y (.atom "dynamic") <;> simp [hY] at g
    simp [Erlang.erlang.«==/2», nY, unfold_map, hY, Erlang.erlang.«is_map_key/2», any_key, pop_dyn]
    rfl
  · have c : Term.compare (Term.fuel (.map X) (.atom "term")) (.map X) (.atom "term") ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    have gr : ((mapLookup X (.atom "dynamic")).isSome || (mapLookup Y (.atom "dynamic")).isSome) = Bool.true := by
      rcases g with ⟨X', e, h⟩ | h
      · simp only [Term.map.injEq] at e; subst e; simp [h]
      · simp [h]
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp [hX, hY] at gr <;>
      simp [Erlang.erlang.«==/2», nY, c, unfold_map, hX, hY, Erlang.erlang.«is_map_key/2», any_key,
        pop_dyn, Lynx.Except.orElse]

/-- Top-level types equal by comparison hold the same points. -/
theorem tc_congr {a b : Term} (ha : TC L a) (hb : TC L b) (e : Term.compare (Term.fuel a b) a b = .eq) (v : TP L) :
    denD a v ↔ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩ <;> rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact Iff.rfl
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · simp only [denD_map, descr_congr (tks L) (tfc L) sA sB e v.1.1 v.1.2 v.2.2]

/-- Putting a dynamic part that includes the static one: a gradual type with these bounds. -/
theorem put_dyn_sem {sp dp : Term} (hs : TC L sp) (hd : TC L dp) (inv : ∀ v : TP L, denD sp v → denD dp v) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«put_dynamic/2» sp dp = .ok c ∧
      (∀ v : TP L, denD c v ↔ denD sp v) ∧ ∀ v : TP L, denD (upper c) v ↔ denD dp v := by
  rcases hs with rfl | ⟨S, rfl, sS⟩
  · exact ⟨_, GC.tc tc_term, by unfold Elixir.Module.Types.Descr.«put_dynamic/2»; rfl, fun v => Iff.rfl,
      fun v => ⟨fun _ => inv v (denD_term v), fun _ => denD_term v⟩⟩
  have tS : TC L (.map S) := Or.inr ⟨S, rfl, sS⟩
  by_cases e₁ : Term.compare (Term.fuel (.map S) dp) (.map S) dp = .eq
  · refine ⟨_, GC.tc tS, ?_, fun v => Iff.rfl, fun v => by rw [upper_tc tS]; exact tc_congr tS hd e₁ v⟩
    unfold Elixir.Module.Types.Descr.«put_dynamic/2»
    simp [Erlang.erlang.«==/2», e₁]
  by_cases e₂ : Term.compare (Term.fuel dp (.map [])) dp (.map []) = .eq
  · have none : ∀ v : TP L, ¬denD dp v := fun v h => denD_nil v ((tc_congr hd tc_nil e₂ v).mp h)
    refine ⟨_, GC.tc tc_nil, ?_, fun v => ⟨fun h => absurd h (denD_nil v), fun h => absurd (inv v h) (none v)⟩,
      fun v => ⟨fun h => absurd h (denD_nil v), fun h => absurd h (none v)⟩⟩
    unfold Elixir.Module.Types.Descr.«put_dynamic/2»
    simp [Erlang.erlang.«==/2», e₁, e₂]
  have st := sS.static
  have hD : mapLookup ((.atom "dynamic", dp) :: S) (.atom "dynamic") = some dp := by simp [mapLookup]
  have same : ∀ v : TP L, denD (.map ((.atom "dynamic", dp) :: S)) v ↔ denD (.map S) v := fun v => by
    rw [← denD_rmDyn, rmDyn_cons_dyn, rmDyn_static st]
  refine ⟨_, Or.inr ⟨_, dp, rfl, hD, hd, by rw [rmDyn_cons_dyn, rmDyn_static st]; exact sS,
    fun v h => inv v ((same v).mp h)⟩, ?_, same, fun v => by rw [upper_dyn hD]⟩
  unfold Elixir.Module.Types.Descr.«put_dynamic/2»
  simp [Erlang.erlang.«==/2», e₁, e₂, Erlang.maps.«put/3»]

/-- Differences hold the points of the first type outside the second, crossing the bounds. -/
def DSem (L : Level) (a b c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD (upper b) v) ∧
    ∀ v : TP L, denD (upper c) v ↔ denD (upper a) v ∧ ¬denD b v

theorem bare_diff_op {n : Nat} (hm : L.K + 13 ≤ n) :
    DiffOp L n (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
      (Elixir.Module.Types.Descr.«bare_difference/3» (D n)) where
  call := fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure n q v₁ v₂
  spec := fun _ _ _ fx fy =>
    let ⟨w, rw', k, sw⟩ := fieldC_diff (tks L) (tfc L) (by omega) fx fy; ⟨w, rw', fun h => (k h).1, sw⟩

theorem opt_diff_op₁ {n : Nat} (hm : L.K + 13 ≤ n) (S : List (Term × Term)) :
    DiffOp L n (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-1-" 3 #[.map S])
      (fun q x y => Elixir.Module.Types.Descr.«opt_difference/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-1-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_diff (tks L) (tfc L) (by omega) fx fy S

theorem opt_diff_op₂ {n : Nat} (hm : L.K + 13 ≤ n) (S : List (Term × Term)) :
    DiffOp L n (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-2-" 3 #[.map S])
      (fun q x y => Elixir.Module.Types.Descr.«opt_difference/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-2-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_diff (tks L) (tfc L) (by omega) fx fy S

/-- The gradual difference: the dynamic part and the static part, put together. -/
theorem diff_grad {n : Nat} {fn₁ fn₂ : Term} {f₁ f₂ : Term → Term → Term → Except Exception Term}
    (op₁ : DiffOp L n fn₁ f₁) (op₂ : DiffOp L n fn₂ f₂) {a b : Term} (ha : GC L a) (hb : GC L b) :
    ∃ c, GC L c ∧ (do
      let dp ← Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) (upper a) (lower b) fn₁
      let sp ← Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) (lower a) (upper b) fn₂
      Elixir.Module.Types.Descr.«put_dynamic/2» sp dp) = .ok c ∧ DSem L a b c := by
  obtain ⟨dp, tdp, rdp, sdp⟩ := dyn_diff_tc op₁ ha.up_tc hb.low_tc
  obtain ⟨sp, tsp, rsp, ssp⟩ := dyn_diff_tc op₂ ha.low_tc hb.up_tc
  obtain ⟨c, hc, rc, lo, up⟩ := put_dyn_sem tsp tdp fun v h => by
    rw [ssp, denD_lower] at h
    rw [sdp, denD_lower]
    exact ⟨ha.inv v h.1, fun h' => h.2 (hb.inv v h')⟩
  refine ⟨c, hc, by simp [rdp, rsp, rc], fun v => ?_, fun v => ?_⟩
  · rw [lo, ssp, denD_lower]
  · rw [up, sdp, denD_lower]

theorem diff_nil_r (d : Dispatcher) (a : Term) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map []) = .ok a := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»; simp [Erlang.erlang.«==/2»]

theorem opt_diff_nil_r (d : Dispatcher) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» d a (.map []) S = .ok a := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»; simp [Erlang.erlang.«==/2»]

theorem dsem_term_r (a : Term) : DSem L a (.atom "term") (.map []) :=
  ⟨fun v => by simp [denD_nil, upper_term, denD_term], fun v => by simp [upper_nil, denD_nil, denD_term]⟩

theorem dsem_nil_r (a : Term) : DSem L a (.map []) a :=
  ⟨fun v => by simp [denD_nil, upper_nil], fun v => by simp [denD_nil]⟩

theorem dsem_tc {a b c : Term} (ha : TC L a) (hb : TC L b) (hc : TC L c)
    (sem : ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v) : DSem L a b c :=
  ⟨by rw [upper_tc hb]; exact sem, by rw [upper_tc ha, upper_tc hc]; exact sem⟩

theorem gc_diff {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c ∧ DSem L a b c := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_nil, diff_term_right _ _, dsem_term_r _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨a, ha, diff_nil_r _ _, dsem_nil_r _⟩
  by_cases st : TC L a ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_diff st.1 st.2 (m := n + 2) (by omega)
    exact ⟨c, GC.tc hc, run, dsem_tc st.1 st.2 hc sem⟩
  have g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sY : TC L (.map Y)
    · rcases ha.shape with rfl | ⟨X, rfl⟩
      · exact absurd ⟨tc_term, sY⟩ st
      · exact Or.inl ⟨X, rfl, dyn_isSome (fun h => st ⟨h, sY⟩) ha⟩
    · exact Or.inr (dyn_isSome sY hb)
  obtain ⟨c, hc, run, sem⟩ := diff_grad (bare_diff_op (n := n) (by omega)) (bare_diff_op (n := n) (by omega)) ha hb
  exact ⟨c, hc, (diff_run_grad _ nY ha.shape g).trans run, sem⟩

theorem gc_opt_diff {a b : Term} (ha : GC L a) (hb : GC L b) (S : List (Term × Term)) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧ DSem L a b c := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_nil, difference_term_term _ _ _, dsem_term_r _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨a, ha, opt_diff_nil_r _ _ _, dsem_nil_r _⟩
  by_cases st : TC L a ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_opt_diff st.1 st.2 S (m := n + 2) (by omega)
    exact ⟨c, GC.tc hc, run, dsem_tc st.1 st.2 hc sem⟩
  have g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sY : TC L (.map Y)
    · rcases ha.shape with rfl | ⟨X, rfl⟩
      · exact absurd ⟨tc_term, sY⟩ st
      · exact Or.inl ⟨X, rfl, dyn_isSome (fun h => st ⟨h, sY⟩) ha⟩
    · exact Or.inr (dyn_isSome sY hb)
  obtain ⟨c, hc, run, sem⟩ := diff_grad (opt_diff_op₁ (n := n) (by omega) S) (opt_diff_op₂ (n := n) (by omega) S) ha hb
  exact ⟨c, hc, (opt_diff_run_grad _ _ nY ha.shape g).trans run, sem⟩

end

end Elixir.STTDescrProofsTest.Nest
