namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Intersections of gradual types. -/

section
variable {L : Level}

/-- Field operations an intersection combines fields with: they keep the common points of their fields. -/
structure InterOp (L : Level) (n : Nat) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term) : Prop where
  call : ∀ q v₁ v₂, (D (n + 1)).pure (.function module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂
  spec : ∀ name x y, FC L name x → FC L name y → ∃ w, f (.atom name) x y = .ok w ∧
    (kept (.atom name, w) = Bool.true → FC L name w) ∧
    ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)

/-- Intersecting static types keeps their common points. -/
theorem inter_descr {n : Nat} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : InterOp L n module name caps f)
    {A B : List (Term × Term)} (sA : DC L A) (sB : DC L B) :
    ∃ I, Elixir.Module.Types.Descr.«symmetrical_intersection/3» (D (n + 1)) (.map A) (.map B)
        (.function module name 3 caps) = .ok (.map I) ∧ DC L I ∧
      ∀ v : TP L, denD (.map I) v ↔ denD (.map A) v ∧ denD (.map B) v := by
  obtain ⟨I, run, look⟩ := intersect_gen n module name caps f op.call A B sA.atoms (fun q x y hx hy => by
    obtain ⟨k, -, rfl⟩ := sA.keys q (by simp [hx])
    obtain ⟨w, rw', -⟩ := op.spec k x y (sA.fields k x hx) (sB.fields k y hy)
    exact ⟨w, rw'⟩)
  have keysI : ∀ q, (mapLookup I q).isSome → (mapLookup A q).isSome := by
    intro q h
    cases hA : mapLookup A q with
    | none => rw [(look q).1 hA] at h; cases h
    | some _ => rfl
  obtain ⟨cI, sem, -⟩ := inter_gen (slh := False) sA sB f
    (fun k => ⟨(look _).1, (look _).2.1, fun x y w hx hy rw' => (look _).2.2 x y w hx hy rw'⟩) keysI
    (fun k x y fx fy => let ⟨w, rw', kw, sw⟩ := op.spec k x y fx fy; ⟨w, rw', fun h => ⟨kw h, False.elim⟩, sw⟩)
  exact ⟨I, run, cI, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

/-- Intersections of dynamic parts. -/
theorem dyn_inter_tc {n : Nat} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : InterOp L n module name caps f)
    {a b : Term} (ha : TC L a) (hb : TC L b) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«dynamic_intersection/3» (D (n + 1)) a b (.function module name 3 caps) =
      .ok c ∧ ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, by unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, by unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl,
      fun v => by simp [denD_term]⟩
  obtain ⟨I, run, sI, sem⟩ := inter_descr op sA sB
  refine ⟨_, Or.inr ⟨I, rfl, sI⟩, ?_, sem⟩
  unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»
  simpa [unfold_map] using run

/-- The dynamic field of an intersection: dropped when empty. -/
def dynZero : Term → Term
  | .map [] => .integer 0
  | c => c

theorem bare_inter_dyn (d : Dispatcher) {x y c : Term}
    (run : Elixir.Module.Types.Descr.«dynamic_intersection/3» d x y
      (.function "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) = .ok c) (hc : TC L c) :
    Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "dynamic") x y = .ok (dynZero c) := by
  unfold Elixir.Module.Types.Descr.«bare_intersection/3»
  rcases hc with rfl | ⟨C, rfl, -⟩
  · have c : Term.compare (Term.fuel (.atom "term") (.map [])) (.atom "term") (.map []) ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    simp [run, Erlang.erlang.«==/2», dynZero, c]
  · cases C <;> simp [run, Erlang.erlang.«==/2», dynZero]

theorem opt_inter_dyn (d : Dispatcher) {x y c S : Term}
    (run : Elixir.Module.Types.Descr.«dynamic_intersection/3» d x y
      (.function "Elixir.Module.Types.Descr" "-opt_intersection/4-fun-0-" 3 #[S]) = .ok c) (hc : TC L c) :
    Elixir.Module.Types.Descr.«opt_intersection/4» d (.atom "dynamic") x y S = .ok (dynZero c) := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/4»
  rcases hc with rfl | ⟨C, rfl, -⟩
  · have c : Term.compare (Term.fuel (.atom "term") (.map [])) (.atom "term") (.map []) ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    simp [run, Erlang.erlang.«==/2», dynZero, c]
  · cases C <;> simp [run, Erlang.erlang.«==/2», dynZero]

/-- Intersections hold the common points of the types, at both bounds. -/
def ISem (L : Level) (a b c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ denD a v ∧ denD b v) ∧ ∀ v : TP L, denD (upper c) v ↔ denD (upper a) v ∧ denD (upper b) v

/-- Intersecting aligned gradual types intersects their fields and their upper bounds. When the upper bounds do not
meet, the dynamic part is dropped, and so are the points of the fields, which the upper bounds include. -/
theorem inter_aligned {n : Nat} {module name module' name' : String} {caps caps' : Array Term}
    {f f' : Term → Term → Term → Except Exception Term} (op : InterOp L (n + 1) module name caps f)
    (op' : InterOp L n module' name' caps' f')
    (dyn : ∀ x y c, Elixir.Module.Types.Descr.«dynamic_intersection/3» (D (n + 1)) x y
      (.function module' name' 3 caps') = .ok c → TC L c → f (.atom "dynamic") x y = .ok (dynZero c))
    {X Y : List (Term × Term)} (hX : GC L (.map X)) (hY : GC L (.map Y)) :
    ∃ c, GC L c ∧
      Elixir.Module.Types.Descr.«symmetrical_intersection/3» (D (n + 2)) (.map (alignT X)) (.map (alignT Y))
        (.function module name 3 caps) = .ok c ∧ ISem L (.map X) (.map Y) c ∧
      ∃ I, c = .map I ∧ InterL f (rmDyn X) (rmDyn Y) (rmDyn I) ∧
        ((mapLookup I (.atom "dynamic") = none ∧ ∀ v : TP L, ¬denD (upper c) v) ∨
          Elixir.Module.Types.Descr.«dynamic_intersection/3» (D (n + 1))
            (upper (.map X)) (upper (.map Y)) (.function module' name' 3 caps') = .ok (upper c)) := by
  obtain ⟨dX, sX, eX⟩ := align_gc hX
  obtain ⟨dY, sY, eY⟩ := align_gc hY
  obtain ⟨Di, ti, ri, si⟩ := dyn_inter_tc op' hX.up_tc hY.up_tc
  have rD := dyn _ _ _ ri ti
  obtain ⟨I, run, look⟩ := intersect_gen (n + 1) module name caps f op.call (alignT X) (alignT Y)
    (rmDyn_atoms sX) (fun q x y hx hy => by
      by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
      · obtain rfl := (compareExact_eq_atom q _).mp e
        rw [dX] at hx; rw [dY] at hy; cases hx; cases hy
        exact ⟨_, rD⟩
      · have hx' : mapLookup (rmDyn (alignT X)) q = some x := by rw [lookup_rmDyn, ite_eq_right e]; exact hx
        have hy' : mapLookup (rmDyn (alignT Y)) q = some y := by rw [lookup_rmDyn, ite_eq_right e]; exact hy
        obtain ⟨k, -, rfl⟩ := sX.keys q (by simp [hx'])
        obtain ⟨w, rw', -⟩ := op.spec k x y (sX.fields k x hx') (sY.fields k y hy')
        exact ⟨w, rw'⟩)
  have lookR : ∀ k, (mapLookup (rmDyn (alignT X)) (.atom k) = none → mapLookup (rmDyn I) (.atom k) = none) ∧
      (mapLookup (rmDyn (alignT Y)) (.atom k) = none → mapLookup (rmDyn I) (.atom k) = none) ∧
      (∀ x y w, mapLookup (rmDyn (alignT X)) (.atom k) = some x → mapLookup (rmDyn (alignT Y)) (.atom k) = some y →
        f (.atom k) x y = .ok w → mapLookup (rmDyn I) (.atom k) = keptO k w) := by
    intro k
    simp only [lookup_rmDyn]
    by_cases e : compareExact (fuel (.atom k) (.atom "dynamic")) (.atom k) (.atom "dynamic") = .eq
    · simp [e]
    · simp only [e, ite_false]; exact ⟨(look _).1, (look _).2.1, fun x y w hx hy rw' => (look _).2.2 x y w hx hy rw'⟩
  have keysI : ∀ q, (mapLookup (rmDyn I) q).isSome → (mapLookup (rmDyn (alignT X)) q).isSome := by
    intro q h
    simp only [lookup_rmDyn] at h ⊢
    by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
    · simp [e] at h
    · simp only [e, ite_false] at h ⊢
      cases hA : mapLookup (alignT X) q with
      | none => rw [(look q).1 hA] at h; cases h
      | some _ => rfl
  have interL : InterL f (rmDyn X) (rmDyn Y) (rmDyn I) := by
    rw [← rmDyn_alignT X, ← rmDyn_alignT Y]; exact ⟨lookR, keysI⟩
  obtain ⟨cI, sem, -⟩ := inter_gen (slh := False) sX sY f lookR keysI
    (fun k x y fx fy => let ⟨w, rw', kw, sw⟩ := op.spec k x y fx fy; ⟨w, rw', fun h => ⟨kw h, False.elim⟩, sw⟩)
  have lo : ∀ v : TP L, denD (.map I) v ↔ denD (.map X) v ∧ denD (.map Y) v := fun v => by
    rw [← denD_rmDyn I, ← eX, ← eY, ← denD_rmDyn (alignT X), ← denD_rmDyn (alignT Y)]
    simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]
  have dI := (look _).2.2 _ _ _ dX dY rD
  -- The upper bounds meet unless their intersection is the empty map.
  by_cases z : Di = .map []
  · subst z
    have none : mapLookup I (.atom "dynamic") = none := by rw [dI]; simp [dynZero, kept]
    have tI : TC L (.map I) := Or.inr ⟨I, rfl, by rw [← rmDyn_static none]; exact cI⟩
    have empty : ∀ v : TP L, ¬(denD (upper (.map X)) v ∧ denD (upper (.map Y)) v) := fun v h =>
      denD_nil v ((si v).mpr h)
    refine ⟨_, GC.tc tI, run, ⟨lo, fun v => ?_⟩, I, rfl, interL, Or.inl ⟨none, fun v h => ?_⟩⟩
    · rw [upper_tc tI, lo]
      exact ⟨fun h => absurd ⟨hX.inv v h.1, hY.inv v h.2⟩ (empty v), fun h => absurd h (empty v)⟩
    · rw [upper_tc tI, lo] at h
      exact empty v ⟨hX.inv v h.1, hY.inv v h.2⟩
  · have kD : dynZero Di = Di := by
      rcases ti with rfl | ⟨C, rfl, -⟩
      · rfl
      · cases C
        · exact absurd rfl z
        · rfl
    have keep : kept (.atom "dynamic", Di) = Bool.true := by
      rcases ti with rfl | ⟨C, rfl, -⟩
      · simp [kept]
      · simp [kept]
    have hD : mapLookup I (.atom "dynamic") = some Di := by rw [dI, kD]; simp [keep]
    refine ⟨_, Or.inr ⟨I, Di, rfl, hD, ti, cI, fun v h => ?_⟩, run, ⟨lo, fun v => by rw [upper_dyn hD, si]⟩,
      I, rfl, interL, Or.inr (by rw [upper_dyn hD]; exact ri)⟩
    rw [si]
    obtain ⟨h₁, h₂⟩ := (lo v).mp h
    exact ⟨hX.inv v h₁, hY.inv v h₂⟩

theorem bare_inter_op {n : Nat} (hm : L.K + 12 ≤ n) :
    InterOp L n "Elixir.Module.Types.Descr" "bare_intersection" #[]
      (Elixir.Module.Types.Descr.«bare_intersection/3» (D n)) where
  call := fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure n q v₁ v₂
  spec := fun _ _ _ fx fy =>
    let ⟨w, rw', k, sw⟩ := fieldC_inter (tks L) (tfc L) (by omega) fx fy; ⟨w, rw', fun h => (k h).1, sw⟩

theorem opt_inter_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    InterOp L n "Elixir.Module.Types.Descr" "-opt_intersection/3-anonymous-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_intersection/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_intersection/3-anonymous-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_inter (tks L) (tfc L) (by omega) fx fy S

theorem opt_inter_dyn_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    InterOp L n "Elixir.Module.Types.Descr" "-opt_intersection/4-fun-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_intersection/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_intersection/4-fun-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_inter (tks L) (tfc L) (by omega) fx fy S

theorem inter_run_grad (d : Dispatcher) {X Y : List (Term × Term)}
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«bare_intersection/2» d (.map X) (.map Y) =
      Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map (alignT X)) (.map (alignT Y))
        (.function "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) := by
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, hX, hY, Erlang.maps.«put/3», alignT]

theorem opt_inter_run_grad (d : Dispatcher) {X Y : List (Term × Term)} (S : Term)
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«opt_intersection/3» d (.map X) (.map Y) S =
      Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map (alignT X)) (.map (alignT Y))
        (.function "Elixir.Module.Types.Descr" "-opt_intersection/3-anonymous-0-" 3 #[S]) := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/3»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, hX, hY, Erlang.maps.«put/3», alignT]

theorem isem_term_l (a : Term) : ISem L (.atom "term") a a :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem isem_term_r (a : Term) : ISem L a (.atom "term") a :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem isem_tc {a b c : Term} (ha : TC L a) (hb : TC L b) (hc : TC L c)
    (sem : ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v) : ISem L a b c :=
  ⟨sem, by rw [upper_tc ha, upper_tc hb, upper_tc hc]; exact sem⟩

/-- Intersections of the dynamic parts of gradual types intersect them as static types. -/
theorem dyn_inter_bare (d : Dispatcher) {a b : Term} (ha : TC L a) (hb : TC L b) :
    Elixir.Module.Types.Descr.«dynamic_intersection/3» d a b
      (.function "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) =
        Elixir.Module.Types.Descr.«bare_intersection/2» d a b := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [inter_term_left]; unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [inter_term_right]; unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl
  unfold Elixir.Module.Types.Descr.«dynamic_intersection/3» Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, sA.static, sB.static]

/-- Intersections of gradual types, whose upper bound is empty or the intersection of the upper bounds. -/
theorem gc_inter {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧ ISem L a b c ∧
      ((∀ v : TP L, ¬denD (upper c) v) ∨ ∃ j, m ≤ j + 1 ∧
        Elixir.Module.Types.Descr.«bare_intersection/2» (D j) (upper a) (upper b) = .ok (upper c)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, hb, inter_term_left _ _, isem_term_l _, Or.inr ⟨k + 2, by omega, by rw [upper_term]; exact inter_term_left _ _⟩⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, ha, inter_term_right _ _, isem_term_r _, Or.inr ⟨k + 2, by omega, by rw [upper_term]; exact inter_term_right _ _⟩⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_inter st.1 st.2 (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, isem_tc st.1 st.2 hc sem,
      Or.inr ⟨k + 2, by omega, by rw [upper_tc st.1, upper_tc st.2, upper_tc hc]; exact run⟩⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, sem, up⟩ := inter_aligned (bare_inter_op (n := k + 1) (by omega))
    (bare_inter_op (n := k) (by omega)) (fun _ _ _ r t => bare_inter_dyn _ r t) ha hb
  obtain ⟨I, rfl, -, up⟩ := up
  refine ⟨_, hc, (inter_run_grad _ g).trans run, sem, ?_⟩
  rcases up with ⟨-, up⟩ | up
  · exact Or.inl up
  · exact Or.inr ⟨k + 1, by omega, by rw [← dyn_inter_bare _ ha.up_tc hb.up_tc]; exact up⟩

theorem gc_opt_inter {a b : Term} (ha : GC L a) (hb : GC L b) (S : List (Term × Term)) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧ ISem L a b c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, hb, opt_inter_term_l _ _ _, isem_term_l _⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, ha, opt_inter_term_r _ _ _, isem_term_r _⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_opt_inter st.1 st.2 S (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, isem_tc st.1 st.2 hc sem⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, sem, -⟩ := inter_aligned (opt_inter_op (n := k + 1) (by omega) S)
    (opt_inter_dyn_op (n := k) (by omega) S) (fun _ _ _ r t => opt_inter_dyn _ r t) ha hb
  exact ⟨c, hc, (opt_inter_run_grad _ _ g).trans run, sem⟩

end

end Elixir.STTDescrProofsTest.Nest
