namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Gradual top-level types: a static part and a dynamic part that includes it. -/

section
variable {L : Level}

abbrev DC (L : Level) := DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E)
abbrev FC (L : Level) := FieldC (FunA L.E) (TField L.E) (LF L.E) (MField L.E)

theorem denD_rmDyn (X : List (Term × Term)) (v : TP L) : denD (.map (rmDyn X)) v ↔ denD (.map X) v := by
  simp only [denD_map, lookup_rmDyn_name X (names_ne_dyn v.2.1)]

/-- Field operations a union merges fields with: they unite the points of their fields. -/
structure UnionOp (L : Level) (d : Dispatcher) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term) : Prop where
  call : ∀ q v₁ v₂, d.pure (.function module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂
  spec : ∀ name x y, FC L name x → FC L name y → ∃ u, f (.atom name) x y = .ok u ∧ FC L name u ∧
    ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (some u) p = (dn name (some x) p || dn name (some y) p)

theorem DC.atoms {X : List (Term × Term)} (sX : DC L X) : ∀ q, (mapLookup X q).isSome → ∃ n, q = .atom n :=
  fun q h => let ⟨n, _, e⟩ := sX.keys q h; ⟨n, e⟩

/-- Maps whose bindings other than the dynamic one are fields have atom keys. -/
theorem rmDyn_atoms {X : List (Term × Term)} (sX : DC L (rmDyn X)) : ∀ q, (mapLookup X q).isSome → ∃ n, q = .atom n := by
  intro q h
  by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
  · exact ⟨"dynamic", (compareExact_eq_atom q _).mp e⟩
  · exact sX.atoms q (by rw [lookup_rmDyn, ite_eq_right e]; exact h)

/-- Merging static types unites them. -/
theorem merge_descr {d : Dispatcher} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    {A B : List (Term × Term)} (sA : DC L A) (sB : DC L B) :
    ∃ U, Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map A) (.map B) (.function module name 3 caps) =
        .ok (.map U) ∧ DC L U ∧ ∀ v : TP L, denD (.map U) v ↔ denD (.map A) v ∨ denD (.map B) v := by
  obtain ⟨U, run, look⟩ := merge_gen d module name caps f op.call A B sB.atoms (fun q x y hx hy => by
    obtain ⟨n, -, rfl⟩ := sA.keys q (by simp [hx])
    obtain ⟨u, ru, -⟩ := op.spec n x y (sA.fields n x hx) (sB.fields n y hy)
    exact ⟨u, ru⟩)
  have keysU : ∀ q, (mapLookup U q).isSome → (mapLookup A q).isSome ∨ (mapLookup B q).isSome := by
    intro q h
    cases hB : mapLookup B q with
    | none => rw [(look q).1 hB] at h; exact Or.inl h
    | some y => exact Or.inr (by simp)
  obtain ⟨cU, sem, -⟩ := union_gen (slh := False) sA sB f
    (fun n => ⟨(look _).1, (look _).2.1, (look _).2.2⟩) keysU
    (fun n x y fx fy => let ⟨u, ru, fu, su⟩ := op.spec n x y fx fy; ⟨u, ru, fu, su, False.elim⟩)
  exact ⟨U, run, cU, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

/-- Unions of dynamic parts: top-level types merged field by field. -/
theorem dyn_union_tc {d : Dispatcher} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    {a b : Term} (ha : TC L a) (hb : TC L b) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«dynamic_union/3» d a b (.function module name 3 caps) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, by unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, by unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl, fun v => by simp [denD_term]⟩
  obtain ⟨U, run, sU, sem⟩ := merge_descr op sA sB
  refine ⟨_, Or.inr ⟨U, rfl, sU⟩, ?_, sem⟩
  unfold Elixir.Module.Types.Descr.«dynamic_union/3»
  simpa [unfold_map] using run

/-- The upper bound of a type: its dynamic part, or the type itself when it is static. -/
def upper (a : Term) : Term :=
  match a with
  | .map X => (mapLookup X (.atom "dynamic")).getD a
  | _ => a

/-- Gradual top-level types: top-level types, or maps of fields with a dynamic part, a top-level type that holds
every point of the fields, as Descr maintains. -/
def GC (L : Level) (a : Term) : Prop :=
  TC L a ∨ ∃ X Dy, a = .map X ∧ mapLookup X (.atom "dynamic") = some Dy ∧ TC L Dy ∧ DC L (rmDyn X) ∧
    ∀ v : TP L, denD a v → denD Dy v

theorem upper_tc {a : Term} (ha : TC L a) : upper a = a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · rfl
  · simp [upper, sX.static]

theorem upper_dyn {X : List (Term × Term)} {Dy : Term} (h : mapLookup X (.atom "dynamic") = some Dy) :
    upper (.map X) = Dy := by
  simp [upper, h]

theorem GC.tc {a : Term} (ha : TC L a) : GC L a := Or.inl ha

theorem GC.up_tc {a : Term} (ha : GC L a) : TC L (upper a) := by
  rcases ha with ha | ⟨X, Dy, rfl, hD, tD, -, -⟩
  · rwa [upper_tc ha]
  · rwa [upper_dyn hD]

theorem GC.inv {a : Term} (ha : GC L a) (v : TP L) (h : denD a v) : denD (upper a) v := by
  rcases ha with ha | ⟨X, Dy, rfl, hD, -, -, inv⟩
  · rwa [upper_tc ha]
  · rw [upper_dyn hD]; exact inv v h

/-- A static operand meets a gradual one as its own dynamic part. -/
def alignT (X : List (Term × Term)) : List (Term × Term) :=
  match mapLookup X (.atom "dynamic") with
  | some _ => X
  | none => (.atom "dynamic", .map X) :: X

theorem rmDyn_cons_dyn (X : List (Term × Term)) (w : Term) : rmDyn ((.atom "dynamic", w) :: X) = rmDyn X := by
  simp [rmDyn]

/-- Aligned maps of gradual types: their dynamic part is the upper bound, and their fields those of the type. -/
theorem align_gc {X : List (Term × Term)} (hX : GC L (.map X)) :
    mapLookup (alignT X) (.atom "dynamic") = some (upper (.map X)) ∧ DC L (rmDyn (alignT X)) ∧
      ∀ v : TP L, denD (.map (alignT X)) v ↔ denD (.map X) v := by
  rcases hX with (h | ⟨X', e, sX⟩) | ⟨X', Dy, e, hD, -, sX, -⟩
  · cases h
  · simp only [Term.map.injEq] at e; subst e
    have st := sX.static
    refine ⟨by rw [alignT, st, upper_tc (Or.inr ⟨X, rfl, sX⟩)]; simp [mapLookup], ?_, fun v => ?_⟩
    · rw [alignT, st]; simp only; rw [rmDyn_cons_dyn, rmDyn_static st]; exact sX
    · rw [alignT, st]; simp only
      rw [← denD_rmDyn, rmDyn_cons_dyn, denD_rmDyn]
  · simp only [Term.map.injEq] at e; subst e
    refine ⟨by simp [alignT, hD, upper], by simpa [alignT, hD] using sX, fun v => by simp [alignT, hD]⟩

/-- The fields of `U` merge those of `L` and `R` with `f`. -/
def MergeL (f : Term → Term → Term → Except Exception Term) (L R U : List (Term × Term)) : Prop :=
  (∀ name, (mapLookup R (.atom name) = none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
    (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = none → mapLookup U (.atom name) = some y) ∧
    (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok u →
      mapLookup U (.atom name) = some u)) ∧
  ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome

/-- The fields of `I` intersect those of `L` and `R` with `f`. -/
def InterL (f : Term → Term → Term → Except Exception Term) (L R I : List (Term × Term)) : Prop :=
  (∀ name, (mapLookup L (.atom name) = none → mapLookup I (.atom name) = none) ∧
    (mapLookup R (.atom name) = none → mapLookup I (.atom name) = none) ∧
    (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok w →
      mapLookup I (.atom name) = keptO name w)) ∧
  ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome

theorem rmDyn_alignT (X : List (Term × Term)) : rmDyn (alignT X) = rmDyn X := by
  unfold alignT
  cases mapLookup X (.atom "dynamic") <;> simp [rmDyn_cons_dyn]

/-- Merging maps with dynamic parts merges their fields and their dynamic parts. -/
theorem merge_grad {d : Dispatcher} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    {X Y : List (Term × Term)} {Dx Dy Du : Term} (hX : mapLookup X (.atom "dynamic") = some Dx)
    (hY : mapLookup Y (.atom "dynamic") = some Dy) (sX : DC L (rmDyn X)) (sY : DC L (rmDyn Y))
    (du : f (.atom "dynamic") Dx Dy = .ok Du) :
    ∃ U, Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map X) (.map Y) (.function module name 3 caps) =
        .ok (.map U) ∧ mapLookup U (.atom "dynamic") = some Du ∧ DC L (rmDyn U) ∧
        (∀ v : TP L, denD (.map U) v ↔ denD (.map X) v ∨ denD (.map Y) v) ∧ MergeL f (rmDyn X) (rmDyn Y) (rmDyn U) := by
  obtain ⟨U, run, look⟩ := merge_gen d module name caps f op.call X Y (rmDyn_atoms sY) (fun q x y hx hy => by
    by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
    · obtain rfl := (compareExact_eq_atom q _).mp e
      rw [hX] at hx; rw [hY] at hy; cases hx; cases hy
      exact ⟨Du, du⟩
    · have hx' : mapLookup (rmDyn X) q = some x := by rw [lookup_rmDyn, ite_eq_right e]; exact hx
      have hy' : mapLookup (rmDyn Y) q = some y := by rw [lookup_rmDyn, ite_eq_right e]; exact hy
      obtain ⟨n, -, rfl⟩ := sX.keys q (by simp [hx'])
      obtain ⟨u, ru, -⟩ := op.spec n x y (sX.fields n x hx') (sY.fields n y hy')
      exact ⟨u, ru⟩)
  have lookR : ∀ q, (mapLookup (rmDyn Y) q = none → mapLookup (rmDyn U) q = mapLookup (rmDyn X) q) ∧
      (∀ y, mapLookup (rmDyn Y) q = some y → mapLookup (rmDyn X) q = none → mapLookup (rmDyn U) q = some y) ∧
      (∀ x y u, mapLookup (rmDyn X) q = some x → mapLookup (rmDyn Y) q = some y → f q x y = .ok u →
        mapLookup (rmDyn U) q = some u) := by
    intro q
    simp only [lookup_rmDyn]
    by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
    · simp [e]
    · simp only [e, ite_false]; exact look q
  have keysU : ∀ q, (mapLookup (rmDyn U) q).isSome → (mapLookup (rmDyn X) q).isSome ∨ (mapLookup (rmDyn Y) q).isSome := by
    intro q h
    cases hB : mapLookup (rmDyn Y) q with
    | none => rw [(lookR q).1 hB] at h; exact Or.inl h
    | some y => exact Or.inr (by simp)
  obtain ⟨cU, sem, -⟩ := union_gen (slh := False) sX sY f
    (fun n => ⟨(lookR _).1, (lookR _).2.1, (lookR _).2.2⟩) keysU
    (fun n x y fx fy => let ⟨u, ru, fu, su⟩ := op.spec n x y fx fy; ⟨u, ru, fu, su, False.elim⟩)
  refine ⟨U, run, (look _).2.2 Dx Dy Du hX hY du, cU, fun v => ?_, fun n => ⟨(lookR _).1, (lookR _).2.1, (lookR _).2.2⟩,
    keysU⟩
  rw [← denD_rmDyn U, ← denD_rmDyn X, ← denD_rmDyn Y]
  simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]

/-- Merging aligned gradual types unites their fields and their upper bounds. -/
theorem merge_aligned {d d' : Dispatcher} {module name module' name' : String} {caps caps' : Array Term}
    {f f' : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    (op' : UnionOp L d' module' name' caps' f')
    (dyn : ∀ x y, f (.atom "dynamic") x y =
      Elixir.Module.Types.Descr.«dynamic_union/3» d' x y (.function module' name' 3 caps'))
    {X Y : List (Term × Term)} (hX : GC L (.map X)) (hY : GC L (.map Y)) :
    ∃ c, GC L c ∧
      Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map (alignT X)) (.map (alignT Y))
        (.function module name 3 caps) = .ok c ∧
      (∀ v : TP L, denD c v ↔ denD (.map X) v ∨ denD (.map Y) v) ∧
      (∀ v : TP L, denD (upper c) v ↔ denD (upper (.map X)) v ∨ denD (upper (.map Y)) v) ∧
      ∃ U, c = .map U ∧ MergeL f (rmDyn X) (rmDyn Y) (rmDyn U) ∧
        Elixir.Module.Types.Descr.«dynamic_union/3» d' (upper (.map X)) (upper (.map Y))
          (.function module' name' 3 caps') = .ok (upper c) := by
  obtain ⟨dX, sX, eX⟩ := align_gc hX
  obtain ⟨dY, sY, eY⟩ := align_gc hY
  obtain ⟨Du, tu, ru, su⟩ := dyn_union_tc op' hX.up_tc hY.up_tc
  obtain ⟨U, run, dU, sU, sem, look⟩ := merge_grad op dX dY sX sY (by rw [dyn]; exact ru)
  rw [rmDyn_alignT, rmDyn_alignT] at look
  have lo : ∀ v : TP L, denD (.map U) v ↔ denD (.map X) v ∨ denD (.map Y) v := fun v => by
    rw [sem, eX, eY]
  refine ⟨_, Or.inr ⟨U, Du, rfl, dU, tu, sU, fun v h => ?_⟩, run, lo, fun v => by rw [upper_dyn dU, su],
    U, rfl, look, by rw [upper_dyn dU]; exact ru⟩
  rw [su]
  rcases (lo v).mp h with h | h
  · exact Or.inl (hX.inv v h)
  · exact Or.inr (hY.inv v h)

end

end Elixir.STTDescrProofsTest.Nest
