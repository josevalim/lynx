namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Subtyping and equality of gradual types are complete for both bounds. -/

section
variable {L : Level}

theorem map_get_dyn {X : List (Term × Term)} {Dx : Term} (h : mapLookup X (.atom "dynamic") = some Dx) :
    Elixir.Map.«get/2» (.map X) (.atom "dynamic") = .ok Dx := by
  simp [Elixir.Map.«get/2», Elixir.Map.«get/3», getMapKeys_single, h]

theorem tc_rmDyn {X : List (Term × Term)} (hX : GC L (.map X)) : TC L (.map (rmDyn X)) := hX.low_tc

/-- Gradual subtyping on maps: compares the bounds. -/
theorem gc_sub_maps {X Y : List (Term × Term)} (hX : GC L (.map X)) (hY : GC L (.map Y)) {m : Nat} (hm : L.K + 13 ≤ m)
    (lo : ∀ v : TP L, denD (.map X) v → denD (.map Y) v)
    (up : ∀ v : TP L, denD (upper (.map X)) v → denD (upper (.map Y)) v) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) = .ok (.atom "true") := by
  have lo' : ∀ v : TP L, denD (.map (rmDyn X)) v → denD (.map (rmDyn Y)) v := fun v h =>
    (denD_rmDyn Y v).mpr (lo v ((denD_rmDyn X v).mp h))
  cases hx : mapLookup X (.atom "dynamic") with
  | none =>
    have tX := hX.static hx
    cases hy : mapLookup Y (.atom "dynamic") with
    | none => exact tc_sub tX (hY.static hy) hm lo
    | some Dy =>
      have run := sstatic_complete tX (tc_rmDyn hY) hm fun v h => by
        have := lo' v; rw [rmDyn_static hx] at this; exact this h
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», Erlang.maps.«remove/2»]
      simpa [rmDyn] using run
  | some Dx =>
    cases hy : mapLookup Y (.atom "dynamic") with
    | none =>
      have tY := hY.static hy
      have run := sstatic_complete hX.up_tc tY hm fun v h => by
        have := up v; rw [upper_tc tY] at this; exact this h
      rw [upper_dyn hx] at run
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», map_get_dyn hx, run]
    | some Dy =>
      have tX := hX.up_tc; have tY := hY.up_tc
      rw [upper_dyn hx] at tX; rw [upper_dyn hy] at tY
      have r₁ := esub_complete tX tY hm fun v h => by
        have := up v; rw [upper_dyn hx, upper_dyn hy] at this; exact this h
      have r₂ := esub_complete (tc_rmDyn hX) (tc_rmDyn hY) hm lo'
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2»]
      unfold Elixir.Module.Types.Descr.«subtype_static?/2»
      by_cases same : compareExact (fuel (.map Y) (.map X)) (.map Y) (.map X) = .eq
      · simp [Erlang.erlang.«=:=/2», same]
      · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, hx, hy, r₁, Erlang.maps.«remove/2», Lynx.Except.andAlso]
        simpa [rmDyn] using r₂

/-- Gradual subtyping is complete for both bounds. -/
theorem gc_sub {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (lo : ∀ v : TP L, denD a v → denD b v) (up : ∀ v : TP L, denD (upper a) v → denD (upper b) v) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨T, term, sT, -, all⟩ := termT L
  have tT : GC L (.map T) := GC.tc (Or.inr ⟨T, rfl, sT⟩)
  have uT : upper (.map T) = .map T := upper_tc (Or.inr ⟨T, rfl, sT⟩)
  have left : ∃ X, GC L (.map X) ∧ (∀ v : TP L, denD a v ↔ denD (.map X) v) ∧
      (∀ v : TP L, denD (upper a) v ↔ denD (upper (.map X)) v) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) b := by
    rcases ha.shape with rfl | ⟨X, rfl⟩
    · exact ⟨T, tT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩,
        fun v => by rw [upper_term, uT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩, subtype_term_l term _ _⟩
    · exact ⟨X, ha, fun v => Iff.rfl, fun v => Iff.rfl, rfl⟩
  obtain ⟨X, hX, eX, uX, rX⟩ := left
  have right : ∃ Y, GC L (.map Y) ∧ (∀ v : TP L, denD b v ↔ denD (.map Y) v) ∧
      (∀ v : TP L, denD (upper b) v ↔ denD (upper (.map Y)) v) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) b =
        Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) := by
    rcases hb.shape with rfl | ⟨Y, rfl⟩
    · exact ⟨T, tT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩,
        fun v => by rw [upper_term, uT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩, subtype_term_r term _ _⟩
    · exact ⟨Y, hb, fun v => Iff.rfl, fun v => Iff.rfl, rfl⟩
  obtain ⟨Y, hY, eY, uY, rY⟩ := right
  rw [rX, rY]
  exact gc_sub_maps hX hY hm (fun v h => (eY v).mp (lo v ((eX v).mpr h)))
    (fun v h => (uY v).mp (up v ((uX v).mpr h)))

/-- Gradual equality is complete for both bounds. -/
theorem gc_equal {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (lo : ∀ v : TP L, denD a v ↔ denD b v) (up : ∀ v : TP L, denD (upper a) v ↔ denD (upper b) v) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  have s₁ := gc_sub ha hb hm (fun v => (lo v).mp) (fun v => (up v).mp)
  have s₂ := gc_sub hb ha hm (fun v => (lo v).mpr) (fun v => (up v).mpr)
  by_cases c : Term.compare (Term.fuel a b) a b = .eq <;>
    simp [Elixir.Module.Types.Descr.«equal?/2», s₁, s₂, Lynx.Except.orElse, Lynx.Except.andAlso,
      Erlang.erlang.«==/2», c, Term.true, Term.false]

end

end Elixir.STTDescrProofsTest.Nest
