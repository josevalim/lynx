namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! A gradual type meets its negation only in its dynamic part, which `lower_bound/1` removes, and united with its
negation it covers every value in its dynamic part, which `upper_bound/1` returns. -/

theorem lower_bound_run {d : Dispatcher} {a : Term} (h : a = .atom "term" ∨ ∃ X, a = .map X) :
    Elixir.Module.Types.Descr.«lower_bound/1» d a = .ok (lower a) := by
  rcases h with rfl | ⟨X, rfl⟩
  · unfold Elixir.Module.Types.Descr.«lower_bound/1»; rfl
  · unfold Elixir.Module.Types.Descr.«lower_bound/1»
    simp [Erlang.maps.«remove/2», lower, rmDyn]

/-- Types whose dynamic part, if any, is the top type or a map. -/
def UB (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ ∀ Dy, mapLookup X (.atom "dynamic") = some Dy → Dy = .atom "term" ∨ ∃ Y, Dy = .map Y

theorem upper_bound_run {d : Dispatcher} {a : Term} (h : UB a) :
    Elixir.Module.Types.Descr.«upper_bound/1» d a = .ok (upper a) := by
  rcases h with rfl | ⟨X, rfl, hd⟩
  · unfold Elixir.Module.Types.Descr.«upper_bound/1»; rfl
  · unfold Elixir.Module.Types.Descr.«upper_bound/1»
    cases e : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, e, upper]
    | some Dy =>
      rcases hd Dy e with rfl | ⟨Y, rfl⟩ <;> simp [getMapKeys_single, e, upper]

@[simp] theorem upper_bound_term (d : Dispatcher) :
    Elixir.Module.Types.Descr.«upper_bound/1» d (.atom "term") = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«upper_bound/1»; rfl

theorem upper_bound_static {d : Dispatcher} {X : List (Term × Term)} (h : mapLookup X (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«upper_bound/1» d (.map X) = .ok (.map X) := by
  rw [upper_bound_run (Or.inr ⟨X, rfl, fun Dy e => by rw [h] at e; cases e⟩)]
  simp [upper, h]

section
variable {L : Level} {m : Nat}

theorem GC.ub {a : Term} (ha : GC L a) : UB a := by
  rcases ha with (h | ⟨X, rfl, sX⟩) | ⟨X, Dy, rfl, e, tc, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨X, rfl, fun Dy e' => by rw [sX.static] at e'; cases e'⟩
  · refine Or.inr ⟨X, rfl, fun Dy' e' => ?_⟩
    rw [e] at e'; cases e'
    rcases tc with h | ⟨Y, rfl, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨Y, rfl⟩

theorem gd_inter_neg_lower {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n i, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a n = .ok i ∧
      Elixir.Module.Types.Descr.«lower_bound/1» (D m) i = .ok (lower i) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) (lower i) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_neg ha hm
  obtain ⟨i, hi, ri, si, -⟩ := gc_inter ha hn (m := m) (by omega)
  exact ⟨n, i, rn, ri, lower_bound_run hi.shape, tc_empty hi.low_tc (by omega) fun v h => by
    obtain ⟨h₁, h₂⟩ := (si.1 v).mp ((denD_lower i v).mp h)
    exact (sn.1 v).mp h₂ (ha.inv v h₁)⟩

theorem gd_opt_inter_neg_lower {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n i, Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a n = .ok i ∧
      Elixir.Module.Types.Descr.«lower_bound/1» (D m) i = .ok (lower i) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) (lower i) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_opt_neg ha hm
  obtain ⟨i, hi, ri, si⟩ := gc_opt_inter2 ha hn (m := m) (by omega)
  exact ⟨n, i, rn, ri, lower_bound_run hi.shape, tc_empty hi.low_tc (by omega) fun v h => by
    obtain ⟨h₁, h₂⟩ := (si.1 v).mp ((denD_lower i v).mp h)
    exact (sn.1 v).mp h₂ (ha.inv v h₁)⟩

theorem gd_union_neg_upper {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n u, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«bare_union/2» (D m) a n = .ok u ∧
      Elixir.Module.Types.Descr.«upper_bound/1» (D m) u = .ok (upper u) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.atom "term") (upper u) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_neg ha hm
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hn (m := m) (by omega)
  refine ⟨n, u, rn, ru, upper_bound_run hu.ub, tc_sub tc_term hu.up_tc (by omega) fun v _ => (su.2 v).mpr ?_⟩
  by_cases h : denD a v
  · exact Or.inl (ha.inv v h)
  · exact Or.inr ((sn.2 v).mpr h)

theorem gd_opt_union_neg_upper {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n u, Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D m) a n = .ok u ∧
      Elixir.Module.Types.Descr.«upper_bound/1» (D m) u = .ok (upper u) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.atom "term") (upper u) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_opt_neg ha hm
  obtain ⟨u, hu, ru, su⟩ := gc_opt_union2 ha hn (m := m) (by omega)
  refine ⟨n, u, rn, ru, upper_bound_run hu.ub, tc_sub tc_term hu.up_tc (by omega) fun v _ => (su.2 v).mpr ?_⟩
  by_cases h : denD a v
  · exact Or.inl (ha.inv v h)
  · exact Or.inr ((sn.2 v).mpr h)

theorem gd_de_morgan_union {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ u x nl nr y, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D m) u = .ok x ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok nl ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D m) b = .ok nr ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) nl nr = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb (m := m) (by omega)
  obtain ⟨x, hx, rx, sx⟩ := gc_neg hu hm
  obtain ⟨nl, hnl, rnl, snl⟩ := gc_neg ha hm
  obtain ⟨nr, hnr, rnr, snr⟩ := gc_neg hb hm
  obtain ⟨y, hy, ry, sy, -⟩ := gc_inter hnl hnr (m := m) (by omega)
  exact ⟨u, x, nl, nr, y, ru, rx, rnl, rnr, ry, gc_equal hx hy (by omega)
    (fun v => by rw [sx.1, su.2, sy.1, snl.1, snr.1]; exact not_or)
    (fun v => by rw [sx.2, su.1, sy.2, snl.2, snr.2]; exact not_or)⟩

end

end Elixir.STTDescrProofsTest.Nest
