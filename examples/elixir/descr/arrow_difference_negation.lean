namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Differences and negations of static types whose function types are arrows. -/

section
variable {t : Term} {n : Nat}

/-- The static types of the laws are element types of the next level. -/
theorem arrows_static_ok {a : Term} (h : «arrows_static?/2» a (.tuple #[.integer n, t]) = .ok (.atom "true")) :
    DE (level t n).E a := by
  unfold «arrows_static?/2» at h
  simp only [Lynx.Except.andAlso_eq_true] at h
  exact arrows_de (opt_negatable_tc t n a (by simpa [Term.true] using h.1)) h.2

/-- Gradual types whose parts' function types are arrows between nested types, the dynamic part including the
static one. -/
theorem arrows_gradual_gc {m : Nat} (hm : (level t n).K + 15 ≤ m) (descr : Term)
    (h : «arrows_gradual?/2» (D m) descr (.tuple #[.integer n, t]) = .ok Term.true) : GC (level t n) descr := by
  have static : «arrows_static?/2» descr (.tuple #[.integer n, t]) = .ok Term.true → GC (level t n) descr := fun h =>
    GC.tc (arrows_static_ok (by simpa [Term.true] using h))
  unfold «arrows_gradual?/2» at h
  cases descr with
  | map X =>
    cases hD : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, hD] at h; exact static h
    | some Dy =>
      simp only [getMapKeys_single, hD, Option.toList, Erlang.maps.«remove/2», Lynx.Except.ok_bind, Term.true,
        Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨hS, hDy⟩, hI⟩ := h
      have tS : TC (level t n) (.map (rmDyn X)) := arrows_static_ok hS
      have tD : TC (level t n) Dy := arrows_static_ok hDy
      have sS : DC (level t n) (rmDyn X) := by
        rcases tS with e | ⟨S, e, sS⟩
        · cases e
        · simp only [Term.map.injEq] at e; rw [e]; exact sS
      obtain ⟨c, tc, run, sem⟩ := tc_diff tS tD (m := m) hm
      rw [← rmDyn, run, Lynx.Except.ok_bind] at hI
      have none : ∀ v : TP (level t n), ¬denD c v := by
        rcases tc with rfl | ⟨C, rfl, sC⟩
        · simp [Elixir.Module.Types.Descr.«empty?/1»] at hI
        · exact tc_empty_sound sC (by omega) hI
      refine Or.inr ⟨X, Dy, rfl, hD, tD, sS, fun v hv => ?_⟩
      exact Classical.byContradiction fun hn => none v ((sem v).mpr ⟨(denD_rmDyn X v).mpr hv, hn⟩)
  | _ => simp at h; exact static h

/-- Gradual types whose parts' function types are arrows between nested types: the parts are element types of
the next level. -/
theorem arrows_gradual_ok {m : Nat} (hm : (level t n).K + 15 ≤ m) {a : Term}
    (h : «arrows_gradual?/2» (D m) a (.tuple #[.integer n, t]) = .ok (.atom "true")) :
    GC (level t n) a ∧ DE (level t n).E (lower a) ∧ DE (level t n).E (upper a) :=
  let ga := arrows_gradual_gc hm a h
  ⟨ga, ga.low_tc, ga.up_tc⟩

theorem denN_nil (v : PN t n) : ¬denD (.map []) v := by simp [denD_map, mapLookup, dn_none]

/-- Negations of element types of the next level. -/
theorem next_neg {a : Term} (ha : DE (level t n).E a) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ c, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c ∧ DE (level t n).E c ∧
      ∀ v : PN t n, denD c v ↔ ¬denD a v := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_negation/1»], (ef_next t n).none,
      fun v => by simp [denN_nil, denD_term]⟩
  obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).diff (ef_next t n).term (Or.inr ⟨X, rfl, sX⟩)
  exact ⟨c, by simpa [Elixir.Module.Types.Descr.«bare_negation/1», Elixir.Module.Types.Descr.«term/0»] using run m hm,
    dc, fun v => by rw [sem]; simp [denD_term]⟩

/-- Equality of element types of the next level is exact. -/
theorem next_eq_true {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) (h : ∀ v : PN t n, denD a v ↔ denD b v) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨ga, la, ua⟩ := de_gd ha
  obtain ⟨gb, lb, ub⟩ := de_gd hb
  exact gd_eq_true ga gb hm (fun v => by rw [la, lb]; exact h v) (fun v => by rw [ua, ub]; exact h v)

/-- A static type is a subtype of another exactly when their difference is empty. -/
theorem next_sub_diff {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) c = .ok (boolAtom s) := by
  obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).diff ha hb
  refine ⟨c, _, run m hm, next_sub ha hb hm, ?_⟩
  rw [next_empty dc hm]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ⟨fun h v h₁ => ?_, fun h v hc => ?_⟩)
  · exact Classical.byContradiction fun h₂ => h v ((sem v).mpr ⟨h₁, h₂⟩)
  · exact ((sem v).mp hc).2 (h v ((sem v).mp hc).1)

end

end Elixir.STTDescrProofsTest.Nest
