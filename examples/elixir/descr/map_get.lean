namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- `map_get/2` on static types of the next level, with keys that split into static keys: types holding only maps give
the union of the values their maps hold at the selected keys, or `:error` when there are none, and others `:badmap`. -/
theorem get_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {rs : List Term} {neg : Term}
    {ds : List Term} (hs : SplitOk rs neg ds) {key : Term} {m : Nat} (hm : (level t n).K + 25 ≤ m)
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok (splitT rs neg ds)) :
    ∃ res, Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) key = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        (res = .atom "error" ∧ MOnly t n X ∧ ∀ w, MT t n X w → ∀ κ, SplitKey rs neg ds κ → w κ = none) ∨
        ∃ T, res = .tuple #[.atom "ok", T] ∧ (level t n).E T ∧ MOnly t n X ∧ (∃ x, (level t n).den T x) ∧
          ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ ∃ κ, SplitKey rs neg ds κ ∧ w κ = some x) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_get/2».eq_def]
  simp only [hk, Lynx.Except.ok_bind, Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
      (.function "Elixir.Module.Types.Descr" "-map_get/2-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get/2-fun-0-/1».pure]
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1»]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 4) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨T, rfl, hT, ⟨w₀, hw₀⟩, sT⟩⟩ := mstatic_get (level t n).ef (n := k) (by omega) hb fb hs
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      have ok : MOnly t n X := only.mpr ⟨restE, w₀, hw₀⟩
      obtain ⟨eb, reb, seb⟩ := (level t n).ef.empty_pub hT
      cases eb
      · refine ⟨_, ?_, Or.inr (Or.inr ⟨T, rfl, hT, ok, Classical.byContradiction fun h => ?_, fun x => ?_⟩)⟩
        · simp [key, mo, run, Lynx.Except.andAlso, reb (k + 4) (by omega), Lynx.Term.isMember,
            boolAtom]
        · exact absurd (seb.mpr fun x hx => h ⟨x, hx⟩) (by simp)
        · rw [sT]
          exact ⟨fun ⟨w, hw, h⟩ => ⟨w, (mt w).mpr hw, h⟩, fun ⟨w, hw, h⟩ => ⟨w, (mt w).mp hw, h⟩⟩
      · refine ⟨.atom "error", ?_, Or.inr (Or.inl ⟨rfl, ok, fun w hw κ hκ => ?_⟩)⟩
        · simp [key, mo, run, Lynx.Except.andAlso, reb (k + 4) (by omega), Lynx.Term.isMember,
            boolAtom]
        · cases h : w κ with
          | none => rfl
          | some x => exact absurd ((sT x).mpr ⟨w, (mt w).mp hw, κ, hκ, h⟩) (seb.mp rfl x)
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1», boolAtom]

theorem get_map_term (d : Dispatcher) (key : Term) :
    Elixir.Module.Types.Descr.«map_get/2» d (.atom "term") key = .ok (.atom "badmap") := by
  rw [Elixir.Module.Types.Descr.«map_get/2».eq_def]
  rfl

end

end Elixir.STTDescrProofsTest.Nest
