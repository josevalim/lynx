namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- `map_to_list/2` with the pair function on static map types of the level above: `:badmap` for types other than non-empty
map types, otherwise lists of the pairs of their maps, holding the empty list exactly when they hold the empty map. -/
theorem tolist_map {X : List (Term × Term)} (hX : DE (level t (n + 1)).E (.map X)) {m : Nat}
    (hm : (level t (n + 1)).K + 30 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_to_list/2» (D m) (.map X) mtlF = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t (n + 1) X) ∨
        (MOnly t (n + 1) X ∧ ∃ b inner L, mapLookup X (.atom "map") = some b ∧ res = .tuple #[.atom "ok", L] ∧
          DE (level t (n + 1)).E inner ∧ InnerSem t n b inner ∧
          ((L = nilT ∧ ∀ p : PN t (n + 1), ¬denD inner p) ∨
            ∃ nil k, L = lTy nil k inner ∧ (nil = Bool.true ↔ MT t (n + 1) X wNone)))) := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 5 := ⟨m - 5, by omega⟩
  have sX := de_map hX
  have ef := (level t (n + 1)).ef
  obtain ⟨dR, sR⟩ := rest_map hX
  have rE := next_empty dR (m := M + 5) (by omega)
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (M + 5)) (.map X) =
      .ok (boolAtom (bp (∀ v : PN t (n + 1), ¬denD (.map (rmM X)) v))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
    exact rE
  rw [Elixir.Module.Types.Descr.«map_to_list/2».eq_def]
  simp only [Erlang.maps.«take/2», sX.static, mo]
  by_cases restE : ∀ v : PN t (n + 1), ¬denD (.map (rmM X)) v
  · rw [bp_true.mpr restE]
    have onlyIff : MOnly t (n + 1) X ↔ ∃ w, MT t (n + 1) X w :=
      ⟨fun h => h.2, fun h => ⟨fun v hv => Classical.byContradiction fun ne => restE v ((sR v).mpr ⟨hv, ne⟩), h⟩⟩
    cases hb : mapLookup X (.atom "map") with
    | none =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
      · simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb]
      · obtain ⟨w, b, hb', -⟩ := (onlyIff.mp h)
        rw [hb] at hb'; cases hb'
    | some b =>
      have fb : MField (level t (n + 1)).E b := fieldC_map (sX.fields "map" b hb)
      have wb : Bdd (MapLitV (level t (n + 1)).E) b := by
        rcases fb with ⟨k, rfl⟩ | wb
        · exact Bdd.leaf_iff.mpr ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩
        · exact wb.mono fun _ h => h.1
      obtain ⟨lines, rl, hl, sl⟩ := dnf_lit_map (den := (level t (n + 1)).den) ef.mopsE ef.mdopsE ef.msemZ rfl
        (m := M + 5) (by omega) wb
      have inB : ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ↔
          ∃ L ∈ lines, InMLine (level t (n + 1)).den L w := by
        intro w
        rw [← sl w]
        rcases fb with ⟨k, rfl⟩ | wb'
        · have lit : MapLitV (level t (n + 1)).E (.tuple #[.integer k, .atom "open", fieldsTerm []]) :=
            ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩
          have v := (valM_iff (w := w) ef.mopsE ef.mdopsE ef.semR lit).mpr (nsem_lit.mpr (msem_open_nil w))
          rw [denMF_top, eval_leaf]
          exact ⟨fun _ => v, fun _ => rfl⟩
        · rw [denMF_bdd wb']
      have mt : ∀ w, MT t (n + 1) X w ↔ denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true :=
        fun w => by simp [MT, hb]
      cases lines with
      | nil =>
        refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb,
            rl, Term.list]
        · obtain ⟨w, hw⟩ := onlyIff.mp h
          simpa using (inB w).mp ((mt w).mp hw)
      | cons L₀ rest =>
        obtain ⟨w₀, h₀⟩ := (hl L₀ List.mem_cons_self).2
        have only : MOnly t (n + 1) X := onlyIff.mpr ⟨w₀, (mt w₀).mpr ((inB w₀).mpr ⟨L₀, List.mem_cons_self, h₀⟩)⟩
        obtain ⟨inner, ri, di, si⟩ := inner_run (M := M) (by omega) fb (L₀ :: rest) hl inB
        by_cases ce : Term.compare (Term.fuel inner (.map [])) inner (.map []) = .eq
        · refine ⟨_, ?_, Or.inr ⟨only, b, inner, nilT, rfl, rfl, di, si, Or.inl ⟨rfl, fun p hp => ?_⟩⟩⟩
          · simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb,
              rl, ri, Erlang.erlang.«==/2», ce, Elixir.Module.Types.Descr.«empty_list/0», nilT]
          · have := (ef_next t (n + 1)).resp de_none di (Lynx.Term.compare_eq_symm ce) hp
            simp [denD_map, mapLookup, dn_none] at this
        · obtain ⟨hb', rh, sh⟩ := has_empty (den := (level t (n + 1)).den) (L₀ :: rest) (fun L m => (hl L m).1) (M + 2)
          obtain ⟨k, rlist, rnel⟩ := list_run ((ef_next t (n + 1)).static di) (M + 5)
          refine ⟨_, ?_, Or.inr ⟨only, b, inner, lTy hb' k inner, rfl, rfl, di, si, Or.inr ⟨hb', k, rfl, ?_⟩⟩⟩
          · cases hb' <;> simp [boolAtom, Lynx.Term.isMember, Elixir.Module.Types.Descr.«map_to_list_static/2»,
              getMapKeys_single, hb, rl, ri, Erlang.erlang.«==/2», ce, rh, rlist, rnel, lTy]
          · rw [sh, mt, inB]
  · rw [bp_false.mpr restE]
    refine ⟨.atom "badmap", by simp [boolAtom, Lynx.Term.isMember], Or.inl ⟨rfl, fun h => restE fun v hv => ?_⟩⟩
    exact ((sR v).mp hv).2 (h.1 v ((sR v).mp hv).1)

end

end Elixir.STTDescrProofsTest.Nest
