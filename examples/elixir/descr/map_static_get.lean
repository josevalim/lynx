namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- A split of keys, as `map_split_keys_and_domains/1` returns it. -/
def splitT (rs : List Term) (neg : Term) (ds : List Term) : Term :=
  .tuple #[Term.list rs, .nil, neg, Term.list ds, .nil]

/-- `map_get_static/2` on a map field and a split of static keys: `:badmap` when it is empty, otherwise the union of
the values its maps hold at the keys the split selects. -/
theorem mstatic_get (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) {rs : List Term} {neg : Term} {ds : List Term}
    (hs : SplitOk rs neg ds) :
    ∃ res, Elixir.Module.Types.Descr.«map_get_static/2» (D (n + 4)) (.map X) (splitT rs neg ds) = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        (∃ T, res = .tuple #[.atom "ok", T] ∧ E T ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey rs neg ds κ ∧ w κ = some x)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · -- Not empty: a map of the literal.
      have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have line : ∀ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list []]) w ↔ MSem den tag l w := fun w => by
        rw [inMLine_iff]; simp
      obtain ⟨T, rT, hT, sT⟩ := get_dnf ef hn fb [.tuple #[tag, fieldsTerm l, Term.list []]]
        (fun L mL => by
          simp only [List.mem_singleton] at mL
          subst mL
          exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, (line w₀).mpr h₀⟩)
        (fun w => by simp [sem, line]) hs
      refine ⟨_, ?_, Or.inr ⟨T, rfl, hT, ⟨w₀, (sem w₀).mpr h₀⟩, sT⟩⟩
      unfold Elixir.Module.Types.Descr.«map_get_static/2»
      simp only [Term.list] at rT
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom, rT, splitT]
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_get_static/2»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_get_static/2»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨T, rT, hT, sT⟩ := get_dnf ef hn fb (L :: rest) hl inB hs
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, rfl, hT, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, sT⟩⟩
      unfold Elixir.Module.Types.Descr.«map_get_static/2»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simp [getMapKeys_single, hb, rl, rT, Term.list, splitT]
      · simp [getMapKeys_single, hb, rl, rT, Term.list, splitT]
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simp [getMapKeys_single, hb, rl, rT, Term.list, splitT]

end

end Elixir.STTDescrProofsTest.Nest
