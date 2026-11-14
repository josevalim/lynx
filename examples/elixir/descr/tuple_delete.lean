namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Deleting elements from tuple types: the remaining tuples of each line at an index. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_pair_projection_keeps_full_snd?/2` checks for a value outside every negated pair. -/
theorem keeps_snd (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {value : Term} (hv : E value) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_snd?/2» (D (n + 1)) (Term.list P) value =
        .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ y, den value y ∧ ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → ¬den f y) := by
  obtain ⟨u, ⟨hu, su⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-tuple_pair_projection_keeps_full_snd?/2-fun-0-" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ den f y) P
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨f, b, rfl, hf, -⟩ := hP x mx
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hf ha hn
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_pair_projection_keeps_full_snd?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_pair_projection_keeps_full_snd?/2-fun-0-/2»,
          Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  obtain ⟨d, hd, rd, sd⟩ := ef.opt_diff [] hv hu (show K ≤ n + 1 by omega)
  obtain ⟨e, re, se⟩ := empty_bool ef hd (show K ≤ n + 1 by omega)
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_snd?/2», run,
      Elixir.Module.Types.Descr.«opt_difference/2», rd, re, Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨y, hy⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [Classical.not_not, sd, su] at hy
      refine ⟨y, hy.1, fun p mp f nb e hf => hy.2 ⟨p, mp, f, nb, e, hf⟩⟩
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro y hy none
      have := (se.mp rfl) y
      rw [sd, su] at this
      apply this ⟨hy, ?_⟩
      rintro ⟨p, mp, f, nb, e, hf⟩
      exact none p mp f nb e hf

/-- The tuples of a line without the element at an index. -/
def Proj (den : Term → V → Prop) (L : Term) (i : Nat) (w : List V) : Prop :=
  ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧ InLine den L (v₁ ++ y :: v₂)

theorem split_at {i : Nat} {w : List V} (h : i ≤ w.length) : ∃ w₁ w₂, w = w₁ ++ w₂ ∧ w₁.length = i :=
  ⟨w.take i, w.drop i, by simp, by simp; omega⟩

/-- One step of `tuple_delete_static/2`: a line without the element at an index, united with the accumulator. -/
theorem delete_step (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (i : Nat) {L : Term} (hL : TLine E L)
    (ne : ∃ v, InLine den L v ∧ i < v.length) {acc : Term} (ha : TField E acc) :
    ∃ r, Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3» (D (n + 2)) (.integer i) L acc = .ok r ∧
      TField E r ∧ ∀ w, denTF E den r w = Bool.true ↔ denTF E den acc w = Bool.true ∨ Proj den L i w := by
  obtain ⟨tag, l, negs, rfl, g, hl, lits⟩ := hL
  obtain ⟨res, rt, ⟨rfl, none⟩ | ⟨⟨value, rest, rfl, hv, hr⟩, nemp, lng, sem⟩⟩ := take_pair (den := den) ef g hl i
  · -- No tuple of the line is long enough: there are none.
    exfalso
    obtain ⟨v, hv, lt⟩ := ne
    obtain ⟨hv, -⟩ := inLine_iff.mp hv
    obtain ⟨v₁, v₂, rfl, l₁⟩ := split_at (w := v) (i := i) (by omega)
    cases v₂ with
    | nil => simp at lt; omega
    | cons y v₂ => exact none v₁ y v₂ l₁ hv
  -- The values and remaining tuples of the line are not empty.
  obtain ⟨y₀, w₀, hy₀, hw₀⟩ : ∃ y w, den value y ∧ denTF E den rest w = Bool.true := by
    obtain ⟨v, hv, lt⟩ := ne
    obtain ⟨hv, -⟩ := inLine_iff.mp hv
    obtain ⟨v₁, v₂, rfl, l₁⟩ := split_at (w := v) (i := i) (by omega)
    cases v₂ with
    | nil => simp at lt; omega
    | cons y v₂ => exact ⟨y, _, pairIn_iff.mp ((sem v₁ y v₂ l₁).mp hv)⟩
  have restLong : ∀ w, denTF E den rest w = Bool.true → i ≤ w.length := fun w h => lng y₀ w (pairIn_iff.mpr ⟨hy₀, h⟩)
  cases negs with
  | nil =>
    obtain ⟨r, rr, tr, sr⟩ := opt_tuple_union_sem ef (m := n + 2) (by omega) hr ha
    refine ⟨r, ?_, tr, fun w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3», rt, rr]
    · rw [sr, Bool.or_eq_true, or_comm]
      refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨v₁, y, v₂, e, l₁, h⟩ => ?_⟩
      · obtain ⟨w₁, w₂, rfl, l₁⟩ := split_at (restLong w h)
        exact ⟨w₁, y₀, w₂, rfl, l₁, inLine_iff.mpr ⟨(sem w₁ y₀ w₂ l₁).mpr (pairIn_iff.mpr ⟨hy₀, h⟩), by simp⟩⟩
      · subst e
        exact (pairIn_iff.mp ((sem v₁ y v₂ l₁).mp (inLine_iff.mp h).1)).2
  | cons N negs =>
    obtain ⟨P, rP, okP, semP⟩ := split_pairs (den := den) ef (N :: negs) lits i (m := n + 2)
    obtain ⟨s, rs, ss⟩ := keeps_snd (den := den) ef (n := n + 1) (by omega) P okP hv
    have line : ∀ v₁ y v₂, v₁.length = i → (InLine den (.tuple #[.atom tag, Term.list l, Term.list (N :: negs)])
        (v₁ ++ y :: v₂) ↔ (den value y ∧ denTF E den rest (v₁ ++ v₂) = Bool.true) ∧
          ¬∃ p ∈ P, PairIn E den p y (v₁ ++ v₂)) := by
      intro v₁ y v₂ l₁
      rw [inLine_iff, sem v₁ y v₂ l₁, pairIn_iff, ← semP v₁ y v₂ l₁]
      simp only [not_exists, not_and]
    cases s
    · obtain ⟨Q, rQ, qQ, sQ, fQ⟩ := project_pairs ef hn P okP hv hr ⟨w₀, hw₀⟩
      have fQ := fQ ⟨y₀, hy₀⟩
      obtain ⟨u, ⟨tu, su⟩, ru⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr" "-tuple_delete_static/2-fun-0-" #[]
        (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔
          denTF E den acc w = Bool.true ∨ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ denTF E den b w = Bool.true) Q
        (fun pre x a mx ⟨ta, sa⟩ => by
          obtain ⟨f, b, rfl, -, hb, -⟩ := qQ x mx
          obtain ⟨c, rc, tc, sc⟩ := opt_tuple_union_sem ef (m := n + 1) (by omega) hb ta
          refine ⟨c, ⟨tc, fun w => ?_⟩, ?_⟩
          · rw [sc, Bool.or_eq_true, sa]
            constructor
            · rintro (h | h | ⟨p, mp, h⟩)
              · exact Or.inr ⟨_, by simp, f, b, rfl, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨p, by simp [mp], h⟩
            · rintro (h | ⟨p, mp, f', b', e, h⟩)
              · exact Or.inr (Or.inl h)
              simp only [List.mem_append, List.mem_singleton] at mp
              rcases mp with mp | rfl
              · exact Or.inr (Or.inr ⟨p, mp, f', b', e, h⟩)
              · simp only [Term.tuple.injEq] at e
                obtain ⟨rfl, rfl, -⟩ := e
                exact Or.inl h
          · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_delete_static/2-fun-0-/2».pure]
            simpa [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-0-/2»] using rc)
        acc ⟨ha, fun w => by simp⟩
      refine ⟨u, ?_, tu, fun w => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3», Term.list, rt, rP, rs, rQ, ru, boolAtom,
          Lynx.Term.isMember]
      · rw [su]
        refine or_congr Iff.rfl ⟨fun ⟨p, mp, f, b, e, h⟩ => ?_, fun ⟨v₁, y, v₂, e, l₁, h⟩ => ?_⟩
        · subst e
          obtain ⟨f', b', e, y, hy⟩ := fQ _ mp
          simp only [Term.tuple.injEq] at e
          obtain ⟨rfl, rfl, -⟩ := e
          obtain ⟨h₁, h₂, h₃⟩ := (sQ y w).mp ⟨_, mp, pairIn_iff.mpr ⟨hy, h⟩⟩
          obtain ⟨w₁, w₂, rfl, l₁⟩ := split_at (restLong w h₂)
          exact ⟨w₁, y, w₂, rfl, l₁, (line w₁ y w₂ l₁).mpr ⟨⟨h₁, h₂⟩, fun ⟨p, mp, hp⟩ => h₃ p mp hp⟩⟩
        · subst e
          obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (line v₁ y v₂ l₁).mp h
          obtain ⟨p, mp, f, b, rfl, -, hb⟩ := (sQ y (v₁ ++ v₂)).mpr ⟨h₁, h₂, fun p mp hp => h₃ ⟨p, mp, hp⟩⟩
          exact ⟨_, mp, f, b, rfl, hb⟩
    · obtain ⟨y, hy, out⟩ := ss.mp rfl
      obtain ⟨r, rr, tr, sr⟩ := opt_tuple_union_sem ef (m := n + 2) (by omega) hr ha
      refine ⟨r, ?_, tr, fun w => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-tuple_delete_static/2-fun-1-/3», Term.list, rt, rP, rs, rr, boolAtom,
          Lynx.Term.isMember]
      · rw [sr, Bool.or_eq_true, or_comm]
        refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨v₁, y', v₂, e, l₁, h'⟩ => ?_⟩
        · obtain ⟨w₁, w₂, rfl, l₁⟩ := split_at (restLong w h)
          refine ⟨w₁, y, w₂, rfl, l₁, (line w₁ y w₂ l₁).mpr ⟨⟨hy, h⟩, fun ⟨p, mp, hp⟩ => ?_⟩⟩
          obtain ⟨f, nb, e, hf, -⟩ := hp
          exact out p mp f nb e hf
        · subst e
          exact ((line v₁ y' v₂ l₁).mp h').1.2

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_delete_static/2` removes the element at an index from every tuple of a tuple type with long tuples. -/
theorem delete_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) {Y : List (Term × Term)} {b : Term}
    (hb : mapLookup Y (.atom "tuple") = some b) (wb : Bdd (TLit E) b) (i : Nat)
    (long : ∀ v, denTF E den b v = Bool.true → i < v.length) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_delete_static/2» (D (n + 3)) (.map Y) (.integer i) =
        .ok (.map [(.atom "tuple", r)]) ∧ TField E r ∧
      ∀ w, denTF E den r w = Bool.true ↔ ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧ denTF E den b (v₁ ++ y :: v₂) = Bool.true := by
  obtain ⟨lines, rl, tl', sl⟩ := dnf_neg (den := den) ef.opsU ef.dopsU ef.msemZ rfl (m := n + 3) (by omega) wb
  have inB : ∀ v, denTF E den b v = Bool.true ↔ ∃ L ∈ lines, InLine den L v := fun v => by rw [denTF_bdd wb]; exact sl v
  obtain ⟨r, ⟨tr, sr⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr" "-tuple_delete_static/2-fun-1-"
    #[.integer i] (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔ ∃ L ∈ pre, Proj den L i w) lines
    (fun pre L a mL ⟨ta, sa⟩ => by
      obtain ⟨hL, v, hv⟩ := tl' L mL
      obtain ⟨c, rc, tc, sc⟩ := delete_step (den := den) ef hn i hL ⟨v, hv, long v ((inB v).mpr ⟨L, mL, hv⟩)⟩ ta
      refine ⟨c, ⟨tc, fun w => ?_⟩, ?_⟩
      · rw [sc, sa]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨L', mL', h⟩ | h)
          · exact ⟨L', Or.inl mL', h⟩
          · exact ⟨L, Or.inr rfl, h⟩
        · rintro ⟨L', mL' | rfl, h⟩
          · exact Or.inl ⟨L', mL', h⟩
          · exact Or.inr h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_delete_static/2-fun-1-/2».pure]
        exact rc)
    (.atom "bdd_bot") ⟨Or.inr Bdd.bot, fun w => by simp [denTF_bot]⟩
  refine ⟨r, ?_, tr, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«tuple_delete_static/2»
    simp [getMapKeys_single, hb, rl, run]
  · rw [sr]
    constructor
    · rintro ⟨L, mL, v₁, y, v₂, rfl, l₁, h⟩
      exact ⟨v₁, y, v₂, rfl, l₁, (inB _).mpr ⟨L, mL, h⟩⟩
    · rintro ⟨v₁, y, v₂, rfl, l₁, h⟩
      obtain ⟨L, mL, hL⟩ := (inB _).mp h
      exact ⟨L, mL, v₁, y, v₂, rfl, l₁, hL⟩

end

section
variable {t : Term} {n : Nat}

/-- `non_empty_tuple_only?/1` decides whether a static type of the next level holds only tuples, and some. -/
theorem only_run {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ c : Bool, Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D m) (.map X) = .ok (boolAtom c) ∧
      (c = Bool.true ↔ TOnly t n X) := by
  have sX := de_map hX
  have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
  obtain ⟨dR, sR⟩ := rest_tuple hX
  have rE := next_empty dR (m := m) hm
  obtain ⟨eb, reb, seb⟩ := tuple_empty_exact (level t n).ef fb []
  have seb := seb (lh b + 1) (by omega) (safeT_nil _)
  have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
  have only : TOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmT X)) v) ∧ eb = Bool.false := by
    constructor
    · rintro ⟨h₁, w, hw⟩
      refine ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), ?_⟩
      cases eb
      · rfl
      · have := seb.mp rfl w; rw [(tt w).mp hw] at this; cases this
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), ?_⟩
      obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt seb.mpr (by simp [h₂]))
      exact ⟨w, (tt w).mpr (by simpa using hw)⟩
  refine ⟨bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb, ?_, ?_⟩
  · simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb]
    rw [show (List.filter (fun entry => compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst != Ordering.eq) X) = rmT X from rfl]
    simp only [Lynx.Except.ok_bind, rE, reb m (by rw [level_K] at hm ⊢; omega)]
    cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
      simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
  · rw [only]
    simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true']

/-- `tuple_delete_at/2` on static types of the next level holding only tuples, all longer than an index: the tuples
without the element at the index. -/
theorem delete_tuple {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) (onlyY : TOnly t n Y) (i : Nat)
    (long : ∀ w, TT t n Y w → i < w.length) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map Y) (.integer i) = .ok (.map [(.atom "tuple", r)]) ∧
      TField (level t n).E r ∧ ∀ w, denTF (level t n).E (level t n).den r w = Bool.true ↔
        ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧ TT t n Y (v₁ ++ y :: v₂) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sY := de_map hY
  obtain ⟨w₀, b, hb, -⟩ := onlyY.2
  have fb : TField (level t n).E b := fieldC_tuple (sY.fields "tuple" b hb)
  have tt : ∀ w, TT t n Y w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
  have wb : Bdd (TLit (level t n).E) b := by
    rcases fb with ⟨k', rfl⟩ | wb
    · have := long [] ((tt []).mpr (denTF_top _ _)); simp at this
    · exact wb
  obtain ⟨c, rc, sc⟩ := only_run hY hb (m := k + 3) (by omega)
  have c_true : c = Bool.true := sc.mpr onlyY
  subst c_true
  obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb (i + 1) (by omega)
  have sz_true : sz = Bool.true := ss.mpr fun v hv => long v ((tt v).mpr hv)
  subst sz_true
  obtain ⟨r, rr, tr, sr⟩ := delete_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb wb i
    fun v hv => long v ((tt v).mpr hv)
  have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map Y) (.atom "tuple") = .ok (.atom "true") := by
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
  refine ⟨r, ?_, tr, fun w => by rw [sr]; simp only [tt]⟩
  have rs' : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map [(.atom "tuple", b)])
      (.integer ((i : Int) + 1)) = .ok (boolAtom Bool.true) := by simpa using rs
  rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def]
  simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
    Erlang.maps.«take/2», sY.static, key, rc, size_map _ hb, rs', boolAtom, Erlang.erlang.«/=/2», rr]

end

end Elixir.STTDescrProofsTest.Nest
