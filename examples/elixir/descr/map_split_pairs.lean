namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Pairs of a field and a map type, as maps split at a key. -/
def MPairOk (E : Term → Prop) (p : Term) : Prop := ∃ f b, p = .tuple #[f, b] ∧ FieldValue E f ∧ MField E b

/-- A value at the key and the rest of a map in a pair. -/
def MPairIn (E : Term → Prop) (den : Term → V → Prop) (p : Term) (o : Option V) (w : MW V) : Prop :=
  ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o ∧ denMF E den b w = Bool.true

theorem mpairIn_iff {f b : Term} {o : Option V} {w : MW V} :
    MPairIn E den (.tuple #[f, b]) o w ↔ FieldSem den f o ∧ denMF E den b w = Bool.true := by
  constructor
  · rintro ⟨f', b', e, h₁, h₂⟩
    simp only [Term.tuple.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact ⟨h₁, h₂⟩
  · intro h; exact ⟨f, b, rfl, h⟩

theorem field_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f g : Term} (hf : FieldValue E f)
    (hg : FieldValue E g) : ∃ h, FieldValue E h ∧ Elixir.Module.Types.Descr.«field_intersection/2» (D m) f g = .ok h ∧
      ∀ o, FieldSem den h o ↔ FieldSem den f o ∧ FieldSem den g o := by
  obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
  obtain ⟨t₂, o₂, rfl, h₂⟩ := hg
  obtain ⟨c, hc, run, sem, -⟩ := ef.inter h₁ h₂
  refine ⟨.tuple #[c, boolAtom (o₁ && o₂)], ⟨c, _, rfl, hc⟩, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_intersection/2», run m hm]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x => simp [sem x]

theorem field_diff_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f g : Term} (hf : FieldValue E f)
    (hg : FieldValue E g) : ∃ h, FieldValue E h ∧ Elixir.Module.Types.Descr.«field_difference/2» (D m) f g = .ok h ∧
      ∀ o, FieldSem den h o ↔ FieldSem den f o ∧ ¬FieldSem den g o := by
  obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
  obtain ⟨t₂, o₂, rfl, h₂⟩ := hg
  obtain ⟨c, hc, run, sem, -⟩ := ef.diff h₁ h₂
  refine ⟨.tuple #[c, boolAtom (o₁ && !o₂)], ⟨c, _, rfl, hc⟩, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_difference/2», run m hm]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x => simp [sem x]

theorem field_empty_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f : Term} (hf : FieldValue E f) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«field_empty?/1» (D m) f = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∀ o, ¬FieldSem den f o) := by
  obtain ⟨t, o, rfl, ht⟩ := hf
  exact field_empty1_val ef hm ht o

/-- The union of the tuple types of pairs. -/
theorem munion_pairs (P : List Term) (hP : ∀ p ∈ P, MPairOk E p) :
    ∃ u, MField E u ∧ (∀ w, denMF E den u w = Bool.true ↔ ∃ p ∈ P, ∃ f b, p = .tuple #[f, b] ∧ denMF E den b w = Bool.true) ∧
      ∀ m, Erlang.lists.«foldl/3» (D m)
        (.function "Elixir.Module.Types.Descr" "-map_pair_projection_keeps_full_fst?/2-fun-0-" 2 #[])
        (.atom "bdd_bot") (Term.list P) = .ok u := by
  obtain ⟨u, ⟨tu, su⟩, run⟩ := foldl_rel (K := 0) "Elixir.Module.Types.Descr" "-map_pair_projection_keeps_full_fst?/2-fun-0-" #[]
    (fun pre a => MField E a ∧ ∀ w, denMF E den a w = Bool.true ↔
      ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ denMF E den b w = Bool.true) P
    (fun pre x a mx ⟨ta, sa⟩ => by
      obtain ⟨f, b, rfl, -, fb⟩ := hP x mx
      obtain ⟨r, run, tr, sr, -⟩ := map_union_lh (den := den) fb ta
      refine ⟨r, ⟨tr, fun w => ?_⟩, fun m _ => ?_⟩
      · rw [sr, Bool.or_eq_true, sa]
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
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_pair_projection_keeps_full_fst?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_pair_projection_keeps_full_fst?/2-fun-0-/2»] using run)
    (.atom "bdd_bot") ⟨Or.inr Bdd.bot, fun w => by simp [denMF_bot]⟩
  exact ⟨u, tu, su, fun m => run m (Nat.zero_le _)⟩

/-- `tuple_pair_projection_keeps_full_fst?/2` checks for a remaining tuple outside every negated pair. -/
theorem mkeeps_full (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {b : Term} (hb : MField E b) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_fst?/2» (D m) (Term.list P) b = .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ w, denMF E den b w = Bool.true ∧
        ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → denMF E den nb w = Bool.false) := by
  obtain ⟨u, tu, su, run⟩ := munion_pairs (den := den) P hP
  obtain ⟨d, rd, td, sd, -⟩ := map_diff_lh hb tu
  obtain ⟨e, re, se⟩ := map_empty_exact ef td []
  have se := se (lh d + 1) (by omega) (safeN_nil _)
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_fst?/2», run m, rd, re m hm,
      Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [sd] at hw
      simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true'] at hw
      refine ⟨w, hw.1, fun p mp f nb e => ?_⟩
      cases h : denMF E den nb w
      · rfl
      · exact absurd ((su w).mpr ⟨p, mp, f, nb, e, h⟩) (by rw [hw.2]; simp)
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro w hw none
      have := (se.mp rfl) w
      rw [sd, hw] at this
      simp only [Bool.true_and, Bool.not_eq_false'] at this
      obtain ⟨p, mp, f, nb, e, h⟩ := (su w).mp this
      rw [none p mp f nb e] at h
      cases h

/-- Lists of pairs whose tuple types are not empty. -/
def MQOk (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) : Prop :=
  ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ FieldValue E f ∧ MField E b ∧ ∃ w, denMF E den b w = Bool.true

/-- A value and a remaining tuple of values in some pair. -/
def MInPairs (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) (y : Option V) (w : MW V) : Prop :=
  ∃ p ∈ Q, MPairIn E den p y w

/-- `prepend_tuple_pair_unless_empty_diff/4` keeps the pair of the difference, unless it is empty. -/
theorem mprepend_pair (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f nv b : Term} (hf : FieldValue E f) (hnv : FieldValue E nv)
    (hb : MField E b) (nb : ∃ w, denMF E den b w = Bool.true) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«prepend_map_pair_unless_empty_diff/4» (D m) f nv b (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ MQOk E den new ∧
      ∀ y w, MInPairs E den new y w ↔ (FieldSem den f y ∧ ¬FieldSem den nv y) ∧ denMF E den b w = Bool.true := by
  obtain ⟨d, hd, rd, sd⟩ := field_diff_val (den := den) ef hm hf hnv
  obtain ⟨e, re, se⟩ := field_empty_val (den := den) ef hm hd
  cases e
  · refine ⟨[.tuple #[d, b]], fun A => ?_, ?_, fun y w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«prepend_map_pair_unless_empty_diff/4»,
        rd, re, Lynx.Term.isMember, Term.list]
    · intro p mp; simp at mp; subst mp; exact ⟨d, b, rfl, hd, hb, nb⟩
    · simp [MInPairs, mpairIn_iff, sd]
  · refine ⟨[], fun A => ?_, by simp [MQOk], fun y w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«prepend_map_pair_unless_empty_diff/4»,
        rd, re, Lynx.Term.isMember]
    · simp only [MInPairs, List.not_mem_nil, false_and, exists_false, false_iff, not_and]
      intro h₁ _
      exact se.mp rfl y ((sd y).mpr h₁)

/-- One step of `tuple_project_negative_pairs/3`: a pair minus a negated pair, as pairs of non-empty tuple types. -/
theorem mproject_step (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {nv nb x : Term} (hnv : FieldValue E nv)
    (hnb : MField E nb) (hx : MQOk E den [x]) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4» (D m) nb nv x (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ MQOk E den new ∧
      ∀ y w, MInPairs E den new y w ↔ MPairIn E den x y w ∧ ¬(FieldSem den nv y ∧ denMF E den nb w = Bool.true) := by
  obtain ⟨f, b, rfl, hf, hb, nbw⟩ := hx _ List.mem_cons_self
  obtain ⟨ib, rib, tib, sib, -⟩ := map_inter_lh (den := den) hb hnb
  obtain ⟨eib, reib, seib⟩ := map_empty_exact ef tib []
  have seib := seib (lh ib + 1) (by omega) (safeN_nil _)
  obtain ⟨i_f, hif, rif, sif⟩ := field_inter_val (den := den) ef (show K ≤ m by omega) hf hnv
  obtain ⟨e1, re1, se1⟩ := field_empty_val (den := den) ef (show K ≤ m by omega) hif
  obtain ⟨db, rdb, tdb, sdb, -⟩ := map_diff_lh hb hnb
  obtain ⟨e2, re2, se2⟩ := map_empty_exact ef tdb []
  have se2 := se2 (lh db + 1) (by omega) (safeN_nil _)
  obtain ⟨pnew, rp, qp, sp⟩ := mprepend_pair ef (m := m) (by omega) hf hnv hb nbw
  have keepSem : ∀ y w, MInPairs E den [.tuple #[f, b]] y w ↔ MPairIn E den (.tuple #[f, b]) y w := fun y w => by
    simp [MInPairs]
  by_cases keep : (∃ k r, nb = .tuple #[k, .atom "closed", r]) ∧ eib = Bool.true
  · obtain ⟨⟨k, r, rfl⟩, rfl⟩ := keep
    refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun y w => ?_⟩
    · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
      simp [rib, reib m hm, Lynx.Term.isMember, Term.list]
    · rw [keepSem, mpairIn_iff]
      refine ⟨fun h => ⟨h, fun ⟨_, h'⟩ => ?_⟩, fun h => h.1⟩
      have := seib.mp rfl w
      rw [sib, h.2, h'] at this
      cases this
  -- The pair meets the negated pair: the intersection of the remaining tuples is not known to be empty.
  cases e1
  · cases e2
    · refine ⟨pnew ++ [.tuple #[i_f, db]], fun A => ?_, ?_, fun y w => ?_⟩
      · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
        have rp' := rp (.tuple #[i_f, db] :: A)
        simp only [Term.list] at rp'
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, rif, re1, rdb,
            re2 m hm, rp']
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, rif, re1, rdb, re2 m hm, rp']
      · intro p mp
        rcases List.mem_append.mp mp with mp | mp
        · exact qp p mp
        · simp at mp; subst mp
          refine ⟨i_f, db, rfl, hif, tdb, ?_⟩
          exact Classical.byContradiction fun none => by
            have := se2.mpr fun v => by
              cases h : denMF E den db v
              · rfl
              · exact absurd ⟨v, h⟩ none
            cases this
      · simp only [MInPairs, List.mem_append, List.mem_singleton] at sp ⊢
        rw [mpairIn_iff]
        constructor
        · rintro ⟨p, mp | rfl, hp⟩
          · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (sp y w).mp ⟨p, mp, hp⟩
            exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
          · rw [mpairIn_iff, sif, sdb] at hp
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
            refine ⟨⟨hp.1.1, hp.2.1⟩, fun h => ?_⟩
            rw [h.2] at hp; cases hp.2.2
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩
          by_cases hn : FieldSem den nv y
          · refine ⟨_, Or.inr rfl, ?_⟩
            rw [mpairIn_iff, sif, sdb, h₂]
            cases h : denMF E den nb w
            · exact ⟨⟨h₁, hn⟩, rfl⟩
            · exact absurd ⟨hn, h⟩ h₃
          · obtain ⟨p, mp, hp⟩ := (sp y w).mpr ⟨⟨h₁, hn⟩, h₂⟩
            exact ⟨p, Or.inl mp, hp⟩
    · refine ⟨pnew, fun A => ?_, qp, fun y w => ?_⟩
      · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, rif, re1, rdb, re2 m hm, rp A]
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, rif, re1, rdb, re2 m hm, rp A]
      · rw [sp, mpairIn_iff]
        have cover : ∀ w, denMF E den b w = Bool.true → denMF E den nb w = Bool.true := fun w h => by
          have := se2.mp rfl w
          rw [sdb, h] at this
          simpa using this
        constructor
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, fun hn => h₃ ⟨hn, cover w h₂⟩⟩, h₂⟩
  · refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun y w => ?_⟩
    · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
      by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
      · obtain ⟨k, r, rfl⟩ := hc
        have : eib = Bool.false := by
          cases eib
          · rfl
          · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
        subst this
        simp [rib, reib m hm, Lynx.Term.isMember, rif, re1, Term.list]
      · simp only
        split
        · exact absurd ⟨_, _, rfl⟩ hc
        · simp [Lynx.Term.isMember, rif, re1, Term.list]
    · rw [keepSem, mpairIn_iff]
      refine ⟨fun h => ⟨h, fun h' => (se1.mp rfl) y ((sif y).mpr ⟨h.1, h'.1⟩)⟩, fun h => h.1⟩

/-- `tuple_project_negative_pairs/3` splits a pair minus negated pairs into pairs of non-empty tuple types. -/
theorem mproject_pairs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {value rest : Term} (hv : FieldValue E value) (hr : MField E rest) (nr : ∃ w, denMF E den rest w = Bool.true) :
    ∃ Q, Elixir.Module.Types.Descr.«map_remove_negative/3» (D (n + 2)) (Term.list P) value rest =
        .ok (Term.list Q) ∧ MQOk E den Q ∧
      ∀ y w, MInPairs E den Q y w ↔ FieldSem den value y ∧ denMF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p y w := by
  obtain ⟨r, ⟨Q, rfl, qQ, sQ⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr"
    "-map_remove_negative/3-fun-1-" #[]
    (fun pre a => ∃ Q, a = Term.list Q ∧ MQOk E den Q ∧ ∀ y w, MInPairs E den Q y w ↔
      FieldSem den value y ∧ denMF E den rest w = Bool.true ∧ ∀ p ∈ pre, ¬MPairIn E den p y w) P
    (fun pre x a mx ⟨Q, ea, qQ, sQ⟩ => by
      subst ea
      obtain ⟨nv, nb, rfl, hnv, hnb⟩ := hP x mx
      have each : ∀ p ∈ Q, ∃ new, (∀ A, Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (new ++ A))) ∧ MQOk E den new ∧
          ∀ y w, MInPairs E den new y w ↔ MPairIn E den p y w ∧ ¬(FieldSem den nv y ∧ denMF E den nb w = Bool.true) :=
        fun p mp => mproject_step ef hn hnv hnb fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact qQ p mp
      classical
      let h : Term → List Term := fun p => if hp : p ∈ Q then Classical.choose (each p hp) else []
      have hh : ∀ p ∈ Q, (∀ A, Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (h p ++ A))) ∧ MQOk E den (h p) ∧
          ∀ y w, MInPairs E den (h p) y w ↔ MPairIn E den p y w ∧ ¬(FieldSem den nv y ∧ denMF E den nb w = Bool.true) := by
        intro p mp
        simp only [h, dite_eq_left mp]
        exact Classical.choose_spec (each p mp)
      have inner := foldl_lists_at (m := n + 1) "Elixir.Module.Types.Descr" "-map_remove_negative/3-fun-0-"
        #[nb, nv] h Q (fun p mp A => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-map_remove_negative/3-fun-0-/2».pure]
          exact (hh p mp).1 A) []
      refine ⟨Term.list (Q.reverse.flatMap h), ⟨Q.reverse.flatMap h, rfl, fun p mp => ?_, fun y w => ?_⟩, ?_⟩
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        exact (hh q mq).2.1 p mp
      · simp only [MInPairs, List.mem_flatMap, List.mem_reverse, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨p, ⟨q, mq, mp⟩, hp⟩
          obtain ⟨hq, hn'⟩ := ((hh q mq).2.2 y w).mp ⟨p, mp, hp⟩
          obtain ⟨h₁, h₂, h₃⟩ := (sQ y w).mp ⟨q, mq, hq⟩
          refine ⟨h₁, h₂, fun p' mp' hp' => ?_⟩
          rcases mp' with mp' | rfl
          · exact h₃ p' mp' hp'
          · exact hn' (mpairIn_iff.mp hp')
        · rintro ⟨h₁, h₂, h₃⟩
          obtain ⟨q, mq, hq⟩ := (sQ y w).mpr ⟨h₁, h₂, fun p' mp' => h₃ p' (Or.inl mp')⟩
          obtain ⟨p, mp, hp⟩ := ((hh q mq).2.2 y w).mpr ⟨hq, fun h => h₃ _ (Or.inr rfl) (mpairIn_iff.mpr h)⟩
          exact ⟨p, ⟨q, mq, mp⟩, hp⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_remove_negative/3-fun-1-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-1-/2»] using inner)
    (Term.list [.tuple #[value, rest]]) ⟨[.tuple #[value, rest]], rfl, fun p mp => by
      simp at mp; subst mp; exact ⟨value, rest, rfl, hv, hr, nr⟩, fun y w => by simp [MInPairs, mpairIn_iff]⟩
  exact ⟨Q, by simp [Elixir.Module.Types.Descr.«map_remove_negative/3», run], qQ, sQ⟩

theorem fieldValue_cases {f : Term} (hf : FieldValue E f) : ∃ t o, f = .tuple #[t, boolAtom o] ∧ E t := hf

/-- The final fold of `map_split_key_line/5` unites the fields of the pairs into the accumulated field. -/
theorem munion_fields (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (Q : List Term)
    (hQ : ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ FieldValue E f) {acc : Term} (ha : FieldValue E acc) :
    ∃ u, FieldValue E u ∧ Erlang.lists.«foldl/3» (D (n + 1))
        (.function "Elixir.Module.Types.Descr" "-map_split_key_line/5-fun-0-" 2 #[]) acc (Term.list Q) = .ok u ∧
      ∀ o, FieldSem den u o ↔ FieldSem den acc o ∨ ∃ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o := by
  obtain ⟨u, ⟨hu, su⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr" "-map_split_key_line/5-fun-0-" #[]
    (fun pre a => FieldValue E a ∧ ∀ o, FieldSem den a o ↔ FieldSem den acc o ∨
      ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o) Q
    (fun pre x a mx ⟨ha', sa⟩ => by
      obtain ⟨f, b, rfl, hf⟩ := hQ x mx
      obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
      obtain ⟨t₂, o₂, rfl, h₂⟩ := ha'
      obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef hn rfl rfl h₁ h₂ []
      refine ⟨.tuple #[c, boolAtom (o₁ || o₂)], ⟨⟨c, _, rfl, hc⟩, fun o => ?_⟩, ?_⟩
      · rw [sc, sa]
        constructor
        · rintro (h | h | ⟨p, mp, h⟩)
          · exact Or.inr ⟨_, by simp, _, b, rfl, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨p, by simp [mp], h⟩
        · rintro (h | ⟨p, mp, f', b', e, h⟩)
          · exact Or.inr (Or.inl h)
          · simp only [List.mem_append, List.mem_singleton] at mp
            rcases mp with mp | rfl
            · exact Or.inr (Or.inr ⟨p, mp, f', b', e, h⟩)
            · simp only [Term.tuple.injEq] at e
              obtain ⟨rfl, rfl, -⟩ := e
              exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_split_key_line/5-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_split_key_line/5-fun-0-/2»] using rc)
    acc ⟨ha, fun o => by simp⟩
  exact ⟨u, hu, run, su⟩

/-- The field a line with negations projects to, united with the accumulated one: the values at the key of its pair,
outside the negated pairs. -/
theorem mproj_value (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {field rest acc : Term} (hv : FieldValue E field) (hr : MField E rest) (nr : ∃ w, denMF E den rest w = Bool.true)
    (ha : FieldValue E acc) :
    ∃ (s : Bool) (acc' : Term), Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_fst?/2» (D (n + 2))
        (Term.list P) rest = .ok (boolAtom s) ∧
      (s = Bool.true → Elixir.Module.Types.Descr.«field_opt_union/3» (D (n + 2)) field acc (.map []) = .ok acc') ∧
      (s = Bool.false → ∃ Q, Elixir.Module.Types.Descr.«map_remove_negative/3» (D (n + 2)) (Term.list P) field rest =
        .ok (Term.list Q) ∧ Erlang.lists.«foldl/3» (D (n + 2))
          (.function "Elixir.Module.Types.Descr" "-map_split_key_line/5-fun-0-" 2 #[]) acc (Term.list Q) = .ok acc') ∧
      FieldValue E acc' ∧
      ∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨
        ∃ w, FieldSem den field o ∧ denMF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p o w := by
  obtain ⟨s, rs, ss⟩ := mkeeps_full (den := den) ef (m := n + 2) (by omega) P hP hr
  cases s
  · obtain ⟨Q, rQ, qQ, sQ⟩ := mproject_pairs ef hn P hP hv hr nr
    obtain ⟨u, hu, ru, su⟩ := munion_fields ef (n := n + 1) (by omega) Q (fun p mp => by
      obtain ⟨f, b, e, hf, -⟩ := qQ p mp
      exact ⟨f, b, e, hf⟩) ha
    refine ⟨Bool.false, u, rs, by simp, fun _ => ⟨Q, rQ, ru⟩, hu, fun o => ?_⟩
    rw [su]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨p, mp, f, b, rfl, hy⟩
      obtain ⟨f', b', e, -, -, w, hw⟩ := qQ _ mp
      simp only [Term.tuple.injEq] at e
      obtain ⟨rfl, rfl, -⟩ := e
      exact ⟨w, (sQ o w).mp ⟨_, mp, mpairIn_iff.mpr ⟨hy, hw⟩⟩⟩
    · rintro ⟨w, h⟩
      obtain ⟨p, mp, hp⟩ := (sQ o w).mpr h
      obtain ⟨f, b, rfl, hy, -⟩ := hp
      exact ⟨_, mp, f, b, rfl, hy⟩
  · obtain ⟨w₀, hw₀, out⟩ := ss.mp rfl
    obtain ⟨t₁, o₁, rfl, h₁⟩ := hv
    obtain ⟨t₂, o₂, rfl, h₂⟩ := ha
    obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef (m := n + 2) (by omega) rfl rfl h₁ h₂ []
    refine ⟨Bool.true, .tuple #[c, boolAtom (o₁ || o₂)], rs, fun _ => rc, by simp, ⟨c, _, rfl, hc⟩, fun o => ?_⟩
    rw [sc, or_comm]
    refine or_congr Iff.rfl ⟨fun hy => ⟨w₀, hy, hw₀, fun p mp hp => ?_⟩, fun ⟨_, hy, _⟩ => hy⟩
    obtain ⟨f, nb, rfl, -, hnb⟩ := hp
    rw [out _ mp f nb rfl] at hnb
    cases hnb

end

end Elixir.STTDescrProofsTest.Nest
