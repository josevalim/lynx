namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Differences of map types on value maps. -/

theorem denMF_botV (v : (MW V)) : denMF E den (.atom "bdd_bot") v = Bool.false := by
  rw [denMF_bdd (Bdd.bot (ok := MLit E))]; rfl

/-- Plain differences of map types hold the maps of the first and not the second. -/
theorem map_diff_val {x y : Term} (fx : MField E x) (fy : MField E y) :
    ∃ w, Elixir.Module.Types.Descr.«map_difference/2» x y = .ok w ∧ MField E w ∧
      ∀ v, denMF E den w v = (denMF E den x v && !denMF E den y v) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl, Or.inr Bdd.bot,
      fun v => by rw [denMF_botV, denMF_top]; simp⟩
  have ny := not_top_of_ok wy mlit_not
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_difference/2»
        simp [diff_leaf_top]
      · rw [denMF_botV, denMF_bdd wy]; rfl
    · refine ⟨_, ?_, Or.inl ⟨kt, rfl⟩, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_difference/2»
        simp [diff_leaf_bot]
      · rw [denMF_bdd wy]; simp
    all_goals
      obtain ⟨w, run, keep, sem⟩ := neg_ok wy
      have ww := keep _ wy
      refine ⟨w, by rw [map_difference_neg ny _ rfl, run], Or.inr ww, fun v => ?_⟩
      rw [denMF_bdd ww, denMF_bdd wy, denMF_top, sem _ (valM_resp v)]
      simp
  · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
    have ww := keep _ wx wy
    refine ⟨w, by rw [map_difference_bdd (not_top_of_ok wx mlit_not) ny, run], Or.inr ww, fun v => ?_⟩
    rw [denMF_bdd ww, denMF_bdd wx, denMF_bdd wy, sem _ (valM_resp v)]

/-- `orddict:find/2` on sorted fields finds the field of a key. -/
theorem find_val (a : String) : ∀ {l : List (Term × Term)}, FieldsV E l →
    Erlang.orddict.«find/2» (.atom a) (fieldsTerm l) =
      match mapLookup l (.atom a) with
      | some f => .ok (.tuple #[.atom "ok", f])
      | none => .ok (.atom "error")
  | [], _ => by rw [Erlang.orddict.«find/2».eq_def]; simp [fieldsTerm, Term.list, mapLookup]
  | (k, v) :: t, sl => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have st := fieldsV_tail sl
    have hd := fieldsV_head sl
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have none : mapLookup t (.atom a) = Option.none := lookup_none fun e me eq => by
        have := cmp_lt_trans cmp (hd e me)
        rw [eq, compare_self] at this; cases this
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_right ne, none]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_left rfl]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have ih := find_val a st
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_right ne, ← ih]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]

theorem field_empty1_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {c : Term} (hc : E c) (o : Bool) :
    ∃ e : Bool, Elixir.Module.Types.Descr.«field_empty?/1» (D m) (.tuple #[c, boolAtom o]) = .ok (boolAtom e) ∧
      (e = Bool.true ↔ ∀ x, ¬FieldSem den (.tuple #[c, boolAtom o]) x) := by
  cases o
  · obtain ⟨b, run, sem⟩ := ef.empty1 hm hc
    refine ⟨b, by simpa [Elixir.Module.Types.Descr.«field_empty?/1», boolAtom] using run, ?_⟩
    rw [sem]
    constructor
    · intro h x hx
      rw [fieldSem_mk] at hx
      rcases hx with ⟨-, h'⟩ | ⟨y, -, hy⟩
      · cases h'
      · exact h y hy
    · intro h y hy
      exact h (some y) ((fieldSem_mk (opt := Bool.false)).mpr (Or.inr ⟨y, rfl, hy⟩))
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«field_empty?/1», boolAtom], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    exact fun h => h Option.none ((fieldSem_mk (opt := Bool.true)).mpr (Or.inl ⟨rfl, rfl⟩))

theorem field_opt_diff_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : Term} {o₁ o₂ : Bool} (h₁ : E t₁) (h₂ : E t₂)
    (S : List (Term × Term)) :
    ∃ c, E c ∧ Elixir.Module.Types.Descr.«field_opt_difference/3» (D m) (.tuple #[t₁, boolAtom o₁])
        (.tuple #[t₂, boolAtom o₂]) (.map S) = .ok (.tuple #[c, boolAtom (o₁ && !o₂)]) ∧
      ∀ x, FieldSem den (.tuple #[c, boolAtom (o₁ && !o₂)]) x ↔
        FieldSem den (.tuple #[t₁, boolAtom o₁]) x ∧ ¬FieldSem den (.tuple #[t₂, boolAtom o₂]) x := by
  obtain ⟨c, hc, run, sem⟩ := ef.opt_diff S h₁ h₂ hm
  refine ⟨c, hc, ?_, fieldSem_diff sem⟩
  simp only [Elixir.Module.Types.Descr.«field_opt_difference/3», run]
  cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]

theorem field_opt_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : Term} {o₁ o₂ : Bool} (h₁ : E t₁) (h₂ : E t₂)
    (S : List (Term × Term)) :
    ∃ c, E c ∧ Elixir.Module.Types.Descr.«field_opt_intersection/3» (D m) (.tuple #[t₁, boolAtom o₁])
        (.tuple #[t₂, boolAtom o₂]) (.map S) = .ok (.tuple #[c, boolAtom (o₁ && o₂)]) ∧
      ∀ x, FieldSem den (.tuple #[c, boolAtom (o₁ && o₂)]) x ↔
        FieldSem den (.tuple #[t₁, boolAtom o₁]) x ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) x := by
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S h₁ h₂ hm
  refine ⟨c, hc, ?_, fieldSem_meet sem⟩
  simp only [Elixir.Module.Types.Descr.«field_opt_intersection/3», run]
  cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso]

/-- Maps a literal allows at every key but one atom key. -/
def MSemExcept (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) (a : String) (w : MW V) : Prop :=
  (∀ s, s ≠ a → FSem den tag l s (w (.atom s))) ∧ ∀ k i, TagSem den tag (domKind k) (w (.dom k i))

theorem msem_split_at {tag : Term} {l : List (Term × Term)} {a : String} {f : Term}
    (at_a : ∀ o, FSem den tag l a o ↔ FieldSem den f o) (w : (MW V)) :
    MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den f (w (.atom a)) := by
  constructor
  · intro h; exact ⟨⟨fun s _ => h s, h.doms⟩, (at_a _).mp (h a)⟩
  · rintro ⟨⟨h, hd⟩, ha⟩
    refine ⟨fun s => ?_, hd⟩
    by_cases e : s = a
    · subst e; exact (at_a _).mpr ha
    · exact h s e

/-- Literals without an atom key allow there the default field of their tag. -/
theorem msem_split_absent (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} {a : String}
    (la : mapLookup l (.atom a) = Option.none) (w : (MW V)) :
    MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den (tagField tag) (w (.atom a)) :=
  msem_split_at (fun o => by rw [fieldSem_tagV ef.mopsE ef.mdopsE ef.semR g]; simp only [FSem, la]) w

theorem msem_split {tag : Term} {l : List (Term × Term)} {a : String} {f : Term} (la : mapLookup l (.atom a) = some f)
    (w : (MW V)) : MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den f (w (.atom a)) := by
  have at_a : FSem den tag l a (w (.atom a)) ↔ FieldSem den f (w (.atom a)) := by unfold FSem; rw [la]
  constructor
  · intro h; exact ⟨⟨fun s _ => h s, h.doms⟩, at_a.mp (h a)⟩
  · rintro ⟨⟨h, hd⟩, ha⟩
    refine ⟨fun s => ?_, hd⟩
    by_cases e : s = a
    · subst e; exact at_a.mpr ha
    · exact h s e

theorem msem_store {tag : Term} {l l' : List (Term × Term)} {a : String} {d : Term}
    (look : ∀ s, mapLookup l' (.atom s) = if a = s then some d else mapLookup l (.atom s)) (w : (MW V)) :
    MSem den tag l' w ↔ MSemExcept den tag l a w ∧ FieldSem den d (w (.atom a)) := by
  have fs : ∀ s o, FSem den tag l' s o ↔ if a = s then FieldSem den d o else FSem den tag l s o := by
    intro s o
    unfold FSem
    rw [look s]
    by_cases e : a = s <;> simp [e]
  constructor
  · intro h
    refine ⟨⟨fun s ne => ?_, h.doms⟩, ?_⟩
    · have := (fs s (w (.atom s))).mp (h s); rwa [ite_eq_right (Ne.symm ne)] at this
    · have := (fs a (w (.atom a))).mp (h a); rwa [ite_eq_left rfl] at this
  · rintro ⟨⟨h, hd⟩, ha⟩
    refine ⟨fun s => ?_, hd⟩
    rw [fs]
    by_cases e : a = s
    · subst e; rw [ite_eq_left rfl]; exact ha
    · rw [ite_eq_right e]; exact h s (Ne.symm e)

/-- Map values. -/
def ValM (E : Term → Prop) (den : Term → V → Prop) (ρ : Term → Bool) : Prop := ∃ w, ρ = valM E den w

theorem valM_respM : ∀ ρ, ValM E den ρ → Resp ρ := fun _ ⟨w, e⟩ => e ▸ valM_resp w

theorem valM_leaf (ef : EF nd E V den tl K) {k : Int} {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l)
    (g : TagV E tag) (w : (MW V)) :
    valM E den w (.tuple #[.integer k, tag, fieldsTerm l]) = Bool.true ↔ MSem den tag l w :=
  (valM_iff ef.mopsE ef.mdopsE ef.semR ⟨k, tag, l, rfl, g, sl⟩).trans nsem_lit

/-- Storing a field into the fields of a literal makes a leaf of the literal's maps with that field. -/
theorem store_leaf (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (a : String) {d : Term} (hd : FieldValue E d) :
    ∃ (k : Int) (l' : List (Term × Term)), Erlang.orddict.«store/3» (.atom a) d (fieldsTerm l) = .ok (fieldsTerm l') ∧
      Elixir.Module.Types.Descr.«bdd_leaf_new/2» tag (fieldsTerm l') =
        .ok (.tuple #[.integer k, tag, fieldsTerm l']) ∧
      MLit E (.tuple #[.integer k, tag, fieldsTerm l']) ∧
      ∀ w, valM E den w (.tuple #[.integer k, tag, fieldsTerm l']) = Bool.true ↔
        MSemExcept den tag l a w ∧ FieldSem den d (w (.atom a)) := by
  obtain ⟨l', runS, sl', -, look⟩ := store_val a hd sl
  obtain ⟨k, leaf, key⟩ := leaf_new_keyM g (l'.map fun e => .tuple #[e.1, e.2])
  have ne : ¬(tag = .atom "open" ∧ l' = []) := by
    rintro ⟨-, rfl⟩
    have := look a
    simp [mapLookup] at this
  refine ⟨k, l', runS, leaf, ⟨⟨k, tag, l', rfl, g, sl'⟩, fun ⟨_, e⟩ => leaf_not_top ne e, key⟩, fun w => ?_⟩
  rw [valM_leaf ef sl' g, msem_store look]

/-- The one-key difference of a literal and another that agrees with it but at one key. -/
theorem one_key_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {k₁ : Int} {tag : Term} (g : TagV E tag)
    {l : List (Term × Term)} (sl : FieldsV E l) (_ntop : ¬(tag = .atom "open" ∧ l = []))
    (_key₁ : KeyOk (.tuple #[.integer k₁, tag, fieldsTerm l])) (a₂ : Term) {a : String}
    {t₁ t₂ : Term} {o₁ o₂ : Bool} (ht₁ : E t₁) (ht₂ : E t₂)
    (split : ∀ w, MSem den tag l w ↔ MSemExcept den tag l a w ∧ FieldSem den (.tuple #[t₁, boolAtom o₁]) (w (.atom a)))
    (type : Term) (S : List (Term × Term))
    (htype : type = .atom "none" ∨ type = .atom "intersection" ∨ type = .atom "union")
    (rel : ∀ w, MSem den tag l w → (valM E den w a₂ = Bool.true ↔ FieldSem den (.tuple #[t₂, boolAtom o₂]) (w (.atom a))))
    (full : type = .atom "union" → ∀ w, valM E den w a₂ = Bool.true ↔
      MSemExcept den tag l a w ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) (w (.atom a))) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7» (D m) tag (fieldsTerm l) (.atom a)
        (.tuple #[t₁, boolAtom o₁]) (.tuple #[t₂, boolAtom o₂]) type (.map S) = .ok res ∧
      CmpOk (ValM E den) (MLit E) (.tuple #[.integer k₁, tag, fieldsTerm l]) a₂ type res := by
  have v₁ : ∀ w, valM E den w (.tuple #[.integer k₁, tag, fieldsTerm l]) = Bool.true ↔ MSem den tag l w :=
    valM_leaf ef sl g
  obtain ⟨c, hc, runc, semc⟩ := field_opt_diff_val ef (m := m) (o₁ := o₁) (o₂ := o₂) (by omega) ht₁ ht₂ S
  obtain ⟨e, rune, seme⟩ := field_empty1_val ef (m := m) (by omega) hc (o₁ && !o₂)
  cases e
  rotate_left
  · refine ⟨.atom "subtype", ?_, Or.inr (Or.inl ⟨rfl, fun ρ ⟨w, ew⟩ h => ?_⟩)⟩
    · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
      simp only [runc, rune, Lynx.Except.ok_bind]
      simp [boolAtom, isMember]
    · subst ew
      have hm₁ := (v₁ w).mp h
      have f₁ := ((split w).mp hm₁).2
      refine (rel w hm₁).mpr (Classical.byContradiction fun nf => ?_)
      exact (seme.mp rfl) (w (.atom a)) ((semc (w (.atom a))).mpr ⟨f₁, nf⟩)
  obtain ⟨kd, ld, runS, leafd, okd, semd⟩ := store_leaf ef g sl a (d := .tuple #[c, boolAtom (o₁ && !o₂)]) ⟨c, _, rfl, hc⟩
  have sad : ∀ ρ, ValM E den ρ → eval ρ (.tuple #[.integer kd, tag, fieldsTerm ld]) =
      (ρ (.tuple #[.integer k₁, tag, fieldsTerm l]) && !ρ a₂) := by
    rintro ρ ⟨w, rfl⟩
    rw [eval_leaf]
    apply Bool.eq_iff_iff.mpr
    rw [semd, Bool.and_eq_true, v₁, Bool.not_eq_true', ← Bool.not_eq_true, split, semc]
    constructor
    · rintro ⟨h, f₁, nf₂⟩
      exact ⟨⟨h, f₁⟩, fun r => nf₂ ((rel w ((split w).mpr ⟨h, f₁⟩)).mp r)⟩
    · rintro ⟨⟨h, f₁⟩, nr⟩
      exact ⟨h, f₁, fun f₂ => nr ((rel w ((split w).mpr ⟨h, f₁⟩)).mpr f₂)⟩
  have ad : LeafOrBot (MLit E) (.tuple #[.integer kd, tag, fieldsTerm ld]) := Or.inr ⟨kd, _, _, rfl, okd⟩
  rcases htype with rfl | rfl | rfl
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, .atom "bdd_bot", rfl, ad, Or.inl rfl, sad, fun h => by simp at h,
      fun h => by simp at h, fun _ => rfl⟩))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
    simp only [runc, rune, runS, leafd, Lynx.Except.ok_bind]
    simp [boolAtom, isMember]
  · obtain ⟨ci, hci, runi, semi⟩ := field_opt_inter_val ef (m := m) (o₁ := o₁) (o₂ := o₂) (by omega) ht₁ ht₂ S
    obtain ⟨ei, runei, semei⟩ := field_empty1_val ef (m := m) (by omega) hci (o₁ && o₂)
    cases ei
    · obtain ⟨ki, li, runSi, leafi, oki, semli⟩ := store_leaf ef g sl a (d := .tuple #[ci, boolAtom (o₁ && o₂)])
        ⟨ci, _, rfl, hci⟩
      refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, _, rfl, ad, Or.inr ⟨ki, _, _, rfl, oki⟩, sad, fun _ ρ hρ => ?_,
        fun h => by simp at h, fun h => by simp at h⟩))⟩
      · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
        simp only [runc, rune, runS, leafd, runi, runei, runSi, leafi, Lynx.Except.ok_bind]
        simp [boolAtom, isMember]
      · obtain ⟨w, rfl⟩ := hρ
        rw [eval_leaf]
        apply Bool.eq_iff_iff.mpr
        rw [semli, Bool.and_eq_true, v₁, split, semi]
        constructor
        · rintro ⟨h, f₁, f₂⟩
          exact ⟨⟨h, f₁⟩, (rel w ((split w).mpr ⟨h, f₁⟩)).mpr f₂⟩
        · rintro ⟨⟨h, f₁⟩, r⟩
          exact ⟨h, f₁, (rel w ((split w).mpr ⟨h, f₁⟩)).mp r⟩
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, .atom "bdd_bot", rfl, ad, Or.inl rfl, sad, fun _ ρ hρ => ?_,
        fun h => by simp at h, fun h => by simp at h⟩))⟩
      · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
        simp only [runc, rune, runS, leafd, runi, runei, Lynx.Except.ok_bind]
        simp [boolAtom, isMember]
      · obtain ⟨w, rfl⟩ := hρ
        symm
        apply Bool.eq_false_iff.mpr
        intro h
        rw [Bool.and_eq_true, v₁] at h
        obtain ⟨h₁, h₂⟩ := h
        have f₁ := ((split w).mp h₁).2
        exact (semei.mp rfl) (w (.atom a)) ((semi (w (.atom a))).mpr ⟨f₁, (rel w h₁).mp h₂⟩)
  · obtain ⟨cu, hcu, runu, semu⟩ := field_opt_union_val ef (m := m) (o₁ := o₁) (o₂ := o₂) (by omega) rfl rfl ht₁ ht₂ S
    obtain ⟨ku, lu, runSu, leafu, oku, semlu⟩ := store_leaf ef g sl a (d := .tuple #[cu, boolAtom (o₁ || o₂)])
      ⟨cu, _, rfl, hcu⟩
    refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨_, _, rfl, ad, Or.inr ⟨ku, _, _, rfl, oku⟩, sad, fun h => by simp at h,
      fun _ ρ hρ => ?_, fun h => by simp at h⟩))⟩
    · rw [Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7».eq_def]
      simp only [runc, rune, runS, leafd, runu, runSu, leafu, Lynx.Except.ok_bind]
      simp [boolAtom, isMember]
    · obtain ⟨w, rfl⟩ := hρ
      rw [eval_leaf]
      apply Bool.eq_iff_iff.mpr
      rw [semlu, Bool.or_eq_true, v₁, split, full rfl w, semu]
      constructor
      · rintro ⟨h, f₁ | f₂⟩
        · exact Or.inl ⟨h, f₁⟩
        · exact Or.inr ⟨h, f₂⟩
      · rintro (⟨h, f₁⟩ | ⟨h, f₂⟩)
        · exact ⟨h, Or.inl f₁⟩
        · exact ⟨h, Or.inr f₂⟩

end Elixir.STTDescrProofsTest.Nest
