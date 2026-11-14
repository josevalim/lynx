namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-! Completeness of map line emptiness on values. -/

/-- Maps in a negated map literal. -/
def NSem (den : Term → V → Prop) (N : Term) (w : (MW V)) : Prop :=
  ∃ (k : Int) (tag : Term) (l : List (Term × Term)), N = .tuple #[.integer k, tag, fieldsTerm l] ∧ MSem den tag l w

def CovM (den : Term → V → Prop) (negs : List Term) (w : (MW V)) : Prop := ∃ N ∈ negs, NSem den N w

/-- Results of `map_line_meet_empty?`: `true`, or `:closed` thrown when the line and the negated literal are
disjoint. -/
def MeetVal (r : Except Exception Term) (disj : Prop) : Prop :=
  r = .ok (.atom "true") ∨ (disj ∧ r = .error (Exception.throw (.atom "closed")))

/-- Replacing a field by a larger one keeps the maps of a literal. -/
theorem msem_mono {tag : Term} {a : String} {A B : List (Term × Term)} (_hA : mapLookup A (.atom a) = Option.none)
    {f g : Term} (fg : ∀ o, FieldSem den f o → FieldSem den g o) {w : (MW V)}
    (h : MSem den tag (A ++ (Term.atom a, f) :: B) w) : MSem den tag (A ++ (Term.atom a, g) :: B) w := by
  refine h.of_atoms fun s hs => ?_
  unfold FSem TagSem at hs ⊢
  rw [lookup_append] at hs ⊢
  cases e : mapLookup A (.atom s) with
  | some x => simpa [e] using hs
  | none =>
    simp only [e, Option.none_or] at hs ⊢
    rw [lookup_cons_atom] at hs ⊢
    by_cases as : a = s
    · subst as; simp at hs ⊢; exact fg _ hs
    · simpa [as] using hs

theorem fieldsV_mid {A B : List (Term × Term)} {k f g : Term} (h : FieldsV E (A ++ (k, f) :: B))
    (hg : FieldValue E g) : FieldsV E (A ++ (k, g) :: B) := by
  obtain ⟨he, hp⟩ := h
  refine ⟨fun e me => ?_, ?_⟩
  · rcases List.mem_append.mp me with me | me
    · exact he e (List.mem_append_left _ me)
    · rcases List.mem_cons.mp me with rfl | me
      · exact ⟨(he (k, f) (by simp)).1, hg⟩
      · exact he e (List.mem_append_right _ (List.mem_cons_of_mem _ me))
  · rw [List.pairwise_append, List.pairwise_cons] at hp ⊢
    obtain ⟨pA, ⟨pk, pB⟩, cross⟩ := hp
    refine ⟨pA, ⟨pk, pB⟩, fun a ma b mb => ?_⟩
    rcases List.mem_cons.mp mb with rfl | mb
    · exact cross a ma (k, f) List.mem_cons_self
    · exact cross a ma b (List.mem_cons_of_mem _ mb)

theorem inhabited_mid {A B : List (Term × Term)} {k f g : Term} (h : Inhabited den (A ++ (k, f) :: B))
    (hg : ∃ o, FieldSem den g o) : Inhabited den (A ++ (k, g) :: B) := by
  intro e me
  rcases List.mem_append.mp me with me | me
  · exact h e (List.mem_append_left _ me)
  · rcases List.mem_cons.mp me with rfl | me
    · exact hg
    · exact h e (List.mem_append_right _ (List.mem_cons_of_mem _ me))

/-- One field of `map_line_meet_empty?/10`: the line minus the negated literal at this field, and the meet at
this field followed by the remaining fields. -/
theorem meet_field_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) (tag ntag : Term)
    (negs : List Term) (tagS : Term) (a : String) (f₁ f₂ : Term)
    (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) (t₂ : Term) (t₁ acc : List (Term × Term))
    (sorted : FieldsV E (acc.reverse ++ (Term.atom a, f₁) :: t₁)) (inh : Inhabited den (acc.reverse ++ (Term.atom a, f₁) :: t₁))
    (fresh : mapLookup acc.reverse (.atom a) = Option.none)
    (line : ∀ l, FieldsV E l → Inhabited den l → (∀ w, MSem den tagS l w → CovM den negs w) →
      Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
        .ok (.atom "true"))
    (H : ∀ w, MSem den tagS (acc.reverse ++ (Term.atom a, f₁) :: t₁) w → ¬FieldSem den f₂ (w (.atom a)) → CovM den negs w)
    {disj : Prop}
    (rec : ∀ f, FieldValue E f → (∃ o, FieldSem den f o) → (∀ o, FieldSem den f o ↔ FieldSem den f₁ o ∧ FieldSem den f₂ o) →
      MeetVal (Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm t₁) t₂ tag ntag
        (fieldsTerm ((.atom a, f) :: acc)) (Term.list negs) (.map S)) disj) :
    MeetVal (Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) f₁ f₂ (fieldsTerm t₁) t₂ tag ntag
      (fieldsTerm acc) (Term.list negs) (.map S)) disj := by
  obtain ⟨ty, o₁, rfl, hty⟩ := h₁
  obtain ⟨nt, o₂, rfl, hnt⟩ := h₂
  have hm2 : K ≤ m := by omega
  obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty hnt
  obtain ⟨bm, em⟩ := field_empty_total ops S lmeet (o₁ && o₂)
  obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty hnt
  obtain ⟨bd, ed⟩ := field_empty_total ops S ldiff (o₁ && !o₂)
  have semMeet := fieldSem_meet (t := meet) (esem.inter hty hnt hm2 (hmeet m hm2)) (o₁ := o₁) (o₂ := o₂)
  have semDiff := fieldSem_diff (t := diff) (esem.diff hty hnt hm2 (hdiff m hm2)) (o₁ := o₁) (o₂ := o₂)
  have emptyMeet := field_empty_sem ops dops esem lmeet hS hm2 (em m hm2)
  have emptyDiff := field_empty_sem ops dops esem ldiff hS hm2 (ed m hm2)
  have unfold10 :
      Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) (.tuple #[ty, boolAtom o₁])
        (.tuple #[nt, boolAtom o₂]) (fieldsTerm t₁) t₂ tag ntag (fieldsTerm acc) (Term.list negs) (.map S) =
      if bm then Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag
        (fieldsTerm (acc.reverse ++ (Term.atom a, Term.tuple #[ty, boolAtom o₁]) :: t₁)) (Term.list negs) (Term.map S)
      else if bd then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm t₁) t₂ tag ntag
        (fieldsTerm ((.atom a, .tuple #[meet, boolAtom (o₁ && o₂)]) :: acc)) (Term.list negs) (.map S)
      else Lynx.Except.andAlso (Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag
          (fieldsTerm (acc.reverse ++ (Term.atom a, Term.tuple #[diff, boolAtom (o₁ && !o₂)]) :: t₁)) (Term.list negs) (Term.map S))
        (Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm t₁) t₂ tag ntag
          (fieldsTerm ((.atom a, .tuple #[meet, boolAtom (o₁ && o₂)]) :: acc)) (Term.list negs) (.map S)) Bool.true := by
    have e₁ := em m hm2
    have e₂ := ed m hm2
    have i₁ := hmeet m hm2
    have d₁ := hdiff m hm2
    have revD := reverse_fields acc ((.atom a, .tuple #[diff, boolAtom (o₁ && !o₂)]) :: t₁)
    have revT := reverse_fields acc ((.atom a, .tuple #[ty, boolAtom o₁]) :: t₁)
    simp only [fieldsTerm_cons] at revD revT ⊢
    rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/10».eq_def]
    cases bm <;> cases bd <;> simp [e₁, e₂, i₁, d₁, revD, revT, isMember]
  rw [unfold10]
  cases bm
  · have recMeet : MeetVal (Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm t₁) t₂ tag ntag
        (fieldsTerm ((.atom a, .tuple #[meet, boolAtom (o₁ && o₂)]) :: acc)) (Term.list negs) (.map S)) disj := by
      refine rec _ ⟨meet, _, rfl, lmeet⟩ ?_ semMeet
      exact Classical.byContradiction fun none => by
        have := emptyMeet.mpr fun o h => none ⟨o, h⟩
        cases this
    cases bd
    · simp only [Bool.false_eq_true, ite_false]
      have nonDiff : ∃ o, FieldSem den (.tuple #[diff, boolAtom (o₁ && !o₂)]) o :=
        Classical.byContradiction fun none => by
          have := emptyDiff.mpr fun o h => none ⟨o, h⟩
          cases this
      have lineDiff := line _ (fieldsV_mid sorted ⟨diff, _, rfl, ldiff⟩) (inhabited_mid inh nonDiff) fun w hw => by
        have hwa : FieldSem den (.tuple #[diff, boolAtom (o₁ && !o₂)]) (w (.atom a)) := by
          have := hw a
          unfold FSem TagSem at this
          rw [lookup_append, fresh] at this
          simpa [lookup_cons_atom] using this
        exact H w (msem_mono fresh (fun o h => ((semDiff o).mp h).1) hw) ((semDiff (w (.atom a))).mp hwa).2
      rw [lineDiff]
      rcases recMeet with r | ⟨d, r⟩
      · left; simp [r, Lynx.Except.andAlso]
      · right; exact ⟨d, by simp [r, Lynx.Except.andAlso]⟩
    · simpa using recMeet
  · left
    simp only [ite_true]
    refine line _ sorted inh fun w hw => H w hw fun h₂ => ?_
    have hwa : FieldSem den (.tuple #[ty, boolAtom o₁]) (w (.atom a)) := by
      have := hw a
      unfold FSem TagSem at this
      rw [lookup_append, fresh] at this
      simpa [lookup_cons_atom] using this
    simp at emptyMeet
    exact emptyMeet (w (.atom a)) ((semMeet (w (.atom a))).mpr ⟨hwa, h₂⟩)

theorem cmp_lt_ne {x y : Term} (h : Term.compare (Term.fuel x y) x y = .lt) : x ≠ y := by
  rintro rfl
  have := Lynx.Term.compare_self x
  rw [h] at this
  cases this

theorem cmp_lt_trans {x y z : Term} (h₁ : Term.compare (Term.fuel x y) x y = .lt) (h₂ : Term.compare (Term.fuel y z) y z = .lt) :
    Term.compare (Term.fuel x z) x z = .lt := Lynx.Term.compare_lt_trans h₁ h₂

theorem lookup_below {A : List (Term × Term)} {a : String} (h : ∀ e ∈ A, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    mapLookup A (.atom a) = Option.none :=
  lookup_none fun e he => cmp_lt_ne (h e he)

theorem lookup_above {A : List (Term × Term)} {a : String} (h : ∀ e ∈ A, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt) :
    mapLookup A (.atom a) = Option.none :=
  lookup_none fun e he eq => cmp_lt_ne (h e he) eq.symm

/-- The default field of a tag at a key outside a map literal adds nothing. -/
theorem msem_defaultV (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {tag : Term}
    (g : TagV E tag) {a : String} {A B : List (Term × Term)} (hB : mapLookup B (.atom a) = Option.none) (w : (MW V)) :
    MSem den tag (A ++ (Term.atom a, tagField tag) :: B) w ↔ MSem den tag (A ++ B) w := by
  refine msem_congr fun s => ?_
  unfold FSem
  rw [lookup_append, lookup_append]
  cases e : mapLookup A (.atom s) with
  | some x => simp
  | none =>
    simp only [Option.none_or]
    rw [lookup_cons_atom]
    by_cases as : a = s
    · subst as; simp [hB, fieldSem_tagV ops dops esem g]
    · simp [as]

theorem fieldsV_insert {A B : List (Term × Term)} {k g : Term} (h : FieldsV E (A ++ B))
    (hA : ∀ e ∈ A, Term.compare (Term.fuel e.1 k) e.1 k = .lt) (hB : ∀ e ∈ B, Term.compare (Term.fuel k e.1) k e.1 = .lt) (hk : ∃ s : String, k = .atom s)
    (hg : FieldValue E g) : FieldsV E (A ++ (k, g) :: B) := by
  obtain ⟨he, hp⟩ := h
  refine ⟨fun e me => ?_, ?_⟩
  · rcases List.mem_append.mp me with me | me
    · exact he e (List.mem_append_left _ me)
    · rcases List.mem_cons.mp me with rfl | me
      · exact ⟨hk, hg⟩
      · exact he e (List.mem_append_right _ me)
  · rw [List.pairwise_append] at hp
    rw [List.pairwise_append, List.pairwise_cons]
    obtain ⟨pA, pB, cross⟩ := hp
    refine ⟨pA, ⟨hB, pB⟩, fun a ma b mb => ?_⟩
    rcases List.mem_cons.mp mb with rfl | mb
    · exact hA a ma
    · exact cross a ma b mb

theorem fieldsV_tail {x : Term × Term} {l : List (Term × Term)} (h : FieldsV E (x :: l)) : FieldsV E l :=
  ⟨fun e me => h.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp h.2).2⟩

theorem fieldsV_head {x : Term × Term} {l : List (Term × Term)} (h : FieldsV E (x :: l)) :
    ∀ e ∈ l, Term.compare (Term.fuel x.1 e.1) x.1 e.1 = .lt := (List.pairwise_cons.mp h.2).1

theorem fieldsV_suffix {A B : List (Term × Term)} (h : FieldsV E (A ++ B)) : FieldsV E B :=
  ⟨fun e me => h.1 e (List.mem_append_right _ me), (List.pairwise_append.mp h.2).2.1⟩

theorem fieldsV_cons {k f : Term} {l : List (Term × Term)} (hk : ∃ s : String, k = .atom s) (hf : FieldValue E f)
    (hl : FieldsV E l) (lt : ∀ e ∈ l, Term.compare (Term.fuel k e.1) k e.1 = .lt) : FieldsV E ((k, f) :: l) := by
  refine ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨lt, hl.2⟩⟩
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨hk, hf⟩
  · exact hl.1 e me

theorem lookup_of_mem : ∀ {l : List (Term × Term)}, FieldsV E l → ∀ {e : Term × Term} {s : String}, e ∈ l →
    e.1 = .atom s → mapLookup l (.atom s) = some e.2
  | [], _, _, _, me, _ => by simp at me
  | x :: xs, sl, e, s, me, ek => by
    obtain ⟨a, ha⟩ := (sl.1 x List.mem_cons_self).1
    obtain ⟨k, f⟩ := x
    simp only at ha
    subst ha
    rcases List.mem_cons.mp me with rfl | me
    · simp only at ek
      simp [lookup_cons_atom, (Term.atom.inj ek)]
    · have lt := fieldsV_head sl e me
      rw [ek] at lt
      have ne : a ≠ s := fun h => by subst h; exact cmp_lt_ne lt rfl
      rw [lookup_cons_atom, ite_eq_right ne]
      exact lookup_of_mem (fieldsV_tail sl) me ek

/-- `orddict:store/3` on sorted fields sets the field of a key. -/
theorem store_val (a : String) {f : Term} (hf : FieldValue E f) :
    ∀ {l : List (Term × Term)}, FieldsV E l → ∃ l', Erlang.orddict.«store/3» (.atom a) f (fieldsTerm l) = .ok (fieldsTerm l') ∧
      FieldsV E l' ∧ (∀ e ∈ l', e = (.atom a, f) ∨ e ∈ l) ∧
      ∀ s, mapLookup l' (.atom s) = if a = s then some f else mapLookup l (.atom s)
  | [], _ => by
    refine ⟨[(.atom a, f)], ?_, fieldsV_cons ⟨a, rfl⟩ hf ⟨by simp, by simp⟩ (by simp), by simp, fun s => ?_⟩
    · rw [Erlang.orddict.«store/3».eq_def]; simp [fieldsTerm, Term.list]
    · by_cases e : a = s
      · subst e; simp [lookup_cons_atom]
      · rw [lookup_cons_atom, ite_eq_right e]
  | (k, v) :: t, sl => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have hv := (sl.1 _ List.mem_cons_self).2
    have st := fieldsV_tail sl
    have hd := fieldsV_head sl
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · refine ⟨(.atom a, f) :: (.atom b, v) :: t, ?_, fieldsV_cons ⟨a, rfl⟩ hf sl fun e me => ?_,
        fun e me => ?_, fun s => ?_⟩
      · rw [Erlang.orddict.«store/3».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
      · rcases List.mem_cons.mp me with rfl | me
        · exact cmp
        · exact cmp_lt_trans cmp (hd e me)
      · rcases List.mem_cons.mp me with rfl | me
        · exact Or.inl rfl
        · exact Or.inr me
      · by_cases e : a = s
        · subst e; simp [lookup_cons_atom]
        · rw [lookup_cons_atom, ite_eq_right e]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      refine ⟨(.atom a, f) :: t, ?_, fieldsV_cons ⟨a, rfl⟩ hf st hd, fun e me => ?_, fun s => ?_⟩
      · rw [Erlang.orddict.«store/3».eq_def]
        have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
        have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
      · rcases List.mem_cons.mp me with rfl | me
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem _ me)
      · by_cases e : a = s
        · subst e; simp [lookup_cons_atom]
        · simp [lookup_cons_atom, e]
    · obtain ⟨l', run, sl', mem, look⟩ := store_val a hf st
      have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
      refine ⟨(.atom b, v) :: l', ?_, fieldsV_cons ⟨b, rfl⟩ hv sl' fun e me => ?_, fun e me => ?_, fun s => ?_⟩
      · rw [Erlang.orddict.«store/3».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
        simp [run]
      · rcases mem e me with rfl | me
        · exact cmp'
        · exact hd e me
      · rcases List.mem_cons.mp me with rfl | me
        · exact Or.inr List.mem_cons_self
        · rcases mem e me with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · rw [lookup_cons_atom, lookup_cons_atom, look s]
        by_cases e : a = s
        · subst e
          have : b ≠ a := fun h => by subst h; exact cmp_lt_ne cmp' rfl
          simp [this]
        · simp [e]

theorem inhabited_insert {A B : List (Term × Term)} {k g : Term} (h : Inhabited den (A ++ B)) (hg : ∃ o, FieldSem den g o) :
    Inhabited den (A ++ (k, g) :: B) := by
  intro e me
  rcases List.mem_append.mp me with me | me
  · exact h e (List.mem_append_left _ me)
  · rcases List.mem_cons.mp me with rfl | me
    · exact hg
    · exact h e (List.mem_append_right _ me)

theorem lookup_head {A : List (Term × Term)} {a : String} {f : Term} {B : List (Term × Term)}
    (hA : mapLookup A (Term.atom a) = Option.none) : mapLookup (A ++ (Term.atom a, f) :: B) (Term.atom a) = some f := by
  rw [lookup_append, hA, lookup_cons_atom]; simp

/-- `map_line_meet_empty?/7` covers the line minus the negated literal, field by field, or throws `:closed`
when the line and the literal are disjoint. -/
theorem meet_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) (tag ntag : Term)
    (gt : TagV E tag) (gn : TagV E ntag) (negs : List Term)
    (line : ∀ l, FieldsV E l → Inhabited den l → (∀ w, MSem den tag l w → CovM den negs w) →
      Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
        .ok (.atom "true"))
    (fields nfields : List (Term × Term)) (sf : FieldsV E fields) (snf : FieldsV E nfields) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
    ∀ (P pre acc : List (Term × Term)), fields = P ++ l₁ → nfields = pre ++ l₂ →
      FieldsV E (acc.reverse ++ l₁) → Inhabited den (acc.reverse ++ l₁) →
      (∀ a ∈ P ++ pre ++ acc, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) →
      (∀ w, MSem den tag (acc.reverse ++ l₁) w → ¬MSem den ntag nfields w → CovM den negs w) →
      MeetVal (Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag
        ntag (fieldsTerm acc) (Term.list negs) (.map S)) (∀ w, MSem den tag fields w → ¬MSem den ntag nfields w) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size P pre acc _ _ _ _ _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    left
    rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
    simp [fieldsTerm, Term.list]
  | succ N ih =>
    intro l₁ l₂ size P pre acc hP hpre sacc iacc below H
    have s₁ : FieldsV E l₁ := by rw [hP] at sf; exact fieldsV_suffix sf
    have s₂ : FieldsV E l₂ := by rw [hpre] at snf; exact fieldsV_suffix snf
    have accBelow : ∀ e ∈ acc.reverse, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel e.1 b.1) e.1 b.1 = .lt := fun e me b mb =>
      below e (by simp at me ⊢; simp [me]) b mb
    have preBelow : ∀ e ∈ pre, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel e.1 b.1) e.1 b.1 = .lt := fun e me b mb =>
      below e (by simp [me]) b mb
    have PBelow : ∀ e ∈ P, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel e.1 b.1) e.1 b.1 = .lt := fun e me b mb =>
      below e (by simp [me]) b mb
    -- the key only in the positive map
    have posStep : ∀ (a : String) (f₁ : Term) (xs : List (Term × Term)), l₁ = (.atom a, f₁) :: xs →
        (∀ y ∈ l₂, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt) →
        MeetVal (Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) f₁ (tagField ntag)
          (fieldsTerm xs) (fieldsTerm l₂) tag ntag (fieldsTerm acc) (Term.list negs) (.map S))
          (∀ w, MSem den tag fields w → ¬MSem den ntag nfields w) := by
      intro a f₁ xs e₁ above
      subst e₁
      have mem₁ : (Term.atom a, f₁) ∈ (Term.atom a, f₁) :: xs ++ l₂ := by simp
      have fresh : mapLookup acc.reverse (.atom a) = Option.none :=
        lookup_below fun e me => accBelow e me _ mem₁
      have nnone : mapLookup nfields (.atom a) = Option.none := by
        rw [hpre, lookup_append, lookup_below fun e me => preBelow e me _ mem₁, lookup_above above]; rfl
      refine meet_field_val ops dops esem hm hS tag ntag negs tag a f₁ (tagField ntag)
        (s₁.1 _ List.mem_cons_self).2 (tagFieldV_value ops gn) (fieldsTerm l₂) xs acc sacc iacc fresh line
        (fun w hw hn => H w hw fun hneg => hn ?_) fun f hf _ sem => ?_
      · have := hneg a
        unfold FSem at this
        rw [nnone] at this
        exact (fieldSem_tagV ops dops esem gn _).mpr this
      · refine ih xs l₂ (by simp at size; omega) (P ++ [(Term.atom a, f₁)]) pre ((Term.atom a, f) :: acc)
          (by rw [hP]; simp) hpre (by simpa using fieldsV_mid sacc hf)
          (by simpa using inhabited_mid iacc ‹∃ o, FieldSem den f o›) (fun x mx y my => ?_) (fun w hw hn => ?_)
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mx my
          have head := fieldsV_head s₁
          rcases mx with ((mx | rfl) | mx) | (rfl | mx)
          · exact PBelow x mx y (by rcases my with my | my <;> simp [my])
          · rcases my with my | my
            · exact head y my
            · exact above y my
          · exact preBelow x mx y (by rcases my with my | my <;> simp [my])
          · rcases my with my | my
            · exact head y my
            · exact above y my
          · exact accBelow x (by simpa using mx) y (by rcases my with my | my <;> simp [my])
        · refine H w ?_ hn
          have hw' : MSem den tag (acc.reverse ++ (Term.atom a, f) :: xs) w := by simpa using hw
          exact msem_mono fresh (fun o h => ((sem o).mp h).1) hw'
    -- the key only in the negative map
    have negStep : ∀ (b : String) (f₂ : Term) (ys : List (Term × Term)), l₂ = (.atom b, f₂) :: ys →
        (∀ y ∈ l₁, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt) →
        MeetVal (Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField tag) f₂
          (fieldsTerm l₁) (fieldsTerm ys) tag ntag (fieldsTerm acc) (Term.list negs) (.map S))
          (∀ w, MSem den tag fields w → ¬MSem den ntag nfields w) := by
      intro b f₂ ys e₂ above
      subst e₂
      have mem₂ : (Term.atom b, f₂) ∈ l₁ ++ (Term.atom b, f₂) :: ys := by simp
      have fresh : mapLookup acc.reverse (.atom b) = Option.none :=
        lookup_below fun e me => accBelow e me _ mem₂
      have none₁ : mapLookup l₁ (.atom b) = Option.none := lookup_above above
      have nsome : mapLookup nfields (.atom b) = some f₂ := by
        rw [hpre]; exact lookup_head (lookup_below fun e me => preBelow e me _ mem₂)
      have sorted : FieldsV E (acc.reverse ++ (Term.atom b, tagField tag) :: l₁) :=
        fieldsV_insert sacc (fun e me => accBelow e me _ mem₂) above ⟨b, rfl⟩ (tagFieldV_value ops gt)
      have inh : Inhabited den (acc.reverse ++ (Term.atom b, tagField tag) :: l₁) := inhabited_insert iacc
        ⟨Option.none, (fieldSem_tagV ops dops esem gt _).mpr (tagSem_none _ _)⟩
      refine meet_field_val ops dops esem hm hS tag ntag negs tag b (tagField tag) f₂
        (tagFieldV_value ops gt) (s₂.1 _ List.mem_cons_self).2 (fieldsTerm ys) l₁ acc sorted inh fresh line
        (fun w hw hn => H w ((msem_defaultV ops dops esem gt none₁ w).mp hw) fun hneg => hn ?_) fun f hf inhf sem => ?_
      · have := hneg b
        unfold FSem TagSem at this
        rw [nsome] at this
        exact this
      · refine ih l₁ ys (by simp at size; omega) P (pre ++ [(Term.atom b, f₂)]) ((Term.atom b, f) :: acc)
          hP (by rw [hpre]; simp) (by simpa using fieldsV_mid sorted hf)
          (by simpa using inhabited_mid inh inhf) (fun x mx y my => ?_) (fun w hw hn => ?_)
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mx my
          have head := fieldsV_head s₂
          rcases mx with ((mx | mx | rfl) | rfl | mx)
          · exact PBelow x mx y (by rcases my with my | my <;> simp [my])
          · exact preBelow x mx y (by rcases my with my | my <;> simp [my])
          · rcases my with my | my
            · exact above y my
            · exact head y my
          · rcases my with my | my
            · exact above y my
            · exact head y my
          · exact accBelow x (by simpa using mx) y (by rcases my with my | my <;> simp [my])
        · refine H w ((msem_defaultV ops dops esem gt none₁ w).mp ?_) hn
          have hw' : MSem den tag (acc.reverse ++ (Term.atom b, f) :: l₁) w := by simpa using hw
          exact msem_mono fresh (fun o h => ((sem o).mp h).1) hw'
    have key₁ : ∀ x ∈ l₁, ∃ a : String, x.1 = .atom a := fun x mx => (s₁.1 x mx).1
    have key₂ : ∀ x ∈ l₂, ∃ a : String, x.1 = .atom a := fun x mx => (s₂.1 x mx).1
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil =>
        left
        rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
        simp [fieldsTerm, Term.list]
      | cons y ys =>
        obtain ⟨k₂, f₂⟩ := y
        obtain ⟨b, rfl⟩ := key₂ _ List.mem_cons_self
        have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm [])
            (fieldsTerm ((.atom b, f₂) :: ys)) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) =
            Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField tag) f₂
              (fieldsTerm []) (fieldsTerm ys) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
          rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, key_tag_field gt]
        rw [e]
        exact negStep b f₂ ys rfl (by simp)
    | cons x xs =>
      obtain ⟨k₁, f₁⟩ := x
      obtain ⟨a, rfl⟩ := key₁ _ List.mem_cons_self
      cases l₂ with
      | nil =>
        have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm ((.atom a, f₁) :: xs))
            (fieldsTerm []) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) =
            Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) f₁ (tagField ntag)
              (fieldsTerm xs) (fieldsTerm []) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
          rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, key_tag_field gn]
        rw [e]
        exact posStep a f₁ xs rfl (by simp)
      | cons y ys =>
        obtain ⟨k₂, f₂⟩ := y
        obtain ⟨b, rfl⟩ := key₂ _ List.mem_cons_self
        obtain ⟨t₁, o₁, rfl, ht₁⟩ := (s₁.1 _ List.mem_cons_self).2
        obtain ⟨t₂, o₂, rfl, ht₂⟩ := (s₂.1 _ List.mem_cons_self).2
        have head₁ := fieldsV_head s₁
        have head₂ := fieldsV_head s₂
        simp only [List.length_cons] at size
        rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
        · have above : ∀ y ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
            intro y my
            rcases List.mem_cons.mp my with rfl | my
            · exact cmp
            · exact cmp_lt_trans cmp (head₂ y my)
          by_cases no : ntag = .atom "open"
          · subst no
            have r := ih xs _ (by simp; omega) (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) pre
              ((.atom a, .tuple #[t₁, boolAtom o₁]) :: acc) (by rw [hP]; simp) hpre (by simpa using sacc)
              (by simpa using iacc) (fun x mx y my => ?_) (fun w hw hn => H w (by simpa using hw) hn)
            · have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                  (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                  (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "open") (fieldsTerm acc)
                  (Term.list negs) (.map S) =
                  Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm xs)
                  (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "open")
                  (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: acc)) (Term.list negs) (.map S) := by
                rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
                simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp]
              rw [e]; exact r
            · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mx my
              rcases mx with ((mx | rfl) | mx) | mx
              · exact PBelow x mx y (by rcases my with my | my <;> simp [my])
              · rcases my with my | my
                · exact head₁ y my
                · exact above y (by simpa using my)
              · exact preBelow x mx y (by rcases my with my | my <;> simp [my])
              · rcases mx with rfl | mx
                · rcases my with my | my
                  · exact head₁ y my
                  · exact above y (by simpa using my)
                · exact accBelow x (by simpa using mx) y (by rcases my with my | my <;> simp [my])
          by_cases nc : ntag = .atom "closed"
          · subst nc
            cases o₁
            · right
              refine ⟨fun w hw hn => ?_, ?_⟩
              · have mem₁ : (Term.atom a, Term.tuple #[t₁, boolAtom Bool.false]) ∈
                    (Term.atom a, Term.tuple #[t₁, boolAtom Bool.false]) :: xs ++
                      (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys := by simp
                have fsome : mapLookup fields (.atom a) = some (.tuple #[t₁, boolAtom Bool.false]) := by
                  rw [hP]; exact lookup_head (lookup_below fun e me => PBelow e me _ mem₁)
                have nnone : mapLookup nfields (.atom a) = Option.none := by
                  rw [hpre, lookup_append, lookup_below fun e me => preBelow e me _ mem₁, lookup_above above]; rfl
                have h₁ := hw a
                have h₂ := hn a
                unfold FSem TagSem at h₁ h₂
                rw [fsome] at h₁
                rw [nnone] at h₂
                dsimp only at h₁ h₂
                rw [fieldSem_mk] at h₁
                rcases h₁ with ⟨-, h⟩ | ⟨x, hx, -⟩
                · cases h
                · simp [hx] at h₂
              · rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
                simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
                  Lynx.Except.andAlso, Erlang.erlang.«not/1»]
            · have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                  (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom Bool.true]) :: xs))
                  (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "closed") (fieldsTerm acc)
                  (Term.list negs) (.map S) =
                  Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) (.tuple #[t₁, boolAtom Bool.true])
                    (tagField (.atom "closed")) (fieldsTerm xs) (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys))
                    tag (.atom "closed") (fieldsTerm acc) (Term.list negs) (.map S) := by
                rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
                simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
                  Lynx.Except.andAlso, Erlang.erlang.«not/1», tag_field, tagField, tagType]
              rw [e]
              exact posStep a _ xs rfl above
          · have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (fieldsTerm acc)
                (Term.list negs) (.map S) =
                Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) (.tuple #[t₁, boolAtom o₁])
                  (tagField ntag) (fieldsTerm xs) (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys))
                  tag ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, tag_eq_false no,
                tag_eq_false nc, Lynx.Except.andAlso, key_tag_field gn]
            rw [e]
            exact posStep a _ xs rfl above
        · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
          subst ab
          have mem₁ : (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++
              (Term.atom a, Term.tuple #[t₂, boolAtom o₂]) :: ys := by simp
          have mem₂ : (Term.atom a, Term.tuple #[t₂, boolAtom o₂]) ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++
              (Term.atom a, Term.tuple #[t₂, boolAtom o₂]) :: ys := by simp
          have fresh : mapLookup acc.reverse (.atom a) = Option.none := lookup_below fun e me => accBelow e me _ mem₁
          have nsome : mapLookup nfields (.atom a) = some (.tuple #[t₂, boolAtom o₂]) := by
            rw [hpre]; exact lookup_head (lookup_below fun e me => preBelow e me _ mem₂)
          have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
              (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
              (fieldsTerm ((.atom a, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (fieldsTerm acc)
              (Term.list negs) (.map S) =
              Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) (.tuple #[t₁, boolAtom o₁])
                (.tuple #[t₂, boolAtom o₂]) (fieldsTerm xs) (fieldsTerm ys) tag ntag (fieldsTerm acc)
                (Term.list negs) (.map S) := by
            rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
            have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
            have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2»,
              Erlang.erlang.«>/2»]
          rw [e]
          refine meet_field_val ops dops esem hm hS tag ntag negs tag a _ _ ⟨t₁, o₁, rfl, ht₁⟩ ⟨t₂, o₂, rfl, ht₂⟩
            (fieldsTerm ys) xs acc sacc iacc fresh line (fun w hw hn => H w hw fun hneg => hn ?_)
            fun f hf inhf sem => ?_
          · have := hneg a; unfold FSem TagSem at this; rw [nsome] at this; exact this
          · refine ih xs ys (by omega) (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])])
              (pre ++ [(Term.atom a, Term.tuple #[t₂, boolAtom o₂])]) ((Term.atom a, f) :: acc) (by rw [hP]; simp)
              (by rw [hpre]; simp) (by simpa using fieldsV_mid sacc hf) (by simpa using inhabited_mid iacc inhf)
              (fun x mx y my => ?_) (fun w hw hn => ?_)
            · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mx my
              have hy : y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++
                  (Term.atom a, Term.tuple #[t₂, boolAtom o₂]) :: ys := by rcases my with my | my <;> simp [my]
              have kx : ∀ y, y ∈ xs ∨ y ∈ ys → Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := fun y my => by
                rcases my with my | my
                · exact head₁ y my
                · exact head₂ y my
              rcases mx with (((mx | rfl) | mx | rfl) | rfl | mx)
              · exact PBelow x mx y hy
              · exact kx y my
              · exact preBelow x mx y hy
              · exact kx y my
              · exact kx y my
              · exact accBelow x (by simpa using mx) y hy
            · have hw' : MSem den tag (acc.reverse ++ (Term.atom a, f) :: xs) w := by simpa using hw
              exact H w (msem_mono fresh (fun o h => ((sem o).mp h).1) hw') hn
        · have lt : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
          have above : ∀ y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
            intro y my
            rcases List.mem_cons.mp my with rfl | my
            · exact lt
            · exact cmp_lt_trans lt (head₁ y my)
          by_cases tc : tag = .atom "closed"
          · subst tc
            cases o₂
            · right
              refine ⟨fun w hw hn => ?_, ?_⟩
              · have mem₂ : (Term.atom b, Term.tuple #[t₂, boolAtom Bool.false]) ∈
                    (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++
                      (Term.atom b, Term.tuple #[t₂, boolAtom Bool.false]) :: ys := by simp
                have fnone : mapLookup fields (.atom b) = Option.none := by
                  rw [hP, lookup_append, lookup_below fun e me => PBelow e me _ mem₂, lookup_above above]; rfl
                have nsome : mapLookup nfields (.atom b) = some (.tuple #[t₂, boolAtom Bool.false]) := by
                  rw [hpre]; exact lookup_head (lookup_below fun e me => preBelow e me _ mem₂)
                have h₁ := hw b
                have h₂ := hn b
                unfold FSem TagSem at h₁ h₂
                rw [fnone] at h₁
                rw [nsome] at h₂
                dsimp only at h₁ h₂
                rw [fieldSem_mk] at h₂
                rcases h₂ with ⟨-, h⟩ | ⟨x, hx, -⟩
                · cases h
                · simp [hx] at h₁
              · rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
                simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
                  Erlang.erlang.«>/2», cmp, boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
            · have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                  (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                  (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom Bool.true]) :: ys)) (.atom "closed") ntag
                  (fieldsTerm acc) (Term.list negs) (.map S) =
                  Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField (.atom "closed"))
                    (.tuple #[t₂, boolAtom Bool.true]) (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                    (fieldsTerm ys) (.atom "closed") ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
                rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
                simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
                  Erlang.erlang.«>/2», cmp, boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1», tag_field, tagField, tagType]
              rw [e]
              exact negStep b _ ys rfl above
          · have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (fieldsTerm acc)
                (Term.list negs) (.map S) =
                Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField tag)
                  (.tuple #[t₂, boolAtom o₂]) (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs)) (fieldsTerm ys)
                  tag ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
              simp only [tag_eq_false tc]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, Lynx.Except.andAlso, key_tag_field gt]
            rw [e]
            exact negStep b _ ys rfl above

/-- Map literals of value maps. -/
def MapLitV (E : Term → Prop) (t : Term) : Prop :=
  ∃ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] ∧
    TagV E tag ∧ FieldsV E l

theorem TagV.atom {tag : String} (g : tag = "open" ∨ tag = "closed") : TagV E (.atom tag) := by
  rcases g with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem TagV.of_atom {tag : String} (g : TagV E (.atom tag)) : tag = "open" ∨ tag = "closed" := by
  rcases g with e | e | ⟨dl, e, -⟩
  · exact Or.inl (Term.atom.inj e)
  · exact Or.inr (Term.atom.inj e)
  · exact absurd e.symm (fieldsTerm_ne_atom dl tag)

theorem MapLitV.atom {k : Int} {tag : String} {l : List (Term × Term)} (g : tag = "open" ∨ tag = "closed")
    (sl : FieldsV E l) : MapLitV E (.tuple #[.integer k, .atom tag, fieldsTerm l]) :=
  ⟨k, _, l, rfl, TagV.atom g, sl⟩

/-- Literals of value maps are open or closed, or have domains. -/
theorem MapLitV.cases {t : Term} (h : MapLitV E t) :
    (∃ (k : Int) (tag : String) (l : List (Term × Term)), t = .tuple #[.integer k, .atom tag, fieldsTerm l] ∧
      (tag = "open" ∨ tag = "closed") ∧ FieldsV E l) ∨
    ∃ (k : Int) (dl l : List (Term × Term)), t = .tuple #[.integer k, fieldsTerm dl, fieldsTerm l] ∧ DomsV E dl ∧
      FieldsV E l := by
  obtain ⟨k, tag, l, rfl, g, sl⟩ := h
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · exact Or.inl ⟨k, "open", l, rfl, Or.inl rfl, sl⟩
  · exact Or.inl ⟨k, "closed", l, rfl, Or.inr rfl, sl⟩
  · exact Or.inr ⟨k, dl, l, rfl, dv, sl⟩

theorem fieldsTerm_inj : ∀ {l l' : List (Term × Term)}, fieldsTerm l = fieldsTerm l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [fieldsTerm, Term.list] at h
  | _ :: _, [], h => by simp [fieldsTerm, Term.list] at h
  | (a, b) :: l, (a', b') :: l', h => by
    simp only [fieldsTerm_cons, Term.cons.injEq, Term.tuple.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    have e₀ := congrArg (fun a : Array Term => a[0]?) h₁
    have e₁ := congrArg (fun a : Array Term => a[1]?) h₁
    simp at e₀ e₁
    rw [e₀, e₁, fieldsTerm_inj h₂]

theorem nsem_lit {k : Int} {tag : Term} {l : List (Term × Term)} {w : (MW V)} :
    NSem den (.tuple #[.integer k, tag, fieldsTerm l]) w ↔ MSem den tag l w := by
  constructor
  · rintro ⟨k', tag', l', e, h⟩
    simp only [Term.tuple.injEq] at e
    have e₁ := congrArg (fun a : Array Term => a[1]?) e
    have e₂ := congrArg (fun a : Array Term => a[2]?) e
    simp at e₁ e₂
    rw [e₁, fieldsTerm_inj e₂]
    exact h
  · intro h; exact ⟨k, tag, l, rfl, h⟩

/-- The atoms of the kinds of domains, in increasing order. -/
def kindAtoms : List Term := domainKinds.map Term.atom

theorem domainKinds_nodup : domainKinds.Nodup := by decide

theorem kindAtoms_nodup : kindAtoms.Nodup := by
  rw [kindAtoms, List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (List.nodup_iff_pairwise_ne.mp domainKinds_nodup).imp fun ne e => ne (Term.atom.inj e)

open Classical in
theorem nodup_length_le : ∀ {l L : List Term}, l.Nodup → (∀ x ∈ l, x ∈ L) → l.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, L, nd, h => by
    obtain ⟨nx, nxs⟩ := List.nodup_cons.mp nd
    have mx := h x List.mem_cons_self
    have le := nodup_length_le (L := L.eraseP fun z => decide (z = x)) nxs fun y my =>
      (List.mem_eraseP_of_neg (by simpa using fun e : y = x => nx (e ▸ my))).mpr (h y (List.mem_cons_of_mem _ my))
    rw [List.length_eraseP_of_mem mx (by simp)] at le
    have := List.length_pos_of_mem mx
    simp only [List.length_cons]
    omega

open Classical in
theorem nodup_full {l L : List Term} (nd : l.Nodup) (h : ∀ x ∈ l, x ∈ L) (len : L.length ≤ l.length) :
    ∀ y ∈ L, y ∈ l := by
  intro y my
  refine Classical.byContradiction fun ny => ?_
  have le := nodup_length_le (L := L.eraseP fun z => decide (z = y)) nd fun x mx =>
    (List.mem_eraseP_of_neg (by simpa using fun e : x = y => ny (e ▸ mx))).mpr (h x mx)
  rw [List.length_eraseP_of_mem my (by simp)] at le
  have := List.length_pos_of_mem my
  omega

/-- Domains name every kind exactly when they have twelve of them. -/
theorem doms_length {dl : List (Term × Term)} (dv : DomsV E dl) :
    dl.length = 12 ↔ ∀ s ∈ domainKinds, (mapLookup dl (.atom s)).isSome := by
  have nd : (dl.map Prod.fst).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact dv.2.imp fun lt e => by rw [e, compare_self] at lt; cases lt
  have sub : ∀ x ∈ dl.map Prod.fst, x ∈ kindAtoms := fun x mx => by
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨⟨s, es, ms⟩, -⟩ := dv.1 e me
    rw [es]; exact List.mem_map.mpr ⟨s, ms, rfl⟩
  have len : kindAtoms.length = 12 := rfl
  have mem : ∀ s, Term.atom s ∈ dl.map Prod.fst ↔ (mapLookup dl (.atom s)).isSome := fun s => by
    rw [mapLookup_isSome]
    constructor
    · intro m
      obtain ⟨x, mx, ex⟩ := List.mem_map.mp m
      exact ⟨x, mx, by rw [ex]; exact compareExact_self _⟩
    · rintro ⟨x, mx, ex⟩
      exact List.mem_map.mpr ⟨x, mx, (atom_compareExact_eq s x.1).mp ex⟩
  constructor
  · intro l s ms
    exact (mem s).mp (nodup_full nd sub (by simp [len, l]) _ (List.mem_map.mpr ⟨s, ms, rfl⟩))
  · intro all
    have le₁ := nodup_length_le nd sub
    have le₂ := nodup_length_le kindAtoms_nodup fun x mx => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp mx
      exact (mem s).mpr (all s ms)
    simp only [List.length_map, len] at le₁ le₂
    omega

theorem lookup_mem_key {l : List (Term × Term)} {k f : Term} (h : mapLookup l k = some f) :
    ∃ e ∈ l, compareExact (fuel k e.1) k e.1 = .eq ∧ e.2 = f := by
  unfold mapLookup at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩

theorem lookup_of_dom : ∀ {dl : List (Term × Term)}, DomsV E dl → ∀ {e : Term × Term}, e ∈ dl →
    ∃ s, e.1 = .atom s ∧ s ∈ domainKinds ∧ mapLookup dl (.atom s) = some e.2
  | [], _, _, me => by simp at me
  | x :: xs, dv, e, me => by
    obtain ⟨⟨a, ha, ka⟩, -⟩ := dv.1 x List.mem_cons_self
    have tail : DomsV E xs := ⟨fun e me => dv.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp dv.2).2⟩
    obtain ⟨k, f⟩ := x
    simp only at ha
    subst ha
    rcases List.mem_cons.mp me with rfl | me
    · exact ⟨a, rfl, ka, by simp [lookup_cons_atom]⟩
    · obtain ⟨s, es, ks, look⟩ := lookup_of_dom tail me
      have lt := (List.pairwise_cons.mp dv.2).1 e me
      rw [es] at lt
      have ne : a ≠ s := fun h => by subst h; exact cmp_lt_ne lt rfl
      exact ⟨s, es, ks, by rw [lookup_cons_atom, ite_eq_right ne]; exact look⟩

/-- Domains allow at a kind what its domain type holds, if any. -/
theorem tagSem_dom_iff (hnone : ∀ v, ¬den (.map []) v) (dl : List (Term × Term)) (s : String) (o : Option V) :
    TagSem den (fieldsTerm dl) s o ↔
      o = Option.none ∨ ∃ v T, o = some v ∧ mapLookup dl (.atom s) = some T ∧ den T v := by
  rw [tagSem_dom, show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]
  cases h : mapLookup dl (.atom s) <;> cases o <;> simp [hnone]

/-- The domains of a tag fit within those of another at the keys of every kind. -/
def TagIncl (den : Term → V → Prop) (tag ntag : Term) : Prop :=
  ∀ s ∈ domainKinds, ∀ o, TagSem den tag s o → TagSem den ntag s o

/-- `lists:all/2` of a closure that decides a property of every element. -/
theorem all_sem {K' : Nat} (mo nm : String) (caps : Array Term) (l : List Term) {m : Nat} (hm : K' + 1 ≤ m)
    (P : Term → Prop) (body : Nat → Term → Except Exception Term)
    (call : ∀ m x, Lynx.Dispatcher.pure (D (m + 1)) (.function mo nm 1 caps) #[x] = body m x)
    (each : ∀ x ∈ l, ∃ b : Bool, (∀ m, K' ≤ m → body m x = .ok (boolAtom b)) ∧ (b = Bool.true ↔ P x)) :
    ∃ b : Bool, Erlang.lists.«all/2» (D m) (.function mo nm 1 caps) (Term.list l) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∀ x ∈ l, P x) := by
  classical
  let res : Term → Bool := fun x => if h : x ∈ l then Classical.choose (each x h) else Bool.false
  have hres : ∀ x (mx : x ∈ l), res x = Classical.choose (each x mx) := fun x mx => by simp only [res, dite_eq_left mx]
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  refine ⟨l.all res, all_list _ _ _ _ res l fun x mx => ?_, ?_⟩
  · rw [call n x, hres x mx]
    exact (Classical.choose_spec (each x mx)).1 n hn
  · rw [List.all_eq_true]
    constructor
    · intro h x mx
      have := h x mx
      rw [hres x mx] at this
      exact (Classical.choose_spec (each x mx)).2.mp this
    · intro h x mx
      rw [hres x mx]
      exact (Classical.choose_spec (each x mx)).2.mpr (h x mx)

/-- `subtype_seen?/3` decides inclusion on element types. -/
theorem sub_sem (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {a b : Term} (ha : E a) (hb : E b) :
    ∃ s : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«subtype_seen?/3» (D m) a b (.map S) = .ok (boolAtom s)) ∧
      (s = Bool.true ↔ ∀ v, den a v → den b v) := by
  obtain ⟨c, hc, run⟩ := dops.diff ha hb
  obtain ⟨s, hs⟩ := ops.empty hc S
  refine ⟨s, fun m' hm' => by simp [Elixir.Module.Types.Descr.«subtype_seen?/3», run m' hm', hs m' hm'], ?_⟩
  rw [esem.empty hc hS hm (hs m hm)]
  constructor
  · intro h v hv
    exact Classical.byContradiction fun nb => h v ((esem.diff ha hb hm (run m hm) v).mpr ⟨hv, nb⟩)
  · intro h v hv
    have := (esem.diff ha hb hm (run m hm) v).mp hv
    exact this.2 (h v this.1)

theorem tagSem_closed {kind : String} {o : Option V} : TagSem den (.atom "closed") kind o ↔ o = Option.none := by
  simp [TagSem]

/-- `map_check_domain_keys?/3` decides whether the domains of a literal fit within those of a negated one, except
for open literals and closed negations, which `map_line_empty?/4` skips before. -/
theorem check_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gt : TagV E tag) (gn : TagV E ntag)
    (skip : ¬(tag = .atom "open" ∧ ntag = .atom "closed")) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«map_check_domain_keys?/3» (D m) tag ntag (.map S) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ TagIncl den tag ntag) := by
  obtain ⟨v₀⟩ := esem.inhabited
  have hm' : K ≤ m := by omega
  by_cases tc : tag = .atom "closed"
  · subst tc
    refine ⟨Bool.true, by rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]; rfl, ?_⟩
    simp only [true_iff]
    intro s _ o h
    rw [tagSem_closed.mp h]
    exact tagSem_none _ _
  by_cases no : ntag = .atom "open"
  · subst no
    refine ⟨Bool.true, by
      rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]; split <;> simp_all [boolAtom], ?_⟩
    simp only [true_iff]
    intro s _ o _
    exact Or.inl rfl
  have hnone := (sem_none ops dops esem).2
  -- subtype answers on domain types, run by the closures of `map_check_domain_keys?/3`
  rcases gt with rfl | rfl | ⟨dl, rfl, dv⟩
  · rcases gn with rfl | rfl | ⟨nl, rfl, nv⟩
    · exact absurd rfl no
    · exact absurd ⟨rfl, rfl⟩ skip
    · obtain ⟨b, run, sem⟩ := all_sem (K' := K) "Elixir.Module.Types.Descr" "-map_check_domain_keys?/3-fun-0-"
        #[.map S] (nl.map fun e => .tuple #[e.1, e.2]) hm (fun x => ∀ e ∈ nl, x = .tuple #[e.1, e.2] → ∀ v, den e.2 v)
        (fun m x => Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-0-/2» (D m) (.map S) x)
        (fun m x => by simp)
        (fun x mx => by
          obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
          obtain ⟨b, run, sem⟩ := sub_sem ops dops esem hm' hS ops.term (nv.1 e me).2
          refine ⟨b, fun m hm => by simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-0-/2», run m hm], ?_⟩
          rw [sem]
          constructor
          · intro h e' me' ee v
            simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at ee
            rw [← ee.2]; exact h v (esem.term v)
          · intro h v _; exact h e me rfl v)
      refine ⟨(nl.length == 12) && b, ?_, ?_⟩
      · have ne := fieldsTerm_ne_atom nl
        have len : Erlang.erlang.«length/1» (fieldsTerm nl) = .ok (.integer nl.length) := by
          simpa [fieldsTerm] using length_list (nl.map fun e => .tuple #[e.1, e.2])
        have all : Erlang.lists.«all/2» (D m) _ (fieldsTerm nl) = _ := run
        generalize fieldsTerm nl = T at ne len all
        rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
        split
        all_goals first | (exfalso; simp_all; done) | skip
        simp only [len, pure_bind, Lynx.Except.ok_bind]
        by_cases twelve : nl.length = 12
        · simp [twelve, Erlang.erlang.«==/2», Lynx.Except.andAlso, all, Term.true]
        · have : (nl.length : Int) ≠ 12 := by omega
          simp [twelve, this, Erlang.erlang.«==/2», Lynx.Except.andAlso, Term.false, boolAtom]
      · simp only [Bool.and_eq_true, beq_iff_eq, sem, doms_length nv, TagIncl, tagSem_dom_iff hnone]
        constructor
        · rintro ⟨present, all⟩ s ms o _
          rcases o with _ | v
          · exact Or.inl rfl
          · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (present s ms)
            obtain ⟨e, me, rfl⟩ := lookup_mem hT
            exact Or.inr ⟨v, _, rfl, hT, all _ (List.mem_map.mpr ⟨e, me, rfl⟩) e me rfl v⟩
        · intro h
          refine ⟨fun s ms => ?_, fun x mx e me ex v => ?_⟩
          · rcases h s ms (some v₀) (Or.inl rfl) with h | ⟨v, T, -, hT, -⟩
            · cases h
            · rw [hT]; rfl
          · obtain ⟨s, es, ks, look⟩ := lookup_of_dom nv me
            rcases h s ks (some v) (Or.inl rfl) with h | ⟨v', T, ev, hT, hv⟩
            · cases h
            · cases ev; rw [look] at hT; cases hT; exact hv
  · exact absurd rfl tc
  · rcases gn with rfl | rfl | ⟨nl, rfl, nv⟩
    · exact absurd rfl no
    · obtain ⟨b, run, sem⟩ := all_sem (K' := K) "Elixir.Module.Types.Descr" "-map_check_domain_keys?/3-fun-1-"
        #[.map S] (dl.map fun e => .tuple #[e.1, e.2]) hm (fun x => ∀ e ∈ dl, x = .tuple #[e.1, e.2] → ∀ v, ¬den e.2 v)
        (fun m x => Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-1-/2» (D m) (.map S) x)
        (fun m x => by simp)
        (fun x mx => by
          obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
          obtain ⟨b, run⟩ := ops.empty (dv.1 e me).2 S
          refine ⟨b, fun m hm => by simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-1-/2», run m hm], ?_⟩
          rw [esem.empty (dv.1 e me).2 hS hm' (run m hm')]
          constructor
          · intro h e' me' ee
            simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at ee
            rw [← ee.2]; exact h
          · intro h; exact h e me rfl)
      refine ⟨b, ?_, ?_⟩
      · have ne := fieldsTerm_ne_atom dl
        have all : Erlang.lists.«all/2» (D m) _ (fieldsTerm dl) = _ := run
        generalize fieldsTerm dl = T at ne all
        rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
        split <;> simp_all
      · rw [sem]
        simp only [TagIncl, tagSem_dom_iff hnone, tagSem_closed]
        constructor
        · rintro all s ms o (h | ⟨v, T, rfl, hT, hv⟩)
          · exact h
          · obtain ⟨e, me, rfl⟩ := lookup_mem hT
            exact absurd hv (all _ (List.mem_map.mpr ⟨e, me, rfl⟩) e me rfl v)
        · intro h x mx e me ex v hv
          obtain ⟨s, es, ks, look⟩ := lookup_of_dom dv me
          cases h s ks (some v) (Or.inr ⟨v, _, rfl, look, hv⟩)
    · obtain ⟨b, run, sem⟩ := all_sem (K' := K) "Elixir.Module.Types.Descr" "-map_check_domain_keys?/3-fun-2-"
        #[.map S, fieldsTerm nl] (dl.map fun e => .tuple #[e.1, e.2]) hm
        (fun x => ∀ e ∈ dl, x = .tuple #[e.1, e.2] → ∀ v, den e.2 v →
          ∃ T, mapLookup nl e.1 = some T ∧ den T v)
        (fun m x => Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-2-/3» (D m) (.map S) (fieldsTerm nl) x)
        (fun m x => by simp)
        (fun x mx => by
          obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
          obtain ⟨s, es, -, -⟩ := lookup_of_dom dv me
          have find := find_dom s nv
          have he : ∀ e' ∈ dl, Term.tuple #[e.1, e.2] = .tuple #[e'.1, e'.2] → e' = e := fun e' _ ee => by
            simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at ee
            exact Prod.ext ee.1.symm ee.2.symm
          cases look : mapLookup nl (.atom s) with
          | none =>
            obtain ⟨b, run, sem⟩ := sub_sem ops dops esem hm' hS (dv.1 e me).2 ops.none
            refine ⟨b, fun m hm => by
              simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-2-/3», es, find, look, run m hm], ?_⟩
            rw [sem]
            constructor
            · intro h e' me' ee v hv
              obtain rfl := he e' me' ee
              exact absurd (h v hv) (hnone v)
            · intro h v hv
              obtain ⟨T, hT, -⟩ := h e me rfl v hv
              rw [es, look] at hT; cases hT
          | some T =>
            obtain ⟨f, mf, rfl⟩ := lookup_mem look
            obtain ⟨b, run, sem⟩ := sub_sem ops dops esem hm' hS (dv.1 e me).2 (nv.1 f mf).2
            refine ⟨b, fun m hm => by
              simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-2-/3», es, find, look, run m hm], ?_⟩
            rw [sem]
            constructor
            · intro h e' me' ee v hv
              obtain rfl := he e' me' ee
              exact ⟨f.2, by rw [es, look], h v hv⟩
            · intro h v hv
              obtain ⟨T, hT, hv'⟩ := h e me rfl v hv
              rw [es, look] at hT; cases hT; exact hv')
      refine ⟨b, ?_, ?_⟩
      · have ne₁ := fieldsTerm_ne_atom dl
        have ne₂ := fieldsTerm_ne_atom nl
        have all : Erlang.lists.«all/2» (D m) _ (fieldsTerm dl) = _ := run
        generalize fieldsTerm nl = T₂ at ne₂ all
        generalize fieldsTerm dl = T₁ at ne₁ all
        rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
        split <;> simp_all
      · rw [sem]
        simp only [TagIncl, tagSem_dom_iff hnone]
        constructor
        · rintro all s ms o (h | ⟨v, T, rfl, hT, hv⟩)
          · exact Or.inl h
          · obtain ⟨e, me, ek, rfl⟩ := lookup_mem_key hT
            have es : e.1 = .atom s := (atom_compareExact_eq s e.1).mp ek
            obtain ⟨T', hT', hv'⟩ := all _ (List.mem_map.mpr ⟨e, me, rfl⟩) e me rfl v hv
            rw [es] at hT'
            exact Or.inr ⟨v, T', rfl, hT', hv'⟩
        · intro h x mx e me ex v hv
          obtain ⟨s, es, ks, look⟩ := lookup_of_dom dv me
          rcases h s ks (some v) (Or.inr ⟨v, _, rfl, look, hv⟩) with h | ⟨v', T, ev, hT, hv'⟩
          · cases h
          · cases ev; exact ⟨T, by rw [es]; exact hT, hv'⟩

/-- What a literal allows at each key of a map. -/
def KeyAllow (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) : MKey → Option V → Prop
  | .atom s, o => FSem den tag l s o
  | .dom k _, o => TagSem den tag (domKind k) o

theorem msem_keys {tag : Term} {l : List (Term × Term)} {w : MW V} :
    MSem den tag l w ↔ ∀ q, KeyAllow den tag l q (w q) :=
  ⟨fun h q => match q with
    | .atom s => h s
    | .dom k i => h.doms k i,
   fun h => ⟨fun s => h (.atom s), fun k i => h (.dom k i)⟩⟩

/-- Maps outside a negated literal are outside it at some key, whatever they hold at the others. -/
theorem nsem_local {N : Term} {w : MW V} (h : ¬NSem den N w) : ∃ q, ∀ w', w' q = w q → ¬NSem den N w' := by
  by_cases lit : ∃ (k : Int) (tag : Term) (l : List (Term × Term)), N = .tuple #[.integer k, tag, fieldsTerm l]
  · obtain ⟨k, tag, l, rfl⟩ := lit
    rw [nsem_lit, msem_keys] at h
    obtain ⟨q, hq⟩ := Classical.not_forall.mp h
    exact ⟨q, fun w' e hn => hq (e ▸ msem_keys.mp (nsem_lit.mp hn) q)⟩
  · exact ⟨.atom "", fun w' _ ⟨k, tag, l, e, _⟩ => lit ⟨k, tag, l, e⟩⟩

/-- Negated literals that a fresh key escapes can be skipped: the other negations still cover the line. -/
theorem skip_fresh {tag : Term} {l : List (Term × Term)} {N : Term} {rest : List Term}
    (escape : ∀ w (fin : List MKey), MSem den tag l w →
      ∃ w', MSem den tag l w' ∧ ¬NSem den N w' ∧ ∀ q ∈ fin, w' q = w q)
    (cover : ∀ w, MSem den tag l w → CovM den (N :: rest) w) :
    ∀ w, MSem den tag l w → CovM den rest w := by
  intro w hw
  refine Classical.byContradiction fun none => ?_
  have each : ∀ N' ∈ rest, ∃ q, ∀ w', w' q = w q → ¬NSem den N' w' :=
    fun N' mN' => nsem_local fun h => none ⟨N', mN', h⟩
  let qs : List MKey := rest.attach.map fun p => Classical.choose (each p.1 p.2)
  obtain ⟨w', hw', nN, same⟩ := escape w qs hw
  obtain ⟨N', mN', hN'⟩ := cover w' hw'
  rcases List.mem_cons.mp mN' with rfl | mN'
  · exact nN hN'
  · exact Classical.choose_spec (each N' mN') w'
      (same _ (List.mem_map.mpr ⟨⟨N', mN'⟩, List.mem_attach _ _, rfl⟩)) hN'

theorem fresh_nat (ns : List Nat) : ∃ i : Nat, i ∉ ns := by
  have le : ∀ (ns : List Nat), ∀ n ∈ ns, n ≤ ns.sum := by
    intro ns
    induction ns with
    | nil => simp
    | cons x xs ih =>
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · simp
      · have := ih n hn; simp; omega
  exact ⟨ns.sum + 1, fun h => by have := le ns _ h; omega⟩

theorem domKind_of_mem {s : String} (hs : s ∈ domainKinds) (na : s ≠ "atom") : ∃ k, domKind k = s := by
  simp only [domainKinds, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl na
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩

/-- A literal whose domains do not fit within a negated literal escapes it at a fresh key. -/
theorem escape_incl {tag ntag : Term} {l nl : List (Term × Term)} {k : Int} (h : ¬TagIncl den tag ntag) :
    ∀ w (fin : List MKey), MSem den tag l w →
      ∃ w', MSem den tag l w' ∧ ¬NSem den (.tuple #[.integer k, ntag, fieldsTerm nl]) w' ∧ ∀ q ∈ fin, w' q = w q := by
  intro w fin hw
  obtain ⟨s, ms, o, ht, hn⟩ : ∃ s, s ∈ domainKinds ∧ ∃ o, TagSem den tag s o ∧ ¬TagSem den ntag s o :=
    Classical.byContradiction fun c => h fun s ms o ht => Classical.byContradiction fun hn => c ⟨s, ms, o, ht, hn⟩
  have hw' := msem_keys.mp hw
  -- a fresh key of kind `s` that the literal allows `o` at and the negated literal does not
  obtain ⟨q, fresh, at₁, at₂⟩ : ∃ q : MKey, q ∉ fin ∧ KeyAllow den tag l q o ∧ ¬KeyAllow den ntag nl q o := by
    by_cases na : s = "atom"
    · subst na
      obtain ⟨a, ha⟩ := fresh_name (keyNames l ++ keyNames nl ++
        fin.filterMap fun q => match q with | .atom a => some a | _ => Option.none)
      simp only [List.mem_append, not_or, List.mem_filterMap] at ha
      obtain ⟨⟨hl, hnl⟩, hf⟩ := ha
      refine ⟨.atom a, fun m => hf ⟨_, m, rfl⟩, ?_, ?_⟩
      · simp only [KeyAllow, FSem, lookup_fresh hl]; exact ht
      · simp only [KeyAllow, FSem, lookup_fresh hnl]; exact hn
    · obtain ⟨kk, rfl⟩ := domKind_of_mem ms na
      obtain ⟨i, hi⟩ := fresh_nat (fin.filterMap fun q => match q with | .dom _ j => some j | _ => Option.none)
      simp only [List.mem_filterMap] at hi
      exact ⟨.dom kk i, fun m => hi ⟨_, m, rfl⟩, ht, hn⟩
  refine ⟨fun q' => if q' = q then o else w q', msem_keys.mpr fun q' => ?_, fun hN => ?_, fun q' mq => ?_⟩
  · by_cases e : q' = q
    · subst e; simpa using at₁
    · simpa [e] using hw' q'
  · have := msem_keys.mp (nsem_lit.mp hN) q
    simp at this
    exact at₂ this
  · have : q' ≠ q := fun e => fresh (e ▸ mq)
    simp [this]

theorem MeetVal.andAlso {r : Except Exception Term} {disj : Prop} (h : MeetVal r disj) :
    MeetVal (Lynx.Except.andAlso (.ok (.atom "true")) r Bool.true) disj := by
  rcases h with h | ⟨d, h⟩
  · left; simp [h, Lynx.Except.andAlso]
  · right; exact ⟨d, by simp [h, Lynx.Except.andAlso]⟩

/-- One key of the field walk: the line where that key holds what the negated literal does not, or nothing. -/
theorem recur_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (negs : List Term) (a : String) {f₁ f₂ : Term}
    (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) {fields nfields : List (Term × Term)} (sf : FieldsV E fields)
    (inh : Inhabited den fields) (at₁ : ∀ o, FSem den tag fields a o ↔ FieldSem den f₁ o)
    (at₂ : ∀ o, FSem den ntag nfields a o ↔ FieldSem den f₂ o)
    (line : ∀ l, FieldsV E l → Inhabited den l → (∀ w, MSem den tag l w → CovM den negs w) →
      Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
        .ok (.atom "true"))
    (H : ∀ w, MSem den tag fields w → ¬MSem den ntag nfields w → CovM den negs w) :
    Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7» (D m) (.atom a) f₁ f₂ tag (fieldsTerm fields)
      (Term.list negs) (.map S) = .ok (.atom "true") := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  have hm' : K ≤ m := by omega
  obtain ⟨diff, ldiff, hdiff⟩ := dops.diff ht₁ ht₂
  obtain ⟨bd, ed⟩ := field_empty_total ops S ldiff (o₁ && !o₂)
  have semDiff := fieldSem_diff (t := diff) (esem.diff ht₁ ht₂ hm' (hdiff m hm')) (o₁ := o₁) (o₂ := o₂)
  have emptyDiff := field_empty_sem ops dops esem ldiff hS hm' (ed m hm')
  have flag : Lynx.Except.andAlso (pure (boolAtom o₁)) (Erlang.erlang.«not/1» (boolAtom o₂)) Bool.true =
      .ok (boolAtom (o₁ && !o₂)) := by
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
  have e := ed m hm'
  cases bd
  · obtain ⟨l', store, sl', mem, look⟩ := store_val a (f := .tuple #[diff, boolAtom (o₁ && !o₂)]) ⟨diff, _, rfl, ldiff⟩ sf
    have inh' : Inhabited den l' := fun x mx => by
      rcases mem x mx with rfl | mx
      · exact Classical.byContradiction fun c => absurd (emptyDiff.mpr fun y hy => c ⟨y, hy⟩) (by simp)
      · exact inh x mx
    have r := line l' sl' inh' fun w hw => by
      have ha : FieldSem den (.tuple #[diff, boolAtom (o₁ && !o₂)]) (w (.atom a)) := by
        have := hw a; unfold FSem at this; rw [look a, ite_eq_left rfl] at this; exact this
      obtain ⟨f1, nf2⟩ := (semDiff _).mp ha
      refine H w ⟨fun s => ?_, hw.doms⟩ fun hN => nf2 ((at₂ _).mp (hN a))
      by_cases es : a = s
      · subst es; exact (at₁ _).mpr f1
      · have := hw s; unfold FSem at this ⊢; rw [look s, ite_eq_right es] at this; exact this
    generalize (o₁ && !o₂) = od at e store flag r
    rw [Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7».eq_def]
    simp only [hdiff m hm', flag]
    cases od <;> simp [boolAtom] at e store ⊢ <;> simp [e, store, r]
  · generalize (o₁ && !o₂) = od at e flag
    rw [Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7».eq_def]
    simp only [hdiff m hm', flag]
    cases od <;> simp [boolAtom] at e ⊢ <;> simp [e]

/-- The positive fields left in the field walk meet the default field of the negated literal. -/
theorem pos_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gn : TagV E ntag) (negs : List Term)
    {fields nfields : List (Term × Term)} (sf : FieldsV E fields) (inh : Inhabited den fields)
    (line : ∀ l, FieldsV E l → Inhabited den l → (∀ w, MSem den tag l w → CovM den negs w) →
      Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
        .ok (.atom "true"))
    (H : ∀ w, MSem den tag fields w → ¬MSem den ntag nfields w → CovM den negs w) :
    ∀ t : List (Term × Term), (∀ e ∈ t, e ∈ fields ∧ ∀ s : String, e.1 = .atom s → mapLookup nfields (.atom s) = Option.none) →
      Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6» (D m) (fieldsTerm t) (tagField ntag) tag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true")
  | [], _ => by rw [Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6».eq_def]; simp [fieldsTerm, Term.list]
  | (k, f) :: t, ht => by
    obtain ⟨mf, nn⟩ := ht _ List.mem_cons_self
    obtain ⟨a, rfl⟩ := (sf.1 _ mf).1
    have r := recur_val ops dops esem hm hS negs a (sf.1 _ mf).2 (tagFieldV_value ops gn) sf inh
      (fun o => by
        have hl : mapLookup fields (.atom a) = some f := lookup_of_mem sf mf rfl
        simp only [FSem, hl])
      (fun o => by unfold FSem; rw [nn a rfl]; exact (fieldSem_tagV ops dops esem gn o).symm) line H
    have rest := pos_val ops dops esem hm hS gn negs sf inh line H t fun e me => ht e (List.mem_cons_of_mem _ me)
    rw [Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6».eq_def, fieldsTerm_cons]
    simp [r, rest, Lynx.Except.andAlso]

/-- The negated fields left in the field walk meet the default field of the line. -/
theorem neg_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gt : TagV E tag) (negs : List Term)
    {fields nfields : List (Term × Term)} (sf : FieldsV E fields) (snf : FieldsV E nfields) (inh : Inhabited den fields)
    (line : ∀ l, FieldsV E l → Inhabited den l → (∀ w, MSem den tag l w → CovM den negs w) →
      Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
        .ok (.atom "true"))
    (H : ∀ w, MSem den tag fields w → ¬MSem den ntag nfields w → CovM den negs w) :
    ∀ t : List (Term × Term), (∀ e ∈ t, e ∈ nfields ∧ ∀ s : String, e.1 = .atom s → mapLookup fields (.atom s) = Option.none) →
      Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6» (D m) (fieldsTerm t) (tagField tag) tag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true")
  | [], _ => by rw [Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6».eq_def]; simp [fieldsTerm, Term.list]
  | (k, f) :: t, ht => by
    obtain ⟨mf, nn⟩ := ht _ List.mem_cons_self
    obtain ⟨b, rfl⟩ := (snf.1 _ mf).1
    have r := recur_val ops dops esem hm hS negs b (tagFieldV_value ops gt) (snf.1 _ mf).2 sf inh
      (fun o => by unfold FSem; rw [nn b rfl]; exact (fieldSem_tagV ops dops esem gt o).symm)
      (fun o => by
        have hl : mapLookup nfields (.atom b) = some f := lookup_of_mem snf mf rfl
        simp only [FSem, hl]) line H
    have rest := neg_val ops dops esem hm hS gt negs sf snf inh line H t fun e me => ht e (List.mem_cons_of_mem _ me)
    rw [Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6».eq_def, fieldsTerm_cons]
    simp [r, rest, Lynx.Except.andAlso]

/-- `map_line_fields_empty?/7` is complete: it answers `true`, or throws `:closed` when the line and the negated
literal are disjoint, whenever the other negations cover the maps of the line outside the negated literal. -/
theorem fields_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gt : TagV E tag) (gn : TagV E ntag) (negs : List Term)
    (line : ∀ l, FieldsV E l → Inhabited den l → (∀ w, MSem den tag l w → CovM den negs w) →
      Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
        .ok (.atom "true"))
    {fields nfields : List (Term × Term)} (sf : FieldsV E fields) (snf : FieldsV E nfields)
    (inh : Inhabited den fields) (H : ∀ w, MSem den tag fields w → ¬MSem den ntag nfields w → CovM den negs w) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → ∀ (P pre : List (Term × Term)),
      fields = P ++ l₁ → nfields = pre ++ l₂ → (∀ a ∈ P ++ pre, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) →
      MeetVal (Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
        (fieldsTerm fields) (Term.list negs) (.map S)) (∀ w, MSem den tag fields w → ¬MSem den ntag nfields w) := by
  have tails : ∀ (l₁ l₂ P pre : List (Term × Term)), fields = P ++ l₁ → nfields = pre ++ l₂ →
      (∀ a ∈ P ++ pre, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) → (l₁ = [] ∨ l₂ = []) →
      MeetVal (Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
        (fieldsTerm fields) (Term.list negs) (.map S)) (∀ w, MSem den tag fields w → ¬MSem den ntag nfields w) := by
    intro l₁ l₂ P pre hP hpre below empty
    have pos := pos_val ops dops esem hm hS gn negs sf inh line H l₁ fun e me => by
      refine ⟨by rw [hP]; simp [me], fun s es => ?_⟩
      rcases empty with rfl | rfl
      · simp at me
      · rw [hpre, List.append_nil]
        exact lookup_below fun x mx => es ▸ below x (by simp [mx]) e (by simp [me])
    have neg := neg_val ops dops esem hm hS gt negs sf snf inh line H l₂ fun e me => by
      refine ⟨by rw [hpre]; simp [me], fun s es => ?_⟩
      rcases empty with rfl | rfl
      · rw [hP, List.append_nil]
        exact lookup_below fun x mx => es ▸ below x (by simp [mx]) e (by simp [me])
      · simp at me
    left
    rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
    rcases empty with rfl | rfl
    · cases l₂ with
      | nil =>
        simp only [show fieldsTerm ([] : List (Term × Term)) = .nil from rfl] at pos neg ⊢
        simp [key_tag_field gt, key_tag_field gn, pos, neg, Lynx.Except.andAlso]
      | cons y ys =>
        simp only [show fieldsTerm ([] : List (Term × Term)) = .nil from rfl] at pos ⊢
        rw [fieldsTerm_cons] at neg ⊢
        simp [key_tag_field gt, key_tag_field gn, pos, neg, Lynx.Except.andAlso]
    · cases l₁ with
      | nil =>
        simp only [show fieldsTerm ([] : List (Term × Term)) = .nil from rfl] at pos neg ⊢
        simp [key_tag_field gt, key_tag_field gn, pos, neg, Lynx.Except.andAlso]
      | cons x xs =>
        simp only [show fieldsTerm ([] : List (Term × Term)) = .nil from rfl] at neg ⊢
        rw [fieldsTerm_cons] at pos ⊢
        simp [key_tag_field gt, key_tag_field gn, pos, neg, Lynx.Except.andAlso]
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size P pre hP hpre below
    exact tails l₁ l₂ P pre hP hpre below (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ N ih =>
    intro l₁ l₂ size P pre hP hpre below
    match l₁, l₂, hP, hpre, below, size with
    | [], l₂, hP, hpre, below, _ => exact tails [] l₂ P pre hP hpre below (Or.inl rfl)
    | x :: xs, [], hP, hpre, below, _ => exact tails (x :: xs) [] P pre hP hpre below (Or.inr rfl)
    | (k₁, f₁) :: xs, (k₂, f₂) :: ys, hP, hpre, below, size =>
      have s₁ : FieldsV E ((k₁, f₁) :: xs) := by rw [hP] at sf; exact fieldsV_suffix sf
      have s₂ : FieldsV E ((k₂, f₂) :: ys) := by rw [hpre] at snf; exact fieldsV_suffix snf
      obtain ⟨a, rfl⟩ := (s₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (s₂.1 _ List.mem_cons_self).1
      have fv₁ := (s₁.1 _ List.mem_cons_self).2
      have fv₂ := (s₂.1 _ List.mem_cons_self).2
      have head₁ := fieldsV_head s₁
      have head₂ := fieldsV_head s₂
      simp only [List.length_cons] at size
      have look₁ : mapLookup fields (.atom a) = some f₁ :=
        lookup_of_mem sf (e := (.atom a, f₁)) (by rw [hP]; simp) rfl
      have look₂ : mapLookup nfields (.atom b) = some f₂ :=
        lookup_of_mem snf (e := (.atom b, f₂)) (by rw [hpre]; simp) rfl
      have at₁ : ∀ o, FSem den tag fields a o ↔ FieldSem den f₁ o := fun o => by simp only [FSem, look₁]
      have at₂ : ∀ o, FSem den ntag nfields b o ↔ FieldSem den f₂ o := fun o => by simp only [FSem, look₂]
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · -- the key only in the line
        have nnone : mapLookup nfields (.atom a) = Option.none := by
          rw [hpre, lookup_append, lookup_below fun x mx => below x (by simp [mx]) (.atom a, f₁) (by simp)]
          refine lookup_above fun y my => ?_
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp
          · exact cmp_lt_trans cmp (head₂ y my)
        have next := ih xs ((Term.atom b, f₂) :: ys) (by simp; omega) (P ++ [(Term.atom a, f₁)]) pre (by rw [hP]; simp)
          hpre fun x mx y my => by
            have hy : y ∈ ((Term.atom a, f₁) :: xs) ++ (Term.atom b, f₂) :: ys := by
              rcases List.mem_append.mp my with my | my <;> simp [my]
            simp only [List.mem_append, List.mem_singleton] at mx
            rcases mx with (mx | rfl) | mx
            · exact below x (by simp [mx]) y hy
            · rcases List.mem_append.mp my with my | my
              · exact head₁ y my
              · rcases List.mem_cons.mp my with rfl | my
                · exact cmp
                · exact cmp_lt_trans cmp (head₂ y my)
            · exact below x (by simp [mx]) y hy
        by_cases no : ntag = .atom "open"
        · subst no
          have e : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm ((.atom a, f₁) :: xs))
              (fieldsTerm ((.atom b, f₂) :: ys)) tag (.atom "open") (fieldsTerm fields) (Term.list negs) (.map S) =
              Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm xs)
              (fieldsTerm ((.atom b, f₂) :: ys)) tag (.atom "open") (fieldsTerm fields) (Term.list negs) (.map S) := by
            obtain ⟨t₁, o₁, rfl, -⟩ := fv₁
            conv => lhs; rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
            simp [fieldsTerm_cons, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp]
          rw [e]; exact next
        by_cases nc : ntag = .atom "closed"
        · subst nc
          obtain ⟨t₁, o₁, rfl, ht₁⟩ := fv₁
          cases o₁
          · right
            refine ⟨fun w hw hn => ?_, ?_⟩
            · have h₁ := (at₁ _).mp (hw a)
              have h₂ := hn a
              unfold FSem TagSem at h₂
              rw [nnone] at h₂
              rw [fieldSem_mk] at h₁
              rcases h₁ with ⟨-, h⟩ | ⟨x, hx, -⟩
              · cases h
              · simp [hx] at h₂
            · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
              simp [fieldsTerm_cons, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
                Lynx.Except.andAlso, Erlang.erlang.«not/1»]
          · have r := recur_val ops dops esem hm hS negs a ⟨t₁, _, rfl, ht₁⟩ (tagFieldV_value ops gn) sf inh at₁
              (fun o => by simp only [FSem, nnone]; exact (fieldSem_tagV ops dops esem gn o).symm) line H
            have e : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom Bool.true]) :: xs))
                (fieldsTerm ((.atom b, f₂) :: ys)) tag (.atom "closed") (fieldsTerm fields) (Term.list negs) (.map S) =
                Lynx.Except.andAlso (.ok (.atom "true")) (Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
                  (fieldsTerm xs) (fieldsTerm ((.atom b, f₂) :: ys)) tag (.atom "closed") (fieldsTerm fields)
                  (Term.list negs) (.map S)) Bool.true := by
              conv => lhs; rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
              simp only [boolAtom_true] at r
              simp [fieldsTerm_cons, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
                Lynx.Except.andAlso, Erlang.erlang.«not/1», key_tag_field gn, r]
            rw [e]; exact MeetVal.andAlso next
        · have r := recur_val ops dops esem hm hS negs a fv₁ (tagFieldV_value ops gn) sf inh at₁
            (fun o => by simp only [FSem, nnone]; exact (fieldSem_tagV ops dops esem gn o).symm) line H
          obtain ⟨t₁, o₁, rfl, -⟩ := fv₁
          have e : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
              (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
              (fieldsTerm ((.atom b, f₂) :: ys)) tag ntag (fieldsTerm fields) (Term.list negs) (.map S) =
              Lynx.Except.andAlso (.ok (.atom "true")) (Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
                (fieldsTerm xs) (fieldsTerm ((.atom b, f₂) :: ys)) tag ntag (fieldsTerm fields)
                (Term.list negs) (.map S)) Bool.true := by
            conv => lhs; rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
            simp only [tag_eq_false no, tag_eq_false nc]
            cases o₁ <;> simp only [boolAtom_true, boolAtom_false] at r ⊢ <;>
              simp [fieldsTerm_cons, Erlang.erlang.«</2», cmp, Lynx.Except.andAlso,
                key_tag_field gn, r]
          rw [e]; exact MeetVal.andAlso next
      · -- the key in both
        have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        have r := recur_val ops dops esem hm hS negs a fv₁ fv₂ sf inh at₁ at₂ line H
        have next := ih xs ys (by omega) (P ++ [(Term.atom a, f₁)]) (pre ++ [(Term.atom a, f₂)]) (by rw [hP]; simp)
          (by rw [hpre]; simp) fun x mx y my => by
            have hy : y ∈ ((Term.atom a, f₁) :: xs) ++ (Term.atom a, f₂) :: ys := by
              rcases List.mem_append.mp my with my | my <;> simp [my]
            have hy₁ : Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
              rcases List.mem_append.mp my with my | my
              · exact head₁ y my
              · exact head₂ y my
            simp only [List.mem_append, List.mem_singleton] at mx
            rcases mx with (mx | rfl) | (mx | rfl)
            · exact below x (by simp [mx]) y hy
            · exact hy₁
            · exact below x (by simp [mx]) y hy
            · exact hy₁
        have e : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm ((.atom a, f₁) :: xs))
            (fieldsTerm ((.atom a, f₂) :: ys)) tag ntag (fieldsTerm fields) (Term.list negs) (.map S) =
            Lynx.Except.andAlso (.ok (.atom "true")) (Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
              (fieldsTerm xs) (fieldsTerm ys) tag ntag (fieldsTerm fields) (Term.list negs) (.map S)) Bool.true := by
          conv => lhs; rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
          have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
          have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
          simp [fieldsTerm_cons, Erlang.erlang.«</2», Erlang.erlang.«>/2», r,
            Lynx.Except.andAlso]
        rw [e]; exact MeetVal.andAlso next
      · -- the key only in the negated literal
        have lt : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have fnone : mapLookup fields (.atom b) = Option.none := by
          rw [hP, lookup_append, lookup_below fun x mx => below x (by simp [mx]) (.atom b, f₂) (by simp)]
          refine lookup_above fun y my => ?_
          rcases List.mem_cons.mp my with rfl | my
          · exact lt
          · exact cmp_lt_trans lt (head₁ y my)
        have next := ih ((Term.atom a, f₁) :: xs) ys (by simp; omega) P (pre ++ [(Term.atom b, f₂)]) hP (by rw [hpre]; simp)
          fun x mx y my => by
            have hy : y ∈ ((Term.atom a, f₁) :: xs) ++ (Term.atom b, f₂) :: ys := by
              rcases List.mem_append.mp my with my | my
              · exact List.mem_append_left _ my
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ my)
            simp only [List.mem_append, List.mem_singleton] at mx
            rcases mx with mx | (mx | rfl)
            · exact below x (by simp [mx]) y hy
            · exact below x (by simp [mx]) y hy
            · rcases List.mem_append.mp my with my | my
              · rcases List.mem_cons.mp my with rfl | my
                · exact lt
                · exact cmp_lt_trans lt (head₁ y my)
              · exact head₂ y my
        by_cases tc : tag = .atom "closed"
        · subst tc
          obtain ⟨t₂, o₂, rfl, ht₂⟩ := fv₂
          cases o₂
          · right
            refine ⟨fun w hw hn => ?_, ?_⟩
            · have h₁ := hw b
              have h₂ := (at₂ _).mp (hn b)
              unfold FSem TagSem at h₁
              rw [fnone] at h₁
              rw [fieldSem_mk] at h₂
              rcases h₂ with ⟨-, h⟩ | ⟨x, hx, -⟩
              · cases h
              · simp [hx] at h₁
            · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
              simp [fieldsTerm_cons, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
                Erlang.erlang.«>/2», cmp, boolAtom, isMember]
          · have e : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm ((.atom a, f₁) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom Bool.true]) :: ys)) (.atom "closed") ntag
                (fieldsTerm fields) (Term.list negs) (.map S) =
                Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm ((.atom a, f₁) :: xs))
                (fieldsTerm ys) (.atom "closed") ntag (fieldsTerm fields) (Term.list negs) (.map S) := by
              conv => lhs; rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
              obtain ⟨t₁, o₁, rfl, -⟩ := fv₁
              simp [fieldsTerm_cons, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
                Erlang.erlang.«>/2», cmp, boolAtom, isMember]
            rw [e]; exact next
        · have r := recur_val ops dops esem hm hS negs b (tagFieldV_value ops gt) fv₂ sf inh
            (fun o => by simp only [FSem, fnone]; exact (fieldSem_tagV ops dops esem gt o).symm) at₂ line H
          have e : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm ((.atom a, f₁) :: xs))
              (fieldsTerm ((.atom b, f₂) :: ys)) tag ntag (fieldsTerm fields) (Term.list negs) (.map S) =
              Lynx.Except.andAlso (.ok (.atom "true")) (Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
                (fieldsTerm ((.atom a, f₁) :: xs)) (fieldsTerm ys) tag ntag (fieldsTerm fields)
                (Term.list negs) (.map S)) Bool.true := by
            conv => lhs; rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
            obtain ⟨t₁, o₁, rfl, -⟩ := fv₁
            obtain ⟨t₂, o₂, rfl, -⟩ := fv₂
            simp only [tag_eq_false tc]
            simp [fieldsTerm_cons, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              key_tag_field gt, r, Lynx.Except.andAlso]
          rw [e]; exact MeetVal.andAlso next

/-- Open literals do not fit within closed ones. -/
theorem open_not_closed (esem : ElemSem E K V den Safe) : ¬TagIncl den (.atom "open") (.atom "closed") := fun h => by
  obtain ⟨v⟩ := esem.inhabited
  have := h "atom" (by simp [domainKinds]) (some v) (Or.inl rfl)
  simp [TagSem] at this

/-- Which walk `map_line_empty?/4` runs: the meet of fields when the line is closed or the negated literal open, and
the field walk otherwise. -/
theorem walk_choice {tag ntag : Term} : ∃ c : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» tag (.atom "closed"))
    (Erlang.erlang.«==/2» ntag (.atom "open")) = .ok (boolAtom c) ∧ (c = Bool.true ↔ tag = .atom "closed" ∨ ntag = .atom "open") := by
  by_cases tc : tag = .atom "closed"
  · subst tc
    exact ⟨Bool.true, by simp [Erlang.erlang.«==/2», Lynx.Except.orElse, Term.true, boolAtom], by simp⟩
  by_cases no : ntag = .atom "open"
  · subst no
    exact ⟨Bool.true, by simp only [tag_eq_false tc]; simp [Erlang.erlang.«==/2», Lynx.Except.orElse, Term.true, boolAtom],
      by simp⟩
  exact ⟨Bool.false, by simp [tag_eq_false tc, tag_eq_false no, Lynx.Except.orElse, boolAtom], by simp [tc, no]⟩

theorem TagV.plain {tag : Term} (g : TagV E tag) : MapTag E tag := by
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · exact MapTag.atom_open
  · exact MapTag.atom_closed
  · exact Or.inr (Or.inr ⟨dl, rfl, fun e me => (dv.1 e me).2⟩)

theorem MapLitV.plain {t : Term} (h : MapLitV E t) : MapLit E t := by
  obtain ⟨k, tag, l, rfl, g, sl⟩ := h
  exact ⟨k, tag, l, rfl, g.plain, fun e me => (sl.1 e me).2⟩

/-- The general clause of `map_line_empty?/4`: the domain check, then the walk, whose `:closed` throws skip the
negated literal. -/
theorem line_general {m : Nat} {S : List (Term × Term)} {tag ntag : Term} {k : Int} {l nl : List (Term × Term)}
    {rest : List Term} (notTop : ¬(ntag = .atom "open" ∧ nl = [])) (skip : ¬(tag = .atom "open" ∧ ntag = .atom "closed"))
    {bc c : Bool}
    (runc : Elixir.Module.Types.Descr.«map_check_domain_keys?/3» (D m) tag ntag (.map S) = .ok (boolAtom bc))
    (hor : Lynx.Except.orElse (Erlang.erlang.«==/2» tag (.atom "closed")) (Erlang.erlang.«==/2» ntag (.atom "open")) =
      .ok (boolAtom c))
    {bk : Bool} (hrest : Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list rest)
      (.map S) = .ok (boolAtom bk))
    {b : Bool} (hb : (if c then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl)
      tag ntag (fieldsTerm []) (Term.list rest) (.map S) else Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
      (fieldsTerm l) (fieldsTerm nl) tag ntag (fieldsTerm l) (Term.list rest) (.map S)) = .ok (boolAtom b) ∨
      ((if c then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl)
      tag ntag (fieldsTerm []) (Term.list rest) (.map S) else Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
      (fieldsTerm l) (fieldsTerm nl) tag ntag (fieldsTerm l) (Term.list rest) (.map S)) =
        .error (Exception.throw (.atom "closed")) ∧ b = bk)) :
    Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
      (Term.list (.tuple #[.integer k, ntag, fieldsTerm nl] :: rest)) (.map S) = .ok (boolAtom (if bc then b else bk)) := by
  have notTop' : ¬(ntag = .atom "open" ∧ fieldsTerm nl = .nil) := fun ⟨a, e⟩ => notTop ⟨a, fieldsTerm_eq_nil'.mp e⟩
  have nilF : fieldsTerm ([] : List (Term × Term)) = .nil := rfl
  rw [nilF] at hb
  rw [list_cons, Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
  split
  all_goals first
    | (exfalso; simp_all; done)
    | (exfalso; rename_i _ _ h _; exact h _ _ _ _ rfl)
    | skip
  rename_i heq
  simp at heq
  obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := heq
  simp only [runc, hor, Lynx.Except.ok_bind]
  rcases hb with hb | ⟨hb, rfl⟩ <;> cases bc <;> cases c <;>
    simp_all [Lynx.Except.tryWith, isMember, boolAtom, Lynx.Exception.classTerm,
      Lynx.Exception.reason]

/-- Map lines of inhabited fields are empty when their negations cover their maps. -/
theorem line_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) :
    ∀ negs : List Term, (∀ t ∈ negs, MapLitV E t) → ∀ tag : Term, TagV E tag →
      ∀ l, FieldsV E l → Inhabited den l → (∀ w, MSem den tag l w → CovM den negs w) →
      Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
        .ok (.atom "true") := by
  intro negs
  induction negs with
  | nil =>
    intro _ tag _ l _ inh cover
    obtain ⟨w, hw⟩ := msem_witness inh tag
    obtain ⟨N, mN, -⟩ := cover w hw
    simp at mN
  | cons N rest ih =>
    intro lits tag gt l sl inh cover
    obtain ⟨k, ntag, nl, rfl, gn, snl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, MapLitV E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    by_cases top : ntag = .atom "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      rw [list_cons, Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      simp [fieldsTerm, Term.list]
    by_cases skip : tag = .atom "open" ∧ ntag = .atom "closed"
    · obtain ⟨rfl, rfl⟩ := skip
      rw [list_cons, Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      simpa using ih lits' _ gt l sl inh (skip_fresh (escape_incl (open_not_closed esem)) cover)
    have rest_of : ∀ w, MSem den tag l w → ¬MSem den ntag nl w → CovM den rest w := fun w hw hn => by
      obtain ⟨N, mN, hN⟩ := cover w hw
      rcases List.mem_cons.mp mN with rfl | mN
      · exact absurd (nsem_lit.mp hN) hn
      · exact ⟨N, mN, hN⟩
    obtain ⟨bc, runc, semc⟩ := check_val ops dops esem hm hS gt gn skip
    obtain ⟨c, hor, hc⟩ := walk_choice (tag := tag) (ntag := ntag)
    have walk : MeetVal (if c then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l)
        (fieldsTerm nl) tag ntag (fieldsTerm []) (Term.list rest) (.map S) else
        Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl) tag ntag
          (fieldsTerm l) (Term.list rest) (.map S)) (∀ w, MSem den tag l w → ¬MSem den ntag nl w) := by
      cases c
      · simpa using fields_val ops dops esem hm hS gt gn rest (ih lits' tag gt) sl snl inh rest_of _ l nl
          (Nat.le_refl _) [] [] rfl rfl (by simp)
      · simpa using meet_val ops dops esem hm hS tag ntag gt gn rest (ih lits' tag gt) l nl sl snl _ l nl
          (Nat.le_refl _) [] [] [] rfl rfl (by simpa using sl) (by simpa using inh) (by simp) (by simpa using rest_of)
    obtain ⟨bk, hbk⟩ := map_line_total ops dops S rest (fun t m => (lits' t m).plain) tag gt.plain l
      fun e me => (sl.1 e me).2
    have hrest := hbk m hm
    dsimp only at hrest
    cases bc
    · have cov := ih lits' tag gt l sl inh (skip_fresh (escape_incl fun h => by simpa using semc.mpr h) cover)
      rw [hrest] at cov
      rcases walk with r | ⟨-, r⟩
      · rw [line_general (b := Bool.true) top skip runc hor hrest (Or.inl r)]; simpa using cov
      · rw [line_general (b := bk) top skip runc hor hrest (Or.inr ⟨r, rfl⟩)]; simpa using cov
    · rcases walk with r | ⟨disj, r⟩
      · rw [line_general (b := Bool.true) top skip runc hor hrest (Or.inl r)]; rfl
      · have cov := ih lits' tag gt l sl inh fun w hw => rest_of w hw (disj w hw)
        rw [hrest] at cov
        rw [line_general (b := bk) top skip runc hor hrest (Or.inr ⟨r, rfl⟩)]; simpa using cov

open Classical in
/-- Required fields of empty types. -/
noncomputable def reqEmpty (den : Term → V → Prop) (x : Term) : Bool :=
  match x with
  | .tuple ⟨[_, .tuple ⟨[t, .atom "false"]⟩]⟩ => decide (∀ v, ¬den t v)
  | _ => Bool.false

/-- `init_map_line_empty?/4` is complete: lines whose negations cover their maps are empty. -/
theorem init_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag : Term}
    (gt : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l) {negs : List Term}
    (lits : ∀ t ∈ negs, MapLitV E t) (cover : ∀ w, MSem den tag l w → CovM den negs w) :
    Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs) (.map S) =
      .ok (.atom "true") := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  have each : ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]),
      Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2» (D n) (.map S) x = .ok (boolAtom (reqEmpty den x)) := by
    intro x mx
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨t, o, ho, ht⟩ := (sl.1 e me).2
    rw [ho]
    cases o
    · obtain ⟨b, hb⟩ := ops.empty ht S
      have run := hb n (by omega)
      have sem := esem.empty ht hS (by omega) run
      simp only [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom, Bool.false_eq_true,
        ite_false, reqEmpty]
      rw [run]
      cases b <;> simp at sem <;> simp [sem, boolAtom]
    · simp [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom, reqEmpty]
  have anyRun := any_list (D (n + 1)) _ _ _ (reqEmpty den) _ fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-init_map_line_empty?/4-fun-0-/1».pure]
    exact each x mx
  rw [Elixir.Module.Types.Descr.«init_map_line_empty?/4».eq_def]
  simp only [fieldsTerm] at anyRun ⊢
  simp only [pure_bind, anyRun]
  cases hany : (l.map fun e => Term.tuple #[e.1, e.2]).any (reqEmpty den)
  · have inh : Inhabited den l := by
      intro e me
      obtain ⟨t, o, ho, -⟩ := (sl.1 e me).2
      rw [ho]
      cases o
      · have r : reqEmpty den (.tuple #[e.1, e.2]) = Bool.false := by
          simp only [List.any_eq_false, List.mem_map] at hany
          exact by simpa using hany _ ⟨e, me, rfl⟩
        rw [ho] at r
        simp [reqEmpty, boolAtom] at r
        obtain ⟨x, hx⟩ := r
        exact ⟨some x, (fieldSem_mk).mpr (Or.inr ⟨x, rfl, hx⟩)⟩
      · exact ⟨Option.none, (fieldSem_mk).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    have := line_val ops dops esem (show K + 1 ≤ n + 1 by omega) hS negs lits tag gt l sl inh cover
    simp only [fieldsTerm] at this
    simpa [boolAtom, Lynx.Except.orElse] using this
  · simp [boolAtom, Lynx.Except.orElse]

end Elixir.STTDescrProofsTest.Nest
