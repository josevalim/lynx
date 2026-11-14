namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Map lines found empty have no maps outside their negations: the soundness of map emptiness. -/

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Maps of a line with another field at a key, when they have a value of that field there. -/
theorem msem_swap {tag : Term} {a : String} {A B : List (Term × Term)} (_fresh : mapLookup A (.atom a) = Option.none)
    {f f' : Term} {w : MW V} (hw : MSem den tag (A ++ (Term.atom a, f) :: B) w) (h : FieldSem den f' (w (.atom a))) :
    MSem den tag (A ++ (Term.atom a, f') :: B) w := by
  refine hw.of_atoms fun s hs => ?_
  unfold FSem at hs ⊢
  rw [lookup_append] at hs ⊢
  cases e : mapLookup A (.atom s) with
  | some x => simpa [e] using hs
  | none =>
    rw [e] at hs
    simp only [Option.none_or] at hs ⊢
    rw [lookup_cons_atom] at hs ⊢
    by_cases as : a = s
    · subst as; simpa using h
    · simpa [as] using hs

/-- One field of `map_line_meet_empty?/10`, read from a `true` answer. -/
theorem meet_field_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) (tag ntag : Term) (negs : List Term)
    (a : String) (f₁ f₂ : Term) (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) (t₂ : Term) (t₁ acc : List (Term × Term))
    (sorted : FieldsV E (acc.reverse ++ (Term.atom a, f₁) :: t₁)) (fresh : mapLookup acc.reverse (Term.atom a) = Option.none)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {Goal : (MW V) → Prop}
    (rec : ∀ f, FieldValue E f → (∀ o, FieldSem den f o ↔ FieldSem den f₁ o ∧ FieldSem den f₂ o) →
      Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm t₁) t₂ tag ntag
        (fieldsTerm ((.atom a, f) :: acc)) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ w, MSem den tag (acc.reverse ++ (Term.atom a, f) :: t₁) w → Goal w ∨ CovM den negs w)
    (run : Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) f₁ f₂ (fieldsTerm t₁) t₂ tag ntag
      (fieldsTerm acc) (Term.list negs) (.map S) = .ok (.atom "true")) :
    ∀ w, MSem den tag (acc.reverse ++ (Term.atom a, f₁) :: t₁) w → Goal w ∨ CovM den negs w := by
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
  rw [unfold10] at run
  have atA : ∀ w f, MSem den tag (acc.reverse ++ (Term.atom a, f) :: t₁) w → FieldSem den f (w (.atom a)) := by
    intro w f hw
    have := hw a
    unfold FSem at this
    rw [lookup_append, fresh] at this
    simpa [lookup_cons_atom] using this
  have recMeet := fun h => rec _ ⟨meet, _, rfl, lmeet⟩ semMeet h
  intro w hw
  have wa := atA w _ hw
  cases bm
  · cases bd
    · simp only [Bool.false_eq_true, ite_false, Lynx.Except.andAlso_eq_true] at run
      by_cases f₂a : FieldSem den (.tuple #[nt, boolAtom o₂]) (w (.atom a))
      · exact recMeet run.2 w (by simpa using msem_swap fresh hw ((semMeet (w (.atom a))).mpr ⟨wa, f₂a⟩))
      · exact Or.inr (lineS _ (fieldsV_mid sorted ⟨diff, _, rfl, ldiff⟩) run.1 w
          (msem_swap fresh hw ((semDiff (w (.atom a))).mpr ⟨wa, f₂a⟩)))
    · simp only [Bool.false_eq_true, ite_false, ite_true] at run
      have f₂a : FieldSem den (.tuple #[nt, boolAtom o₂]) (w (.atom a)) :=
        Classical.byContradiction fun nf => (emptyDiff.mp rfl) (w (.atom a)) ((semDiff (w (.atom a))).mpr ⟨wa, nf⟩)
      exact recMeet run w (by simpa using msem_swap fresh hw ((semMeet (w (.atom a))).mpr ⟨wa, f₂a⟩))
  · simp only [ite_true] at run
    exact Or.inr (lineS _ sorted run w hw)

theorem fsem_lookup {tag : Term} {l : List (Term × Term)} {s : String} {f : Term}
    (h : mapLookup l (.atom s) = some f) (o : Option V) : FSem den tag l s o ↔ FieldSem den f o := by
  simp only [FSem, h]

theorem fsem_default (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {tag : Term}
    (g : TagV E tag) {l : List (Term × Term)} {s : String} (h : mapLookup l (.atom s) = Option.none) (o : Option V) :
    FSem den tag l s o ↔ FieldSem den (tagField tag) o := by
  rw [fieldSem_tagV ops dops esem g]; simp only [FSem, h]

/-- One key of a field walk, read from a `true` answer: a map of the line outside the remaining negations holds
the negated field at the key. -/
theorem recur_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag : Term} {negs : List Term}
    {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    (a : String) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) {w : MW V}
    (hw : MSemExcept den tag fields a w) (wa : FieldSem den f₁ (w (.atom a))) (nc : ¬CovM den negs w)
    (run : Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7» (D m) (.atom a) f₁ f₂ tag (fieldsTerm fields)
      (Term.list negs) (.map S) = .ok (.atom "true")) :
    FieldSem den f₂ (w (.atom a)) := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  have hm2 : K ≤ m := by omega
  obtain ⟨diff, ldiff, hdiff⟩ := dops.diff ht₁ ht₂
  obtain ⟨bd, ed⟩ := field_empty_total ops S ldiff (o₁ && !o₂)
  have semDiff := fieldSem_diff (t := diff) (esem.diff ht₁ ht₂ hm2 (hdiff m hm2)) (o₁ := o₁) (o₂ := o₂)
  have emptyDiff := field_empty_sem ops dops esem ldiff hS hm2 (ed m hm2)
  obtain ⟨l', runS, sl', -, look⟩ := store_val a ⟨diff, _, rfl, ldiff⟩ sf
  refine Classical.byContradiction fun nf => ?_
  have wd := (semDiff (w (.atom a))).mpr ⟨wa, nf⟩
  cases bd
  · have flag : Lynx.Except.andAlso (pure (boolAtom o₁)) (Erlang.erlang.«not/1» (boolAtom o₂)) Bool.true =
        .ok (boolAtom (o₁ && !o₂)) := by
      cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
    have e := ed m hm2
    have cover := fun r => nc (lineS l' sl' r w ((msem_store look w).mpr ⟨hw, wd⟩))
    generalize (o₁ && !o₂) = od at e runS flag
    rw [Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7».eq_def] at run
    simp only [hdiff m hm2, flag] at run
    simp [e, runS] at run
    exact cover run
  · exact (emptyDiff.mp rfl) _ wd

/-- The fields left on the positive side of a field walk, read from a `true` answer. -/
theorem pos_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gn : TagV E ntag) {negs : List Term}
    {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {nfields : List (Term × Term)} {w : MW V} (hw : MSem den tag fields w) (nc : ¬CovM den negs w) :
    ∀ (l P : List (Term × Term)), fields = P ++ l →
      (∀ e ∈ l, ∀ s : String, e.1 = .atom s → mapLookup nfields (.atom s) = Option.none) →
      Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6» (D m) (fieldsTerm l) (tagField ntag) tag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l, ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
  intro l
  induction l with
  | nil => intro _ _ _ _ e me; simp at me
  | cons x t ih =>
    intro P hP fresh run e me s es
    obtain ⟨k, f⟩ := x
    rw [Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6».eq_def] at run
    simp only [fieldsTerm_cons, Lynx.Except.andAlso_eq_true] at run
    have mem : (k, f) ∈ fields := by rw [hP]; simp
    obtain ⟨a, rfl⟩ := (sf.1 _ mem).1
    rcases List.mem_cons.mp me with rfl | me
    · simp only [Term.atom.injEq] at es
      subst es
      have wa := (fsem_lookup (lookup_of_mem sf mem rfl) _).mp (hw a)
      exact (fsem_default ops dops esem gn (fresh _ List.mem_cons_self _ rfl) _).mpr
        (recur_sound ops dops esem hm hS sf lineS a (sf.1 _ mem).2 (tagFieldV_value ops gn) ⟨fun s _ => hw s, hw.doms⟩
          wa nc run.1)
    · exact ih (P ++ [(Term.atom a, f)]) (by rw [hP]; simp) (fun e me => fresh e (List.mem_cons_of_mem _ me)) run.2 e me s es

/-- The fields left on the negative side of a field walk, read from a `true` answer. -/
theorem neg_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gt : TagV E tag) {negs : List Term}
    {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {nfields : List (Term × Term)} (snf : FieldsV E nfields) {w : MW V} (hw : MSem den tag fields w)
    (nc : ¬CovM den negs w) :
    ∀ (l Q : List (Term × Term)), nfields = Q ++ l →
      (∀ e ∈ l, ∀ s : String, e.1 = .atom s → mapLookup fields (.atom s) = Option.none) →
      Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6» (D m) (fieldsTerm l) (tagField tag) tag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l, ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
  intro l
  induction l with
  | nil => intro _ _ _ _ e me; simp at me
  | cons x t ih =>
    intro Q hQ fresh run e me s es
    obtain ⟨k, f⟩ := x
    rw [Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6».eq_def] at run
    simp only [fieldsTerm_cons, Lynx.Except.andAlso_eq_true] at run
    have mem : (k, f) ∈ nfields := by rw [hQ]; simp
    obtain ⟨a, rfl⟩ := (snf.1 _ mem).1
    rcases List.mem_cons.mp me with rfl | me
    · simp only [Term.atom.injEq] at es
      subst es
      have wa := (fsem_default ops dops esem gt (fresh _ List.mem_cons_self _ rfl) _).mp (hw a)
      exact (fsem_lookup (lookup_of_mem snf mem rfl) _).mpr
        (recur_sound ops dops esem hm hS sf lineS a (tagFieldV_value ops gt) (snf.1 _ mem).2 ⟨fun s _ => hw s, hw.doms⟩
          wa nc run.1)
    · exact ih (Q ++ [(Term.atom a, f)]) (by rw [hQ]; simp) (fun e me => fresh e (List.mem_cons_of_mem _ me)) run.2 e me s es

/-- `map_line_fields_empty?/7` answers `true` only when every map of the line outside the remaining negations
holds at the walked keys what the negated literal allows. -/
theorem fields_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) {S : List (Term × Term)} (hS : Safe S) {tag ntag : Term} (gt : TagV E tag) (gn : TagV E ntag)
    {negs : List Term} {fields : List (Term × Term)} (sf : FieldsV E fields)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    {nfields : List (Term × Term)} (snf : FieldsV E nfields) {w : MW V} (hw : MSem den tag fields w)
    (nc : ¬CovM den negs w) :
    ∀ N (P l₁ Q l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → fields = P ++ l₁ → nfields = Q ++ l₂ →
      (∀ a ∈ P ++ Q, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) →
      Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l₁ ++ l₂, ∀ s : String, e.1 = Term.atom s → FSem den ntag nfields s (w (.atom s)) := by
  have d₁ := key_tag_field gt
  have d₂ := key_tag_field gn
  have recur := fun a {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) (wa : FieldSem den f₁ (w (.atom a))) r =>
    recur_sound ops dops esem hm hS sf lineS a h₁ h₂ (f₂ := f₂) ⟨fun s _ => hw s, hw.doms⟩ wa nc r
  -- lookups at a key of the walk in the walked sides and in the sides before it
  have lookPos : ∀ {P l₁ : List (Term × Term)} {a : String} {f : Term}, fields = P ++ l₁ → (Term.atom a, f) ∈ l₁ →
      mapLookup fields (.atom a) = some f := fun hP me => lookup_of_mem sf (e := (.atom _, _)) (by rw [hP]; simp [me]) rfl
  have lookNeg : ∀ {Q l₂ : List (Term × Term)} {a : String} {f : Term}, nfields = Q ++ l₂ → (Term.atom a, f) ∈ l₂ →
      mapLookup nfields (.atom a) = some f := fun hQ me => lookup_of_mem snf (e := (.atom _, _)) (by rw [hQ]; simp [me]) rfl
  have tails : ∀ P l₁ Q l₂, fields = P ++ l₁ → nfields = Q ++ l₂ →
      (∀ a ∈ P ++ Q, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) → (l₁ = [] ∨ l₂ = []) →
      Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag ntag
        (fieldsTerm fields) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ e ∈ l₁ ++ l₂, ∀ s : String, e.1 = Term.atom s → FSem den ntag nfields s (w (.atom s)) := by
    intro P l₁ Q l₂ hP hQ below empty run
    have run' : Lynx.Except.andAlso
        (Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6» (D m) (fieldsTerm l₁) (tagField ntag) tag
          (fieldsTerm fields) (Term.list negs) (.map S))
        (Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6» (D m) (fieldsTerm l₂) (tagField tag) tag
          (fieldsTerm fields) (Term.list negs) (.map S)) Bool.true = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
      rcases empty with rfl | rfl
      · cases l₂ <;> simpa [fieldsTerm, Term.list, d₁, d₂] using run
      · cases l₁ <;> simpa [fieldsTerm, Term.list, d₁, d₂] using run
    rw [Lynx.Except.andAlso_eq_true] at run'
    intro e me s es
    rcases List.mem_append.mp me with me | me
    · refine pos_sound ops dops esem hm hS gn sf lineS hw nc l₁ P hP (fun x mx s' es' => ?_) run'.1 e me s es
      rcases empty with rfl | rfl
      · simp at mx
      · rw [hQ]
        exact lookup_below fun y my => es' ▸ below y (by simp at my; simp [my]) x (by simp [mx])
    · refine neg_sound ops dops esem hm hS gt sf lineS snf hw nc l₂ Q hQ (fun x mx s' es' => ?_) run'.2 e me s es
      rcases empty with rfl | rfl
      · rw [hP]
        exact lookup_below fun y my => es' ▸ below y (by simp at my; simp [my]) x (by simp [mx])
      · simp at mx
  intro N
  induction N with
  | zero =>
    intro P l₁ Q l₂ size hP hQ below run
    exact tails P l₁ Q l₂ hP hQ below (Or.inl (List.eq_nil_of_length_eq_zero (by omega))) run
  | succ N ih =>
    intro P l₁ Q l₂ size hP hQ below run
    match l₁, l₂ with
    | [], l₂ => exact tails P [] Q l₂ hP hQ below (Or.inl rfl) run
    | x :: xs, [] => exact tails P _ Q [] hP hQ below (Or.inr rfl) run
    | (k₁, f₁) :: xs, (k₂, f₂) :: ys =>
      have m₁ : (k₁, f₁) ∈ fields := by rw [hP]; simp
      have m₂ : (k₂, f₂) ∈ nfields := by rw [hQ]; simp
      obtain ⟨a, rfl⟩ := (sf.1 _ m₁).1
      obtain ⟨b, rfl⟩ := (snf.1 _ m₂).1
      obtain ⟨t₁, o₁, rfl, ht₁⟩ := (sf.1 _ m₁).2
      obtain ⟨t₂, o₂, rfl, ht₂⟩ := (snf.1 _ m₂).2
      have fv₁ : FieldValue E (.tuple #[t₁, boolAtom o₁]) := ⟨t₁, o₁, rfl, ht₁⟩
      have fv₂ : FieldValue E (.tuple #[t₂, boolAtom o₂]) := ⟨t₂, o₂, rfl, ht₂⟩
      have s₁ : FieldsV E ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs) := by rw [hP] at sf; exact fieldsV_suffix sf
      have s₂ : FieldsV E ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys) := by rw [hQ] at snf; exact fieldsV_suffix snf
      have head₁ := fieldsV_head s₁
      have head₂ := fieldsV_head s₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · -- the key is only in the positive map
        have above : ∀ y ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp
          · exact cmp_lt_trans cmp (head₂ y my)
        have nnone : mapLookup nfields (.atom a) = Option.none := by
          rw [hQ, lookup_append, lookup_below fun e me => below e (by simp [me])
            (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) (by simp), lookup_above above]; rfl
        have below' : ∀ x ∈ (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) ++ Q, ∀ y ∈ xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
            Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt := by
          intro x mx y my
          simp only [List.mem_append, List.mem_singleton] at mx
          rcases mx with (mx | rfl) | mx
          · exact below x (by simp [mx]) y (by simp at my ⊢; rcases my with my | my <;> simp [my])
          · rcases List.mem_append.mp my with my | my
            · exact head₁ y my
            · exact above y my
          · exact below x (by simp [mx]) y (by simp at my ⊢; rcases my with my | my <;> simp [my])
        have rest := fun r => ih (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) xs Q _ (by simp; omega)
          (by rw [hP]; simp) hQ below' r
        have finish : (FSem den ntag nfields a (w (.atom a))) →
            Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm xs)
              (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag ntag (fieldsTerm fields) (Term.list negs)
              (.map S) = .ok (.atom "true") →
            ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
              ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
          intro ha r e me s es
          rcases List.mem_cons.mp me with rfl | me
          · simp only [Term.atom.injEq] at es; subst es; exact ha
          · exact rest r e me s es
        have wa := (fsem_lookup (lookPos hP (List.mem_cons_self)) _).mp (hw a)
        by_cases no : ntag = .atom "open"
        · subst no
          rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp] at run
          exact finish (by simp only [FSem, nnone]; exact Or.inl rfl) run
        by_cases nc' : ntag = .atom "closed"
        · subst nc'
          cases o₁
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1»] at run
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Erlang.erlang.«not/1», d₂] at run
            exact finish ((fsem_default ops dops esem gn nnone _).mpr
              (recur a fv₁ (tagFieldV_value ops gn) wa run.1)) run.2
        · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, tag_eq_false no,
            tag_eq_false nc', d₂] at run
          exact finish ((fsem_default ops dops esem gn nnone _).mpr
            (recur a fv₁ (tagFieldV_value ops gn) wa run.1)) run.2
      · -- the key is in both maps
        have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»] at run
        have wa := (fsem_lookup (lookPos hP (List.mem_cons_self (a := (Term.atom a, Term.tuple #[t₁, boolAtom o₁])))) _).mp
          (hw a)
        have ha := (fsem_lookup (tag := ntag) (lookNeg hQ (List.mem_cons_self (a := (Term.atom a, Term.tuple #[t₂, boolAtom o₂])))) _).mpr
          (recur a fv₁ fv₂ wa run.1)
        have below' : ∀ x ∈ (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) ++ (Q ++ [(Term.atom a, Term.tuple #[t₂, boolAtom o₂])]),
            ∀ y ∈ xs ++ ys, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt := by
          intro x mx y my
          simp only [List.mem_append, List.mem_singleton] at mx
          have hy : Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
            rcases List.mem_append.mp my with my | my
            · exact head₁ y my
            · exact head₂ y my
          rcases mx with (mx | rfl) | (mx | rfl)
          · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with my | my <;> simp [my])
          · exact hy
          · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with my | my <;> simp [my])
          · exact hy
        have rest := ih (P ++ [(Term.atom a, Term.tuple #[t₁, boolAtom o₁])]) xs (Q ++ [(Term.atom a, Term.tuple #[t₂, boolAtom o₂])]) ys
          (by omega) (by rw [hP]; simp) (by rw [hQ]; simp) below' run.2
        intro e me s es
        simp only [List.mem_append, List.mem_cons] at me
        rcases me with (rfl | me) | (rfl | me)
        · simp only [Term.atom.injEq] at es; subst es; exact ha
        · exact rest e (by simp [me]) s es
        · simp only [Term.atom.injEq] at es; subst es; exact ha
        · exact rest e (by simp [me]) s es
      · -- the key is only in the negative map
        have lt : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact lt
          · exact cmp_lt_trans lt (head₁ y my)
        have pnone : mapLookup fields (.atom b) = Option.none := by
          rw [hP, lookup_append, lookup_below fun e me => below e (by simp [me])
            (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) (by simp), lookup_above above]; rfl
        have below' : ∀ x ∈ P ++ (Q ++ [(Term.atom b, Term.tuple #[t₂, boolAtom o₂])]),
            ∀ y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ ys, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt := by
          intro x mx y my
          have conv : y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys := by
            simp only [List.mem_append, List.mem_cons] at my ⊢
            rcases my with (my | my) | my
            · exact Or.inl (Or.inl my)
            · exact Or.inl (Or.inr my)
            · exact Or.inr (Or.inr my)
          simp only [List.mem_append, List.mem_singleton] at mx
          rcases mx with mx | (mx | rfl)
          · exact below x (by simp [mx]) y conv
          · exact below x (by simp [mx]) y conv
          · rcases List.mem_append.mp my with my | my
            · exact above y my
            · exact head₂ y my
        have rest := fun r => ih P _ (Q ++ [(Term.atom b, Term.tuple #[t₂, boolAtom o₂])]) ys (by simp; omega)
          hP (by rw [hQ]; simp) below' r
        have finish : FSem den ntag nfields b (w (.atom b)) →
            Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m)
              (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs)) (fieldsTerm ys) tag ntag (fieldsTerm fields)
              (Term.list negs) (.map S) = .ok (.atom "true") →
            ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys,
              ∀ s : String, e.1 = .atom s → FSem den ntag nfields s (w (.atom s)) := by
          intro hb r e me s es
          simp only [List.mem_append, List.mem_cons] at me
          rcases me with me | (rfl | me)
          · exact rest r e (by simp at me ⊢; rcases me with me | me <;> simp [me]) s es
          · simp only [Term.atom.injEq] at es; subst es; exact hb
          · exact rest r e (by simp [me]) s es
        have nb := lookNeg hQ (List.mem_cons_self (a := (Term.atom b, Term.tuple #[t₂, boolAtom o₂])))
        by_cases tc : tag = .atom "closed"
        · subst tc
          cases o₂
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
              Erlang.erlang.«>/2», cmp, boolAtom, isMember] at run
          · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
              Erlang.erlang.«>/2», cmp, boolAtom, isMember] at run
            have wb : w (.atom b) = Option.none := by
              have := hw b
              simp only [FSem, pnone, TagSem] at this
              rcases this with h | h
              · exact absurd h (by decide)
              · exact h
            exact finish ((fsem_lookup nb _).mpr (by rw [wb, fieldSem_mk]; exact Or.inl ⟨rfl, rfl⟩)) run
        · rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def] at run
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            tag_eq_false tc, d₁] at run
          have wb := (fsem_default ops dops esem gt pnone _).mp (hw b)
          exact finish ((fsem_lookup nb _).mpr (recur b (tagFieldV_value ops gt) fv₂ wb run.1)) run.2

/-- `map_line_meet_empty?/7` answers `true` only when every map of the line, with the meets of the walked fields, is in
the negated literal or covered by the remaining negations. -/
theorem meet_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) (tag ntag : Term) (gt : TagV E tag)
    (gn : TagV E ntag) (tagOk : tag = .atom "closed" ∨ ntag = .atom "open") (negs : List Term)
    (lineS : ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
      (Term.list negs) (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w)
    (nfields : List (Term × Term)) (snf : FieldsV E nfields) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
    ∀ (pre acc : List (Term × Term)), nfields = pre ++ l₂ → FieldsV E (acc.reverse ++ l₁) →
      (∀ a ∈ pre ++ acc, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) →
      (∀ e ∈ acc, ∃ s : String, e.1 = .atom s ∧ ∀ o, FieldSem den e.2 o → FSem den ntag nfields s o) →
      (∀ e ∈ pre, ∃ e' ∈ acc, e.1 = e'.1) →
      Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂) tag
        ntag (fieldsTerm acc) (Term.list negs) (.map S) = .ok (.atom "true") →
      ∀ w, MSem den tag (acc.reverse ++ l₁) w → MSem den ntag nfields w ∨ CovM den negs w := by
  -- the walk is over: the line is in the negated literal
  have base : ∀ (pre acc : List (Term × Term)), nfields = pre → FieldsV E acc.reverse →
      (∀ e ∈ acc, ∃ s : String, e.1 = .atom s ∧ ∀ o, FieldSem den e.2 o → FSem den ntag nfields s o) →
      (∀ e ∈ pre, ∃ e' ∈ acc, e.1 = e'.1) →
      ∀ w, MSem den tag acc.reverse w → MSem den ntag nfields w := by
    intro pre acc hpre sacc accN preIn w hw
    refine ⟨fun s => ?_, fun k i => ?_⟩
    rotate_left
    · rcases tagOk with rfl | rfl
      · exact (hw.doms k i).resolve_left (by decide) ▸ tagSem_none _ _
      · exact Or.inl rfl
    by_cases hs : ∃ e ∈ acc, e.1 = .atom s
    · obtain ⟨e, me, es⟩ := hs
      have look := lookup_of_mem sacc (List.mem_reverse.mpr me) es
      have := hw s
      unfold FSem at this
      rw [look] at this
      obtain ⟨s', es', ok⟩ := accN e me
      rw [es] at es'
      simp only [Term.atom.injEq] at es'
      subst es'
      exact ok _ this
    · have none₁ : mapLookup acc.reverse (.atom s) = Option.none :=
        lookup_none fun e me eq => hs ⟨e, List.mem_reverse.mp me, eq⟩
      have none₂ : mapLookup nfields (.atom s) = Option.none := by
        refine lookup_none fun e me eq => hs ?_
        rw [hpre] at me
        obtain ⟨e', me', ee⟩ := preIn e me
        exact ⟨e', me', ee ▸ eq⟩
      have := hw s
      simp only [FSem, none₁] at this
      simp only [FSem, none₂]
      rcases tagOk with rfl | rfl
      · exact (this.resolve_left (by decide)) ▸ tagSem_none _ _
      · exact Or.inl rfl
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size pre acc hpre sacc below accN preIn run
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    intro w hw
    exact Or.inl (base pre acc (by simpa using hpre) (by simpa using sacc) accN preIn w (by simpa using hw))
  | succ N ih =>
    intro l₁ l₂ size pre acc hpre sacc below accN preIn run
    have s₂ : FieldsV E l₂ := by rw [hpre] at snf; exact fieldsV_suffix snf
    have s₁ : FieldsV E l₁ := fieldsV_suffix sacc
    have accBelow : ∀ e ∈ acc.reverse, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel e.1 b.1) e.1 b.1 = .lt := fun e me b mb =>
      below e (by simp at me ⊢; simp [me]) b mb
    have preBelow : ∀ e ∈ pre, ∀ b ∈ l₁ ++ l₂, Term.compare (Term.fuel e.1 b.1) e.1 b.1 = .lt := fun e me b mb =>
      below e (by simp [me]) b mb
    -- the key only in the positive map
    have posStep : ∀ (a : String) (f₁ : Term) (xs : List (Term × Term)), l₁ = (.atom a, f₁) :: xs →
        (∀ y ∈ l₂, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt) →
        Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) f₁ (tagField ntag)
          (fieldsTerm xs) (fieldsTerm l₂) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) =
            .ok (.atom "true") →
        ∀ w, MSem den tag (acc.reverse ++ l₁) w → MSem den ntag nfields w ∨ CovM den negs w := by
      intro a f₁ xs e₁ above r10
      subst e₁
      have mem₁ : (Term.atom a, f₁) ∈ (Term.atom a, f₁) :: xs ++ l₂ := by simp
      have fresh : mapLookup acc.reverse (.atom a) = Option.none :=
        lookup_below fun e me => accBelow e me _ mem₁
      have nnone : mapLookup nfields (.atom a) = Option.none := by
        rw [hpre, lookup_append, lookup_below fun e me => preBelow e me _ mem₁, lookup_above above]; rfl
      refine meet_field_sound ops dops esem hm hS tag ntag negs a f₁ (tagField ntag)
        (s₁.1 _ List.mem_cons_self).2 (tagFieldV_value ops gn) (fieldsTerm l₂) xs acc sacc fresh lineS
        (fun f hf sem r7 w hw => ?_) r10
      refine ih xs l₂ (by simp at size; omega) pre ((.atom a, f) :: acc) hpre (by simpa using fieldsV_mid sacc hf)
        (fun x mx y my => ?_) (fun e me => ?_) (fun e me => ?_) r7 w (by simpa using hw)
      · simp only [List.mem_append, List.mem_cons] at mx my
        have head := fieldsV_head s₁
        rcases mx with mx | rfl | mx
        · exact preBelow x mx y (by rcases my with my | my <;> simp [my])
        · rcases my with my | my
          · exact head y my
          · exact above y my
        · exact below x (by simp [mx]) y (by rcases my with my | my <;> simp [my])
      · rcases List.mem_cons.mp me with rfl | me
        · refine ⟨a, rfl, fun o ho => ?_⟩
          exact (fsem_default ops dops esem gn nnone o).mpr ((sem o).mp ho).2
        · exact accN e me
      · obtain ⟨e', me', ee⟩ := preIn e me
        exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
    -- the key only in the negative map
    have negStep : ∀ (b : String) (f₂ : Term) (ys : List (Term × Term)), l₂ = (.atom b, f₂) :: ys →
        (∀ y ∈ l₁, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt) →
        Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField tag) f₂
          (fieldsTerm l₁) (fieldsTerm ys) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) =
            .ok (.atom "true") →
        ∀ w, MSem den tag (acc.reverse ++ l₁) w → MSem den ntag nfields w ∨ CovM den negs w := by
      intro b f₂ ys e₂ above r10
      subst e₂
      have mem₂ : (Term.atom b, f₂) ∈ l₁ ++ (Term.atom b, f₂) :: ys := by simp
      have fresh : mapLookup acc.reverse (.atom b) = Option.none :=
        lookup_below fun e me => accBelow e me _ mem₂
      have none₁ : mapLookup l₁ (.atom b) = Option.none := lookup_above above
      have nsome : mapLookup nfields (.atom b) = some f₂ := by
        rw [hpre]; exact lookup_head (lookup_below fun e me => preBelow e me _ mem₂)
      have sorted : FieldsV E (acc.reverse ++ (Term.atom b, tagField tag) :: l₁) :=
        fieldsV_insert sacc (fun e me => accBelow e me _ mem₂) above ⟨b, rfl⟩ (tagFieldV_value ops gt)
      intro w hw
      refine meet_field_sound ops dops esem hm hS tag ntag negs b (tagField tag) f₂
        (tagFieldV_value ops gt) (s₂.1 _ List.mem_cons_self).2 (fieldsTerm ys) l₁ acc sorted fresh lineS
        (fun f hf sem r7 w hw => ?_) r10 w ((msem_defaultV ops dops esem gt none₁ w).mpr hw)
      refine ih l₁ ys (by simp at size; omega) (pre ++ [(Term.atom b, f₂)]) ((Term.atom b, f) :: acc)
        (by rw [hpre]; simp) (by simpa using fieldsV_mid sorted hf) (fun x mx y my => ?_) (fun e me => ?_)
        (fun e me => ?_) r7 w (by simpa using hw)
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mx my
        have head := fieldsV_head s₂
        rcases mx with (mx | rfl) | rfl | mx
        · exact preBelow x mx y (by rcases my with my | my <;> simp [my])
        · rcases my with my | my
          · exact above y my
          · exact head y my
        · rcases my with my | my
          · exact above y my
          · exact head y my
        · exact below x (by simp [mx]) y (by rcases my with my | my <;> simp [my])
      · rcases List.mem_cons.mp me with rfl | me
        · refine ⟨b, rfl, fun o ho => ?_⟩
          unfold FSem
          rw [nsome]
          exact ((sem o).mp ho).2
        · exact accN e me
      · rcases List.mem_append.mp me with me | me
        · obtain ⟨e', me', ee⟩ := preIn e me
          exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
        · simp at me; subst me; exact ⟨_, List.mem_cons_self, rfl⟩
    have key₁ : ∀ x ∈ l₁, ∃ a : String, x.1 = .atom a := fun x mx => (s₁.1 x mx).1
    have key₂ : ∀ x ∈ l₂, ∃ a : String, x.1 = .atom a := fun x mx => (s₂.1 x mx).1
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil =>
        intro w hw
        exact Or.inl (base pre acc (by simpa using hpre) (by simpa using sacc) accN preIn w (by simpa using hw))
      | cons y ys =>
        obtain ⟨k₂, f₂⟩ := y
        obtain ⟨b, rfl⟩ := key₂ _ List.mem_cons_self
        have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm [])
            (fieldsTerm ((.atom b, f₂) :: ys)) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) =
            Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField tag) f₂
              (fieldsTerm []) (fieldsTerm ys) tag ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
          rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, key_tag_field gt]
        rw [e] at run
        exact negStep b f₂ ys rfl (by simp) run
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
        rw [e] at run
        exact posStep a f₁ xs rfl (by simp) run
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
          rcases gn with rfl | rfl | ⟨dl, rfl, dv⟩
          · have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "open") (fieldsTerm acc)
                (Term.list negs) (.map S) =
                Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm xs)
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (.atom "open")
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: acc)) (Term.list negs) (.map S) := by
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp]
            rw [e] at run
            have mem₁ : (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs ++
                (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys := by simp
            have nnone : mapLookup nfields (.atom a) = Option.none := by
              rw [hpre, lookup_append, lookup_below fun e me => preBelow e me _ mem₁, lookup_above above]; rfl
            intro w hw
            refine ih xs _ (by simp; omega) pre ((.atom a, .tuple #[t₁, boolAtom o₁]) :: acc) hpre (by simpa using sacc)
              (fun x mx y my => ?_) (fun e me => ?_) (fun e me => ?_) run w (by simpa using hw)
            · simp only [List.mem_append, List.mem_cons] at mx my
              rcases mx with mx | rfl | mx
              · exact preBelow x mx y (by rcases my with my | my <;> simp [my])
              · rcases my with my | my
                · exact head₁ y my
                · exact above y (by simpa using my)
              · exact below x (by simp [mx]) y (by rcases my with my | my <;> simp [my])
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨a, rfl, fun o _ => by simp only [FSem, nnone]; exact Or.inl rfl⟩
              · exact accN e me
            · obtain ⟨e', me', ee⟩ := preIn e me
              exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
          · cases o₁
            · exfalso
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def] at run
              simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
                Lynx.Except.andAlso, Erlang.erlang.«not/1»] at run
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
              rw [e] at run
              exact posStep a _ xs rfl above run
          · have kd := key_tag_field (E := E) (Or.inr (Or.inr ⟨dl, rfl, dv⟩))
            have no := fieldsTerm_ne_atom dl "open"
            have nc := fieldsTerm_ne_atom dl "closed"
            have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) tag (fieldsTerm dl) (fieldsTerm acc)
                (Term.list negs) (.map S) =
                Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom a) (.tuple #[t₁, boolAtom o₁])
                  (tagField (fieldsTerm dl)) (fieldsTerm xs) (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys))
                  tag (fieldsTerm dl) (fieldsTerm acc) (Term.list negs) (.map S) := by
              generalize fieldsTerm dl = T at kd no nc ⊢
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, tag_eq_false no,
                tag_eq_false nc, Lynx.Except.andAlso, kd]
            rw [e] at run
            exact posStep a _ xs rfl above run
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
          rw [e] at run
          refine meet_field_sound ops dops esem hm hS tag ntag negs a _ _ ⟨t₁, o₁, rfl, ht₁⟩
            ⟨t₂, o₂, rfl, ht₂⟩ (fieldsTerm ys) xs acc sacc fresh lineS (fun f hf sem r7 w hw => ?_) run
          refine ih xs ys (by omega) (pre ++ [(Term.atom a, Term.tuple #[t₂, boolAtom o₂])]) ((Term.atom a, f) :: acc)
            (by rw [hpre]; simp) (by simpa using fieldsV_mid sacc hf) (fun x mx y my => ?_) (fun e me => ?_)
            (fun e me => ?_) r7 w (by simpa using hw)
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mx my
            have kx : ∀ y, y ∈ xs ∨ y ∈ ys → Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := fun y my => by
              rcases my with my | my
              · exact head₁ y my
              · exact head₂ y my
            rcases mx with (mx | rfl) | rfl | mx
            · exact preBelow x mx y (by rcases my with my | my <;> simp [my])
            · exact kx y my
            · exact kx y my
            · exact below x (by simp [mx]) y (by rcases my with my | my <;> simp [my])
          · rcases List.mem_cons.mp me with rfl | me
            · refine ⟨a, rfl, fun o ho => ?_⟩
              unfold FSem
              rw [nsome]
              exact ((sem o).mp ho).2
            · exact accN e me
          · rcases List.mem_append.mp me with me | me
            · obtain ⟨e', me', ee⟩ := preIn e me
              exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
            · simp at me; subst me; exact ⟨_, List.mem_cons_self, rfl⟩
        · have lt : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
          have above : ∀ y ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
            intro y my
            rcases List.mem_cons.mp my with rfl | my
            · exact lt
            · exact cmp_lt_trans lt (head₁ y my)
          rcases gt with rfl | rfl | ⟨dl, rfl, dv⟩
          · have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) (.atom "open") ntag (fieldsTerm acc)
                (Term.list negs) (.map S) =
                Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField (.atom "open"))
                  (.tuple #[t₂, boolAtom o₂]) (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs)) (fieldsTerm ys)
                  (.atom "open") ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                cmp, boolAtom, Lynx.Except.andAlso, tag_field, tagField, tagType]
            rw [e] at run
            exact negStep b _ ys rfl above run
          · cases o₂
            · exfalso
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def] at run
              simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2»,
                Erlang.erlang.«>/2», cmp, boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»] at run
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
              rw [e] at run
              exact negStep b _ ys rfl above run
          · have kd := key_tag_field (E := E) (Or.inr (Or.inr ⟨dl, rfl, dv⟩))
            have nc := fieldsTerm_ne_atom dl "closed"
            have e : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m)
                (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs))
                (fieldsTerm ((.atom b, .tuple #[t₂, boolAtom o₂]) :: ys)) (fieldsTerm dl) ntag (fieldsTerm acc)
                (Term.list negs) (.map S) =
                Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) (.atom b) (tagField (fieldsTerm dl))
                  (.tuple #[t₂, boolAtom o₂]) (fieldsTerm ((.atom a, .tuple #[t₁, boolAtom o₁]) :: xs)) (fieldsTerm ys)
                  (fieldsTerm dl) ntag (fieldsTerm acc) (Term.list negs) (.map S) := by
              generalize fieldsTerm dl = T at kd nc ⊢
              rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
                tag_eq_false nc, Lynx.Except.andAlso, kd]
            rw [e] at run
            exact negStep b _ ys rfl above run

end Elixir.STTDescrProofsTest.Nest
