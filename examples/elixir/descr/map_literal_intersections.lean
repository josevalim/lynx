namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-! Map literal intersections on value maps. -/

/-- Intersection functions of element types, at every call depth from `Kf`. -/
def IFun (E : Term → Prop) (den : Term → V → Prop) (Kf : Nat) (ifun : Term) : Prop :=
  ∀ m, Kf ≤ m → ∀ a b, E a → E b → ∃ c, E c ∧ (∀ x, den c x ↔ den a x ∧ den b x) ∧
    Lynx.Dispatcher.pure (D m) ifun #[a, b] = .ok c

/-- Results of literal intersections of value maps: sorted fields of keys of either literal allowing, at each key,
what both literals allow, or `:empty` thrown when some key allows nothing in both. -/
def InterV (E : Term → Prop) (den : Term → V → Prop) (r : Except Exception Term) (t₁ t₂ tR : Term)
    (l₁ l₂ ks : List (Term × Term)) : Prop :=
  (∃ l, r = .ok (fieldsTerm l) ∧ FieldsV E l ∧ (∀ e ∈ l, ∃ e' ∈ ks, e.1 = e'.1) ∧
    ∀ s o, FSem den tR l s o ↔ FSem den t₁ l₁ s o ∧ FSem den t₂ l₂ s o) ∨
  ((∃ s, ∀ o, ¬(FSem den t₁ l₁ s o ∧ FSem den t₂ l₂ s o)) ∧ r = .error (Exception.throw (.atom "empty")))

theorem fsem_absent {tag : Term} {s : String} {l : List (Term × Term)} (h : mapLookup l (.atom s) = Option.none) :
    FSem den tag l s Option.none := by
  simp only [FSem, h]; exact tagSem_none tag "atom"


/-- A throw at a key of the tails is a throw for the whole lists. -/
theorem disj_cons₁ {t₁ t₂ : Term} {a : String} {f : Term} {xs l₂ : List (Term × Term)} (s₁ : FieldsV E ((.atom a, f) :: xs))
    (above : ∀ e ∈ l₂, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt)
    (h : ∃ s, ∀ o, ¬(FSem den t₁ xs s o ∧ FSem den t₂ l₂ s o)) :
    ∃ s, ∀ o, ¬(FSem den t₁ ((.atom a, f) :: xs) s o ∧ FSem den t₂ l₂ s o) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun o ho => hs o ?_⟩
  by_cases e : a = s
  · subst e
    exact absurd ⟨fsem_absent (lookup_above (fieldsV_head s₁)), fsem_absent (lookup_above above)⟩ (hs Option.none)
  · exact ⟨(fsem_cons_ne e _ _ _).mp ho.1, ho.2⟩

theorem disj_cons₂ {t₁ t₂ : Term} {a : String} {f : Term} {l₁ ys : List (Term × Term)} (s₂ : FieldsV E ((.atom a, f) :: ys))
    (above : ∀ e ∈ l₁, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt)
    (h : ∃ s, ∀ o, ¬(FSem den t₁ l₁ s o ∧ FSem den t₂ ys s o)) :
    ∃ s, ∀ o, ¬(FSem den t₁ l₁ s o ∧ FSem den t₂ ((.atom a, f) :: ys) s o) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun o ho => hs o ?_⟩
  by_cases e : a = s
  · subst e
    exact absurd ⟨fsem_absent (lookup_above above), fsem_absent (lookup_above (fieldsV_head s₂))⟩ (hs Option.none)
  · exact ⟨ho.1, (fsem_cons_ne e _ _ _).mp ho.2⟩

theorem disj_both {t₁ t₂ : Term} {a : String} {f₁ f₂ : Term} {xs ys : List (Term × Term)} (s₁ : FieldsV E ((.atom a, f₁) :: xs))
    (s₂ : FieldsV E ((.atom a, f₂) :: ys)) (h : ∃ s, ∀ o, ¬(FSem den t₁ xs s o ∧ FSem den t₂ ys s o)) :
    ∃ s, ∀ o, ¬(FSem den t₁ ((.atom a, f₁) :: xs) s o ∧ FSem den t₂ ((.atom a, f₂) :: ys) s o) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun o ho => hs o ?_⟩
  by_cases e : a = s
  · subst e
    exact absurd ⟨fsem_absent (lookup_above (fieldsV_head s₁)), fsem_absent (lookup_above (fieldsV_head s₂))⟩
      (hs Option.none)
  · exact ⟨(fsem_cons_ne e _ _ _).mp ho.1, (fsem_cons_ne e _ _ _).mp ho.2⟩

theorem fsem_nil {tag s : String} {o : Option V} : FSem den (.atom tag) [] s o ↔ (tag = "open" ∨ o = Option.none) :=
  fsem_none rfl o

/-- Fields that are all optional allow absent keys. -/
theorem fsem_optional {tag : String} {l : List (Term × Term)}
    (opt : ∀ e ∈ l, ∃ t, e.2 = .tuple #[t, boolAtom Bool.true]) (s : String) : FSem den (.atom tag) l s Option.none := by
  unfold FSem TagSem
  cases e : mapLookup l (.atom s) with
  | none => exact Or.inr rfl
  | some f =>
    obtain ⟨x, mx, rfl⟩ := lookup_mem e
    obtain ⟨t, ht⟩ := opt x mx
    rw [ht]
    exact (fieldSem_mk).mpr (Or.inl ⟨rfl, rfl⟩)

/-- A required field allows only present keys. -/
theorem fsem_required {tag : String} {l : List (Term × Term)} (sl : FieldsV E l) {e : Term × Term} (me : e ∈ l)
    {t : Term} (he : e.2 = .tuple #[t, boolAtom Bool.false]) {s : String} (ek : e.1 = .atom s) :
    ¬FSem den (.atom tag) l s Option.none := by
  unfold FSem TagSem
  rw [lookup_of_mem sl me ek, he]
  dsimp only
  rw [fieldSem_mk]
  simp

theorem any_optFlag {l : List (Term × Term)} (sl : FieldsV E l) :
    (l.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = Bool.false ↔
      ∀ e ∈ l, ∃ t, e.2 = .tuple #[t, boolAtom Bool.true] := by
  simp only [List.any_eq_false, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Bool.not_eq_true', Bool.not_eq_false]
  refine forall₂_congr fun e me => ?_
  obtain ⟨t, o, ho, -⟩ := (sl.1 e me).2
  rw [ho]
  constructor
  · intro h
    have := optFlag_entry e.1 t o
    rw [h] at this
    exact ⟨t, by rw [← this]⟩
  · rintro ⟨t', e'⟩
    simp only [Term.tuple.injEq] at e'
    have e₁ := congrArg (fun a : Array Term => a[1]?) e'
    simp at e₁
    have : o = Bool.true := by cases o <;> simp_all [boolAtom]
    subst this
    exact optFlag_entry e.1 t Bool.true

theorem closed_tails (m : Nat) (l₁ l₂ : List (Term × Term)) (h₁ : FieldsV E l₁) (h₂ : FieldsV E l₂) :
    Lynx.Except.orElse
      (Erlang.lists.«any/2» (D m)
        (.function "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-0-" 1 #[]) (fieldsTerm l₁))
      (Erlang.lists.«any/2» (D m)
        (.function "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-1-" 1 #[]) (fieldsTerm l₂))
      Bool.true = .ok (boolAtom ((l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) ||
        (l₂.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x))) := by
  have r₁ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (E := E) (D m) _ _
    (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-0-/1».pure m) (fun o => !o)
    closed_fun₀ l₁ fun e me => (h₁.1 e me).2)
  have r₂ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (E := E) (D m) _ _
    (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-1-/1».pure m) (fun o => !o)
    closed_fun₁ l₂ fun e me => (h₂.1 e me).2)
  simp only [fieldsTerm] at r₁ r₂ ⊢
  rw [r₁, r₂]
  cases (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) <;>
    simp [boolAtom, Lynx.Except.orElse] <;> rfl

theorem any_required {l : List (Term × Term)} (sl : FieldsV E l)
    (h : (l.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = Bool.true) :
    ∃ e ∈ l, ∃ (t : Term) (s : String), e.2 = .tuple #[t, boolAtom Bool.false] ∧ e.1 = .atom s := by
  simp only [List.any_eq_true, List.mem_map] at h
  obtain ⟨x, ⟨e, me, rfl⟩, hx⟩ := h
  obtain ⟨t, o, ho, -⟩ := (sl.1 e me).2
  obtain ⟨s, hs⟩ := (sl.1 e me).1
  rw [ho, optFlag_entry] at hx
  cases o
  · exact ⟨e, me, t, s, ho, hs⟩
  · simp at hx

/-- The intersection of element types at a key, with its emptiness. -/
theorem meet_run (ops : ElemOk E K) (_dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf ≤ m) (hm : K ≤ m) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) {t₁ t₂ : Term} (h₁ : E t₁) (h₂ : E t₂) :
    ∃ c b, E c ∧ (∀ x, den c x ↔ den t₁ x ∧ den t₂ x) ∧
      Lynx.Dispatcher.pure (D m) ifun #[t₁, t₂] = .ok c ∧
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m) c (.map S) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∀ x, ¬den c x) := by
  obtain ⟨c, hc, sem, run⟩ := hI m hK t₁ t₂ h₁ h₂
  obtain ⟨b, hb⟩ := ops.empty hc S
  exact ⟨c, b, hc, sem, run, hb m hm, esem.empty hc hS hm (hb m hm)⟩

/-- Fields of a key in both literals: their meet, or nothing when the meet is required and empty. -/
theorem meet_field_sem {t₁ t₂ c : Term} {o₁ o₂ : Bool} (sem : ∀ x, den c x ↔ den t₁ x ∧ den t₂ x)
    (o : Option V) : FieldSem den (.tuple #[c, boolAtom (o₁ && o₂)]) o ↔
      FieldSem den (.tuple #[t₁, boolAtom o₁]) o ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) o :=
  fieldSem_meet sem o

theorem meet_field_empty {t₁ t₂ c : Term} {o₁ o₂ : Bool} (sem : ∀ x, den c x ↔ den t₁ x ∧ den t₂ x)
    (req : (o₁ && o₂) = Bool.false) (empty : ∀ x, ¬den c x) (o : Option V) :
    ¬(FieldSem den (.tuple #[t₁, boolAtom o₁]) o ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) o) := by
  rw [← meet_field_sem sem, fieldSem_mk]
  rintro (⟨-, h⟩ | ⟨x, -, hx⟩)
  · rw [req] at h; cases h
  · exact empty x hx

/-- `map_literal_intersection_closed/4` on value maps. -/
theorem closed_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf ≤ m) (hm : K ≤ m) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂)
        ifun (.map S)) (.atom "closed") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), FieldsV E l₁ → FieldsV E l₂ → (l₁ = [] ∨ l₂ = []) →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂)
        ifun (.map S)) (.atom "closed") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
    intro l₁ l₂ h₁ h₂ empty
    have hb := closed_tails m l₁ l₂ h₁ h₂
    generalize ha₁ : (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = a₁ at hb
    generalize ha₂ : (l₂.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = a₂ at hb
    have absent : ∀ (l : List (Term × Term)), l = [] → ∀ s o, FSem den (.atom "closed") l s o → o = Option.none := by
      rintro l rfl s o h
      rw [fsem_none (by simp [mapLookup])] at h
      simpa using h
    cases a₁ <;> cases a₂
    · left
      have o₁ := (any_optFlag h₁).mp ha₁
      have o₂ := (any_optFlag h₂).mp ha₂
      refine ⟨[], ?_, ⟨by simp, by simp⟩, by simp, fun s o => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
        · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
      · constructor
        · intro h
          rw [absent [] rfl s o h]
          exact ⟨fsem_optional o₁ s, fsem_optional o₂ s⟩
        · rintro ⟨g₁, g₂⟩
          have : o = Option.none := by
            rcases empty with rfl | rfl
            · exact absent [] rfl s o g₁
            · exact absent [] rfl s o g₂
          subst this
          exact fsem_absent (by simp [mapLookup])
    all_goals
      right
      refine ⟨?_, ?_⟩
      rotate_left
      · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp only [fieldsTerm, List.map_nil, List.map_cons] at hb ⊢ <;>
            simp [Term.list, hb, boolAtom, isMember]
        · cases l₁ <;> simp only [fieldsTerm, List.map_nil, List.map_cons] at hb ⊢ <;>
            simp [Term.list, hb, boolAtom, isMember]
    · obtain ⟨e, me, t, s, he, ek⟩ := any_required h₂ ha₂
      have : l₁ = [] := by rcases empty with h | rfl; exact h; simp at me
      exact ⟨s, fun o ⟨g₁, g₂⟩ => fsem_required h₂ me he ek (by rwa [absent l₁ this s o g₁] at g₂)⟩
    all_goals
      obtain ⟨e, me, t, s, he, ek⟩ := any_required h₁ ha₁
      have : l₂ = [] := by rcases empty with rfl | h; simp at me; exact h
      exact ⟨s, fun o ⟨g₁, g₂⟩ => fsem_required h₁ me he ek (by rwa [absent l₂ this s o g₂] at g₁)⟩
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
    | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨t₁, o₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨t₂, o₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      have hx := fieldsV_head h₁
      have hy := fieldsV_head h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (hy e me)
        have absent₂ := lookup_above above
        cases o₁
        · right
          refine ⟨⟨a, fun o ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_none absent₂] at g₂
            rw [fsem_cons_self, fieldSem_mk] at g₁
            rcases g₁ with ⟨-, h⟩ | ⟨x, hx, -⟩
            · cases h
            · simp [hx] at g₂
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs _ (by simp; omega) sx h₂ with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨l, ?_, sl, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [sem, fsem_cons_self, fsem_none (lookup_above hx), fsem_none absent₂, fieldSem_mk]
                constructor
                · rintro ⟨h, -⟩; exact ⟨Or.inl ⟨by simpa using h, rfl⟩, h⟩
                · rintro ⟨-, h⟩; exact ⟨h, h⟩
              · rw [sem, fsem_cons_ne e]
          · right
            refine ⟨disj_cons₁ h₁ above disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, bc, lc, semc, disp, emp, empSem⟩ := meet_run ops dops esem hK hm hI hS f₁ f₂
        have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
        have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ bc = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          right
          refine ⟨⟨a, fun o' ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁ g₂
            exact meet_field_empty semc o (empSem.mp rfl) o' ⟨g₁, g₂⟩
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            cases o₁ <;> cases o₂ <;> simp at o <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp]
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (o₁ && o₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simp only [fieldsTerm] at run
              cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
                simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                  isMember, Lynx.Except.andAlso, disp, emp, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              exact hy e' me'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp only [fieldsTerm] at run
            cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp, run]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (hx e me)
        have absent₁ := lookup_above above
        cases o₂
        · right
          refine ⟨⟨b, fun o ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_none absent₁] at g₁
            rw [fsem_cons_self, fieldSem_mk] at g₂
            rcases g₂ with ⟨-, h⟩ | ⟨x, hx, -⟩
            · cases h
            · simp [hx] at g₁
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember]
        · rcases ih _ ys (by simp; omega) h₁ sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨l, ?_, sl, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember] using run
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
            · by_cases e : b = s
              · subst e
                rw [sem, fsem_cons_self, fsem_none (lookup_above hy), fsem_none absent₁, fieldSem_mk]
                constructor
                · rintro ⟨h, -⟩; exact ⟨h, Or.inl ⟨by simpa using h, rfl⟩⟩
                · rintro ⟨h, -⟩; exact ⟨h, h⟩
              · rw [sem, fsem_cons_ne e]
          · right
            refine ⟨disj_cons₂ h₂ above disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember] using run

theorem all_optFlag {l : List (Term × Term)} (sl : FieldsV E l) :
    (l.map fun e => Term.tuple #[e.1, e.2]).all (fun x => optFlag x) = Bool.true ↔
      ∀ e ∈ l, ∃ t, e.2 = .tuple #[t, boolAtom Bool.true] := by
  have := any_optFlag sl
  rw [← this]
  simp [List.all_eq_true, List.any_eq_false]

/-- `map_literal_intersection_open_closed/4` on value maps: the open literal first. -/
theorem open_closed_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf ≤ m) (hm : K ≤ m) {ifun : Term} (hI : IFun E den Kf ifun)
    {S : List (Term × Term)} (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
      FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m) (fieldsTerm l₁)
        (fieldsTerm l₂) ifun (.map S)) (.atom "open") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), FieldsV E l₁ → FieldsV E l₂ → (l₁ = [] ∨ l₂ = []) →
      InterV E den (Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m) (fieldsTerm l₁)
        (fieldsTerm l₂) ifun (.map S)) (.atom "open") (.atom "closed") (.atom "closed") l₁ l₂ l₂ := by
    intro l₁ l₂ h₁ h₂ empty
    have hb := all_list (D m) _ _ _ (fun x => optFlag x) _ (optional_list (E := E) (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_open_closed/4-fun-0-/1».pure m)
      (fun o => o) open_closed_fun l₁ fun e me => (h₁.1 e me).2)
    cases b : (l₁.map fun e => Term.tuple #[e.1, e.2]).all (fun x => optFlag x)
    · right
      refine ⟨?_, ?_⟩
      · have : (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) = Bool.true := by
          simpa [List.all_eq_true, List.any_eq_true] using b
        obtain ⟨e, me, t, s, he, ek⟩ := any_required h₁ this
        have : l₂ = [] := by rcases empty with rfl | h; simp at me; exact h
        subst this
        refine ⟨s, fun o ⟨g₁, g₂⟩ => fsem_required (den := den) (tag := "open") h₁ me he ek ?_⟩
        rw [fsem_nil] at g₂
        rcases g₂ with h | h
        · exact absurd h (by decide)
        · rwa [h] at g₁
      · rw [b] at hb
        unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
        · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
    · left
      have opt := (all_optFlag h₁).mp b
      refine ⟨l₂, ?_, h₂, fun e me => ⟨e, me, rfl⟩, fun s o => ?_⟩
      · rw [b] at hb
        unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
        rcases empty with rfl | rfl
        · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
        · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb]
      · refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
        rcases empty with rfl | rfl
        · exact fsem_nil.mpr (Or.inl rfl)
        · rw [fsem_nil] at h
          rcases h with h | h
          · exact absurd h (by decide)
          · rw [h]; exact fsem_optional opt s
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
    | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨t₁, o₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨t₂, o₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      have hx := fieldsV_head h₁
      have hy := fieldsV_head h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (hy e me)
        have absent₂ := lookup_above above
        cases o₁
        · right
          refine ⟨⟨a, fun o ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_none absent₂] at g₂
            rw [fsem_cons_self, fieldSem_mk] at g₁
            rcases g₁ with ⟨-, h⟩ | ⟨x, hx, -⟩
            · cases h
            · simp [hx] at g₂
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs _ (by simp; omega) sx h₂ with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨l, ?_, sl, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [sem, fsem_cons_self, fsem_none (lookup_above hx), fsem_none absent₂, fieldSem_mk]
                constructor
                · rintro ⟨-, h⟩; exact ⟨Or.inl ⟨by simpa using h, rfl⟩, h⟩
                · rintro ⟨-, h⟩; exact ⟨Or.inl rfl, h⟩
              · rw [sem, fsem_cons_ne e]
          · right
            refine ⟨disj_cons₁ h₁ above disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using run
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, bc, lc, semc, disp, emp, empSem⟩ := meet_run ops dops esem hK hm hI hS f₁ f₂
        have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
        have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ bc = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          right
          refine ⟨⟨a, fun o' ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁ g₂
            exact meet_field_empty semc o (empSem.mp rfl) o' ⟨g₁, g₂⟩
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            cases o₁ <;> cases o₂ <;> simp at o <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp]
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (o₁ && o₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
              simp only [fieldsTerm] at run
              cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
                simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                  isMember, Lynx.Except.andAlso, disp, emp, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              exact hy e' me'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by simp [me'], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp only [fieldsTerm] at run
            cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», boolAtom,
                isMember, Lynx.Except.andAlso, disp, emp, run]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (hx e me)
        have absent₁ := lookup_above above
        rcases ih _ ys (by simp; omega) h₁ sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
        · left
          refine ⟨(.atom b, .tuple #[t₂, boolAtom o₂]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
          · unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
            simp [run]
          · refine fieldsV_cons ⟨b, rfl⟩ ⟨t₂, _, rfl, f₂⟩ sl fun e me => ?_
            obtain ⟨e', me', ee⟩ := keys e me
            rw [ee]
            exact hy e' me'
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, by simp, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp [me'], ee⟩
          · by_cases e : b = s
            · subst e
              rw [fsem_cons_self, fsem_cons_self, fsem_none absent₁]
              exact ⟨fun h => ⟨Or.inl rfl, h⟩, fun h => h.2⟩
            · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
        · right
          refine ⟨disj_cons₂ h₂ above disj, ?_⟩
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
          simp [run]

/-- Domains intersect kind by kind, dropping the kinds whose intersection is empty. -/
theorem domain_fields_val (ops : ElemOk E K) (_dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    {S : List (Term × Term)} (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
      DomsV E l₁ → DomsV E l₂ → ∃ l : List (Term × Term),
        Elixir.Module.Types.Descr.«map_domain_intersection_fields/3» (D m) (fieldsTerm l₁) (fieldsTerm l₂) (.map S) =
          .ok (fieldsTerm l) ∧ DomsV E l ∧ (∀ e ∈ l, ∃ e' ∈ l₁, e.1 = e'.1) ∧
        ∀ (s : String) v, (∃ T, mapLookup l (.atom s) = some T ∧ den T v) ↔
          (∃ T, mapLookup l₁ (.atom s) = some T ∧ den T v) ∧ (∃ T, mapLookup l₂ (.atom s) = some T ∧ den T v) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨[], by rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list],
      ⟨by simp, by simp⟩, by simp, fun s v => by simp [mapLookup]⟩
  | succ N ih =>
    intro l₁ l₂ size d₁ d₂
    have tail : ∀ {x : Term × Term} {xs : List (Term × Term)}, DomsV E (x :: xs) → DomsV E xs :=
      fun d => ⟨fun e me => d.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp d.2).2⟩
    match l₁, l₂ with
    | [], l₂ =>
      exact ⟨[], by rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; cases l₂ <;> simp [fieldsTerm, Term.list],
        ⟨by simp, by simp⟩, by simp, fun s v => by simp [mapLookup]⟩
    | x :: xs, [] =>
      exact ⟨[], by rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list],
        ⟨by simp, by simp⟩, by simp, fun s v => by simp [mapLookup]⟩
    | (k₁, T₁) :: xs, (k₂, T₂) :: ys =>
      obtain ⟨⟨a, rfl, -⟩, E₁⟩ := d₁.1 _ List.mem_cons_self
      obtain ⟨⟨b, rfl, -⟩, E₂⟩ := d₂.1 _ List.mem_cons_self
      have h₁ := (List.pairwise_cons.mp d₁.2).1
      have h₂ := (List.pairwise_cons.mp d₂.2).1
      simp only [List.length_cons] at size
      -- lookups at a key below every key of a list find nothing
      have below : ∀ {c : String} {zs : List (Term × Term)}, (∀ z ∈ zs, Term.compare (Term.fuel (.atom c) z.1) (.atom c) z.1 = .lt) →
          ∀ T v, ¬(mapLookup zs (.atom c) = some T ∧ den T v) := fun hz T v ⟨h, _⟩ => by
        rw [lookup_above hz] at h; cases h
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · obtain ⟨l, run, dl, keys, sem⟩ := ih xs ((.atom b, T₂) :: ys) (by simp; omega) (tail d₁) d₂
        refine ⟨l, ?_, dl, fun e me => ?_, fun s v => ?_⟩
        · rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
        · obtain ⟨e', me', ee⟩ := keys e me; exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
        · by_cases as : a = s
          · subst as
            have nb : ∀ z ∈ (Term.atom b, T₂) :: ys, Term.compare (Term.fuel (.atom a) z.1) (.atom a) z.1 = .lt := fun z mz => by
              rcases List.mem_cons.mp mz with rfl | mz
              · exact cmp
              · exact cmp_lt_trans cmp (h₂ z mz)
            rw [sem]
            constructor
            · rintro ⟨-, T, h, hv⟩; exact absurd ⟨h, hv⟩ (below nb T v)
            · rintro ⟨-, T, h, hv⟩; exact absurd ⟨h, hv⟩ (below nb T v)
          · have e₁ : mapLookup ((.atom a, T₁) :: xs) (.atom s) = mapLookup xs (.atom s) := by
              rw [lookup_cons_atom, ite_eq_right as]
            rw [e₁]; exact sem s v
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, hc, inter⟩ := ops.inter E₁ E₂
        have semc := esem.inter E₁ E₂ hm (inter m hm)
        obtain ⟨bc, empty⟩ := ops.empty hc S
        have semE := esem.empty hc hS hm (empty m hm)
        obtain ⟨l, run, dl, keys, sem⟩ := ih xs ys (by omega) (tail d₁) (tail d₂)
        have r := run
        simp only [fieldsTerm] at r
        have rest : ∀ z ∈ l, Term.compare (Term.fuel (.atom a) z.1) (.atom a) z.1 = .lt := fun z mz => by
          obtain ⟨e', me', ee⟩ := keys z mz; rw [ee]; exact h₁ e' me'
        cases bc
        · refine ⟨(.atom a, c) :: l, ?_, ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨rest, dl.2⟩⟩, fun e me => ?_,
            fun s v => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              inter m hm, empty m hm, boolAtom, isMember, r]
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨(d₁.1 _ List.mem_cons_self).1.imp fun _ h => h, hc⟩
            · exact dl.1 e me
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, List.mem_cons_self, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me; exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
          · by_cases as : a = s
            · subst as
              simp only [lookup_cons_atom]
              simp [semc]
            · have e₁ : mapLookup ((.atom a, T₁) :: xs) (.atom s) = mapLookup xs (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              have e₂ : mapLookup ((.atom a, T₂) :: ys) (.atom s) = mapLookup ys (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              have e₀ : mapLookup ((.atom a, c) :: l) (.atom s) = mapLookup l (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              rw [e₀, e₁, e₂]; exact sem s v
        · refine ⟨l, ?_, dl, fun e me => ?_, fun s v => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              inter m hm, empty m hm, boolAtom, isMember, r]
          · obtain ⟨e', me', ee⟩ := keys e me; exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
          · by_cases as : a = s
            · subst as
              have l₁' : mapLookup ((.atom a, T₁) :: xs) (.atom a) = some T₁ := by simp [lookup_cons_atom]
              have l₂' : mapLookup ((.atom a, T₂) :: ys) (.atom a) = some T₂ := by simp [lookup_cons_atom]
              rw [l₁', l₂']
              constructor
              · rintro ⟨T, h, hv⟩; exact absurd ⟨h, hv⟩ (below rest T v)
              · rintro ⟨⟨_, e₁, hv₁⟩, ⟨_, e₂, hv₂⟩⟩
                cases e₁; cases e₂
                exact absurd ((semc v).mpr ⟨hv₁, hv₂⟩) (semE.mp rfl v)
            · have e₁ : mapLookup ((.atom a, T₁) :: xs) (.atom s) = mapLookup xs (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              have e₂ : mapLookup ((.atom a, T₂) :: ys) (.atom s) = mapLookup ys (.atom s) := by
                rw [lookup_cons_atom, ite_eq_right as]
              rw [e₁, e₂]; exact sem s v
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        obtain ⟨l, run, dl, keys, sem⟩ := ih ((.atom a, T₁) :: xs) ys (by simp; omega) d₁ (tail d₂)
        refine ⟨l, ?_, dl, keys, fun s v => ?_⟩
        · have r := run
          simp only [fieldsTerm] at r
          rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
          exact r
        · by_cases bs : b = s
          · subst bs
            have na : ∀ z ∈ (Term.atom a, T₁) :: xs, Term.compare (Term.fuel (.atom b) z.1) (.atom b) z.1 = .lt := fun z mz => by
              rcases List.mem_cons.mp mz with rfl | mz
              · exact cmp'
              · exact cmp_lt_trans cmp' (h₁ z mz)
            rw [sem]
            constructor
            · rintro ⟨⟨T, h, hv⟩, -⟩; exact absurd ⟨h, hv⟩ (below na T v)
            · rintro ⟨⟨T, h, hv⟩, -⟩; exact absurd ⟨h, hv⟩ (below na T v)
          · have e₂ : mapLookup ((.atom b, T₂) :: ys) (.atom s) = mapLookup ys (.atom s) := by
              rw [lookup_cons_atom, ite_eq_right bs]
            rw [e₂]; exact sem s v

theorem tagSem_closed' {kind : String} {o : Option V} : TagSem den (.atom "closed") kind o ↔ o = Option.none := by
  simp [TagSem]

/-- `map_domain_intersection/3` on tags of value maps: the tag allowing at keys of every kind what both allow. -/
theorem domain_inter_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {t₁ t₂ : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂) :
    ∃ tR, Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) t₁ t₂ (.map S) = .ok tR ∧ TagV E tR ∧
      ∀ (kind : String) o, TagSem den tR kind o ↔ TagSem den t₁ kind o ∧ TagSem den t₂ kind o := by
  have hnone := (sem_none ops dops esem).2
  have closedL : ∀ t, ∀ kind (o : Option V), TagSem den (.atom "closed") kind o ↔ TagSem den (.atom "closed") kind o ∧ TagSem den t kind o :=
    fun t kind o => ⟨fun h => ⟨h, by rw [tagSem_closed'.mp h]; exact tagSem_none _ _⟩, fun h => h.1⟩
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, d₁⟩
  · refine ⟨t₂, ?_, g₂, fun kind o => ⟨fun h => ⟨Or.inl rfl, h⟩, fun h => h.2⟩⟩
    rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]
    rcases g₂ with rfl | rfl | ⟨dl₂, rfl, _⟩ <;> simp [fieldsTerm_ne_atom]
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp, Or.inr (Or.inl rfl), closedL t₂⟩
  · rcases g₂ with rfl | rfl | ⟨dl₂, rfl, d₂⟩
    · exact ⟨_, by rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom],
        Or.inr (Or.inr ⟨dl₁, rfl, d₁⟩), fun kind o => ⟨fun h => ⟨h, Or.inl rfl⟩, fun h => h.1⟩⟩
    · exact ⟨_, by rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom],
        Or.inr (Or.inl rfl), fun kind o => (closedL (fieldsTerm dl₁) kind o).trans And.comm⟩
    · obtain ⟨l, run, dl, -, sem⟩ := domain_fields_val ops dops esem hm hS _ dl₁ dl₂ (Nat.le_refl _) d₁ d₂
      have step : Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) (fieldsTerm dl₁) (fieldsTerm dl₂)
          (.map S) = (match fieldsTerm l with
            | .nil => Except.ok (Term.atom "closed")
            | t => Except.ok t) := by
        have ne₁ := fieldsTerm_ne_atom dl₁
        have ne₂ := fieldsTerm_ne_atom dl₂
        have r := run
        generalize fieldsTerm dl₁ = T₁ at r ne₁
        generalize fieldsTerm dl₂ = T₂ at r ne₂
        rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]
        split
        · exact absurd rfl (ne₁ "closed")
        · exact absurd rfl (ne₂ "closed")
        · exact absurd rfl (ne₁ "open")
        · exact absurd rfl (ne₂ "open")
        · simp only [r]
          cases fieldsTerm l <;> rfl
      have both : ∀ kind o, (TagSem den (fieldsTerm dl₁) kind o ∧ TagSem den (fieldsTerm dl₂) kind o) ↔
          (o = Option.none ∨ ∃ v T, o = some v ∧ mapLookup l (.atom kind) = some T ∧ den T v) := by
        intro kind o
        rw [tagSem_dom_iff hnone, tagSem_dom_iff hnone]
        rcases o with _ | v
        · simp
        · have := sem kind v
          simp only [reduceCtorEq, false_or, Option.some.injEq] at this ⊢
          simp only [exists_and_left, exists_eq_left'] at this ⊢
          exact this.symm
      cases l with
      | nil =>
        refine ⟨_, by rw [step]; rfl, Or.inr (Or.inl rfl), fun kind o => ?_⟩
        rw [both, tagSem_closed']
        simp [mapLookup]
      | cons x xs =>
        refine ⟨_, by rw [step]; simp [fieldsTerm, Term.list], Or.inr (Or.inr ⟨x :: xs, rfl, dl⟩), fun kind o => ?_⟩
        rw [both, tagSem_dom_iff hnone]

def mergeFunV (ifun : Term) (S : List (Term × Term)) : Term :=
  .function "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-0-" 3 #[ifun, .map S]

/-- The merge function of open literals meets fields, throwing `:empty` on required empty meets. -/
theorem merge_fun_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf n : Nat} (hK : Kf ≤ n) (hn : K ≤ n) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) (key : Term) {t₁ t₂ : Term} (f₁ : E t₁) (f₂ : E t₂) (o₁ o₂ : Bool) :
    ∃ c, E c ∧ (∀ x, den c x ↔ den t₁ x ∧ den t₂ x) ∧
      ((¬((o₁ && o₂) = Bool.false ∧ ∀ x, ¬den c x) ∧
        Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) key
          (.tuple #[t₁, boolAtom o₁]) (.tuple #[t₂, boolAtom o₂]) = .ok (.tuple #[c, boolAtom (o₁ && o₂)])) ∨
       (((o₁ && o₂) = Bool.false ∧ ∀ x, ¬den c x) ∧
        Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) key
          (.tuple #[t₁, boolAtom o₁]) (.tuple #[t₂, boolAtom o₂]) = .error (Exception.throw (.atom "empty")))) := by
  obtain ⟨c, bc, lc, semc, disp, emp, empSem⟩ := meet_run ops dops esem hK hn hI hS f₁ f₂
  refine ⟨c, lc, semc, ?_⟩
  by_cases thrown : (o₁ && o₂) = Bool.false ∧ bc = Bool.true
  · obtain ⟨o, rfl⟩ := thrown
    right
    refine ⟨⟨o, empSem.mp rfl⟩, ?_⟩
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> simp at o <;>
      simp [boolAtom, Lynx.Except.andAlso, disp, emp, isMember]
  · left
    refine ⟨fun ⟨o, e⟩ => thrown ⟨o, empSem.mpr e⟩, ?_⟩
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> cases bc <;> simp at thrown <;>
      simp [boolAtom, Lynx.Except.andAlso, disp, emp, isMember]

/-- `orddict:merge/3` of open literals on value maps. -/
theorem merge_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf n : Nat} (hK : Kf ≤ n) (hn : K ≤ n) {ifun : Term} (hI : IFun E den Kf ifun) {S : List (Term × Term)}
    (hS : Safe S) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Erlang.orddict.«merge/3» (D (n + 1)) (mergeFunV ifun S) (fieldsTerm l₁) (fieldsTerm l₂))
        (Term.atom "open") (Term.atom "open") (Term.atom "open") l₁ l₂ (l₁ ++ l₂) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    left
    refine ⟨[], ?_, h₁, by simp, fun s o => by simp [fsem_nil]⟩
    unfold Erlang.orddict.«merge/3»
    simp [fieldsTerm, mergeFunV, Erlang.erlang.«is_function/2»]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ =>
      left
      refine ⟨l₂, ?_, h₂, fun e me => ⟨e, by simp [me], rfl⟩, fun s o => by simp [fsem_nil]⟩
      unfold Erlang.orddict.«merge/3»
      cases l₂ <;> simp [fieldsTerm, mergeFunV, Erlang.erlang.«is_function/2»]
    | x :: xs, [] =>
      left
      refine ⟨x :: xs, ?_, h₁, fun e me => ⟨e, by simp at me ⊢; exact me, rfl⟩, fun s o => by simp [fsem_nil]⟩
      unfold Erlang.orddict.«merge/3»
      simp [fieldsTerm, mergeFunV, Erlang.erlang.«is_function/2»]
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨t₁, o₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨t₂, o₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      have hx := fieldsV_head h₁
      have hy := fieldsV_head h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[t₂, boolAtom o₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (hy e me)
        rcases ih xs _ (by simp; omega) sx h₂ with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
        · left
          refine ⟨(.atom a, .tuple #[t₁, boolAtom o₁]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
          · unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», cmp] at run ⊢
            simp [run]
          · refine fieldsV_cons ⟨a, rfl⟩ ⟨t₁, _, rfl, f₁⟩ sl fun e me => ?_
            obtain ⟨e', me', ee⟩ := keys e me
            rw [ee]
            rcases List.mem_append.mp me' with m' | m'
            · exact hx e' m'
            · exact above e' m'
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, by simp, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
          · by_cases e : a = s
            · subst e
              rw [fsem_cons_self, fsem_cons_self, fsem_none (lookup_above above)]
              exact ⟨fun h => ⟨h, Or.inl rfl⟩, fun h => h.1⟩
            · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
        · right
          refine ⟨disj_cons₁ h₁ above disj, ?_⟩
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp] at run ⊢
          simp [run]
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, lc, semc, ⟨nt, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom a) f₁ f₂ o₁ o₂
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (o₁ && o₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · unfold Erlang.orddict.«merge/3»
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», mergeFunV,
                Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at run ⊢
              simp [lam, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              rcases List.mem_append.mp me' with m' | m'
              · exact hx e' m'
              · exact hy e' m'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», mergeFunV,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at run ⊢
            simp [lam, run]
        · right
          refine ⟨⟨a, fun o' ⟨g₁, g₂⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁ g₂
            exact meet_field_empty semc thrown.1 thrown.2 o' ⟨g₁, g₂⟩
          · unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», mergeFunV,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure]
            simp [lam]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[t₁, boolAtom o₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (hx e me)
        rcases ih _ ys (by simp; omega) h₁ sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
        · left
          refine ⟨(.atom b, .tuple #[t₂, boolAtom o₂]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
          · unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
            simp [run]
          · refine fieldsV_cons ⟨b, rfl⟩ ⟨t₂, _, rfl, f₂⟩ sl fun e me => ?_
            obtain ⟨e', me', ee⟩ := keys e me
            rw [ee]
            rcases List.mem_append.mp me' with m' | m'
            · exact above e' m'
            · exact hy e' m'
          · rcases List.mem_cons.mp me with rfl | me
            · exact ⟨_, by simp, rfl⟩
            · obtain ⟨e', me', ee⟩ := keys e me
              exact ⟨e', by simp only [List.mem_append, List.mem_cons] at me'; rcases me' with (h | h) | h <;> simp [h], ee⟩
          · by_cases e : b = s
            · subst e
              rw [fsem_cons_self, fsem_cons_self, fsem_none (lookup_above above)]
              exact ⟨fun h => ⟨Or.inl rfl, h⟩, fun h => h.2⟩
            · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
        · right
          refine ⟨disj_cons₂ h₂ above disj, ?_⟩
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
          simp [run]

def mergeFunV₁ (ifun : Term) (S : List (Term × Term)) : Term :=
  .function "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-1-" 3 #[ifun, .map S]

theorem merge_fun₁_call (n : Nat) (ifun : Term) (S : List (Term × Term)) (k v₁ v₂ : Term) :
    Lynx.Dispatcher.pure (D (n + 1)) (mergeFunV₁ ifun S) #[k, v₁, v₂] =
      Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) k v₁ v₂ := by
  simp [mergeFunV₁, Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-1-/3».pure,
    merge_fun₁_eq]

/-- `fields_merge_with_defaults/5` on value maps: the fields of each literal meet the field of the other, or its
default field when absent, so the result allows at atom keys what both literals allow. -/
theorem merge_defaults_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf n : Nat} (hK : Kf ≤ n) (hn : K ≤ n) {ifun : Term} (hI : IFun E den Kf ifun)
    {S : List (Term × Term)} (hS : Safe S) {t₁ t₂ tR : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂)
    (htag : ∀ o, TagSem den tR "atom" o ↔ TagSem den t₁ "atom" o ∧ TagSem den t₂ "atom" o) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → FieldsV E l₁ → FieldsV E l₂ →
      InterV E den (Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm l₁) (tagField t₁)
        (fieldsTerm l₂) (tagField t₂) (mergeFunV₁ ifun S)) t₁ t₂ tR l₁ l₂ (l₁ ++ l₂) := by
  have df₁ : tagField t₁ = .tuple #[tagType t₁ "atom", boolAtom Bool.true] := rfl
  have df₂ : tagField t₂ = .tuple #[tagType t₂ "atom", boolAtom Bool.true] := rfl
  have E₁ := tagType_value ops g₁ "atom"
  have E₂ := tagType_value ops g₂ "atom"
  have dsem₁ : ∀ {l : List (Term × Term)} {s : String}, mapLookup l (.atom s) = Option.none → ∀ o,
      FSem den t₁ l s o ↔ FieldSem den (.tuple #[tagType t₁ "atom", boolAtom Bool.true]) o := fun h o => by
    rw [← df₁, fieldSem_tagV ops dops esem g₁]; simp only [FSem, h]
  have dsem₂ : ∀ {l : List (Term × Term)} {s : String}, mapLookup l (.atom s) = Option.none → ∀ o,
      FSem den t₂ l s o ↔ FieldSem den (.tuple #[tagType t₂ "atom", boolAtom Bool.true]) o := fun h o => by
    rw [← df₂, fieldSem_tagV ops dops esem g₂]; simp only [FSem, h]
  -- a key of the first literal only, meeting the default field of the second
  have stepL : ∀ (a : String) (u₁ : Term) (p₁ : Bool) (xs l₂ : List (Term × Term)),
      E u₁ → FieldsV E ((.atom a, .tuple #[u₁, boolAtom p₁]) :: xs) → FieldsV E l₂ →
      (∀ e ∈ l₂, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt) →
      InterV E den (Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm xs) (tagField t₁)
        (fieldsTerm l₂) (tagField t₂) (mergeFunV₁ ifun S)) t₁ t₂ tR xs l₂ (xs ++ l₂) →
      InterV E den (Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) (.atom a)
          (.tuple #[u₁, boolAtom p₁]) (tagField t₂) >>= fun c =>
        Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm xs) (tagField t₁)
          (fieldsTerm l₂) (tagField t₂) (mergeFunV₁ ifun S) >>= fun t => pure (Term.cons (.tuple #[.atom a, c]) t))
        t₁ t₂ tR ((Term.atom a, Term.tuple #[u₁, boolAtom p₁]) :: xs) l₂ (((Term.atom a, Term.tuple #[u₁, boolAtom p₁]) :: xs) ++ l₂) := by
    intro a u₁ p₁ xs l₂ f₁ h₁ h₂ above ih
    obtain ⟨c, lc, semc, ⟨-, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom a) f₁ E₂ p₁ Bool.true <;>
      rw [← df₂] at lam
    · rcases ih with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
      · left
        refine ⟨(.atom a, .tuple #[c, boolAtom (p₁ && Bool.true)]) :: l, by simp [lam, run, fieldsTerm_cons], ?_,
          fun e me => ?_, fun s o => ?_⟩
        · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
          obtain ⟨e', me', ee⟩ := keys e me
          rw [ee]
          rcases List.mem_append.mp me' with m' | m'
          · exact fieldsV_head h₁ e' m'
          · exact above e' m'
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨_, List.mem_cons_self, rfl⟩
          · obtain ⟨e', me', ee⟩ := keys e me
            exact ⟨e', List.mem_cons_of_mem _ me', ee⟩
        · by_cases e : a = s
          · subst e
            rw [fsem_cons_self, fsem_cons_self, dsem₂ (lookup_above above)]
            exact meet_field_sem semc o
          · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
      · right
        exact ⟨disj_cons₁ h₁ above disj, by simp [lam, run]⟩
    · right
      refine ⟨⟨a, fun o ⟨g₁', g₂'⟩ => meet_field_empty semc thrown.1 thrown.2 o
        ⟨(fsem_cons_self _ _ _ _ _).mp g₁', (dsem₂ (lookup_above above) o).mp g₂'⟩⟩, by simp [lam]⟩
  -- a key of the second literal only, meeting the default field of the first
  have stepR : ∀ (b : String) (u₂ : Term) (p₂ : Bool) (l₁ ys : List (Term × Term)),
      E u₂ → FieldsV E l₁ → FieldsV E ((.atom b, .tuple #[u₂, boolAtom p₂]) :: ys) →
      (∀ e ∈ l₁, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt) →
      InterV E den (Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm l₁) (tagField t₁)
        (fieldsTerm ys) (tagField t₂) (mergeFunV₁ ifun S)) t₁ t₂ tR l₁ ys (l₁ ++ ys) →
      InterV E den (Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D n) ifun (.map S) (.atom b)
          (tagField t₁) (.tuple #[u₂, boolAtom p₂]) >>= fun c =>
        Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D (n + 1)) (fieldsTerm l₁) (tagField t₁)
          (fieldsTerm ys) (tagField t₂) (mergeFunV₁ ifun S) >>= fun t => pure (Term.cons (.tuple #[.atom b, c]) t))
        t₁ t₂ tR l₁ ((Term.atom b, Term.tuple #[u₂, boolAtom p₂]) :: ys) (l₁ ++ (Term.atom b, Term.tuple #[u₂, boolAtom p₂]) :: ys) := by
    intro b u₂ p₂ l₁ ys f₂ h₁ h₂ above ih
    obtain ⟨c, lc, semc, ⟨-, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom b) E₁ f₂ Bool.true p₂ <;>
      rw [← df₁] at lam
    · rcases ih with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
      · left
        refine ⟨(.atom b, .tuple #[c, boolAtom (Bool.true && p₂)]) :: l, by simp [lam, run, fieldsTerm_cons], ?_,
          fun e me => ?_, fun s o => ?_⟩
        · refine fieldsV_cons ⟨b, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
          obtain ⟨e', me', ee⟩ := keys e me
          rw [ee]
          rcases List.mem_append.mp me' with m' | m'
          · exact above e' m'
          · exact fieldsV_head h₂ e' m'
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨(.atom b, .tuple #[u₂, boolAtom p₂]), by simp, rfl⟩
          · obtain ⟨e', me', ee⟩ := keys e me
            exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
        · by_cases e : b = s
          · subst e
            rw [fsem_cons_self, fsem_cons_self, dsem₁ (lookup_above above)]
            exact meet_field_sem semc o
          · rw [fsem_cons_ne e, fsem_cons_ne e, sem]
      · right
        exact ⟨disj_cons₂ h₂ above disj, by simp [lam, run]⟩
    · right
      refine ⟨⟨b, fun o ⟨g₁', g₂'⟩ => meet_field_empty semc thrown.1 thrown.2 o
        ⟨(dsem₁ (lookup_above above) o).mp g₁', (fsem_cons_self _ _ _ _ _).mp g₂'⟩⟩, by simp [lam]⟩
  have lk : ∀ s : String, mapLookup ([] : List (Term × Term)) (.atom s) = Option.none := fun s => by simp [mapLookup]
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    left
    refine ⟨[], ?_, ⟨by simp, by simp⟩, by simp, fun s o => by simp only [FSem, lk]; exact htag o⟩
    rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], [] =>
      left
      refine ⟨[], ?_, ⟨by simp, by simp⟩, by simp, fun s o => by simp only [FSem, lk]; exact htag o⟩
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]
    | [], (k₂, v₂) :: ys =>
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨u₂, p₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have r := stepR b u₂ p₂ [] ys f₂ h₁ h₂ (by simp) (ih [] ys (by simp at size ⊢; omega) h₁ (fieldsV_tail h₂))
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simpa [fieldsTerm, Term.list, merge_fun₁_call] using r
    | (k₁, v₁) :: xs, [] =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨u₁, p₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      have r := stepL a u₁ p₁ xs [] f₁ h₁ h₂ (by simp) (ih xs [] (by simp at size ⊢; omega) (fieldsV_tail h₁) h₂)
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simpa [fieldsTerm, Term.list, merge_fun₁_call] using r
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨u₁, p₁, rfl, f₁⟩ := (h₁.1 _ List.mem_cons_self).2
      obtain ⟨u₂, p₂, rfl, f₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have sx := fieldsV_tail h₁
      have sy := fieldsV_tail h₂
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · have above : ∀ e ∈ (Term.atom b, Term.tuple #[u₂, boolAtom p₂]) :: ys, Term.compare (Term.fuel (.atom a) e.1) (.atom a) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp
          · exact cmp_lt_trans cmp (fieldsV_head h₂ e me)
        have r := stepL a u₁ p₁ xs _ f₁ h₁ h₂ above (ih xs _ (by simp; omega) sx h₂)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simpa [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», cmp] using r
      · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        obtain ⟨c, lc, semc, ⟨-, lam⟩ | ⟨thrown, lam⟩⟩ := merge_fun_val ops dops esem hK hn hI hS (.atom a) f₁ f₂ p₁ p₂
        · rcases ih xs ys (by omega) sx sy with ⟨l, run, sl, keys, sem⟩ | ⟨disj, run⟩
          · left
            refine ⟨(.atom a, .tuple #[c, boolAtom (p₁ && p₂)]) :: l, ?_, ?_, fun e me => ?_, fun s o => ?_⟩
            · rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
              simp [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2»] at run ⊢
              simp [lam, run]
            · refine fieldsV_cons ⟨a, rfl⟩ ⟨c, _, rfl, lc⟩ sl fun e me => ?_
              obtain ⟨e', me', ee⟩ := keys e me
              rw [ee]
              rcases List.mem_append.mp me' with m' | m'
              · exact fieldsV_head h₁ e' m'
              · exact fieldsV_head h₂ e' m'
            · rcases List.mem_cons.mp me with rfl | me
              · exact ⟨_, List.mem_cons_self, rfl⟩
              · obtain ⟨e', me', ee⟩ := keys e me
                exact ⟨e', by rcases List.mem_append.mp me' with h | h <;> simp [h], ee⟩
            · by_cases e : a = s
              · subst e
                rw [fsem_cons_self, fsem_cons_self, fsem_cons_self]
                exact meet_field_sem semc o
              · rw [fsem_cons_ne e, fsem_cons_ne e, fsem_cons_ne e, sem]
          · right
            refine ⟨disj_both h₁ h₂ disj, ?_⟩
            rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
            simp [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2»] at run ⊢
            simp [lam, run]
        · right
          refine ⟨⟨a, fun o ⟨g₁', g₂'⟩ => ?_⟩, ?_⟩
          · rw [fsem_cons_self] at g₁' g₂'
            exact meet_field_empty semc thrown.1 thrown.2 o ⟨g₁', g₂'⟩
          · rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
            simp [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
            simp [lam]
      · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ e ∈ (Term.atom a, Term.tuple #[u₁, boolAtom p₁]) :: xs, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt := by
          intro e me
          rcases List.mem_cons.mp me with rfl | me
          · exact cmp'
          · exact cmp_lt_trans cmp' (fieldsV_head h₁ e me)
        have r := stepR b u₂ p₂ _ ys f₂ h₁ h₂ above (ih _ ys (by simp; omega) h₁ sy)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simpa [fieldsTerm, Term.list, merge_fun₁_call, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] using r

/-- Map literal intersections on value maps: a literal of the maps of both, or `:empty` when they share none. -/
def LitInterV (E : Term → Prop) (den : Term → V → Prop) (r : Except Exception Term) (t₁ t₂ : Term) (l₁ l₂ : List (Term × Term)) : Prop :=
  (∃ (tR : Term) (l : List (Term × Term)), r = .ok (.tuple #[tR, fieldsTerm l]) ∧ TagV E tR ∧ FieldsV E l ∧
    ∀ w, MSem den tR l w ↔ MSem den t₁ l₁ w ∧ MSem den t₂ l₂ w) ∨
  ((∀ w, ¬(MSem den t₁ l₁ w ∧ MSem den t₂ l₂ w)) ∧ r = .error (Exception.throw (.atom "empty")))

theorem InterV.lit {r : Except Exception Term} {t₁ t₂ tR : Term} {l₁ l₂ ks : List (Term × Term)}
    (h : InterV E den r t₁ t₂ tR l₁ l₂ ks) (g : TagV E tR)
    (dom : ∀ kind o, TagSem den tR kind o ↔ TagSem den t₁ kind o ∧ TagSem den t₂ kind o) :
    LitInterV E den (r >>= fun f => pure (Term.tuple #[tR, f])) t₁ t₂ l₁ l₂ := by
  rcases h with ⟨l, run, sl, -, sem⟩ | ⟨⟨s, hs⟩, run⟩
  · refine Or.inl ⟨tR, l, by simp [run], g, sl, fun w => ?_⟩
    exact ⟨fun h => ⟨⟨fun s => ((sem s _).mp (h s)).1, fun k i => ((dom _ _).mp (h.doms k i)).1⟩,
        ⟨fun s => ((sem s _).mp (h s)).2, fun k i => ((dom _ _).mp (h.doms k i)).2⟩⟩,
      fun h => ⟨fun s => (sem s _).mpr ⟨h.1 s, h.2 s⟩, fun k i => (dom _ _).mpr ⟨h.1.doms k i, h.2.doms k i⟩⟩⟩
  · exact Or.inr ⟨fun w h => hs (w (.atom s)) ⟨h.1 s, h.2 s⟩, by simp [run]⟩

/-- Open and closed tags allow at keys outside fields what both allow when open exactly if both are. -/
theorem tagSem_atom_meet {t₁ t₂ tR : String} (htag : tR = "open" ↔ t₁ = "open" ∧ t₂ = "open") (kind : String)
    (o : Option V) : TagSem den (.atom tR) kind o ↔ TagSem den (.atom t₁) kind o ∧ TagSem den (.atom t₂) kind o := by
  simp only [tagSem_atom]
  constructor
  · rintro (h | h)
    · obtain ⟨h₁, h₂⟩ := htag.mp h
      exact ⟨Or.inl h₁, Or.inl h₂⟩
    · exact ⟨Or.inr h, Or.inr h⟩
  · rintro ⟨h₁ | h₁, h₂ | h₂⟩
    · exact Or.inl (htag.mpr ⟨h₁, h₂⟩)
    all_goals exact Or.inr ‹_›

theorem LitInterV.swap {r : Except Exception Term} {t₁ t₂ : Term} {l₁ l₂ : List (Term × Term)}
    (h : LitInterV E den r t₂ t₁ l₂ l₁) : LitInterV E den r t₁ t₂ l₁ l₂ := by
  rcases h with ⟨tR, l, run, g, sl, sem⟩ | ⟨disj, run⟩
  · exact Or.inl ⟨tR, l, run, g, sl, fun w => (sem w).trans And.comm⟩
  · exact Or.inr ⟨fun w h => disj w ⟨h.2, h.1⟩, run⟩

/-- `map_literal_intersection/6` on value maps. -/
theorem literal_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {Kf m : Nat} (hK : Kf + 1 ≤ m) (hm : K + 1 ≤ m) {ifun : Term} (hI : IFun E den Kf ifun)
    {S : List (Term × Term)} (hS : Safe S) {t₁ t₂ : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂)
    {l₁ l₂ : List (Term × Term)} (h₁ : FieldsV E l₁) (h₂ : FieldsV E l₂) :
    LitInterV E den (Elixir.Module.Types.Descr.«map_literal_intersection/6» (D m) t₁ (fieldsTerm l₁) t₂
      (fieldsTerm l₂) ifun (.map S)) t₁ t₂ l₁ l₂ := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  have hK' : Kf ≤ n + 1 := by omega
  have general : (∀ s₁ s₂, ¬(t₁ = .atom s₁ ∧ t₂ = .atom s₂)) → LitInterV E den
      (Elixir.Module.Types.Descr.«map_literal_intersection/6» (D (n + 1)) t₁ (fieldsTerm l₁) t₂ (fieldsTerm l₂)
        ifun (.map S)) t₁ t₂ l₁ l₂ := by
    intro notAtoms
    obtain ⟨tR, runT, gR, semT⟩ := domain_inter_val ops dops esem (show K ≤ n + 1 by omega) hS g₁ g₂
    have merged := (merge_defaults_val ops dops esem (show Kf ≤ n by omega) (by omega) hI hS g₁ g₂ (semT "atom") _ l₁ l₂
      (Nat.le_refl _) h₁ h₂).lit gR semT
    unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
    split <;> try (exfalso; exact notAtoms _ _ ⟨rfl, rfl⟩)
    simpa [key_tag_field g₁, key_tag_field g₂, runT, mergeFunV₁] using merged
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, -⟩ <;> rcases g₂ with rfl | rfl | ⟨dl₂, rfl, -⟩ <;>
    try exact general (fun _ _ h => fieldsTerm_ne_atom _ _ (by first | exact h.1 | exact h.2))
  all_goals unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»; simp only [pure_bind]
  · exact (merge_val ops dops esem (show Kf ≤ n by omega) (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).lit
      (TagV.atom (Or.inl rfl)) (tagSem_atom_meet (by simp))
  · exact (open_closed_val ops dops esem hK' (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).lit
      (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp))
  · exact LitInterV.swap ((open_closed_val ops dops esem hK' (by omega) hI hS _ l₂ l₁ (Nat.le_refl _) h₂ h₁).lit
      (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp)))
  · exact (closed_val ops dops esem hK' (by omega) hI hS _ l₁ l₂ (Nat.le_refl _) h₁ h₂).lit
      (TagV.atom (Or.inr rfl)) (tagSem_atom_meet (by simp))

end Elixir.STTDescrProofsTest.Nest
