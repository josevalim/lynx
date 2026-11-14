namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-! Maps of values: keys to values, absent at the other keys. Keys are atoms, or keys of the other kinds that
map domains name, of which a map has any number. -/

/-- The kinds of keys of map domains, other than atoms. -/
def domKind (k : Fin 11) : String :=
  ["binary", "bitstring_no_binary", "float", "fun", "integer", "list", "map", "pid", "port", "reference",
    "tuple"][k]

inductive MKey where
  | atom (s : String)
  | dom (k : Fin 11) (i : Nat)
deriving DecidableEq

abbrev MW (V : Type) : Type := MKey → Option V

/-- The values a field allows at its key: absent when optional, or a value of its type. -/
def FieldSem (den : Term → V → Prop) (f : Term) (o : Option V) : Prop :=
  ∃ (t : Term) (opt : Bool), f = .tuple #[t, boolAtom opt] ∧ ((o = Option.none ∧ opt = Bool.true) ∨ ∃ x, o = some x ∧ den t x)

/-- The pairs of a list of domains. -/
def domFields : Term → List (Term × Term)
  | .cons (.tuple ⟨[k, t]⟩) rest => (k, t) :: domFields rest
  | _ => []

/-- The values a tag allows at the keys of a kind outside the fields of a literal: anything for open literals,
nothing for closed ones, and those of the domain of the kind, if any, for domains. -/
def TagSem (den : Term → V → Prop) (tag : Term) (kind : String) (o : Option V) : Prop :=
  match tag with
  | .atom t => t = "open" ∨ o = Option.none
  | t => FieldSem den (.tuple #[(mapLookup (domFields t) (.atom kind)).getD (.map []), .atom "true"]) o

/-- The values a map literal allows at an atom key: those of its field, or what its tag allows. -/
def FSem (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) (s : String) (o : Option V) : Prop :=
  match mapLookup l (.atom s) with
  | some f => FieldSem den f o
  | Option.none => TagSem den tag "atom" o

/-- Maps in a map literal of a tag and fields: atom keys hold what the literal allows, and the keys of other kinds
what its tag allows. -/
structure MSem (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) (w : (MW V)) : Prop where
  atoms : ∀ s, FSem den tag l s (w (.atom s))
  doms : ∀ k i, TagSem den tag (domKind k) (w (.dom k i))

instance {den : Term → V → Prop} {tag : Term} {l : List (Term × Term)} {w : MW V} :
    CoeFun (MSem den tag l w) (fun _ => ∀ s, FSem den tag l s (w (.atom s))) := ⟨MSem.atoms⟩

theorem tagSem_atom {tag kind : String} (o : Option V) :
    TagSem den (.atom tag) kind o ↔ (tag = "open" ∨ o = Option.none) := Iff.rfl

theorem MSem.of_atoms {tag : Term} {l l' : List (Term × Term)} {w : MW V} (m : MSem den tag l w)
    (h : ∀ s, FSem den tag l s (w (.atom s)) → FSem den tag l' s (w (.atom s))) : MSem den tag l' w :=
  ⟨fun s => h s (m s), m.doms⟩

theorem msem_congr {tag : Term} {l l' : List (Term × Term)} {w : MW V}
    (h : ∀ s, FSem den tag l s (w (.atom s)) ↔ FSem den tag l' s (w (.atom s))) : MSem den tag l w ↔ MSem den tag l' w :=
  ⟨fun m => m.of_atoms fun s => (h s).mp, fun m => m.of_atoms fun s => (h s).mpr⟩

theorem fieldSem_mk {t : Term} {opt : Bool} {o : Option V} :
    FieldSem den (.tuple #[t, boolAtom opt]) o ↔ ((o = Option.none ∧ opt = Bool.true) ∨ ∃ x, o = some x ∧ den t x) := by
  constructor
  · rintro ⟨t', opt', e, h⟩
    simp only [Term.tuple.injEq] at e
    have e₀ := congrArg (fun a : Array Term => a[0]?) e
    have e₁ := congrArg (fun a : Array Term => a[1]?) e
    simp at e₀ e₁
    subst e₀
    have : opt = opt' := by cases opt <;> cases opt' <;> simp_all [boolAtom]
    subst this
    exact h
  · intro h; exact ⟨t, opt, rfl, h⟩

/-- Meets of fields allow what both allow. -/
theorem fieldSem_meet {t₁ t₂ t : Term} {o₁ o₂ : Bool} (sem : ∀ x, den t x ↔ den t₁ x ∧ den t₂ x) (o : Option V) :
    FieldSem den (.tuple #[t, boolAtom (o₁ && o₂)]) o ↔
      FieldSem den (.tuple #[t₁, boolAtom o₁]) o ∧ FieldSem den (.tuple #[t₂, boolAtom o₂]) o := by
  simp only [fieldSem_mk]
  cases o with
  | none => cases o₁ <;> cases o₂ <;> simp
  | some x => simp [sem x]

/-- Differences of fields allow what the first allows and the second does not. -/
theorem fieldSem_diff {t₁ t₂ t : Term} {o₁ o₂ : Bool} (sem : ∀ x, den t x ↔ den t₁ x ∧ ¬den t₂ x) (o : Option V) :
    FieldSem den (.tuple #[t, boolAtom (o₁ && !o₂)]) o ↔
      FieldSem den (.tuple #[t₁, boolAtom o₁]) o ∧ ¬FieldSem den (.tuple #[t₂, boolAtom o₂]) o := by
  simp only [fieldSem_mk]
  cases o with
  | none => cases o₁ <;> cases o₂ <;> simp
  | some x => simp [sem x]

/-- `field_empty_seen?/3` finds fields that allow nothing. -/
theorem field_empty_sem (_ops : ElemOk E K) (_dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {t : Term} (ht : E t) {o : Bool} {S : List (Term × Term)}
    (hS : Safe S) {m : Nat} (hm : K ≤ m) {b : Bool}
    (run : Elixir.Module.Types.Descr.«field_empty_seen?/3» (D m) t (boolAtom o) (.map S) = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ x, ¬FieldSem den (.tuple #[t, boolAtom o]) x := by
  cases o
  · simp only [boolAtom, Bool.false_eq_true, ite_false] at run
    rw [Elixir.Module.Types.Descr.«field_empty_seen?/3».eq_def] at run
    simp only at run
    rw [esem.empty ht hS hm run]
    simp only [fieldSem_mk]
    constructor
    · intro h x hx
      rcases hx with ⟨-, h'⟩ | ⟨y, -, hy⟩
      · cases h'
      · exact h y hy
    · intro h y hy
      exact h (some y) (Or.inr ⟨y, rfl, hy⟩)
  · simp only [boolAtom, ite_true] at run
    rw [Elixir.Module.Types.Descr.«field_empty_seen?/3».eq_def] at run
    simp at run
    have : b = Bool.false := by cases b <;> simp_all
    subst this
    simp only [Bool.false_eq_true, false_iff]
    exact fun h => h Option.none ((fieldSem_mk (opt := Bool.true)).mpr (Or.inl ⟨rfl, rfl⟩))

theorem fresh_name (names : List String) : ∃ s : String, s ∉ names := by
  have le : ∀ (names : List String), ∀ n ∈ names, n.length ≤ (names.map String.length).sum := by
    intro names
    induction names with
    | nil => simp
    | cons x xs ih =>
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · simp
      · have := ih n hn; simp; omega
  refine ⟨String.ofList (List.replicate (names.map String.length).sum.succ 'a'), fun h => ?_⟩
  have := le names _ h
  simp at this
  omega

theorem atoms_cmp (a b : String) : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b) = compare a b :=
  Term.compare_atoms a b

/-- Fields of value maps: atom keys in increasing order, holding fields of element types. -/
def FieldsV (E : Term → Prop) (l : List (Term × Term)) : Prop :=
  (∀ e ∈ l, (∃ s : String, e.1 = .atom s) ∧ FieldValue E e.2) ∧
    l.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt)

/-- Fields that allow some value at their key. -/
def Inhabited (den : Term → V → Prop) (l : List (Term × Term)) : Prop := ∀ e ∈ l, ∃ o, FieldSem den e.2 o

theorem lookup_cons_atom (a s : String) (f : Term) (t : List (Term × Term)) :
    mapLookup ((.atom a, f) :: t) (.atom s) = if a = s then some f else mapLookup t (.atom s) := by
  unfold mapLookup
  by_cases h : a = s
  · subst h; simp
  · have : ¬compare s a = .eq := fun e => h (Std.compare_eq_iff_eq.mp e).symm
    simp [this, h]

theorem lookup_append (A B : List (Term × Term)) (k : Term) :
    mapLookup (A ++ B) k = (mapLookup A k).or (mapLookup B k) := by
  unfold mapLookup
  rw [List.find?_append]
  cases A.find? (fun entry => decide (compareExact (fuel k entry.1) k entry.1 = .eq)) <;> simp

theorem lookup_mem {l : List (Term × Term)} {k f : Term} (h : mapLookup l k = some f) : ∃ e ∈ l, e.2 = f := by
  unfold mapLookup at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_of_find?_eq_some he, rfl⟩

theorem lookup_none {l : List (Term × Term)} {s : String} (h : ∀ e ∈ l, e.1 ≠ .atom s) :
    mapLookup l (.atom s) = Option.none := by
  unfold mapLookup
  simp only [Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro e he eq
  exact h e he ((atom_compareExact_eq s e.1).mp eq)

theorem fsem_cons_self (tag : Term) (a : String) (f : Term) (t : List (Term × Term)) (o : Option V) :
    FSem den tag ((.atom a, f) :: t) a o ↔ FieldSem den f o := by
  simp [FSem, lookup_cons_atom]

theorem fsem_cons_ne {tag : Term} {a s : String} (h : a ≠ s) (f : Term) (t : List (Term × Term)) (o : Option V) :
    FSem den tag ((.atom a, f) :: t) s o ↔ FSem den tag t s o := by
  simp [FSem, lookup_cons_atom, h]

theorem fsem_none {tag s : String} {l : List (Term × Term)} (h : mapLookup l (.atom s) = Option.none) (o : Option V) :
    FSem den (.atom tag) l s o ↔ (tag = "open" ∨ o = Option.none) := by
  simp [FSem, TagSem, h]

/-- Tags allow keys outside fields to be absent. -/
theorem tagSem_none (tag : Term) (kind : String) : TagSem den tag kind Option.none := by
  unfold TagSem
  split
  · exact Or.inr rfl
  · exact ⟨_, Bool.true, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Element types hold the empty type, which has no values. -/
theorem sem_none (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) :
    E (.map []) ∧ ∀ v, ¬den (.map []) v := by
  obtain ⟨c, hc, run⟩ := dops.diff ops.term ops.term
  have e := run K (Nat.le_refl K)
  rw [diff_term_right] at e
  cases e
  exact ⟨hc, fun v h => by have := (esem.diff ops.term ops.term (Nat.le_refl K) (diff_term_right _ _) v).mp h; exact this.2 this.1⟩

/-- The type a tag gives the keys of a kind outside the fields of a literal. -/
def tagType (tag : Term) (kind : String) : Term :=
  match tag with
  | .atom t => if t = "open" then .atom "term" else .map []
  | t => (mapLookup (domFields t) (.atom kind)).getD (.map [])

/-- The field a tag gives the atom keys outside a map literal. -/
def tagField (tag : Term) : Term := .tuple #[tagType tag "atom", .atom "true"]

/-- The kinds of keys that map domains name. -/
def domainKinds : List String :=
  ["atom", "binary", "bitstring_no_binary", "float", "fun", "integer", "list", "map", "pid", "port", "reference",
    "tuple"]

/-- Domains of value maps: kinds of keys in increasing order, holding element types. -/
def DomsV (E : Term → Prop) (dl : List (Term × Term)) : Prop :=
  (∀ e ∈ dl, (∃ s, e.1 = .atom s ∧ s ∈ domainKinds) ∧ E e.2) ∧
    dl.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt)

/-- Tags of value maps: open, closed, or domains. -/
def TagV (E : Term → Prop) (tag : Term) : Prop :=
  tag = .atom "open" ∨ tag = .atom "closed" ∨ ∃ dl, tag = fieldsTerm dl ∧ DomsV E dl

theorem domFields_fieldsTerm : ∀ dl : List (Term × Term), domFields (fieldsTerm dl) = dl
  | [] => by simp [fieldsTerm, Term.list, domFields]
  | (a, b) :: t => by
    simp only [fieldsTerm_cons, domFields]
    rw [domFields_fieldsTerm t]

theorem tagType_dom (dl : List (Term × Term)) (kind : String) :
    tagType (fieldsTerm dl) kind = (mapLookup dl (.atom kind)).getD (.map []) := by
  have h := domFields_fieldsTerm dl
  have ne := fieldsTerm_ne_atom dl
  generalize fieldsTerm dl = T at h ne
  unfold tagType
  split
  · exact absurd rfl (ne _)
  · rw [h]

theorem tagSem_dom (dl : List (Term × Term)) (kind : String) (o : Option V) :
    TagSem den (fieldsTerm dl) kind o ↔ FieldSem den (.tuple #[(mapLookup dl (.atom kind)).getD (.map []), .atom "true"]) o := by
  have h := domFields_fieldsTerm dl
  have ne := fieldsTerm_ne_atom dl
  generalize fieldsTerm dl = T at h ne
  unfold TagSem
  split
  · exact absurd rfl (ne _)
  · rw [h]

theorem fieldSem_tag (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {tag : String}
    (g : tag = "open" ∨ tag = "closed") (o : Option V) :
    FieldSem den (tagField (.atom tag)) o ↔ (tag = "open" ∨ o = Option.none) := by
  have hterm := esem.term
  have hnone := (sem_none ops dops esem).2
  have e : tagField (.atom tag) = .tuple #[if tag = "open" then .atom "term" else .map [], boolAtom Bool.true] := rfl
  rw [e, fieldSem_mk]
  rcases g with rfl | rfl
  · cases o <;> simp [hterm]
  · cases o <;> simp [hnone]

/-- The default field of a tag holds what the tag allows at atom keys outside the fields of a literal. -/
theorem fieldSem_tagV (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {tag : Term}
    (g : TagV E tag) (o : Option V) : FieldSem den (tagField tag) o ↔ TagSem den tag "atom" o := by
  rcases g with rfl | rfl | ⟨dl, rfl, -⟩
  · exact (fieldSem_tag ops dops esem (Or.inl rfl) o).trans (tagSem_atom o).symm
  · exact (fieldSem_tag ops dops esem (Or.inr rfl) o).trans (tagSem_atom o).symm
  · rw [tagField, tagType_dom, tagSem_dom]

theorem tagType_value (ops : ElemOk E K) {tag : Term} (g : TagV E tag) (kind : String) : E (tagType tag kind) := by
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · exact ops.term
  · exact ops.none
  · rw [tagType_dom]
    cases h : mapLookup dl (.atom kind) with
    | none => exact ops.none
    | some t =>
      obtain ⟨e, me, rfl⟩ := lookup_mem h
      exact (dv.1 e me).2

theorem tagFieldV_value (ops : ElemOk E K) {tag : Term} (g : TagV E tag) : FieldValue E (tagField tag) :=
  ⟨_, Bool.true, rfl, tagType_value ops g "atom"⟩

theorem find_dom (a : String) : ∀ {dl : List (Term × Term)}, DomsV E dl →
    Erlang.orddict.«find/2» (.atom a) (fieldsTerm dl) =
      match mapLookup dl (.atom a) with
      | some f => .ok (.tuple #[.atom "ok", f])
      | none => .ok (.atom "error")
  | [], _ => by rw [Erlang.orddict.«find/2».eq_def]; simp [fieldsTerm, Term.list, mapLookup]
  | (k, v) :: t, dv => by
    obtain ⟨⟨b, rfl, -⟩, -⟩ := dv.1 _ List.mem_cons_self
    have st : DomsV E t := ⟨fun e me => dv.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp dv.2).2⟩
    have hd := (List.pairwise_cons.mp dv.2).1
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have none : mapLookup t (.atom a) = Option.none := lookup_none fun e me eq => by
        have := Lynx.Term.compare_lt_trans cmp (hd e me)
        rw [eq, compare_self] at this; cases this
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_right ne, none]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_left rfl]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have ih := find_dom a st
      rw [Erlang.orddict.«find/2».eq_def, lookup_cons_atom, ite_eq_right ne, ← ih]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]

/-- `map_key_tag_to_field/1` gives the default field of a tag. -/
theorem key_tag_field {tag : Term} (g : TagV E tag) :
    Elixir.Module.Types.Descr.«map_key_tag_to_field/1» tag = .ok (tagField tag) := by
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · simp [Elixir.Module.Types.Descr.«map_key_tag_to_field/1», tagField, tagType]
  · simp [Elixir.Module.Types.Descr.«map_key_tag_to_field/1», tagField, tagType]
  · have f := find_dom "atom" dv
    have ne := fieldsTerm_ne_atom dl
    rw [tagField, tagType_dom]
    generalize fieldsTerm dl = T at f ne
    rw [Elixir.Module.Types.Descr.«map_key_tag_to_field/1».eq_def]
    split
    · exact absurd rfl (ne _)
    · exact absurd rfl (ne _)
    · rw [f]; cases mapLookup dl (.atom "atom") <;> rfl

/-- Fields that allow values have maps of every tag. -/
theorem msem_witness {l : List (Term × Term)} (h : Inhabited den l) (tag : Term) : ∃ w, MSem den tag l w := by
  classical
  have each : ∀ s, ∃ o, FSem den tag l s o := by
    intro s
    unfold FSem
    cases e : mapLookup l (.atom s) with
    | none => exact ⟨Option.none, tagSem_none tag "atom"⟩
    | some f =>
      obtain ⟨x, hx, rfl⟩ := lookup_mem e
      exact h x hx
  refine ⟨fun k => match k with | .atom s => Classical.choose (each s) | .dom _ _ => Option.none,
    fun s => Classical.choose_spec (each s), fun k i => tagSem_none tag _⟩

/-- The atom names of keys. -/
def keyNames (l : List (Term × Term)) : List String :=
  l.filterMap fun e => match e.1 with | .atom s => some s | _ => Option.none

theorem lookup_fresh {l : List (Term × Term)} {s : String} (h : s ∉ keyNames l) : mapLookup l (.atom s) = Option.none := by
  refine lookup_none fun e he eq => h ?_
  simp only [keyNames, List.mem_filterMap]
  exact ⟨e, he, by rw [eq]⟩

/-- Inclusions of open or closed literals at their atom keys hold at the keys of other kinds: a fresh atom key
shows that the first is closed or the second open. -/
theorem tagSem_of_atoms {t₁ t₂ : String} {l₁ l₂ : List (Term × Term)} (v : V)
    (sub : ∀ s o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o) (kind : String) (o : Option V)
    (h : TagSem den (.atom t₁) kind o) : TagSem den (.atom t₂) kind o := by
  obtain ⟨s, hs⟩ := fresh_name (keyNames l₁ ++ keyNames l₂)
  simp only [List.mem_append, not_or] at hs
  have := sub s (some v)
  rw [fsem_none (lookup_fresh hs.1), fsem_none (lookup_fresh hs.2)] at this
  simp only [tagSem_atom] at h ⊢
  rcases h with h | h
  · exact Or.inl (by simpa using this (Or.inl h))
  · exact Or.inr h

theorem msem_of_atoms {t₁ t₂ : String} {l₁ l₂ : List (Term × Term)} (v : V)
    (sub : ∀ s o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o) {w : MW V}
    (h : MSem den (.atom t₁) l₁ w) : MSem den (.atom t₂) l₂ w :=
  ⟨fun s => sub s _ (h s), fun k i => tagSem_of_atoms v sub _ _ (h.doms k i)⟩

end Elixir.STTDescrProofsTest.Nest
