namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized unions of map literals on value maps. -/

/-- `field_subtype?/2` returns a Boolean, and `true` only when the first field allows less. -/
theorem field_sub_bool (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) :
    ∃ s : Bool, Elixir.Module.Types.Descr.«field_subtype?/2» (D m) f₁ f₂ = .ok (boolAtom s) ∧
      (s = Bool.true → ∀ o, FieldSem den f₁ o → FieldSem den f₂ o) := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  obtain ⟨b, run, sound⟩ := sub_bool ef hm ht₁ ht₂
  refine ⟨(!o₁ || o₂) && b, ?_, fun e o h => ?_⟩
  · rw [Elixir.Module.Types.Descr.«field_subtype?/2».eq_def]
    cases o₁ <;> cases o₂ <;> cases b <;> simp [boolAtom, run, Lynx.Except.andAlso]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at e
    obtain ⟨eo, eb⟩ := e
    rw [fieldSem_mk] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | ⟨x, rfl, hx⟩
    · simp at eo; exact Or.inl ⟨rfl, eo⟩
    · exact Or.inr ⟨x, rfl, sound eb x hx⟩

/-- Fields that compare exactly equal allow the same values. -/
theorem fieldSem_exact (ef : EF nd E V den tl K) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂)
    (h : compareExact (fuel f₂ f₁) f₂ f₁ = .eq) (o : Option V) : FieldSem den f₁ o ↔ FieldSem den f₂ o := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  rw [compareExact_tuple] at h
  simp [List.compareLex_cons_cons] at h
  obtain ⟨et, eo, -⟩ := h
  have oo : o₁ = o₂ := by
    cases o₁ <;> cases o₂ <;> simp_all [boolAtom] <;> simp [compareExact_step, Compare.compareStep] at eo
  subst oo
  have same := same_of_exact ef ht₁ ht₂ et
  rw [fieldSem_mk, fieldSem_mk]
  simp [same _]

theorem fsem_tag_mono {t₁ t₂ s : String} {l : List (Term × Term)} (tags : t₁ = "open" → t₂ = "open") {o : Option V}
    (h : FSem den (.atom t₁) l s o) : FSem den (.atom t₂) l s o := by
  unfold FSem TagSem at h ⊢
  cases e : mapLookup l (.atom s) with
  | some f => simpa [e] using h
  | none =>
    simp only [e] at h ⊢
    rcases h with h | h
    · exact Or.inl (tags h)
    · exact Or.inr h

/-- Fields that agree at a key whatever the tag. -/
def EqvK (den : Term → V → Prop) (P₁ P₂ : List (Term × Term)) (s : String) : Prop := ∀ tag o, FSem den (.atom tag) P₁ s o ↔ FSem den (.atom tag) P₂ s o

/-- What the status of a walk over the fields of two map literals says about the walked fields. -/
def MInv (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (P₁ P₂ : List (Term × Term)) : Prop :=
  (st = .atom "all_equal" ∧ ∀ s, EqvK den P₁ P₂ s) ∨
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup P₁ (.atom a) = some p₁ ∧
    mapLookup P₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den P₁ P₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ ((t₁ = "open" → t₂ = "open") → ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o)) ∨
  (st = .atom "right_subtype_of_left" ∧ ((t₂ = "open" → t₁ = "open") → ∀ s o, FSem den (.atom t₂) P₂ s o → FSem den (.atom t₁) P₁ s o)) ∨
  st = .atom "none"

/-- What the result of the walk says about the fields of two map literals. -/
def MRes (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (l₁ l₂ : List (Term × Term)) : Prop :=
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup l₁ (.atom a) = some p₁ ∧
    mapLookup l₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den l₁ l₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ ∀ s o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o) ∨
  (st = .atom "right_subtype_of_left" ∧ ∀ s o, FSem den (.atom t₂) l₂ s o → FSem den (.atom t₁) l₁ s o) ∨
  st = .atom "none"

/-- Appending a key above the walked ones. -/
theorem lookup_snoc {P : List (Term × Term)} {a s : String} {f : Term}
    (below : ∀ e ∈ P, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    mapLookup (P ++ [(Term.atom a, f)]) (Term.atom s) = if a = s then some f else mapLookup P (Term.atom s) := by
  rw [lookup_append]
  by_cases e : a = s
  · subst e; rw [lookup_below below]; simp [lookup_cons_atom]
  · simp [lookup_cons_atom, e]
    cases mapLookup P (.atom s) <;> simp [mapLookup]

theorem fsem_snoc {tag : String} {P : List (Term × Term)} {a s : String} {f : Term}
    (below : ∀ e ∈ P, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) (o : Option V) :
    FSem den (Term.atom tag) (P ++ [(Term.atom a, f)]) s o ↔ if a = s then FieldSem den f o else FSem den (Term.atom tag) P s o := by
  unfold FSem TagSem
  rw [lookup_snoc below]
  by_cases e : a = s <;> simp [e]

theorem tags_open {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
    (h : ¬(t₁ = "open" ∧ t₂ = "closed")) : t₁ = "open" → t₂ = "open" := by
  intro e; subst e; rcases g₂ with rfl | rfl
  · rfl
  · exact absurd ⟨rfl, rfl⟩ h

theorem eqv_sub {t₁ t₂ : String} {P₁ P₂ : List (Term × Term)} (eqv : ∀ s, EqvK den P₁ P₂ s)
    (tags : t₁ = "open" → t₂ = "open") : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o :=
  fun s o h => (eqv s t₂ o).mp (fsem_tag_mono tags h)

/-- The walk ends on both fields at once. -/
theorem mres_end (d : Dispatcher) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
    {st : Term} {P₁ P₂ : List (Term × Term)} (inv : MInv E den t₁ t₂ st P₁ P₂) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d (fieldsTerm []) (fieldsTerm []) (.atom t₁)
      (.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res P₁ P₂ := by
  rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
  · -- equal fields: the open literal, if any, is the supertype
    rcases g₁ with rfl | rfl
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, eqv_sub (fun s => fun tag o => (h s tag o).symm)
        fun _ => rfl⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, eqv_sub h fun e => by simp at e⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inl ⟨a, p₁, p₂, rfl, h⟩⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list]
  · by_cases oc : t₁ = "open" ∧ t₂ = "closed"
    · obtain ⟨rfl, rfl⟩ := oc
      refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, h (tags_open g₁ g₂ oc)⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
        simp_all [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · by_cases oc : t₂ = "open" ∧ t₁ = "closed"
    · obtain ⟨rfl, rfl⟩ := oc
      refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, h (tags_open g₂ g₁ oc)⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
        simp_all [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list]

theorem fsem_append_notin {tag s : String} {A B : List (Term × Term)} (h : mapLookup B (.atom s) = Option.none)
    (o : Option V) : FSem den (Term.atom tag) (A ++ B) s o ↔ FSem den (Term.atom tag) A s o := by
  unfold FSem TagSem
  rw [lookup_append, h]
  cases mapLookup A (.atom s) <;> simp

/-- Fields of the first literal beyond the second, which is open, keep the first a subtype. -/
theorem left_extend {t₁ : String} {P₁ P₂ r₁ : List (Term × Term)}
    (h : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom "open") P₂ s o)
    (fresh : ∀ e ∈ r₁, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∀ s o, FSem den (Term.atom t₁) (P₁ ++ r₁) s o → FSem den (Term.atom "open") P₂ s o := by
  intro s o hs
  cases e : mapLookup P₂ (.atom s) with
  | none => exact (fsem_none e o).mpr (Or.inl rfl)
  | some f =>
    have notin : mapLookup r₁ (.atom s) = Option.none :=
      lookup_none fun x mx ex => by rw [fresh x mx s ex] at e; cases e
    exact h s o ((fsem_append_notin notin o).mp hs)

/-- Left subtypes from the walked fields of literals equal everywhere but at one key. -/
theorem one_key_sub {t₁ t₂ a : String} {P₁ P₂ : List (Term × Term)} {p₁ p₂ : Term}
    (l₁ : mapLookup P₁ (.atom a) = some p₁) (l₂ : mapLookup P₂ (.atom a) = some p₂)
    (eqv : ∀ s, s ≠ a → EqvK den P₁ P₂ s) (sub : ∀ o, FieldSem den p₁ o → FieldSem den p₂ o) (tags : t₁ = "open" → t₂ = "open") :
    ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o := by
  intro s o h
  by_cases e : s = a
  · subst e
    unfold FSem TagSem at h ⊢
    rw [l₁] at h; rw [l₂]
    exact sub o h
  · exact (eqv s e t₂ o).mp (fsem_tag_mono tags h)

/-- The walk ends on the second fields first. -/
theorem mres_tail₁ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (x : Term × Term)
    (xs : List (Term × Term)) (inv : MInv E den t₁ t₂ st P₁ P₂)
    (fresh : ∀ e ∈ x :: xs, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm (x :: xs)) (fieldsTerm [])
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res (P₁ ++ x :: xs) (P₂ ++ []) := by
  obtain ⟨k, v⟩ := x
  have none : MRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (k, v) :: xs) (P₂ ++ []) := Or.inr (Or.inr (Or.inr rfl))
  rcases g₂ with rfl | rfl
  · rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (eqv_sub h (fun _ => rfl)) fresh⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · obtain ⟨b, run, sound⟩ := field_sub_bool ef hm hp₁ hp₂
      cases b
      · refine ⟨_, ?_, none⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₁ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
      · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, by
          simpa using left_extend (one_key_sub l₁ l₂ eqv (sound rfl) (fun _ => rfl)) fresh⟩)⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₁ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
    · refine ⟨_, ?_, Or.inr (Or.inl ⟨rfl, by simpa using left_extend (h fun _ => rfl) fresh⟩)⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    all_goals
      refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
  · refine ⟨_, ?_, none⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl <;>
    rcases g₁ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«=:=/2», Erlang.erlang.«/=/2»]

theorem EqvK.symm {P₁ P₂ : List (Term × Term)} {s : String} (h : EqvK den P₁ P₂ s) : EqvK den P₂ P₁ s :=
  fun tag o => (h tag o).symm

/-- The walk ends on the first fields first. -/
theorem mres_tail₂ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (y : Term × Term)
    (ys : List (Term × Term)) (inv : MInv E den t₁ t₂ st P₁ P₂)
    (fresh : ∀ e ∈ y :: ys, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm []) (fieldsTerm (y :: ys))
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res (P₁ ++ []) (P₂ ++ y :: ys) := by
  obtain ⟨k, v⟩ := y
  have none : MRes E den t₁ t₂ (Term.atom "none") (P₁ ++ []) (P₂ ++ (k, v) :: ys) := Or.inr (Or.inr (Or.inr rfl))
  rcases g₁ with rfl | rfl
  · rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (eqv_sub (fun s => (h s).symm) (fun _ => rfl)) fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · obtain ⟨b, run, sound⟩ := field_sub_bool ef hm hp₂ hp₁
      cases b
      · refine ⟨_, ?_, none⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₂ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
      · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
          simpa using left_extend (one_key_sub l₂ l₁ (fun s ne => (eqv s ne).symm) (sound rfl) (fun _ => rfl))
            fresh⟩))⟩
        rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
        rcases g₂ with rfl | rfl <;>
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            run, boolAtom, Erlang.erlang.«/=/2»]
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (h fun _ => rfl) fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«=:=/2»]
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · refine ⟨_, ?_, none⟩
    rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
    rcases inv with ⟨rfl, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl <;>
    rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«=:=/2», Erlang.erlang.«/=/2»]

/-- A key of the first fields only, below the remaining keys of an open second literal. -/
theorem snoc_left {t₁ : String} {P₁ P₂ : List (Term × Term)} {a : String} {v : Term}
    (h : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom "open") P₂ s o) (fresh : mapLookup P₂ (.atom a) = Option.none)
    (below : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    ∀ s o, FSem den (Term.atom t₁) (P₁ ++ [(Term.atom a, v)]) s o → FSem den (Term.atom "open") P₂ s o := by
  intro s o hs
  rw [fsem_snoc below] at hs
  by_cases e : a = s
  · subst e; exact (fsem_none fresh o).mpr (Or.inl rfl)
  · rw [ite_eq_right e] at hs; exact h s o hs

/-- A key of both fields, the first allowing less. -/
theorem snoc_both {t₁ t₂ : String} {P₁ P₂ : List (Term × Term)} {a : String} {v₁ v₂ : Term}
    (h : ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o) (sub : ∀ o, FieldSem den v₁ o → FieldSem den v₂ o)
    (b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) (b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    ∀ s o, FSem den (Term.atom t₁) (P₁ ++ [(Term.atom a, v₁)]) s o → FSem den (Term.atom t₂) (P₂ ++ [(Term.atom a, v₂)]) s o := by
  intro s o hs
  rw [fsem_snoc b₁] at hs
  rw [fsem_snoc b₂]
  by_cases e : a = s
  · rw [ite_eq_left e] at hs ⊢; exact sub o hs
  · rw [ite_eq_right e] at hs ⊢; exact h s o hs

theorem eqv_snoc {P₁ P₂ : List (Term × Term)} {a : String} {v₁ v₂ : Term} {s : String}
    (b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) (b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt)
    (h : a ≠ s → EqvK den P₁ P₂ s) (same : a = s → ∀ o, FieldSem den v₁ o ↔ FieldSem den v₂ o) :
    EqvK den (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) s := by
  intro tag o
  rw [fsem_snoc b₁, fsem_snoc b₂]
  by_cases e : a = s
  · rw [ite_eq_left e, ite_eq_left e]; exact same e o
  · rw [ite_eq_right e, ite_eq_right e]; exact h e tag o

theorem lookup_snoc_ne {P : List (Term × Term)} {a c : String} {v : Term} (ne : a ≠ c)
    (below : ∀ e ∈ P, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt) :
    mapLookup (P ++ [(Term.atom a, v)]) (Term.atom c) = mapLookup P (Term.atom c) := by
  rw [lookup_snoc below, ite_eq_right ne]

/-- `opt_map_union_strategy/5` walks the fields of two map literals, keeping what its status says. -/
theorem mwalk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") :
    ∀ N (r₁ r₂ P₁ P₂ : List (Term × Term)) (st : Term), r₁.length + r₂.length ≤ N →
      FieldsV E (P₁ ++ r₁) → FieldsV E (P₂ ++ r₂) → (∀ x ∈ P₁ ++ P₂, ∀ y ∈ r₁ ++ r₂, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt) →
      MInv E den t₁ t₂ st P₁ P₂ →
      ∃ res, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm r₁) (fieldsTerm r₂) (.atom t₁)
        (Term.atom t₂) st = .ok res ∧ MRes E den t₁ t₂ res (P₁ ++ r₁) (P₂ ++ r₂) := by
  intro N
  induction N with
  | zero =>
    intro r₁ r₂ P₁ P₂ st size _ _ _ inv
    have : r₁ = [] ∧ r₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    simpa using mres_end (D m) t₁ t₂ g₁ g₂ inv
  | succ N ih =>
    intro r₁ r₂ P₁ P₂ st size s₁ s₂ below inv
    have fresh₁ : ∀ e ∈ r₁, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    have fresh₂ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    match r₁, r₂ with
    | [], [] => simpa using mres_end (D m) t₁ t₂ g₁ g₂ inv
    | x :: xs, [] => exact mres_tail₁ ef hm t₁ t₂ g₁ g₂ x xs inv fresh₁
    | [], y :: ys => exact mres_tail₂ ef hm t₁ t₂ g₁ g₂ y ys inv fresh₂
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨a, rfl⟩ := (s₁.1 (k₁, v₁) (by simp)).1
      obtain ⟨b, rfl⟩ := (s₂.1 (k₂, v₂) (by simp)).1
      have hv₁ : FieldValue E v₁ := (s₁.1 (.atom a, v₁) (by simp)).2
      have hv₂ : FieldValue E v₂ := (s₂.1 (.atom b, v₂) (by simp)).2
      have sx := fieldsV_head (fieldsV_suffix s₁)
      have sy := fieldsV_head (fieldsV_suffix s₂)
      have a₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt := fun e me =>
        below e (by simp [me]) (.atom a, v₁) (by simp)
      have a₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom a)) e.1 (.atom a) = .lt := fun e me =>
        below e (by simp [me]) (.atom a, v₁) (by simp)
      have b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt := fun e me =>
        below e (by simp [me]) (.atom b, v₂) (by simp)
      have b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt := fun e me =>
        below e (by simp [me]) (.atom b, v₂) (by simp)
      simp only [List.length_cons] at size
      have none₀ : MRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) :=
        Or.inr (Or.inr (Or.inr rfl))
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · -- a key only in the first literal
        have above : ∀ y ∈ (Term.atom b, v₂) :: ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp
          · exact cmp_lt_trans cmp (sy y my)
        have recur : ∀ st', MInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) P₂ → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
              (fieldsTerm ((.atom b, v₂) :: ys)) (.atom t₁) (.atom t₂) st' = .ok res ∧
            MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih xs _ (P₁ ++ [(Term.atom a, v₁)]) P₂ st' (by simp; omega) (by simpa using s₁) s₂
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              rcases mx with (mx | rfl) | mx
              · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with h | h <;> simp [h])
              · simp only [List.mem_append] at my
                rcases my with my | my
                · exact sx y my
                · exact above y my
              · exact below x (by simp [mx]) y (by rcases List.mem_append.mp my with h | h <;> simp [h])) inv'
          exact ⟨res, run, by simpa using mr⟩
        rcases g₂ with rfl | rfl
        · rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (eqv_sub h fun _ => rfl) (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»] at run ⊢
            exact run
          · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
            cases bs
            · refine ⟨_, ?_, none₀⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2», runb,
                boolAtom, isMember]
            · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
                (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (one_key_sub l₁ l₂ eqv (sound rfl) fun _ => rfl)
                  (lookup_below a₂) a₁⟩)))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2», runb,
                boolAtom, isMember] at run ⊢
              exact run
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (h fun _ => rfl) (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»] at run ⊢
            exact run
          all_goals
            refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»]
        · refine ⟨_, ?_, none₀⟩
          rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«/=/2»]
      · -- a key of both literals
        have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
        have notGt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isGT = Bool.true := by simp
        have recur : ∀ st', MInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs) (fieldsTerm ys) (.atom t₁)
              (.atom t₂) st' = .ok res ∧
            MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih xs ys (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) st' (by omega)
            (by simpa using s₁) (by simpa using s₂)
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              have my' : y ∈ (Term.atom a, v₁) :: xs ++ (Term.atom a, v₂) :: ys := by
                rcases List.mem_append.mp my with h | h <;> simp [h]
              have ka : ∀ y ∈ xs ++ ys, Term.compare (Term.fuel (Term.atom a) y.1) (Term.atom a) y.1 = .lt := fun y my => by
                rcases List.mem_append.mp my with h | h
                · exact sx y h
                · exact sy y h
              rcases mx with (mx | rfl) | (mx | rfl)
              · exact below x (by simp [mx]) y my'
              · exact ka y my
              · exact below x (by simp [mx]) y my'
              · exact ka y my) inv'
          exact ⟨res, run, by simpa using mr⟩
        have left_of : ∀ (h : (t₁ = "open" → t₂ = "open") → ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o),
            (∀ o, FieldSem den v₁ o → FieldSem den v₂ o) →
            MInv E den t₁ t₂ (Term.atom "left_subtype_of_right") (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) :=
          fun h sub => Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) sub a₁ a₂⟩))
        have right_of : ∀ (h : (t₂ = "open" → t₁ = "open") → ∀ s o, FSem den (.atom t₂) P₂ s o → FSem den (.atom t₁) P₁ s o),
            (∀ o, FieldSem den v₂ o → FieldSem den v₁ o) →
            MInv E den t₁ t₂ (Term.atom "right_subtype_of_left") (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) :=
          fun h sub => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) sub a₂ a₁⟩)))
        by_cases same : compareExact (fuel v₂ v₁) v₂ v₁ = .eq
        · have sv := fieldSem_exact ef hv₁ hv₂ same
          have inv' : MInv E den t₁ t₂ st (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) := by
            rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
            · exact Or.inl ⟨rfl, fun s => eqv_snoc a₁ a₂ (fun _ => h s) fun _ => sv⟩
            · have ca : a ≠ c := by
                rintro rfl
                obtain ⟨x, mx, -⟩ := lookup_mem l₁
                have := lookup_below a₁
                rw [this] at l₁; cases l₁
              refine Or.inr (Or.inl ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, by rw [lookup_snoc_ne ca a₁]; exact l₁,
                by rw [lookup_snoc_ne ca a₂]; exact l₂, fun s sc => eqv_snoc a₁ a₂ (fun _ => eqv s sc) fun _ => sv⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) (fun o => (sv o).mp) a₁ a₂⟩))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun pre => snoc_both (h pre) (fun o => (sv o).mpr) a₂ a₁⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          obtain ⟨res, run, mr⟩ := recur st inv'
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Erlang.erlang.«=:=/2», same] at run ⊢
          exact run
        · obtain ⟨b₁₂, run₁₂, sound₁₂⟩ := field_sub_bool ef hm hv₁ hv₂
          obtain ⟨b₂₁, run₂₁, sound₂₁⟩ := field_sub_bool ef hm hv₂ hv₁
          -- the walk once subtyping decides the status
          have bySub : ∀ (h₁ : (t₁ = "open" → t₂ = "open") → ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o)
              (h₂ : (t₂ = "open" → t₁ = "open") → ∀ s o, FSem den (.atom t₂) P₂ s o → FSem den (.atom t₁) P₁ s o),
              ∃ res, (if b₁₂ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
                  (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right")
                else if b₂₁ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
                  (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "right_subtype_of_left")
                else .ok (.atom "none")) = .ok res ∧
              MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
            intro h₁ h₂
            cases b₁₂
            · cases b₂₁
              · exact ⟨_, rfl, none₀⟩
              · simpa using recur _ (right_of h₂ (sound₂₁ rfl))
            · simpa using recur _ (left_of h₁ (sound₁₂ rfl))
          rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
          · by_cases cond : a ≠ "__struct__" ∧ t₁ = t₂
            · obtain ⟨ns, rfl⟩ := cond
              obtain ⟨res, run, mr⟩ := recur (.tuple #[.atom "one_key_difference", .atom a, v₁, v₂])
                (Or.inr (Or.inl ⟨a, v₁, v₂, rfl, rfl, hv₁, hv₂, by rw [lookup_snoc a₁, ite_eq_left rfl],
                  by rw [lookup_snoc a₂, ite_eq_left rfl],
                  fun s sa => eqv_snoc a₁ a₂ (fun _ => h s) fun e => absurd e.symm sa⟩))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Erlang.erlang.«==/2», Lynx.Except.andAlso,
                ns] at run ⊢
              exact run
            · obtain ⟨res, run, mr⟩ := bySub (fun pre => eqv_sub h pre) (fun pre => eqv_sub (fun s => (h s).symm) pre)
              refine ⟨res, ?_, mr⟩
              rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              have cond' : (Term.compare (Term.fuel (.atom a) (.atom "__struct__")) (.atom a) (.atom "__struct__") = .eq) ∨ t₁ ≠ t₂ := by
                by_cases e : a = "__struct__"
                · left; subst e; exact compare_self _
                · right; intro ht; exact cond ⟨e, ht⟩
              rcases cond' with c' | c'
              · simp [fieldsTerm, Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                  Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Lynx.Except.andAlso, c',
                  run₁₂, run₂₁, boolAtom]
                cases b₁₂ <;> cases b₂₁ <;> simp
              · simp [fieldsTerm, Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                  Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Erlang.erlang.«==/2», Lynx.Except.andAlso, c',
                  run₁₂, run₂₁, boolAtom]
                by_cases e : a = "__struct__" <;> cases b₁₂ <;> cases b₂₁ <;> simp [e]
          · obtain ⟨c₁₂, rc₁₂, sc₁₂⟩ := field_sub_bool ef hm hp₁ hp₂
            obtain ⟨c₂₁, rc₂₁, sc₂₁⟩ := field_sub_bool ef hm hp₂ hp₁
            have go : ∃ res, (if c₁₂ && b₁₂ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m)
                  (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right")
                else if c₂₁ && b₂₁ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm xs)
                  (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "right_subtype_of_left")
                else .ok (.atom "none")) = .ok res ∧
                MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
              by_cases l : c₁₂ && b₁₂
              · simp only [Bool.and_eq_true] at l
                obtain ⟨e₁, e₂⟩ := l
                subst e₁ e₂
                simpa using recur _ (left_of (fun pre => one_key_sub l₁ l₂ eqv (sc₁₂ rfl) pre) (sound₁₂ rfl))
              · by_cases r : c₂₁ && b₂₁
                · simp only [Bool.and_eq_true] at r
                  obtain ⟨e₁, e₂⟩ := r
                  subst e₁ e₂
                  simpa [l] using recur _
                    (right_of (fun pre => one_key_sub l₂ l₁ (fun s ne => (eqv s ne).symm) (sc₂₁ rfl) pre) (sound₂₁ rfl))
                · exact ⟨_, by simp [l, r], none₀⟩
            obtain ⟨res, run, mr⟩ := go
            refine ⟨res, ?_, mr⟩
            rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«/=/2», Erlang.erlang.«=:=/2», same, Lynx.Except.andAlso,
              run₁₂, run₂₁, rc₁₂, rc₂₁, boolAtom]
            cases c₁₂ <;> cases b₁₂ <;> cases c₂₁ <;> cases b₂₁ <;> simp
          · have go : ∃ res, (if b₁₂ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m)
                  (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right")
                else .ok (.atom "none")) = .ok res ∧
                MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
              cases b₁₂
              · exact ⟨_, rfl, none₀⟩
              · simpa using recur _ (left_of h (sound₁₂ rfl))
            obtain ⟨res, run, mr⟩ := go
            refine ⟨res, ?_, mr⟩
            rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«=:=/2», same,
              run₁₂, boolAtom, isMember]
            cases b₁₂ <;> simp
          · have go : ∃ res, (if b₂₁ then Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m)
                  (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "right_subtype_of_left")
                else .ok (.atom "none")) = .ok res ∧
                MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
              cases b₂₁
              · exact ⟨_, rfl, none₀⟩
              · simpa using recur _ (right_of h (sound₂₁ rfl))
            obtain ⟨res, run, mr⟩ := go
            refine ⟨res, ?_, mr⟩
            rw [← run, Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«=:=/2», same,
              run₂₁, boolAtom, isMember]
            cases b₂₁ <;> simp
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«=:=/2», same]
      · -- a key only in the second literal
        have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ y ∈ (Term.atom a, v₁) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp'
          · exact cmp_lt_trans cmp' (sx y my)
        have recur : ∀ st', MInv E den t₁ t₂ st' P₁ (P₂ ++ [(Term.atom b, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm ((.atom a, v₁) :: xs))
              (fieldsTerm ys) (.atom t₁) (.atom t₂) st' = .ok res ∧
            MRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
          intro st' inv'
          obtain ⟨res, run, mr⟩ := ih _ ys P₁ (P₂ ++ [(Term.atom b, v₂)]) st' (by simp; omega) s₁ (by simpa using s₂)
            (fun x mx y my => by
              simp only [List.mem_append, List.mem_singleton] at mx
              rcases mx with mx | (mx | rfl)
              · exact below x (by simp [mx]) y (by
                  simp only [List.mem_append, List.mem_cons] at my; rcases my with (h | h) | h <;> simp [h])
              · exact below x (by simp [mx]) y (by
                  simp only [List.mem_append, List.mem_cons] at my; rcases my with (h | h) | h <;> simp [h])
              · simp only [List.mem_append] at my
                rcases my with my | my
                · exact above y my
                · exact sy y my) inv'
          exact ⟨res, run, by simpa using mr⟩
        rcases g₁ with rfl | rfl
        · rcases inv with ⟨rfl, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
          · obtain ⟨res, run, mr⟩ := recur (.atom "right_subtype_of_left")
              (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ =>
                snoc_left (eqv_sub (fun s => (h s).symm) fun _ => rfl) (lookup_below b₁) b₂⟩))))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»] at run ⊢
            exact run
          · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₂ hp₁
            cases bs
            · refine ⟨_, ?_, none₀⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
                Erlang.erlang.«/=/2», runb, boolAtom, isMember]
            · obtain ⟨res, run, mr⟩ := recur (.atom "right_subtype_of_left")
                (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ =>
                  snoc_left (one_key_sub l₂ l₁ (fun s ne => (eqv s ne).symm) (sound rfl) fun _ => rfl)
                    (lookup_below b₁) b₂⟩))))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
                Erlang.erlang.«/=/2», runb, boolAtom, isMember] at run ⊢
              exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»]
          · obtain ⟨res, run, mr⟩ := recur (.atom "right_subtype_of_left")
              (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fun _ => snoc_left (h fun _ => rfl) (lookup_below b₁) b₂⟩))))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»] at run ⊢
            exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2»]
        · refine ⟨_, ?_, none₀⟩
          rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            Erlang.erlang.«/=/2»]


/-- Storing a key a map has keeps its size. -/
theorem store_len (a : String) {f : Term} (hf : FieldValue E f) :
    ∀ {l : List (Term × Term)}, FieldsV E l → (mapLookup l (.atom a)).isSome →
      ∃ l', Erlang.orddict.«store/3» (.atom a) f (fieldsTerm l) = .ok (fieldsTerm l') ∧ l'.length = l.length
  | [], _, h => by simp [mapLookup] at h
  | (k, v) :: t, sl, h => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have hv := (sl.1 _ List.mem_cons_self).2
    have st := fieldsV_tail sl
    have hd := fieldsV_head sl
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · exfalso
      have ne : b ≠ a := fun e => by subst e; exact cmp_lt_ne cmp rfl
      rw [lookup_cons_atom, ite_eq_right ne, lookup_above fun e me => cmp_lt_trans cmp (hd e me)] at h
      simp at h
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      refine ⟨(.atom a, f) :: t, ?_, rfl⟩
      rw [Erlang.orddict.«store/3».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
    · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
      have ne : b ≠ a := fun e => by subst e; exact cmp_lt_ne cmp' rfl
      rw [lookup_cons_atom, ite_eq_right ne] at h
      obtain ⟨l', run, len⟩ := store_len a hf st h
      refine ⟨(.atom b, v) :: l', ?_, by simp [len]⟩
      rw [Erlang.orddict.«store/3».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at run ⊢
      simp [run]

/-- Optimized unions of element types are their unions. -/
def ElemFields (E : Term → Prop) (l : List (Term × Term)) : Prop := ∀ e ∈ l, ∃ (t : Term) (o : Bool), e.2 = .tuple #[t, boolAtom o] ∧ E t

theorem field_opt_union_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f₁ f₂ : Term} {t₁ t₂ : Term} {o₁ o₂ : Bool}
    (e₁ : f₁ = .tuple #[t₁, boolAtom o₁]) (e₂ : f₂ = .tuple #[t₂, boolAtom o₂]) (h₁ : E t₁) (h₂ : E t₂)
    (S : List (Term × Term)) :
    ∃ t, E t ∧ Elixir.Module.Types.Descr.«field_opt_union/3» (D m) f₁ f₂ (.map S) =
      .ok (.tuple #[t, boolAtom (o₁ || o₂)]) ∧
      ∀ o, FieldSem den (.tuple #[t, boolAtom (o₁ || o₂)]) o ↔ FieldSem den f₁ o ∨ FieldSem den f₂ o := by
  subst e₁ e₂
  obtain ⟨c, hc, run, sem⟩ := ef.opt_union S h₁ h₂ hm
  refine ⟨c, hc, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_opt_union/3», run]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.orElse]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x => simp [sem x]

/-- What `opt_map_union_strategy/5` finds for two literals of value maps, and what `opt_map_union/3` makes of it. -/
def StratM (E : Term → Prop) (den : Term → V → Prop) (m : Nat) (S : List (Term × Term)) (t₁ t₂ : String) (l₁ l₂ : List (Term × Term)) (st : Term) : Prop :=
  (∃ (key v₁ v₂ f : Term) (l : List (Term × Term)), st = .tuple #[.atom "one_key_difference", key, v₁, v₂] ∧
    Elixir.Module.Types.Descr.«field_opt_union/3» (D m) v₁ v₂ (.map S) = .ok f ∧
    Erlang.orddict.«store/3» key f (fieldsTerm l₁) = .ok (fieldsTerm l) ∧ FieldsV E l ∧ ElemFields E l ∧
    l.length = l₁.length ∧
    ∀ w, MSem den (.atom t₁) l w ↔ MSem den (.atom t₁) l₁ w ∨ MSem den (.atom t₂) l₂ w) ∨
  (st = .atom "left_subtype_of_right" ∧ ∀ w, MSem den (.atom t₁) l₁ w → MSem den (.atom t₂) l₂ w) ∨
  (st = .atom "right_subtype_of_left" ∧ ∀ w, MSem den (.atom t₂) l₂ w → MSem den (.atom t₁) l₁ w) ∨
  st = .atom "none"

theorem fieldsTerm_eq_nil {l : List (Term × Term)} : fieldsTerm l = .nil ↔ l = [] := by
  cases l
  · simp [fieldsTerm, Term.list]
  · simp [fieldsTerm, Term.list]

/-- `opt_map_union_strategy/5` on literals of value maps. -/
theorem strat_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {l₁ l₂ : List (Term × Term)} (s₁ : FieldsV E l₁) (s₂ : FieldsV E l₂)
    (e₁ : ElemFields E l₁) (e₂ : ElemFields E l₂) (S : List (Term × Term)) :
    ∃ st, Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (D m) (fieldsTerm l₁) (fieldsTerm l₂) (.atom t₁)
      (.atom t₂) (.atom "all_equal") = .ok st ∧ StratM E den m S t₁ t₂ l₁ l₂ st := by
  obtain ⟨st, run, mres⟩ := mwalk ef hm t₁ t₂ g₁ g₂ _ l₁ l₂ [] [] (.atom "all_equal") (Nat.le_refl _)
    (by simpa using s₁) (by simpa using s₂) (by simp) (Or.inl ⟨rfl, fun s tag o => Iff.rfl⟩)
  simp only [List.nil_append] at mres
  refine ⟨st, by simpa using run, ?_⟩
  · rcases mres with ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, la₁, la₂, eqv⟩ | ⟨rfl, sub⟩ | ⟨rfl, sub⟩ | rfl
    · subst et
      obtain ⟨x₁, mx₁, ex₁⟩ := lookup_mem la₁
      obtain ⟨x₂, mx₂, ex₂⟩ := lookup_mem la₂
      obtain ⟨u₁, o₁, eu₁, hu₁⟩ := e₁ x₁ mx₁
      obtain ⟨u₂, o₂, eu₂, hu₂⟩ := e₂ x₂ mx₂
      rw [ex₁] at eu₁
      rw [ex₂] at eu₂
      obtain ⟨t, ht, runF, semF⟩ := field_opt_union_val ef (show K ≤ m by omega) eu₁ eu₂ hu₁ hu₂ S
      obtain ⟨l', runS, sl', mem, look⟩ := store_val a ⟨t, o₁ || o₂, rfl, ht⟩ s₁
      obtain ⟨l'', runS', len⟩ := store_len a ⟨t, o₁ || o₂, rfl, ht⟩ s₁ (by rw [la₁]; rfl)
      have ll : l' = l'' := by rw [runS] at runS'; exact fieldsTerm_inj (Except.ok.inj runS')
      subst ll
      refine Or.inl ⟨_, _, _, _, l', rfl, runF, runS, sl', fun e me => ?_, len, fun w => ?_⟩
      · rcases mem e me with rfl | me
        · exact ⟨t, _, rfl, ht⟩
        · exact e₁ e me
      · have fs : ∀ s o, FSem den (.atom t₁) l' s o ↔ if a = s then FieldSem den (.tuple #[t, boolAtom (o₁ || o₂)]) o
            else FSem den (.atom t₁) l₁ s o := by
          intro s o
          unfold FSem TagSem
          rw [look s]
          by_cases e : a = s <;> simp [e]
        have at₁ : ∀ o, FSem den (.atom t₁) l₁ a o ↔ FieldSem den p₁ o := fun o => by unfold FSem TagSem; rw [la₁]
        have at₂ : ∀ o, FSem den (.atom t₁) l₂ a o ↔ FieldSem den p₂ o := fun o => by unfold FSem TagSem; rw [la₂]
        constructor
        · intro h
          have ha := (fs a (w (.atom a))).mp (h a)
          rw [ite_eq_left rfl, semF] at ha
          rcases ha with ha | ha
          · left
            refine ⟨fun s => ?_, h.doms⟩
            by_cases e : a = s
            · subst e; exact (at₁ _).mpr ha
            · have := (fs s (w (.atom s))).mp (h s); rwa [ite_eq_right e] at this
          · right
            refine ⟨fun s => ?_, h.doms⟩
            by_cases e : a = s
            · subst e; exact (at₂ _).mpr ha
            · have := (fs s (w (.atom s))).mp (h s); rw [ite_eq_right e] at this
              exact (eqv s (Ne.symm e) t₁ (w (.atom s))).mp this
        · intro h
          refine ⟨fun s => ?_, fun k i => h.elim (fun h => h.doms k i) (fun h => h.doms k i)⟩
          rw [fs]
          by_cases e : a = s
          · subst e; rw [ite_eq_left rfl, semF]
            rcases h with h | h
            · exact Or.inl ((at₁ _).mp (h a))
            · exact Or.inr ((at₂ _).mp (h a))
          · rw [ite_eq_right e]
            rcases h with h | h
            · exact h s
            · exact (eqv s (Ne.symm e) t₁ (w (.atom s))).mpr (h s)
    · obtain ⟨v⟩ := ef.inhabited
      exact Or.inr (Or.inl ⟨rfl, fun w h₁ => msem_of_atoms v (fun s o => sub s o) h₁⟩)
    · obtain ⟨v⟩ := ef.inhabited
      exact Or.inr (Or.inr (Or.inl ⟨rfl, fun w h₂ => msem_of_atoms v (fun s o => sub s o) h₂⟩))
    · exact Or.inr (Or.inr (Or.inr rfl))

end Elixir.STTDescrProofsTest.Nest
