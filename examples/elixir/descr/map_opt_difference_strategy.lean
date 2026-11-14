namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized differences of map literals: the strategy. -/

theorem field_disj_bool (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) :
    ∃ s : Bool, Elixir.Module.Types.Descr.«field_disjoint?/2» (D m) f₁ f₂ = .ok (boolAtom s) ∧
      (s = Bool.true → ∀ o, FieldSem den f₁ o → FieldSem den f₂ o → False) := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  obtain ⟨b, hb, sound⟩ := ef.disj ht₁ ht₂
  have run := hb m hm
  refine ⟨(!o₁ || !o₂) && b, ?_, fun e o f₁ f₂ => ?_⟩
  · rw [Elixir.Module.Types.Descr.«field_disjoint?/2».eq_def]
    cases o₁ <;> cases o₂ <;> cases b <;>
      simp [boolAtom, run, Erlang.erlang.«not/1»]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at e
    obtain ⟨eo, eb⟩ := e
    subst eb
    rw [fieldSem_mk] at f₁ f₂
    rcases f₁ with ⟨rfl, rfl⟩ | ⟨x, rfl, hx⟩
    · rcases f₂ with ⟨-, rfl⟩ | ⟨x, h, -⟩
      · simp at eo
      · cases h
    · rcases f₂ with ⟨h, -⟩ | ⟨y, h, hy⟩
      · cases h
      · cases h
        exact sound rfl x hx hy

/-- What the status of the difference walk says about the walked fields. -/
def DInv (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (P₁ P₂ : List (Term × Term)) : Prop :=
  (st = .atom "all_equal" ∧ (t₁ = t₂ ∨ t₂ = "open") ∧ ∀ s, EqvK den P₁ P₂ s) ∨
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup P₁ (.atom a) = some p₁ ∧
    mapLookup P₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den P₁ P₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ (t₁ = t₂ ∨ t₂ = "open") ∧ ∀ s o, FSem den (.atom t₁) P₁ s o → FSem den (.atom t₂) P₂ s o) ∨
  st = .atom "none"

/-- What the result of the difference walk says about the fields of two map literals. -/
def DRes (E : Term → Prop) (den : Term → V → Prop) (t₁ t₂ : String) (st : Term) (l₁ l₂ : List (Term × Term)) : Prop :=
  (st = .atom "disjoint" ∧ ∃ s, ∀ o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o → False) ∨
  (∃ (a : String) (p₁ p₂ : Term), st = .tuple #[.atom "one_key_difference", .atom a, p₁, p₂] ∧ t₁ = t₂ ∧
    FieldValue E p₁ ∧ FieldValue E p₂ ∧ mapLookup l₁ (.atom a) = some p₁ ∧
    mapLookup l₂ (.atom a) = some p₂ ∧ ∀ s, s ≠ a → EqvK den l₁ l₂ s) ∨
  (st = .atom "left_subtype_of_right" ∧ ∀ s o, FSem den (.atom t₁) l₁ s o → FSem den (.atom t₂) l₂ s o) ∨
  st = .atom "none"

theorem tags_mono {t₁ t₂ : String} (h : t₁ = t₂ ∨ t₂ = "open") :
    t₁ = "open" → t₂ = "open" := by
  intro e; rcases h with rfl | h
  · exact e
  · exact h

/-- The status after a key of the second literal only, which is optional, while the first is closed. -/
theorem missing_optional (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₂ : String} {st : Term} {P₁ P₂ : List (Term × Term)} {b : String}
    {v₂ : Term} (inv : DInv E den "closed" t₂ st P₁ P₂) (opt : FieldSem den v₂ Option.none)
    (b₁ : ∀ e ∈ P₁, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt) (b₂ : ∀ e ∈ P₂, Term.compare (Term.fuel e.1 (.atom b)) e.1 (.atom b) = .lt) :
    ∃ st', Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1» (D m) st = .ok st' ∧
      DInv E den "closed" t₂ st' P₁ (P₂ ++ [(Term.atom b, v₂)]) := by
  have extend : (∀ s o, FSem den (.atom "closed") P₁ s o → FSem den (.atom t₂) P₂ s o) →
      ∀ s o, FSem den (Term.atom "closed") P₁ s o → FSem den (Term.atom t₂) (P₂ ++ [(Term.atom b, v₂)]) s o := by
    intro h s o hs
    rw [fsem_snoc b₂]
    by_cases e : b = s
    · subst e
      rw [ite_eq_left rfl]
      have := (fsem_none (lookup_below b₁) o).mp hs
      rcases this with h | rfl
      · exact absurd h (by decide)
      · exact opt
    · rw [ite_eq_right e]; exact h s o hs
  rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl,
      Or.inr (Or.inr (Or.inl ⟨rfl, tags, extend (eqv_sub h (fun e => absurd e (by decide)))⟩))⟩
  · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
    cases bs
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
      simp [runb, boolAtom, isMember]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl et, extend (one_key_sub l₁ l₂ eqv (sound rfl)
        (fun e => absurd e (by decide)))⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
      simp [runb, boolAtom, isMember]
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl,
      Or.inr (Or.inr (Or.inl ⟨rfl, tags, extend h⟩))⟩
  · exact ⟨_, by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl,
      Or.inr (Or.inr (Or.inr rfl))⟩

/-- Required fields: those that do not allow absence. -/
def req (v : Term) : Bool :=
  match v with
  | .tuple ⟨[_, .atom "false"]⟩ => Bool.true
  | _ => Bool.false

theorem req_true {v : Term} (h : FieldValue E v) (r : req v = Bool.true) : ¬FieldSem den v Option.none := by
  obtain ⟨t, o, rfl, -⟩ := h
  rw [fieldSem_mk]
  cases o <;> simp_all [req, boolAtom]

theorem req_false {v : Term} (h : FieldValue E v) (r : req v = Bool.false) : FieldSem den v Option.none := by
  obtain ⟨t, o, rfl, -⟩ := h
  rw [fieldSem_mk]
  cases o <;> simp_all [req, boolAtom]

theorem any_req (m : Nat) (name : String) (hname : name = "-opt_map_difference_strategy/5-fun-0-" ∨
      name = "-opt_map_difference_strategy/5-fun-1-") (l : List (Term × Term)) (hl : ∀ e ∈ l, FieldValue E e.2) :
    Erlang.lists.«any/2» (D m) (.function "Elixir.Module.Types.Descr" name 1 #[]) (fieldsTerm l) =
      .ok (boolAtom (l.any fun e => req e.2)) := by
  have := any_list (D m) "Elixir.Module.Types.Descr" name #[]
    (fun x => match x with | .tuple ⟨[_, v]⟩ => req v | _ => Bool.false) (l.map fun e => .tuple #[e.1, e.2]) (by
      intro x mx
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨t, o, ev, -⟩ := hl e me
      rcases hname with rfl | rfl
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_map_difference_strategy/5-fun-0-/1».pure, ev]
        cases o <;> simp [Elixir.Module.Types.Descr.«-opt_map_difference_strategy/5-fun-0-/1», Erlang.erlang.«not/1»,
          boolAtom, req]
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_map_difference_strategy/5-fun-1-/1».pure, ev]
        cases o <;> simp [Elixir.Module.Types.Descr.«-opt_map_difference_strategy/5-fun-1-/1», Erlang.erlang.«not/1»,
          boolAtom, req])
  simpa [fieldsTerm, List.any_map, Function.comp_def] using this

/-- A required field of the first literal at a key the closed second one lacks. -/
theorem disj_left {t₁ s : String} {l₁ l₂ : List (Term × Term)} {v : Term} (hl : mapLookup l₁ (.atom s) = some v)
    (hv : FieldValue E v) (r : req v = Bool.true) (hn : mapLookup l₂ (.atom s) = Option.none) :
    ∀ o, FSem den (.atom t₁) l₁ s o → FSem den (.atom "closed") l₂ s o → False := by
  intro o h₁ h₂
  rcases (fsem_none hn o).mp h₂ with h | rfl
  · exact absurd h (by decide)
  · exact req_true hv r (by simpa [FSem, TagSem, hl] using h₁)

/-- A required field of the second literal at a key the closed first one lacks. -/
theorem disj_right {t₂ s : String} {l₁ l₂ : List (Term × Term)} {v : Term} (hl : mapLookup l₂ (.atom s) = some v)
    (hv : FieldValue E v) (r : req v = Bool.true) (hn : mapLookup l₁ (.atom s) = Option.none) :
    ∀ o, FSem den (.atom "closed") l₁ s o → FSem den (.atom t₂) l₂ s o → False := by
  intro o h₁ h₂
  rcases (fsem_none hn o).mp h₁ with h | rfl
  · exact absurd h (by decide)
  · exact req_true hv r (by simpa [FSem, TagSem, hl] using h₂)

theorem dres_end (d : Dispatcher) (t₁ t₂ : String) (_g₁ : t₁ = "open" ∨ t₁ = "closed")
    {st : Term} {P₁ P₂ : List (Term × Term)} (inv : DInv E den t₁ t₂ st P₁ P₂) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» d (fieldsTerm []) (fieldsTerm []) (.atom t₁)
      (.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res P₁ P₂ := by
  rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, h⟩ | ⟨rfl, tags, h⟩ | rfl
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, eqv_sub h (tags_mono tags)⟩))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inr (Or.inl ⟨a, p₁, p₂, rfl, h⟩)⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]
  · refine ⟨_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    simp [fieldsTerm, Term.list, Erlang.erlang.«==/2»]

/-- The walk ends on the second fields first. -/
theorem dres_tail₁ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (x : Term × Term)
    (xs : List (Term × Term)) (inv : DInv E den t₁ t₂ st P₁ P₂) (s₁ : FieldsV E (P₁ ++ x :: xs))
    (fresh : ∀ e ∈ x :: xs, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm (x :: xs)) (fieldsTerm [])
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res (P₁ ++ x :: xs) (P₂ ++ []) := by
  obtain ⟨k, v⟩ := x
  have none : DRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (k, v) :: xs) (P₂ ++ []) := Or.inr (Or.inr (Or.inr rfl))
  rcases g₂ with rfl | rfl
  · rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
        simpa using left_extend (eqv_sub h (fun _ => rfl)) fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · obtain ⟨b, run, sound⟩ := field_sub_bool ef hm hp₁ hp₂
      cases b
      · refine ⟨_, ?_, none⟩
        rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso, run, boolAtom,
          isMember]
      · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by
          simpa using left_extend (one_key_sub l₁ l₂ eqv (sound rfl) (fun _ => rfl)) fresh⟩))⟩
        rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso, run, boolAtom,
          isMember]
    · refine ⟨_, ?_, Or.inr (Or.inr (Or.inl ⟨rfl, by simpa using left_extend h fresh⟩))⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · have fv : ∀ e ∈ (k, v) :: xs, FieldValue E e.2 := fun e me => (s₁.1 e (by simp [me])).2
    have any₁ := any_req m "-opt_map_difference_strategy/5-fun-1-" (Or.inr rfl) _ fv
    simp only [fieldsTerm, Term.list, List.map] at any₁
    cases ar : ((k, v) :: xs).any (fun e => req e.2)
    · refine ⟨_, ?_, none⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«/=/2», any₁, ar, boolAtom]
    · obtain ⟨e, me, re⟩ := List.any_eq_true.mp ar
      obtain ⟨s, es⟩ := (s₁.1 e (by simp [me])).1
      refine ⟨_, ?_, Or.inl ⟨rfl, s, fun o h₁ h₂ => disj_left (t₁ := t₁)
        (lookup_of_mem s₁ (by simp [me]) es) (fv e me) re (by simpa using fresh e me s es) o h₁ h₂⟩⟩
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      rcases g₁ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«/=/2», any₁, ar, boolAtom]

theorem lookup_some_mem {l : List (Term × Term)} {s : String} {f : Term} (h : mapLookup l (.atom s) = some f) :
    ∃ e ∈ l, e.1 = .atom s ∧ e.2 = f := by
  unfold mapLookup at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_of_find?_eq_some he, (atom_compareExact_eq s e.1).mp (by simpa using List.find?_some he), rfl⟩

/-- Optional fields of the second literal beyond the first, which is closed, keep the first a subtype. -/
theorem right_extend {t₂ : String} {P₁ P₂ r₂ : List (Term × Term)}
    (h : ∀ s o, FSem den (.atom "closed") P₁ s o → FSem den (.atom t₂) P₂ s o)
    (fresh₁ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none)
    (fresh₂ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none)
    (opt : ∀ e ∈ r₂, FieldSem den e.2 Option.none) :
    ∀ s o, FSem den (Term.atom "closed") P₁ s o → FSem den (Term.atom t₂) (P₂ ++ r₂) s o := by
  intro s o hs
  cases e : mapLookup r₂ (.atom s) with
  | none => exact (fsem_append_notin e o).mpr (h s o hs)
  | some f =>
    obtain ⟨x, mx, kx, fx⟩ := lookup_some_mem e
    have n₁ := fresh₁ x mx s kx
    have n₂ := fresh₂ x mx s kx
    rcases (fsem_none n₁ o).mp hs with c | rfl
    · exact absurd c (by decide)
    · unfold FSem TagSem
      rw [lookup_append, n₂, e]
      simpa [← fx] using opt x mx

/-- The walk ends on the first fields first. -/
theorem dres_tail₂ (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {st : Term} {P₁ P₂ : List (Term × Term)} (y : Term × Term)
    (ys : List (Term × Term)) (inv : DInv E den t₁ t₂ st P₁ P₂) (s₂ : FieldsV E (P₂ ++ y :: ys))
    (fresh₁ : ∀ e ∈ y :: ys, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none)
    (fresh₂ : ∀ e ∈ y :: ys, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm []) (fieldsTerm (y :: ys))
      (Term.atom t₁) (Term.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res (P₁ ++ []) (P₂ ++ y :: ys) := by
  obtain ⟨k, v⟩ := y
  have none : DRes E den t₁ t₂ (Term.atom "none") (P₁ ++ []) (P₂ ++ (k, v) :: ys) := Or.inr (Or.inr (Or.inr rfl))
  have fv : ∀ e ∈ (k, v) :: ys, FieldValue E e.2 := fun e me => (s₂.1 e (by simp [me])).2
  have any₀ := any_req m "-opt_map_difference_strategy/5-fun-0-" (Or.inl rfl) _ fv
  simp only [fieldsTerm, Term.list, List.map] at any₀
  rcases g₁ with rfl | rfl
  · refine ⟨_, ?_, none⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«/=/2»]
  cases ar : ((k, v) :: ys).any (fun e => req e.2)
  · have opt : ∀ e ∈ (k, v) :: ys, FieldSem den e.2 Option.none := fun e me =>
      req_false (fv e me) (by
        have := List.any_eq_false.mp ar e me
        simpa using this)
    have ext := fun h => right_extend (t₂ := t₂) h fresh₁ fresh₂ opt
    have run : ∀ st', Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1» (D m) st = .ok st' →
        Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm []) (fieldsTerm ((k, v) :: ys))
          (.atom "closed") (.atom t₂) st = .ok st' := by
      intro st' h
      rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
      rcases g₂ with rfl | rfl <;>
        simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
          Erlang.erlang.«/=/2», any₀, ar, boolAtom, h]
    rcases inv with ⟨rfl, tags, h⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
    · exact ⟨_, run _ (by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl),
        Or.inr (Or.inr (Or.inl ⟨rfl, by simpa using ext (eqv_sub h (fun e => absurd e (by decide)))⟩))⟩
    · obtain ⟨b, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
      cases b
      · exact ⟨_, run _ (by
          rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
          simp [runb, boolAtom, isMember]), none⟩
      · exact ⟨_, run _ (by
          rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]
          simp [runb, boolAtom, isMember]),
          Or.inr (Or.inr (Or.inl ⟨rfl, by
            simpa using ext (one_key_sub l₁ l₂ eqv (sound rfl) (fun e => absurd e (by decide)))⟩))⟩
    · exact ⟨_, run _ (by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl),
        Or.inr (Or.inr (Or.inl ⟨rfl, by simpa using ext h⟩))⟩
    · exact ⟨_, run _ (by rw [Elixir.Module.Types.Descr.«opt_map_difference_missing_optional/1».eq_def]; rfl), none⟩
  · obtain ⟨e, me, re⟩ := List.any_eq_true.mp ar
    obtain ⟨s, es⟩ := (s₂.1 e (by simp [me])).1
    refine ⟨_, ?_, Or.inl ⟨rfl, s, fun o h₁ h₂ => disj_right (t₂ := t₂)
      (lookup_of_mem s₂ (by simp [me]) es) (fv e me) re (by simpa using fresh₁ e me s es) o h₁ h₂⟩⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
    rcases g₂ with rfl | rfl <;>
      simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso,
        Erlang.erlang.«/=/2», any₀, ar, boolAtom]

/-- `opt_map_difference_strategy/5` walks the fields of two map literals, keeping what its status says. -/
theorem dwalk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") :
    ∀ N (r₁ r₂ P₁ P₂ : List (Term × Term)) (st : Term), r₁.length + r₂.length ≤ N →
      FieldsV E (P₁ ++ r₁) → FieldsV E (P₂ ++ r₂) → (∀ x ∈ P₁ ++ P₂, ∀ y ∈ r₁ ++ r₂, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt) →
      DInv E den t₁ t₂ st P₁ P₂ →
      ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm r₁) (fieldsTerm r₂) (.atom t₁)
        (Term.atom t₂) st = .ok res ∧ DRes E den t₁ t₂ res (P₁ ++ r₁) (P₂ ++ r₂) := by
  intro N
  induction N with
  | zero =>
    intro r₁ r₂ P₁ P₂ st size _ _ _ inv
    have : r₁ = [] ∧ r₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    simpa using dres_end (D m) t₁ t₂ g₁ inv
  | succ N ih =>
    intro r₁ r₂ P₁ P₂ st size s₁ s₂ below inv
    have fresh₁ : ∀ e ∈ r₁, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    have fresh₂ : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₁ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    have fresh₂' : ∀ e ∈ r₂, ∀ s : String, e.1 = .atom s → mapLookup P₂ (.atom s) = Option.none :=
      fun e me s es => lookup_below fun x mx => by rw [← es]; exact below x (by simp [mx]) e (by simp [me])
    match r₁, r₂ with
    | [], [] => simpa using dres_end (D m) t₁ t₂ g₁ inv
    | x :: xs, [] => exact dres_tail₁ ef hm t₁ t₂ g₁ g₂ x xs inv s₁ fresh₁
    | [], y :: ys => exact dres_tail₂ ef hm t₁ t₂ g₁ g₂ y ys inv s₂ fresh₂ fresh₂'
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
      have la₁ : mapLookup (P₁ ++ (Term.atom a, v₁) :: xs) (Term.atom a) = some v₁ :=
        lookup_of_mem s₁ (e := (.atom a, v₁)) (by simp) rfl
      have lb₂ : mapLookup (P₂ ++ (Term.atom b, v₂) :: ys) (Term.atom b) = some v₂ :=
        lookup_of_mem s₂ (e := (.atom b, v₂)) (by simp) rfl
      simp only [List.length_cons] at size
      obtain ⟨u₁, o₁, ev₁, hu₁⟩ := id hv₁
      obtain ⟨u₂, o₂, ev₂, hu₂⟩ := id hv₂
      have none₀ : DRes E den t₁ t₂ (Term.atom "none") (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) :=
        Or.inr (Or.inr (Or.inr rfl))
      rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
      · -- a key only in the first literal
        have above : ∀ y ∈ (Term.atom b, v₂) :: ys, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp
          · exact cmp_lt_trans cmp (sy y my)
        have na₂ : mapLookup (P₂ ++ (Term.atom b, v₂) :: ys) (Term.atom a) = Option.none := by
          rw [lookup_append, lookup_below a₂]
          refine lookup_none fun y my eq => ?_
          have := above y my
          rw [eq, compare_self] at this
          cases this
        have recur : ∀ st', DInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) P₂ → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm xs)
              (fieldsTerm ((.atom b, v₂) :: ys)) (.atom t₁) (.atom t₂) st' = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
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
        · rcases inv with ⟨rfl, tags, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl,
                snoc_left (eqv_sub h fun _ => rfl) (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂] at run ⊢
            exact run
          · obtain ⟨bs, runb, sound⟩ := field_sub_bool ef hm hp₁ hp₂
            cases bs
            · refine ⟨_, ?_, none₀⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«==/2», runb, ev₁, ev₂,
                boolAtom, isMember]
            · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
                (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl, snoc_left (one_key_sub l₁ l₂ eqv (sound rfl) fun _ => rfl)
                  (lookup_below a₂) a₁⟩)))
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, Erlang.erlang.«==/2», runb, ev₁, ev₂,
                boolAtom, isMember] at run ⊢
              exact run
          · obtain ⟨res, run, mr⟩ := recur (.atom "left_subtype_of_right")
              (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl, snoc_left h (lookup_below a₂) a₁⟩)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂] at run ⊢
            exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂]
        · cases o₁
          · refine ⟨_, ?_, Or.inl ⟨rfl, a, disj_left la₁ hv₁ (by simp [ev₁, req, boolAtom]) na₂⟩⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂, boolAtom]
          · obtain ⟨res, run, mr⟩ := recur (.atom "none") (Or.inr (Or.inr (Or.inr rfl)))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp,
              Erlang.erlang.«==/2», ev₁, ev₂, boolAtom] at run ⊢
            exact run
      · -- a key of both literals
        have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
        subst ab
        have recur : ∀ st', DInv E den t₁ t₂ st' (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm xs) (fieldsTerm ys) (.atom t₁)
              (.atom t₂) st' = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) := by
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
        have noneR : ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm xs)
            (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "none") = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) :=
          recur _ (Or.inr (Or.inr (Or.inr rfl)))
        by_cases same : compareExact (fuel v₂ v₁) v₂ v₁ = .eq
        · have sv := fieldSem_exact ef hv₁ hv₂ same
          have inv' : DInv E den t₁ t₂ st (P₁ ++ [(Term.atom a, v₁)]) (P₂ ++ [(Term.atom a, v₂)]) := by
            rcases inv with ⟨rfl, tags, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
            · exact Or.inl ⟨rfl, tags, fun s => eqv_snoc a₁ a₂ (fun _ => h s) fun _ => sv⟩
            · have ca : a ≠ c := by
                rintro rfl
                have := lookup_below a₁
                rw [this] at l₁; cases l₁
              refine Or.inr (Or.inl ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, by rw [lookup_snoc_ne ca a₁]; exact l₁,
                by rw [lookup_snoc_ne ca a₂]; exact l₂, fun s sc => eqv_snoc a₁ a₂ (fun _ => eqv s sc) fun _ => sv⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, tags, snoc_both h (fun o => (sv o).mp) a₁ a₂⟩))
            · exact Or.inr (Or.inr (Or.inr rfl))
          obtain ⟨res, run, mr⟩ := recur st inv'
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Erlang.erlang.«=:=/2», same] at run ⊢
          exact run
        obtain ⟨bd, rund, soundd⟩ := field_disj_bool ef hm hv₁ hv₂
        cases bd
        rotate_left
        · refine ⟨_, ?_, Or.inl ⟨rfl, a, fun o h₁ h₂ => soundd rfl o (by simpa [FSem, TagSem, la₁] using h₁)
            (by simpa [FSem, TagSem, lb₂] using h₂)⟩⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Erlang.erlang.«=:=/2», same, rund,
            boolAtom, isMember]
        obtain ⟨b₁₂, run₁₂, sound₁₂⟩ := field_sub_bool ef hm hv₁ hv₂
        have lsrR : (∀ s o, FSem den (Term.atom t₁) (P₁ ++ [(Term.atom a, v₁)]) s o → FSem den (Term.atom t₂) (P₂ ++ [(Term.atom a, v₂)]) s o) →
            (t₁ = t₂ ∨ t₂ = "open") → ∃ res, Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m)
              (fieldsTerm xs) (fieldsTerm ys) (.atom t₁) (.atom t₂) (.atom "left_subtype_of_right") = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom a, v₂) :: ys) :=
          fun h tags => recur _ (Or.inr (Or.inr (Or.inl ⟨rfl, tags, h⟩)))
        rcases inv with ⟨rfl, tags, h⟩ | ⟨c, p₁, p₂, rfl, et, hp₁, hp₂, l₁, l₂, eqv⟩ | ⟨rfl, tags, h⟩ | rfl
        · by_cases et : t₁ = t₂
          · subst et
            obtain ⟨res, run, mr⟩ := recur (.tuple #[.atom "one_key_difference", .atom a, v₁, v₂])
              (Or.inr (Or.inl ⟨a, v₁, v₂, rfl, rfl, hv₁, hv₂, by rw [lookup_snoc a₁, ite_eq_left rfl],
                by rw [lookup_snoc a₂, ite_eq_left rfl], fun s sa => eqv_snoc a₁ a₂ (fun _ => h s) fun e => absurd e.symm sa⟩))
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Erlang.erlang.«==/2», Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember] at run ⊢
            exact run
          · cases b₁₂
            · obtain ⟨res, run, mr⟩ := noneR
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
                boolAtom, isMember, run₁₂, et] at run ⊢
              exact run
            · obtain ⟨res, run, mr⟩ := lsrR (snoc_both (eqv_sub h (tags_mono tags)) (sound₁₂ rfl) a₁ a₂) tags
              refine ⟨res, ?_, mr⟩
              rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
                boolAtom, isMember, run₁₂, et] at run ⊢
              exact run
        · obtain ⟨c₁₂, rc₁₂, sc₁₂⟩ := field_sub_bool ef hm hp₁ hp₂
          by_cases both : c₁₂ = Bool.true ∧ b₁₂ = Bool.true
          · obtain ⟨rfl, rfl⟩ := both
            obtain ⟨res, run, mr⟩ := lsrR (snoc_both (one_key_sub l₁ l₂ eqv (sc₁₂ rfl) (tags_mono (Or.inl et)))
              (sound₁₂ rfl) a₁ a₂) (Or.inl et)
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember, run₁₂, rc₁₂] at run ⊢
            exact run
          · refine ⟨_, ?_, none₀⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            cases c₁₂ <;> cases b₁₂
            rotate_right
            · exact absurd ⟨rfl, rfl⟩ both
            all_goals
              simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
                Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
                boolAtom, isMember, rc₁₂, run₁₂]
        · cases b₁₂
          · obtain ⟨res, run, mr⟩ := noneR
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember, run₁₂] at run ⊢
            exact run
          · obtain ⟨res, run, mr⟩ := lsrR (snoc_both h (sound₁₂ rfl) a₁ a₂) tags
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
              boolAtom, isMember, run₁₂] at run ⊢
            exact run
        · obtain ⟨res, run, mr⟩ := noneR
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2»,
            Lynx.Except.andAlso, Erlang.erlang.«=:=/2», same, rund,
            boolAtom, isMember] at run ⊢
          exact run
      · -- a key only in the second literal
        have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
        have above : ∀ y ∈ (Term.atom a, v₁) :: xs, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
          intro y my
          rcases List.mem_cons.mp my with rfl | my
          · exact cmp'
          · exact cmp_lt_trans cmp' (sx y my)
        have nb₁ : mapLookup (P₁ ++ (Term.atom a, v₁) :: xs) (Term.atom b) = Option.none := by
          rw [lookup_append, lookup_below b₁]
          refine lookup_none fun y my eq => ?_
          have := above y my
          rw [eq, compare_self] at this
          cases this
        have recur : ∀ st', DInv E den t₁ t₂ st' P₁ (P₂ ++ [(Term.atom b, v₂)]) → ∃ res,
            Elixir.Module.Types.Descr.«opt_map_difference_strategy/5» (D m) (fieldsTerm ((.atom a, v₁) :: xs))
              (fieldsTerm ys) (.atom t₁) (.atom t₂) st' = .ok res ∧
            DRes E den t₁ t₂ res (P₁ ++ (Term.atom a, v₁) :: xs) (P₂ ++ (Term.atom b, v₂) :: ys) := by
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
        · obtain ⟨res, run, mr⟩ := recur (.atom "none") (Or.inr (Or.inr (Or.inr rfl)))
          refine ⟨res, ?_, mr⟩
          rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            Erlang.erlang.«/=/2», ev₁, ev₂] at run ⊢
          exact run
        · cases o₂
          · refine ⟨_, ?_, Or.inl ⟨rfl, b, disj_right lb₂ hv₂ (by simp [ev₂, req, boolAtom]) nb₁⟩⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2», Lynx.Except.andAlso, ev₁, ev₂, boolAtom]
          · obtain ⟨st', runm, inv'⟩ := missing_optional ef (v₂ := v₂) hm inv (by rw [ev₂, fieldSem_mk]; simp) b₁ b₂
            obtain ⟨res, run, mr⟩ := recur st' inv'
            refine ⟨res, ?_, mr⟩
            rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/5».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              Erlang.erlang.«/=/2», Lynx.Except.andAlso, ev₁, ev₂, boolAtom, runm] at run ⊢
            exact run

end Elixir.STTDescrProofsTest.Nest
