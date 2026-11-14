open BddProofs

def isNone : Term → Bool
  | .map [] => Bool.true
  | _ => Bool.false

/-- The emptiness of flat element types is decided without recursion. -/
theorem flat_empty {t : Term} (ht : ElemTerm t) (S : List (Term × Term)) (d : Dispatcher) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d t (.map S) = .ok (boolAtom (isNone t)) := by
  rcases ht with rfl | ⟨X, rfl, valid⟩
  · rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    rfl
  have absent : ∀ name, name ≠ "bitmap" → name ≠ "atom" → mapLookup X (.atom name) = Option.none := by
    intro name nb na
    cases h : mapLookup X (.atom name) with
    | none => rfl
    | some w =>
      rcases valid.keys (.atom name) (by rw [h]; rfl) with e | e
      · cases e; exact absurd rfl nb
      · cases e; exact absurd rfl na
  have anyKey : ∀ name, (X.any fun e => compareExact (fuel (.atom name) e.1) (.atom name) e.1 == .eq) =
      (mapLookup X (.atom name)).isSome := by
    intro name
    rw [Bool.eq_iff_iff, mapLookup_isSome]
    simp
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [getMapKeys_single, absent "dynamic" (by decide) (by decide), Erlang.erlang.«==/2»,
    Erlang.erlang.«is_map_key/2», anyKey, absent "tuple" (by decide) (by decide), absent "map" (by decide) (by decide),
    absent "list" (by decide) (by decide), absent "fun" (by decide) (by decide), Term.true, Term.false]
  by_cases empty : X = []
  · simp [empty, boolAtom, isNone]
  have nn : isNone (.map X) = Bool.false := by cases X <;> simp_all [isNone]
  rw [nn]
  obtain ⟨e, rest, hX⟩ := List.exists_cons_of_ne_nil empty
  have key : (mapLookup X e.1).isSome := (mapLookup_isSome _ _).mpr ⟨e, by simp [hX], compareExact_self _⟩
  simp only [empty, ite_false]
  cases ha : mapLookup X (.atom "atom") <;> cases hb : mapLookup X (.atom "bitmap") <;>
    simp [Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  rcases valid.keys _ key with k | k <;> rw [k] at key <;> simp_all

/-! Map literals. -/

/-- Results of literal intersections at every call depth from `K`, which throw `:empty` when a required
field is empty. -/
def Throws (K : Nat) (e : Nat → Except Exception Term) (P : Term → Prop) : Prop :=
  (∃ v, P v ∧ ∀ m, K ≤ m → e m = .ok v) ∨ ∀ m, K ≤ m → e m = .error (Exception.throw (.atom "empty"))

/-- Map fields: a type and whether it is optional. -/
def FieldValue (E : Term → Prop) (v : Term) : Prop :=
  ∃ (t : Term) (o : Bool), v = .tuple #[t, boolAtom o] ∧ E t

def bareIntersection : Term := .function "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]

theorem merge_fun (ops : ElemOk E K) (S : List (Term × Term)) (key v₁ v₂ : Term) (h₁ : FieldValue E v₁)
    (h₂ : FieldValue E v₂) :
    Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D m)
      bareIntersection (.map S) key v₁ v₂) (FieldValue E) := by
  obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂
  obtain ⟨e, fe, run⟩ := ops.inter f₁ f₂
  obtain ⟨b, empty⟩ := ops.empty fe S
  have dispatch : ∀ m, K + 1 ≤ m → Lynx.Dispatcher.pure (D m) bareIntersection #[t₁, t₂] = .ok e := by
    intro m hm
    obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
    exact run n hn
  by_cases thrown : (o₁ && o₂) = Bool.false ∧ b = Bool.true
  · obtain ⟨o, rfl⟩ := thrown
    refine Or.inr fun m hm => ?_
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> simp at o <;>
      simp [boolAtom, Lynx.Except.andAlso, dispatch m hm, empty m (by omega),
        isMember]
  · refine Or.inl ⟨_, ⟨e, o₁ && o₂, rfl, fe⟩, fun m hm => ?_⟩
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
      simp [boolAtom, Lynx.Except.andAlso, dispatch m hm, empty m (by omega),
        isMember]

def fieldsTerm (l : List (Term × Term)) : Term := Term.list (l.map fun e => .tuple #[e.1, e.2])

def Fields (E : Term → Prop) (v : Term) : Prop :=
  ∃ l : List (Term × Term), v = fieldsTerm l ∧ ∀ e ∈ l, FieldValue E e.2

def mergeFun (S : List (Term × Term)) : Term :=
  .function "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-0-" 3 #[bareIntersection, .map S]

theorem fields_cons {x : Term × Term} {l : List (Term × Term)} (hx : FieldValue E x.2)
    (hl : ∀ e ∈ l, FieldValue E e.2) : ∀ e ∈ x :: l, FieldValue E e.2 := fun e me => by
  rcases List.mem_cons.mp me with rfl | me
  · exact hx
  · exact hl e me

theorem merge_fields (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 2) (fun m => Erlang.orddict.«merge/3» (D m) (mergeFun S) (fieldsTerm l₁) (fieldsTerm l₂))
      (Fields E) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    refine Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => ?_⟩
    unfold Erlang.orddict.«merge/3»
    simp [fieldsTerm, mergeFun, Erlang.erlang.«is_function/2»]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ =>
      refine Or.inl ⟨fieldsTerm l₂, ⟨l₂, rfl, h₂⟩, fun m _ => ?_⟩
      unfold Erlang.orddict.«merge/3»
      cases l₂ <;> simp [fieldsTerm, mergeFun, Erlang.erlang.«is_function/2»]
    | x :: xs, [] =>
      refine Or.inl ⟨fieldsTerm (x :: xs), ⟨x :: xs, rfl, h₁⟩, fun m _ => ?_⟩
      unfold Erlang.orddict.«merge/3»
      simp [fieldsTerm, mergeFun, Erlang.erlang.«is_function/2»]
    | x :: xs, y :: ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel x.1 y.1) x.1 y.1
      · rcases ih xs (y :: ys) (by simp; omega) hxs h₂ with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
        · refine Or.inl ⟨fieldsTerm (x :: l), ⟨x :: l, rfl, fields_cons hx hl⟩, fun m hm => ?_⟩
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp] at this ⊢
          simp [this]
        · refine Or.inr fun m hm => ?_
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp] at this ⊢
          simp [this]
      · rcases merge_fun ops S x.1 x.2 y.2 hx hy with ⟨v, fv, hv⟩ | hv
        · rcases ih xs ys (by omega) hxs hys with ⟨r, ⟨l, rfl, hl⟩, run⟩ | run
          · refine Or.inl ⟨fieldsTerm ((x.1, v) :: l), ⟨(x.1, v) :: l, rfl, fields_cons fv hl⟩, fun m hm => ?_⟩
            obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
            have h1 := hv n hn
            have h2 := run (n + 1) hm
            unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, mergeFun,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at h2 ⊢
            simp [h1, h2]
          · refine Or.inr fun m hm => ?_
            obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
            have h1 := hv n hn
            have h2 := run (n + 1) hm
            unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, mergeFun,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at h2 ⊢
            simp [h1, h2]
        · refine Or.inr fun m hm => ?_
          obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
          have h1 := hv n hn
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, mergeFun,
            Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure]
          simp [h1]
      · rcases ih (x :: xs) ys (by simp; omega) h₁ hys with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
        · refine Or.inl ⟨fieldsTerm (y :: l), ⟨y :: l, rfl, fields_cons hy hl⟩, fun m hm => ?_⟩
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]
        · refine Or.inr fun m hm => ?_
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]

theorem any1_list (d : Dispatcher) (f : Term) (res : Term → Bool) :
    ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (boolAtom (res x))) →
      Erlang.lists.«any_1/2» d f (Term.list l) = .ok (boolAtom (l.any res)) := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«any_1/2», boolAtom]
  | cons x xs ih =>
    intro hf
    rw [Erlang.lists.«any_1/2».eq_def]
    have hx := hf x List.mem_cons_self
    have tail := ih fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;> simp [hx, h, boolAtom, tail]

theorem any_list (d : Dispatcher) (m nm : String) (caps : Array Term) (res : Term → Bool) (l : List Term)
    (hf : ∀ x ∈ l, d.pure (.function m nm 1 caps) #[x] = .ok (boolAtom (res x))) :
    Erlang.lists.«any/2» d (.function m nm 1 caps) (Term.list l) = .ok (boolAtom (l.any res)) := by
  cases l with
  | nil => simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», boolAtom]
  | cons x xs =>
    have hx := hf x List.mem_cons_self
    have tail := any1_list d _ res xs fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;>
      simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», hx, h, boolAtom, tail]

theorem all1_list (d : Dispatcher) (f : Term) (res : Term → Bool) :
    ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (boolAtom (res x))) →
      Erlang.lists.«all_1/2» d f (Term.list l) = .ok (boolAtom (l.all res)) := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«all_1/2», boolAtom]
  | cons x xs ih =>
    intro hf
    rw [Erlang.lists.«all_1/2».eq_def]
    have hx := hf x List.mem_cons_self
    have tail := ih fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;> simp [hx, h, boolAtom, tail]

theorem all_list (d : Dispatcher) (m nm : String) (caps : Array Term) (res : Term → Bool) (l : List Term)
    (hf : ∀ x ∈ l, d.pure (.function m nm 1 caps) #[x] = .ok (boolAtom (res x))) :
    Erlang.lists.«all/2» d (.function m nm 1 caps) (Term.list l) = .ok (boolAtom (l.all res)) := by
  cases l with
  | nil => simp [Erlang.lists.«all/2», Erlang.erlang.«is_function/2», boolAtom]
  | cons x xs =>
    have hx := hf x List.mem_cons_self
    have tail := all1_list d _ res xs fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;>
      simp [Erlang.lists.«all/2», Erlang.erlang.«is_function/2», hx, h, boolAtom, tail]

/-- The optional flag of a field entry. -/
def optFlag (x : Term) : Bool :=
  match x with
  | .tuple #[_, .tuple #[_, .atom "true"]] => Bool.true
  | _ => Bool.false

theorem optFlag_entry (k t : Term) (o : Bool) : optFlag (.tuple #[k, .tuple #[t, boolAtom o]]) = o := by
  cases o <;> rfl

/-- Predicates on the optional flags of fields return Booleans. -/
theorem optional_list (d : Dispatcher) (f : Term) (lam : Term → Except Exception Term)
    (isF : ∀ x, d.pure f #[x] = lam x) (flag : Bool → Bool)
    (lamOk : ∀ k t o, lam (.tuple #[k, .tuple #[t, boolAtom o]]) = .ok (boolAtom (flag o)))
    (l : List (Term × Term)) (hl : ∀ e ∈ l, FieldValue E e.2) :
    ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]), d.pure f #[x] = .ok (boolAtom (flag (optFlag x))) := by
  intro x mx
  obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
  obtain ⟨t, o, ho, -⟩ := hl e me
  rw [isF, ho, lamOk, optFlag_entry]

theorem closed_fun₀ (k t : Term) (o : Bool) :
    Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-0-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
      .ok (boolAtom (!o)) := by
  cases o <;> simp [Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-0-/1», boolAtom,
    Erlang.erlang.«not/1»]

theorem closed_fun₁ (k t : Term) (o : Bool) :
    Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-1-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
      .ok (boolAtom (!o)) := by
  cases o <;> simp [Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-1-/1», boolAtom,
    Erlang.erlang.«not/1»]

theorem closed_fields (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m)
      (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
  have tails : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
      ∃ b, ∀ m, Lynx.Except.orElse
        (Erlang.lists.«any/2» (D m)
          (.function "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-0-" 1 #[]) (fieldsTerm l₁))
        (Erlang.lists.«any/2» (D m)
          (.function "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-1-" 1 #[]) (fieldsTerm l₂))
        Bool.true = .ok (boolAtom b) := by
    intro l₁ l₂ h₁ h₂
    refine ⟨(l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) ||
      (l₂.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x), fun m => ?_⟩
    have r₁ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-0-/1».pure m) (fun o => !o)
      closed_fun₀ l₁ h₁)
    have r₂ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-1-/1».pure m) (fun o => !o)
      closed_fun₁ l₂ h₂)
    simp only [fieldsTerm] at r₁ r₂ ⊢
    rw [r₁, r₂]
    cases (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) <;>
      simp [boolAtom, Lynx.Except.orElse] <;> rfl
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
      (l₁ = [] ∨ l₂ = []) →
      Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m)
        (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
    intro l₁ l₂ h₁ h₂ empty
    obtain ⟨b, hb⟩ := tails l₁ l₂ h₁ h₂
    cases b
    · refine Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => ?_⟩
      have hb := hb m
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
    · refine Or.inr fun m _ => ?_
      have hb := hb m
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
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
      obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁ _ List.mem_cons_self
      obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂ _ List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel k₁ k₂) k₁ k₂
      · cases o₁
        · refine Or.inr fun m _ => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs ((k₂, _) :: ys) (by simp; omega) hxs h₂ with ⟨v, hv, run⟩ | run
          · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
          · refine Or.inr fun m hm => ?_
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
      · obtain ⟨e, fe, run⟩ := ops.inter f₁ f₂
        obtain ⟨b, empty⟩ := ops.empty fe S
        have dispatch : ∀ m, K + 1 ≤ m → Lynx.Dispatcher.pure (D m) bareIntersection #[t₁, t₂] = .ok e := by
          intro m hm
          obtain ⟨n, rfl, hn⟩ := succ_of_le hm
          rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
          exact run n hn
        have value : FieldValue E (.tuple #[e, boolAtom (o₁ && o₂)]) := ⟨e, _, rfl, fe⟩
        have notLt : ¬(Term.compare (Term.fuel k₁ k₂) k₁ k₂).isLT = Bool.true := by simp [cmp]
        have notGt : ¬(Term.compare (Term.fuel k₁ k₂) k₁ k₂).isGT = Bool.true := by simp [cmp]
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ b = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          refine Or.inr fun m hm => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          cases o₁ <;> cases o₂ <;> simp at o <;>
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega)]
        · rcases ih xs ys (by omega) hxs hys with ⟨r, ⟨l, rfl, hl⟩, rest⟩ | rest
          · refine Or.inl ⟨fieldsTerm ((k₁, .tuple #[e, boolAtom (o₁ && o₂)]) :: l),
              ⟨_, rfl, fields_cons value hl⟩, fun m hm => ?_⟩
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
          · refine Or.inr fun m hm => ?_
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
      · have cmp' : Term.compare (Term.fuel k₂ k₁) k₂ k₁ = .lt := Lynx.Term.compare_lt_of_gt cmp
        cases o₂
        · refine Or.inr fun m _ => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember]
        · rcases ih ((k₁, _) :: xs) ys (by simp; omega) h₁ hys with ⟨v, hv, run⟩ | run
          · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember] using this
          · refine Or.inr fun m hm => ?_
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember] using this

theorem open_closed_fun (k t : Term) (o : Bool) :
    Elixir.Module.Types.Descr.«-map_literal_intersection_open_closed/4-fun-0-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
      .ok (boolAtom o) := by
  simp [Elixir.Module.Types.Descr.«-map_literal_intersection_open_closed/4-fun-0-/1»]

theorem open_closed_fields (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m)
      (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
      (l₁ = [] ∨ l₂ = []) →
      Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m)
        (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
    intro l₁ l₂ h₁ h₂ empty
    have hb := fun m => all_list (D m) _ _ _ (fun x => optFlag x) _ (optional_list (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_open_closed/4-fun-0-/1».pure m)
      (fun o => o) open_closed_fun l₁ h₁)
    cases b : (l₁.map fun e => Term.tuple #[e.1, e.2]).all (fun x => optFlag x)
    · refine Or.inr fun m _ => ?_
      have hb := hb m
      rw [b] at hb
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
    · refine Or.inl ⟨fieldsTerm l₂, ⟨l₂, rfl, h₂⟩, fun m _ => ?_⟩
      have hb := hb m
      rw [b] at hb
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
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
      obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁ _ List.mem_cons_self
      obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂ _ List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel k₁ k₂) k₁ k₂
      · cases o₁
        · refine Or.inr fun m _ => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs ((k₂, _) :: ys) (by simp; omega) hxs h₂ with ⟨v, hv, run⟩ | run
          · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
          · refine Or.inr fun m hm => ?_
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
      · obtain ⟨e, fe, run⟩ := ops.inter f₁ f₂
        obtain ⟨b, empty⟩ := ops.empty fe S
        have dispatch : ∀ m, K + 1 ≤ m → Lynx.Dispatcher.pure (D m) bareIntersection #[t₁, t₂] = .ok e := by
          intro m hm
          obtain ⟨n, rfl, hn⟩ := succ_of_le hm
          rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
          exact run n hn
        have value : FieldValue E (.tuple #[e, boolAtom (o₁ && o₂)]) := ⟨e, _, rfl, fe⟩
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ b = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          refine Or.inr fun m hm => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          cases o₁ <;> cases o₂ <;> simp at o <;>
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega)]
        · rcases ih xs ys (by omega) hxs hys with ⟨r, ⟨l, rfl, hl⟩, rest⟩ | rest
          · refine Or.inl ⟨fieldsTerm ((k₁, .tuple #[e, boolAtom (o₁ && o₂)]) :: l),
              ⟨_, rfl, fields_cons value hl⟩, fun m hm => ?_⟩
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
          · refine Or.inr fun m hm => ?_
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
      · rcases ih ((k₁, _) :: xs) ys (by simp; omega) h₁ hys with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
        · refine Or.inl ⟨fieldsTerm ((k₂, _) :: l), ⟨_, rfl, fields_cons (h₂ _ List.mem_cons_self) hl⟩,
            fun m hm => ?_⟩
          have := run m hm
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]
        · refine Or.inr fun m hm => ?_
          have := run m hm
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]

/-- Map tags: open, closed, or domains, the types of the values of each kind of keys. -/
def MapTag (E : Term → Prop) (tag : Term) : Prop :=
  tag = .atom "open" ∨ tag = .atom "closed" ∨ ∃ dl : List (Term × Term), tag = fieldsTerm dl ∧ ∀ e ∈ dl, E e.2

/-- Lines of maps: a tag and fields. -/
def MapPos (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)), p = .tuple #[tag, fieldsTerm l] ∧ MapTag E tag ∧
    ∀ e ∈ l, FieldValue E e.2

/-- Map literals: a key, a tag, and fields. -/
def MapLit (E : Term → Prop) (t : Term) : Prop :=
  ∃ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] ∧
    MapTag E tag ∧ ∀ e ∈ l, FieldValue E e.2

theorem Throws.wrap {K : Nat} {e : Nat → Except Exception Term} (h : Throws K e (Fields E)) {tag : Term}
    (htag : MapTag E tag) :
    Throws K (fun m => e m >>= fun r => pure (Term.tuple #[tag, r])) (MapPos E) := by
  rcases h with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
  · exact Or.inl ⟨_, ⟨tag, l, rfl, htag, hl⟩, fun m hm => by simp [run m hm]⟩
  · exact Or.inr fun m hm => by simp [run m hm]

theorem Throws.mono {K K' : Nat} {e : Nat → Except Exception Term} {P : Term → Prop} (h : Throws K e P)
    (le : K ≤ K') : Throws K' e P := by
  rcases h with ⟨v, hv, run⟩ | run
  · exact Or.inl ⟨v, hv, fun m hm => run m (by omega)⟩
  · exact Or.inr fun m hm => run m (by omega)

theorem Throws.bind {K : Nat} {e : Nat → Except Exception Term} {P Q : Term → Prop} (h : Throws K e P)
    {f : Nat → Term → Except Exception Term} (hf : ∀ v, P v → Throws K (fun m => f m v) Q) :
    Throws K (fun m => e m >>= f m) Q := by
  rcases h with ⟨v, hv, run⟩ | run
  · rcases hf v hv with ⟨w, hw, run'⟩ | run'
    · exact Or.inl ⟨w, hw, fun m hm => by simp [run m hm, run' m hm]⟩
    · exact Or.inr fun m hm => by simp [run m hm, run' m hm]
  · exact Or.inr fun m hm => by simp [run m hm]

theorem MapTag.atom_open : MapTag E (.atom "open") := Or.inl rfl

theorem MapTag.atom_closed : MapTag E (.atom "closed") := Or.inr (Or.inl rfl)

theorem MapTag.of_string {tag : String} (g : tag = "open" ∨ tag = "closed") : MapTag E (.atom tag) := by
  rcases g with rfl | rfl
  · exact MapTag.atom_open
  · exact MapTag.atom_closed

theorem fieldsTerm_ne_atom (l : List (Term × Term)) (s : String) : fieldsTerm l ≠ .atom s := by
  cases l <;> simp [fieldsTerm, Term.list]

/-- `orddict:find/2` finds the value of an entry, or nothing. -/
theorem find_entry_or_error (k : Term) : ∀ l : List (Term × Term),
    Erlang.orddict.«find/2» k (fieldsTerm l) = .ok (.atom "error") ∨
      ∃ e ∈ l, Erlang.orddict.«find/2» k (fieldsTerm l) = .ok (.tuple #[.atom "ok", e.2])
  | [] => Or.inl (by rw [Erlang.orddict.«find/2».eq_def]; simp [fieldsTerm, Term.list])
  | (a, v) :: t => by
    rcases cmp : Term.compare (Term.fuel k a) k a
    · left
      rw [Erlang.orddict.«find/2».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
    · right
      refine ⟨(a, v), List.mem_cons_self, ?_⟩
      rw [Erlang.orddict.«find/2».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
    · have step : Erlang.orddict.«find/2» k (fieldsTerm ((a, v) :: t)) = Erlang.orddict.«find/2» k (fieldsTerm t) := by
        conv => lhs; rw [Erlang.orddict.«find/2».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
      rw [step]
      rcases find_entry_or_error k t with h | ⟨e, me, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ me, h⟩

/-- The field of the atom keys outside the fields of a literal: `term()` when open, `none()` when closed, and
the atom domain, if any, otherwise. -/
theorem tag_field_ok (hterm : E (.atom "term")) (hnone : E (.map [])) {tag : Term} (g : MapTag E tag) :
    ∃ f, Elixir.Module.Types.Descr.«map_key_tag_to_field/1» tag = .ok f ∧ FieldValue E f := by
  rcases g with rfl | rfl | ⟨dl, rfl, hdl⟩
  · exact ⟨_, rfl, ⟨_, Bool.true, rfl, hterm⟩⟩
  · exact ⟨_, rfl, ⟨_, Bool.true, rfl, hnone⟩⟩
  · have ne := fieldsTerm_ne_atom dl
    rcases find_entry_or_error (.atom "atom") dl with h | ⟨e, me, h⟩
    · refine ⟨_, ?_, ⟨_, Bool.true, rfl, hnone⟩⟩
      generalize fieldsTerm dl = T at h ne
      rw [Elixir.Module.Types.Descr.«map_key_tag_to_field/1».eq_def]
      split
      · exact absurd rfl (ne "open")
      · exact absurd rfl (ne "closed")
      · simp [h, boolAtom]
    · refine ⟨_, ?_, ⟨_, Bool.true, rfl, hdl e me⟩⟩
      generalize fieldsTerm dl = T at h ne
      rw [Elixir.Module.Types.Descr.«map_key_tag_to_field/1».eq_def]
      split
      · exact absurd rfl (ne "open")
      · exact absurd rfl (ne "closed")
      · simp [h, boolAtom]

/-- Domains intersect kind by kind, dropping the empty intersections. -/
theorem domain_fields_ok (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, E e.2) → (∀ e ∈ l₂, E e.2) → ∃ l : List (Term × Term),
      (∀ e ∈ l, E e.2) ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«map_domain_intersection_fields/3» (D m)
        (fieldsTerm l₁) (fieldsTerm l₂) (.map S) = .ok (fieldsTerm l) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨[], by simp, fun m _ => by
      rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list]⟩
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ =>
      exact ⟨[], by simp, fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
        cases l₂ <;> simp [fieldsTerm, Term.list]⟩
    | x :: xs, [] =>
      exact ⟨[], by simp, fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list]⟩
    | x :: xs, y :: ys =>
      have hxs : ∀ e ∈ xs, E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel x.1 y.1) x.1 y.1
      · obtain ⟨l, hl, run⟩ := ih xs (y :: ys) (by simp; omega) hxs h₂
        refine ⟨l, hl, fun m hm => ?_⟩
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run m hm]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
      · obtain ⟨c, hc, inter⟩ := ops.inter (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
        obtain ⟨b, empty⟩ := ops.empty hc S
        obtain ⟨l, hl, run⟩ := ih xs ys (by omega) hxs hys
        cases b
        · refine ⟨(x.1, c) :: l, fun e me => ?_, fun m hm => ?_⟩
          · rcases List.mem_cons.mp me with rfl | me
            · exact hc
            · exact hl e me
          · have r := run m hm
            simp only [fieldsTerm] at r
            rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              inter m hm, empty m hm, boolAtom, isMember, r]
        · refine ⟨l, hl, fun m hm => ?_⟩
          rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run m hm]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            inter m hm, empty m hm, boolAtom, isMember]
      · obtain ⟨l, hl, run⟩ := ih (x :: xs) ys (by simp; omega) h₁ hys
        refine ⟨l, hl, fun m hm => ?_⟩
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run m hm]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]

/-- The domains of intersections of map literals. -/
theorem domain_inter_ok (ops : ElemOk E K) (S : List (Term × Term)) {t₁ t₂ : Term} (g₁ : MapTag E t₁)
    (g₂ : MapTag E t₂) : ∃ t, MapTag E t ∧ ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) t₁ t₂ (.map S) = .ok t := by
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, h₁⟩
  · exact ⟨t₂, g₂, fun m _ => by
      rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]
      rcases g₂ with rfl | rfl | ⟨dl₂, rfl, _⟩ <;> simp [fieldsTerm_ne_atom]⟩
  · exact ⟨_, MapTag.atom_closed, fun m _ => by
      rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp⟩
  · rcases g₂ with rfl | rfl | ⟨dl₂, rfl, h₂⟩
    · exact ⟨_, Or.inr (Or.inr ⟨dl₁, rfl, h₁⟩), fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom]⟩
    · exact ⟨_, MapTag.atom_closed, fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom]⟩
    · obtain ⟨l, hl, run⟩ := domain_fields_ok ops S _ dl₁ dl₂ (Nat.le_refl _) h₁ h₂
      have step : ∀ m, K ≤ m → Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) (fieldsTerm dl₁)
          (fieldsTerm dl₂) (.map S) = (match fieldsTerm l with
            | .nil => Except.ok (Term.atom "closed")
            | t => Except.ok t) := by
        intro m hm
        have r := run m hm
        have ne₁ := fieldsTerm_ne_atom dl₁
        have ne₂ := fieldsTerm_ne_atom dl₂
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
      cases l with
      | nil => exact ⟨_, MapTag.atom_closed, fun m hm => by rw [step m hm]; rfl⟩
      | cons x xs =>
        exact ⟨_, Or.inr (Or.inr ⟨x :: xs, rfl, hl⟩), fun m hm => by
          rw [step m hm]; simp [fieldsTerm, Term.list]⟩

def mergeFun₁ (S : List (Term × Term)) : Term :=
  .function "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-1-" 3 #[bareIntersection, .map S]

theorem merge_fun₁_eq (d : Dispatcher) (f s k a b : Term) :
    Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-1-/5» d f s k a b =
      Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» d f s k a b := by
  unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-1-/5»
    Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
  rfl

/-- Merging a field with a default field. -/
theorem merge_call₁ (ops : ElemOk E K) (S : List (Term × Term)) (key v₁ v₂ : Term) (h₁ : FieldValue E v₁)
    (h₂ : FieldValue E v₂) :
    Throws (K + 2) (fun m => Lynx.Dispatcher.pure (D m) (mergeFun₁ S) #[key, v₁, v₂]) (FieldValue E) := by
  rcases merge_fun ops S key v₁ v₂ h₁ h₂ with ⟨v, hv, run⟩ | run
  · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
    obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
    simp [mergeFun₁, Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-1-/3».pure,
      merge_fun₁_eq, run n hn]
  · refine Or.inr fun m hm => ?_
    obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
    simp [mergeFun₁, Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-1-/3».pure,
      merge_fun₁_eq, run n hn]

theorem Throws.congr {K : Nat} {e e' : Nat → Except Exception Term} {P : Term → Prop}
    (h : ∀ m, K ≤ m → e m = e' m) (h' : Throws K e' P) : Throws K e P := by
  rcases h' with ⟨v, hv, run⟩ | run
  · exact Or.inl ⟨v, hv, fun m hm => by rw [h m hm]; exact run m hm⟩
  · exact Or.inr fun m hm => by rw [h m hm]; exact run m hm

/-- Fields merged with defaults: keys of one side meet the default field of the other. -/
theorem merge_defaults (ops : ElemOk E K) (S : List (Term × Term)) {d₁ d₂ : Term} (fd₁ : FieldValue E d₁)
    (fd₂ : FieldValue E d₂) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
    (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 2) (fun m => Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D m) (fieldsTerm l₁) d₁
      (fieldsTerm l₂) d₂ (mergeFun₁ S)) (Fields E) := by
  have call := merge_call₁ ops S
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    exact Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => by
      dsimp only; rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]⟩
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    have step : ∀ (k : Term) {v₁ v₂ : Term} (l₁' l₂' : List (Term × Term)),
        FieldValue E v₁ → FieldValue E v₂ → l₁'.length + l₂'.length ≤ N →
        (∀ e ∈ l₁', FieldValue E e.2) → (∀ e ∈ l₂', FieldValue E e.2) →
        Throws (K + 2) (fun m => Lynx.Dispatcher.pure (D m) (mergeFun₁ S) #[k, v₁, v₂] >>= fun r =>
          Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D m) (fieldsTerm l₁') d₁ (fieldsTerm l₂') d₂
            (mergeFun₁ S) >>= fun t => pure (Term.cons (.tuple #[k, r]) t)) (Fields E) := by
      intro k v₁ v₂ l₁' l₂' f₁ f₂ sz g₁ g₂
      refine Throws.bind (call k v₁ v₂ f₁ f₂) fun r hr => ?_
      refine Throws.bind (ih l₁' l₂' sz g₁ g₂) fun t ht => ?_
      obtain ⟨l, rfl, hl⟩ := ht
      exact Or.inl ⟨fieldsTerm ((k, r) :: l), ⟨_, rfl, fields_cons hr hl⟩, fun m _ => rfl⟩
    match l₁, l₂ with
    | [], [] =>
      exact Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => by
        dsimp only; rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]⟩
    | [], y :: ys =>
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      refine Throws.congr (fun m _ => ?_) (step y.1 [] ys fd₁ (h₂ y List.mem_cons_self) (by simp at size ⊢; omega)
        (by simp) hys)
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simp [fieldsTerm, Term.list]
    | x :: xs, [] =>
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      refine Throws.congr (fun m _ => ?_) (step x.1 xs [] (h₁ x List.mem_cons_self) fd₂ (by simp at size ⊢; omega)
        hxs (by simp))
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simp [fieldsTerm, Term.list]
    | x :: xs, y :: ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel x.1 y.1) x.1 y.1
      · refine Throws.congr (fun m _ => ?_) (step x.1 xs (y :: ys) hx fd₂ (by simp; omega) hxs h₂)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
      · refine Throws.congr (fun m _ => ?_) (step x.1 xs ys hx hy (by omega) hxs hys)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
      · refine Throws.congr (fun m _ => ?_) (step y.1 (x :: xs) ys fd₁ hy (by simp; omega) h₁ hys)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]

/-- Intersections of map literals with domains merge their fields with the defaults of the other side. -/
theorem literal_domains_ok (ops : ElemOk E K) (S : List (Term × Term)) {t₁ t₂ : Term} (g₁ : MapTag E t₁)
    (g₂ : MapTag E t₂) (notAtoms : ∀ s₁ s₂, ¬(t₁ = .atom s₁ ∧ t₂ = .atom s₂)) (l₁ l₂ : List (Term × Term))
    (h₁ : ∀ e ∈ l₁, FieldValue E e.2) (h₂ : ∀ e ∈ l₂, FieldValue E e.2) :
    Throws (K + 2) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection/6» (D m)
      t₁ (fieldsTerm l₁) t₂ (fieldsTerm l₂) bareIntersection (.map S)) (MapPos E) := by
  obtain ⟨d₁, run₁, fd₁⟩ := tag_field_ok ops.term ops.none g₁
  obtain ⟨d₂, run₂, fd₂⟩ := tag_field_ok ops.term ops.none g₂
  obtain ⟨t, gt, runT⟩ := domain_inter_ok ops S g₁ g₂
  have merged := merge_defaults ops S fd₁ fd₂ _ l₁ l₂ (Nat.le_refl _) h₁ h₂
  refine Throws.congr (fun m hm => ?_) (merged.wrap gt)
  unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
  split <;> try (exfalso; exact notAtoms _ _ ⟨rfl, rfl⟩)
  simp [run₁, run₂, runT m (by omega), mergeFun₁]

theorem literal_ok (ops : ElemOk E K) (S : List (Term × Term)) {t₁ t₂ : Term} (g₁ : MapTag E t₁)
    (g₂ : MapTag E t₂) (l₁ l₂ : List (Term × Term)) (h₁ : ∀ e ∈ l₁, FieldValue E e.2)
    (h₂ : ∀ e ∈ l₂, FieldValue E e.2) :
    Throws (K + 2) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection/6» (D m)
      t₁ (fieldsTerm l₁) t₂ (fieldsTerm l₂) bareIntersection (.map S)) (MapPos E) := by
  have size := Nat.le_refl (l₁.length + l₂.length)
  have size' : l₂.length + l₁.length ≤ l₁.length + l₂.length := by omega
  have general := literal_domains_ok ops S g₁ g₂
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, -⟩ <;> rcases g₂ with rfl | rfl | ⟨dl₂, rfl, -⟩ <;>
    try exact general (fun _ _ h => fieldsTerm_ne_atom _ _ (by first | exact h.1 | exact h.2)) l₁ l₂ h₁ h₂
  all_goals unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
  · have := (merge_fields ops S _ l₁ l₂ size h₁ h₂).wrap MapTag.atom_open
    simpa [mergeFun] using this.mono (by omega)
  · simpa using ((open_closed_fields ops S _ l₁ l₂ size h₁ h₂).wrap MapTag.atom_closed).mono (by omega)
  · simpa using ((open_closed_fields ops S _ l₂ l₁ size' h₂ h₁).wrap MapTag.atom_closed).mono (by omega)
  · simpa using ((closed_fields ops S _ l₁ l₂ size h₁ h₂).wrap MapTag.atom_closed).mono (by omega)

theorem map_line_ok (ops : ElemOk E K) (S : List (Term × Term)) {p t : Term} (hp : MapPos E p) (ht : MapLit E t) :
    (∀ m, K + 2 ≤ m → Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) p t (.map S) =
        .ok (.atom "empty")) ∨
      ∃ p', MapPos E p' ∧ ∀ m, K + 2 ≤ m →
        Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) p t (.map S) = .ok p' := by
  obtain ⟨t₁, l₁, rfl, g₁, h₁⟩ := hp
  obtain ⟨k, t₂, l₂, rfl, g₂, h₂⟩ := ht
  rcases literal_ok ops S g₁ g₂ l₁ l₂ h₁ h₂ with ⟨v, hv, run⟩ | run
  · right
    refine ⟨v, hv, fun m hm => ?_⟩
    have run := run m hm
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run]
  · left
    intro m hm
    have run := run m hm
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason]

theorem map_bdd_empty_unsat (ops : ElemOk E K) {m : Nat} (hm : K + 2 ≤ m) {ok : Term → Prop} {r : Term}
    (wr : Bdd ok r) (lits : ∀ t, ok t → MapLit E t) (unsat : Unsat r) :
    ∀ pos negs S, MapPos E pos →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos negs r (.map S) = .ok (.atom "true") := by
  revert lits unsat
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLit E t) → Unsat r → ∀ pos negs S, MapPos E pos →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos negs r (.map S) = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro _ _ _ pos negs S _
    unfold Elixir.Module.Types.Descr.«map_bdd_empty?/4»
    rfl
  · intro _ k x y _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro ok h lit c u d _ okl hc hu hd ic iu id lits unsat pos negs S hp
    obtain ⟨uc, uu, ud⟩ := unsat_children hc hu hd unsat
    have lits' : ∀ t, Above ok lit t → MapLit E t := fun t ht => lits t ht.1
    have dTrue := id lits' ud pos (.cons lit negs) S hp
    have uTrue := iu lits' uu pos negs S hp
    unfold Elixir.Module.Types.Descr.«map_bdd_empty?/4»
    simp only [dTrue, uTrue, Lynx.Except.andAlso]
    rcases map_line_ok ops S hp (lits lit okl) with line | ⟨p', hp', line⟩
    · simp [line m hm]
    · have cTrue := ic lits' uc p' negs S hp'
      obtain ⟨tg, l, rfl, -, -⟩ := hp'
      simp [line m hm, cTrue]

def EmptyMap (K : Nat) (r : Term) : Prop :=
  ∀ m S, K + 2 ≤ m → Elixir.Module.Types.Descr.«map_empty?/2» (D m) r (.map S) = .ok (.atom "true")

theorem map_empty_unsat (ops : ElemOk E K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
    (lits : ∀ t, ok t → MapLit E t) (unsat : Unsat r) : EmptyMap K r := by
  intro m S hm
  have run := fun S' => map_bdd_empty_unsat ops hm wr lits unsat (.tuple #[.atom "open", .nil]) .nil S'
    ⟨.atom "open", [], rfl, MapTag.atom_open, by simp⟩
  unfold Elixir.Module.Types.Descr.«map_empty?/2»
  by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "map") r) e.1) (.cons (.atom "map") r) e.1 == .eq) = Bool.true
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen,
      Term.false, Erlang.maps.«put/3», run]

def MapOk (E : Term → Prop) (t : Term) : Prop := MapLit E t ∧ ¬IsTop t

/-- Map types are the top map literal or ordered BDDs of other map literals. -/
abbrev MapField (E : Term → Prop) (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd (MapOk E) w

def MapCancel (K : Nat) (x nb : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«map_intersection/2» x nb = .ok r ∧
    (kept (.atom "map", r) = Bool.true → EmptyMap K r)

theorem map_intersection_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«map_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«map_intersection/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem map_cancel (ops : ElemOk E K) (x : Term) (field : MapField E x) :
    ∃ nb, Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok nb ∧
      (kept (.atom "map", nb) = Bool.true → MapCancel K x nb) := by
  rcases field with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«map_difference/2»], fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
    unfold Elixir.Module.Types.Descr.«map_difference/2»
    simp [diff_leaf_top]
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun _ => ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩⟩
    · unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_bot]
    · unfold Elixir.Module.Types.Descr.«map_intersection/2»
      rfl
  · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
    have wnb := keep _ wx
    refine ⟨nb, ?_, fun _ => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_difference/2»
      split
      · next _ _ e => exact (notTop _ e).elim
      · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact run
      · next h₁ => exact (h₁ _ _ rfl rfl).elim
    · have wl : Bdd (MapLit E) (.tuple #[.integer k, tg, l]) := wx.mono fun _ h => h.1
      obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
      refine ⟨r, ?_, fun _ => map_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
        fun ρ resp => ?_⟩
      · rw [map_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
        exact rr
      · rw [sr ρ resp, sem ρ resp]
        cases eval ρ (.tuple #[.integer k, tg, l]) <;> rfl
  · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
    have wnb := keep _ wx
    refine ⟨nb, ?_, fun _ => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [run]
    · have wl : Bdd (MapLit E) (.tuple #[.integer h, lit, c, u, d]) := wx.mono fun _ h => h.1
      obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
      refine ⟨r, ?_, fun _ => map_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
        fun ρ resp => ?_⟩
      · rw [map_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
        exact rr
      · rw [sr ρ resp, sem ρ resp]
        cases eval ρ (.tuple #[.integer h, lit, c, u, d]) <;> rfl

/-! Reading the map specification. -/

theorem map_fields_spec (hE : NestedOk E depth) (fs : Term) (h : «map_fields?/2» fs depth = .ok Term.true) :
    ∃ l : List (Term × Term), fs = fieldsTerm l ∧ ∀ e ∈ l, FieldValue E e.2 := by
  unfold «map_fields?/2» at h
  split at h
  · rename_i k t o rest
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨hb, ht⟩, hr⟩ := h
    obtain ⟨l, rfl, hl⟩ := map_fields_spec hE rest hr
    have ob : ∃ b, o = boolAtom b := by
      cases o <;> simp [Erlang.erlang.«is_boolean/1»] at hb
      rename_i name
      by_cases t : name = "true"
      · exact ⟨Bool.true, by simp [boolAtom, t]⟩
      · by_cases f : name = "false"
        · exact ⟨Bool.false, by simp [boolAtom, f]⟩
        · simp [t, f] at hb
    obtain ⟨b, rfl⟩ := ob
    refine ⟨(k, .tuple #[t, boolAtom b]) :: l, rfl, fun e me => ?_⟩
    rcases List.mem_cons.mp me with rfl | me
    · exact ⟨t, b, rfl, hE _ ht⟩
    · exact hl e me
  · exact ⟨[], rfl, by simp⟩
  · simp [Term.true] at h
termination_by sizeOf fs
decreasing_by all_goals (simp_wf; subst_vars; simp; omega)

theorem map_domains_spec (hE : NestedOk E depth) (ds : Term) (h : «map_domains?/2» ds depth = .ok Term.true) :
    ∃ dl : List (Term × Term), ds = fieldsTerm dl ∧ ∀ e ∈ dl, E e.2 := by
  unfold «map_domains?/2» at h
  split at h
  · rename_i k t rest
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨ht, hr⟩ := h
    obtain ⟨dl, rfl, hdl⟩ := map_domains_spec hE rest hr
    refine ⟨(k, t) :: dl, rfl, fun e me => ?_⟩
    rcases List.mem_cons.mp me with rfl | me
    · exact hE _ ht
    · exact hdl e me
  · exact ⟨[], rfl, by simp⟩
  · simp [Term.true] at h
termination_by sizeOf ds
decreasing_by all_goals (simp_wf; subst_vars; simp; omega)

theorem map_tag_spec (hE : NestedOk E depth) (tag : Term) (h : «map_tag?/2» tag depth = .ok Term.true) :
    MapTag E tag := by
  by_cases o : tag = .atom "open"
  · exact Or.inl o
  by_cases c : tag = .atom "closed"
  · exact Or.inr (Or.inl c)
  unfold «map_tag?/2» at h
  simp [isMember, o, c] at h
  obtain ⟨dl, rfl, hdl⟩ := map_domains_spec hE _ h
  exact Or.inr (Or.inr ⟨dl, rfl, hdl⟩)

theorem map_literal_spec (hE : NestedOk E depth) {lit lower : Term}
    (h : «map_literal?/3» lit lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ MapOk E lit := by
  unfold «map_literal?/3» at h
  split at h
  · rename_i key tag fields
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨⟨⟨hk, hlt⟩, htag⟩, hopen⟩, hfields⟩ := h
    cases key <;> simp [Erlang.erlang.«is_integer/1»] at hk
    rename_i k
    have lt : Term.compare (Term.fuel lower (.tuple #[.integer k, tag, fields])) lower (.tuple #[.integer k, tag, fields]) = .lt :=
      Lynx.Term.compare_lt_of_gt (by simpa [Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, boolAtom] using hlt)
    have g := map_tag_spec hE tag htag
    obtain ⟨l, rfl, hl⟩ := map_fields_spec hE _ hfields
    refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, tag, l, rfl, g, hl⟩, ?_⟩
    rintro ⟨_, e⟩
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨-, rfl, hnil⟩ := e
    simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», hnil] at hopen
  · simp [Term.true] at h

theorem ordered_map_spec (hE : NestedOk E depth) : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
    «ordered_map_bdd?/3» b lower depth = .ok Term.true → Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ MapOk E t) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «ordered_map_bdd?/3» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := map_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := map_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ MapOk E t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ MapOk E t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

theorem map_bdd_spec (hE : NestedOk E depth) {w : Term} (h : «map_bdd?/2» w depth = .ok Term.true) :
    MapField E w := by
  unfold «map_bdd?/2» at h
  split at h
  · rename_i key
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ((ordered_map_spec hE _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)
