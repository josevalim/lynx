open BddProofs

/-- List literals other than the top literal `{_, term, term}`, which list operations treat as the top type. -/
def ListOk (t : Term) : Prop := ¬∃ k : Term, t = .tuple #[k, .atom "term", .atom "term"]

/-- List literals whose element and tail types are `E`. -/
def ListLit (E : Term → Prop) (t : Term) : Prop :=
  ListOk t ∧ ∃ (k : Int) (a b : Term), t = .tuple #[.integer k, a, b] ∧ E a ∧ E b

theorem bind_true {e : Except Exception Term} {f : Term → Except Exception Term}
    (h : (e >>= f) = .ok (.atom "true")) : ∃ v, e = .ok v ∧ f v = .ok (.atom "true") := by
  cases e with
  | error x => simp [bind, Except.bind] at h
  | ok v => exact ⟨v, rfl, by simpa [bind, Except.bind] using h⟩

theorem list_literal_spec (hE : NestedOk E depth) {lit lower : Term}
    (h : «list_literal?/3» lit lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ ListLit E lit := by
  unfold «list_literal?/3» at h
  split at h
  · rename_i key list last
    obtain ⟨v, hA, hrest⟩ := bind_true h
    obtain ⟨hm, hlast⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp hrest
    have hv : v = .atom "true" := by
      split at hm
      · simp at hm
      · rfl
      · simp at hm
    subst hv
    simp only at hm
    obtain ⟨⟨hint, hgt⟩, hnt⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp hA |>.imp_left
      (Lynx.Except.andAlso_eq_true _ _ _).mp
    cases key <;> simp [Erlang.erlang.«is_integer/1»] at hint
    rename_i k
    simp [Erlang.erlang.«>/2»] at hgt
    refine ⟨⟨k, list, last, rfl⟩, Lynx.Term.compare_lt_of_gt hgt, ?_, k, list, last, rfl, hE _ hm, hE _ hlast⟩
    rintro ⟨_, e⟩
    simp at e
    obtain ⟨-, rfl, rfl⟩ := e
    simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2»] at hnt
  · simp [Term.true] at h

theorem ordered_spec (hE : NestedOk E depth) : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
    «ordered_bdd?/3» b lower depth = .ok Term.true → Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ ListLit E t) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «ordered_bdd?/3» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := list_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := list_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ ListLit E t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ ListLit E t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

/-- List types are the top list literal or ordered BDDs of other list literals. -/
abbrev ListField (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "term", .atom "term"]) ∨ Bdd ListOk w

/-- List types whose literals have element and tail types `E`. -/
abbrev LField (E : Term → Prop) (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "term", .atom "term"]) ∨ Bdd (ListLit E) w

theorem LField.list {w : Term} (h : LField E w) : ListField w := by
  rcases h with top | b
  · exact Or.inl top
  · exact Or.inr (b.mono fun _ h => h.1)

theorem list_bdd_spec (hE : NestedOk E depth) {w : Term} (h : «list_bdd?/2» w depth = .ok Term.true) :
    LField E w := by
  unfold «list_bdd?/2» at h
  split at h
  · rename_i key
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ((ordered_spec hE _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)

/-- Function types map arities to BDDs. -/
def ArityBdds (w : Term) : Prop :=
  ∀ t R, w = .tuple #[t, .map R] → ∀ q v, mapLookup R q = some v → Bdd (fun _ => True) v

theorem arity_bdds_spec (es : List (Term × Term))
    (valid : «arity_bdds?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
    ∀ p ∈ es, Bdd (fun _ => True) p.2 := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons, Term.list, «arity_bdds?/1», Term.true, Lynx.Except.andAlso_eq_true] at valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact (any_bdd_spec _ _ _ (Nat.le_refl _) valid.1).mono fun _ _ => trivial
    · exact ih valid.2 p member

theorem arity_bdds_map (R : List (Term × Term))
    (valid : «arity_bdds?/1» (Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
    ∀ q v, mapLookup R q = some v → Bdd (fun _ => True) v := by
  intro q v lookup
  obtain ⟨p, mp, -, rfl⟩ := lookup_found _ q v (by rw [mapLookup_mapEntries]; exact lookup)
  exact arity_bdds_spec _ valid p mp

/-- Function literals `{key, args, return}` with `n` arguments, whose argument and return types are `E`. -/
def FunLit (E : Term → Prop) (n : Int) (t : Term) : Prop :=
  ∃ (k : Int) (args : List Term) (ret : Term), t = .tuple #[.integer k, Term.list args, ret] ∧
    (args.length : Int) = n ∧ (∀ a ∈ args, E a) ∧ E ret

/-- The literals of the BDD of arity `q`. -/
def FunArity (E : Term → Prop) (q t : Term) : Prop := ∃ n : Int, q = .integer n ∧ FunLit E n t

/-- Nested function types: unions or negations of maps from arities to BDDs of literals of that arity. -/
def FField (E : Term → Prop) (w : Term) : Prop :=
  ∃ (pos : Bool) (R : List (Term × Term)), w = .tuple #[.atom (if pos then "union" else "negation"), .map R] ∧
    ∀ q v, mapLookup R q = some v → Bdd (FunArity E q) v

theorem fun_literal_spec (hE : NestedOk E depth) {lit lower : Term} {n : Int}
    (h : «fun_literal?/4» lit (.integer n) lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ FunLit E n lit := by
  unfold «fun_literal?/4» at h
  split at h
  · rename_i key args ret
    obtain ⟨h₁, hret⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
    obtain ⟨h₂, hlen⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h₁
    obtain ⟨h₃, hargs⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h₂
    obtain ⟨hint, hgt⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h₃
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at hint
    rename_i k
    obtain ⟨l, rfl, hl⟩ := elements_spec hE hargs
    simp [Erlang.erlang.«>/2»] at hgt
    simp [length_list, Erlang.erlang.«==/2», Term.true] at hlen
    exact ⟨⟨k, _, _, rfl⟩, Lynx.Term.compare_lt_of_gt hgt, k, l, ret, rfl, hlen, hl, hE _ hret⟩
  · simp [Term.true] at h

theorem ordered_fun_spec (hE : NestedOk E depth) (n : Int) : ∀ (s : Nat) (b lower : Term), sizeOf b ≤ s →
    «fun_bdd?/4» b (.integer n) lower depth = .ok Term.true →
      Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ FunLit E n t) b := by
  intro s
  induction s with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ s ih =>
    intro b lower size h
    unfold «fun_bdd?/4» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := fun_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := fun_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ FunLit E n t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ FunLit E n t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

theorem fun_arities_spec (hE : NestedOk E depth) (es : List (Term × Term))
    (valid : «fun_arities?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ p ∈ es, Bdd (FunArity E p.1) p.2 := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons, Term.list] at valid
    unfold «fun_arities?/2» at valid
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at valid
    obtain ⟨⟨int, bdd⟩, tail⟩ := valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨q, v⟩ := p
      cases q <;> simp [Erlang.erlang.«is_integer/1»] at int
      rename_i n
      exact (ordered_fun_spec hE n _ v _ (Nat.le_refl _) bdd).mono fun t h => ⟨n, rfl, h.2⟩
    · exact ih tail p member

theorem fun_arities_map (hE : NestedOk E depth) (R : List (Term × Term))
    (valid : «fun_arities?/2» (Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ q v, mapLookup R q = some v → Bdd (FunArity E q) v := by
  intro q v lookup
  obtain ⟨p, mp, qp, rfl⟩ := lookup_found _ q v (by rw [mapLookup_mapEntries]; exact lookup)
  exact (fun_arities_spec hE _ valid p mp).mono fun t ⟨n, e, lit⟩ => ⟨n, by rw [e] at qp; exact (compareExact_eq_integer _ _).mp qp, lit⟩

theorem FField.funField {w : Term} (h : FField E w) : FunField w ∧ ArityBdds w := by
  obtain ⟨pos, R, rfl, bdds⟩ := h
  refine ⟨⟨pos, R, rfl⟩, fun t R' e q v lookup => ?_⟩
  simp at e
  obtain ⟨-, rfl⟩ := e
  exact (bdds q v lookup).mono fun _ _ => trivial

/-- What `negatable?/2` checks of a type, whose tuple elements and map fields are `E`. -/
structure Negatable (E : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome →
    q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨ q = .atom "list" ∨ q = .atom "tuple" ∨
      q = .atom "map"
  bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
  atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
  atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []
  funs : ∀ w, mapLookup X (.atom "fun") = some w → FunField w
  arities : ∀ w, mapLookup X (.atom "fun") = some w → ArityBdds w
  lists : ∀ w, mapLookup X (.atom "list") = some w → LField E w
  tuples : ∀ w, mapLookup X (.atom "tuple") = some w → TupleField E w
  maps : ∀ w, mapLookup X (.atom "map") = some w → MapField E w

theorem Negatable.static {X : List (Term × Term)} (valid : Negatable E X) :
    mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w =>
    rcases valid.keys _ (by rw [h]; rfl) with bad | bad | bad | bad | bad | bad <;> simp only [Term.atom.injEq] at bad <;>
      exact absurd bad (by decide)

/-- What `nested?/2` checks of the fields of a nested type, whose tuple elements and map fields are `E`. -/
structure NestMap (E : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
    q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map"
  bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
  atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
  atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []
  funs : ∀ w, mapLookup X (.atom "fun") = some w → FField E w
  lists : ∀ w, mapLookup X (.atom "list") = some w → LField E w
  tuples : ∀ w, mapLookup X (.atom "tuple") = some w → TupleField E w
  maps : ∀ w, mapLookup X (.atom "map") = some w → MapField E w

def NestOf (E : Term → Prop) (t : Term) : Prop := t = .atom "term" ∨ ∃ X, t = .map X ∧ NestMap E X

/-- The generator of the recursive node of the laws. -/
def gen : Term := .function "Elixir.STTDescrProofsTest" "tuple_list" 1 #[]

/-- Recursive nodes of the reference `r`: their state maps `t` to the reference and the generator. -/
def NodeAt (r : List Nat) (e : Term) : Prop :=
  ∃ S, e = .tuple #[.reference r, .map S, gen] ∧ getMapKeys [.atom "t"] (.map S) = [.tuple #[.reference r, gen]]

theorem recursive_node_shape {e : Term} (h : «recursive_node?/1» e = .ok Term.true) : ∃ r, NodeAt r e := by
  unfold «recursive_node?/1» at h
  simp only at h
  split at h
  · rename_i _ r M g₄
    split at h
    · rename_i _ x g' hk
      simp only [Lynx.Except.guard, Erlang.erlang.«=:=/2»] at h
      by_cases h₁ : Term.compareExact (Term.fuel x (.reference r)) x (.reference r) = .eq <;> by_cases h₂ : Term.compareExact (Term.fuel g₄ g') g₄ g' = .eq <;>
        simp [h₁, h₂, Erlang.erlang.«and/2», Term.true] at h
      subst h
      rw [compareExact_eq_closed_function] at h₂
      rw [compareExact_eq_reference] at h₁
      subst h₁ h₂
      cases M with
      | map S => exact ⟨r, S, rfl, hk⟩
      | _ => simp [getMapKeys] at hk
    · simp at h
  · simp at h

/-- The reference of a node. -/
def refOf : Term → List Nat
  | .tuple ⟨[.reference r, _, _]⟩ => r
  | _ => []

/-- The recursive nodes the laws accept: those equal to their node `t`. -/
def IsT (t e : Term) : Prop :=
  compareExact (fuel e t) e t = .eq ∧ «recursive_node?/1» e = .ok Term.true

/-- Accepted nodes hash as `t` does in expansion literals. -/
theorem IsT.hash {t e : Term} (h : IsT t e) :
    Erlang.erlang.«phash2/1» (Term.list [.atom "term", e]) = Erlang.erlang.«phash2/1» (Term.list [.atom "term", t]) :=
  Erlang.erlang.phash2_congr (by simp [Term.list, compareExact_cons, h.1])

theorem IsT.node {t e : Term} (h : IsT t e) : NodeAt (refOf t) e := by
  obtain ⟨r, S, rfl, hk⟩ := recursive_node_shape h.2
  have same := h.1
  rw [compareExact_step] at same
  cases t <;> simp [Compare.compareStep] at same
  rename_i ts
  obtain ⟨l⟩ := ts
  match l, same with
  | [a, b, c], same =>
    simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at same
    obtain ⟨ha, -⟩ := same
    subst ha
    exact ⟨S, rfl, hk⟩
  | [], same => simp [List.compareLex] at same
  | [_], same => simp [List.compareLex] at same
  | [_, _], same => simp [List.compareLex] at same
  | _ :: _ :: _ :: _ :: _, same => simp [List.compareLex] at same

theorem isT_exact {t e e' : Term} (h₁ : IsT t e) (h₂ : IsT t e') : compareExact (fuel e e') e e' = .eq := by
  have b : compareExact (fuel t e') t e' = .eq := by
    rw [Lynx.Term.compareExact_swap, h₂.1]; rfl
  exact Lynx.Term.compareExact_eq_trans h₁.1 b

/-- Optimized laws hold no recursive node. -/
theorem not_isT_nil {e : Term} : ¬IsT (.atom "nil") e := fun ⟨same, h⟩ => by
  obtain ⟨r, S, rfl, -⟩ := recursive_node_shape h
  simp at same

/-- Nested types of a depth: flat element types at depth 0, and the recursive node `t` at every depth. -/
def Nest (t : Term) : Nat → Term → Prop
  | 0 => fun e => ElemTerm e ∨ IsT t e
  | d + 1 => fun e => NestOf (Nest t d) e ∨ IsT t e

theorem NestMap.negatable {X : List (Term × Term)} (v : NestMap E X) : Negatable E X := by
  exact ⟨v.keys, v.bitmap, v.atom, v.atomUnion, fun w h => (v.funs w h).funField.1,
    fun w h => (v.funs w h).funField.2, v.lists, v.tuples, v.maps⟩

/-- Each field `nested_field?/2` accepts. -/
theorem nested_field_spec (hE : NestedOk E depth) (k w : Term)
    (h : «nested_field?/2» (.tuple #[k, w]) depth = .ok Term.true) :
    (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
      (k = .atom "fun" ∧ FField E w) ∨ (k = .atom "list" ∧ LField E w) ∨ (k = .atom "tuple" ∧ TupleField E w) ∨
      (k = .atom "map" ∧ MapField E w) := by
  unfold «nested_field?/2» at h
  simp only at h
  split at h
  · rename_i tag arities shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    simp only [Lynx.Except.guard, Lynx.Except.tryWith] at h
    split at h
    · rename_i member
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      cases arities <;> simp [Erlang.erlang.«is_map/1», Lynx.Except.andAlso] at h
      rename_i R
      have bdds := fun_arities_map hE R (by simpa [Erlang.maps.«to_list/1»] using h)
      by_cases u : tag = .atom "union"
      · exact ⟨Bool.true, R, by simp [u], bdds⟩
      · by_cases n : tag = .atom "negation"
        · exact ⟨Bool.false, R, by simp [n], bdds⟩
        · simp [isMember, u, n] at member
    · exfalso
      split at h
      · simp_all
      · simp_all
      · simp_all
      · rcases valid_fields [(.atom "fun", .tuple #[tag, arities])] (by simpa [Term.list] using h) _
          List.mem_cons_self with h | h <;> simp at h
  split at h
  · rename_i bdd shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, list_bdd_spec hE h⟩)))
  · rename_i bdd shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tuple_bdd_spec hE h⟩))))
  · rename_i bdd shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, map_bdd_spec hE h⟩))))
  · rcases valid_fields [(k, w)] (by simpa [Term.list] using h) (k, w) (by simp) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem nested_fields_spec (hE : NestedOk E depth) (es : List (Term × Term))
    (valid : «nested_fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) ∨
      (p.1 = .atom "fun" ∧ FField E p.2) ∨ (p.1 = .atom "list" ∧ LField E p.2) ∨
      (p.1 = .atom "tuple" ∧ TupleField E p.2) ∨ (p.1 = .atom "map" ∧ MapField E p.2) := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    unfold «nested_fields?/2» at valid
    simp only [List.map_cons, Term.list, Term.true, Lynx.Except.andAlso_eq_true] at valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact nested_field_spec hE k w valid.1
    · exact ih valid.2 p member

theorem nest_map (hE : NestedOk E depth) (X : List (Term × Term))
    (valid : «nested_fields?/2» (Term.list ((mapEntries X).map fun e => .tuple #[e.1, e.2])) depth =
      .ok Term.true) : NestMap E X := by
  have each := nested_fields_spec hE (mapEntries X) valid
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  have key : ∀ {q : Term} {name : String}, compareExact (fuel q (.atom name)) q (.atom name) = .eq → q = .atom name :=
    fun e => (compareExact_eq_atom _ _).mp e
  refine ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?atomU,
    fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_⟩
  case atomU =>
    obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f.2 S e | (simp at qp)
  · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
    obtain ⟨p, mp, qp, -⟩ := entry q w lookup
    rcases each p mp with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> rw [k] at qp <;> simp [key qp]
  all_goals
    obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f | exact f.1 | exact f.2 | (simp at qp)

/-- The node clause of `nested?/2` accepts only the node of the depth. -/
theorem nested_node {e t : Term} {d : Nat} (h : «nested?/2» e (.tuple #[.integer d, t]) = .ok Term.true)
    (shape : ∃ a b c, e = .tuple #[a, b, c]) : IsT t e := by
  obtain ⟨a, b, c, rfl⟩ := shape
  unfold «nested?/2» at h
  simp only [Lynx.Except.guard, Erlang.erlang.«=:=/2»] at h
  by_cases hc : Term.compareExact (Term.fuel (Term.tuple #[a, b, c]) t) (Term.tuple #[a, b, c]) t = .eq
  · simp only [hc, ite_true] at h
    exact ⟨hc, h⟩
  · simp [hc, Term.true, Term.false] at h
    split at h
    · simp [«valid?/1»] at h
    · rename_i heq _; cases heq
    · simp at h

/-- `nested?/2` accepts nested types of its depth. -/
theorem nested_spec (t : Term) : ∀ (d : Nat), NestedOk (Nest t d) (.tuple #[.integer d, t])
  | d, e, h => by
    by_cases shape : ∃ a b c, e = .tuple #[a, b, c]
    · cases d <;> exact Or.inr (nested_node h shape)
    have notNode : ∀ a b c, e ≠ .tuple #[a, b, c] := fun a b c he => shape ⟨a, b, c, he⟩
    cases d with
    | zero =>
      cases e
      case atom name =>
        by_cases top : name = "term"
        · subst top; exact Or.inl (Or.inl rfl)
        · simp [«nested?/2», top, «valid?/1»] at h
      case map X =>
        unfold «nested?/2» at h
        simp at h
        obtain ⟨X', e, valid⟩ := valid_map _ h
        exact Or.inl (Or.inr ⟨X', e, valid⟩)
      case tuple ts =>
        obtain ⟨l⟩ := ts
        match l, notNode with
        | [a, b, c], notNode => exact absurd rfl (notNode a b c)
        | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ =>
          unfold «nested?/2» at h; simp [«valid?/1»] at h
      all_goals (unfold «nested?/2» at h; simp [«valid?/1»] at h)
    | succ d =>
      have notMap : ∀ {e : Term}, (∀ X, e ≠ .map X) → (∀ a b c, e ≠ .tuple #[a, b, c]) → e ≠ .atom "term" →
          «nested?/2» e (.tuple #[.integer ↑(d + 1), t]) ≠ .ok Term.true := by
        intro e nm nn nt h
        unfold «nested?/2» at h
        split at h
        · exact nt rfl
        simp only [Lynx.Except.guard] at h
        split at h
        · rename_i heq _; cases heq; exact nn _ _ _ rfl
        split at h
        · first | (simp_all; omega) | simp_all
        · exact nm _ rfl
        · simp [Term.true] at h
      cases e
      case atom name =>
        by_cases top : name = "term"
        · subst top; exact Or.inl (Or.inl rfl)
        · exact absurd h (notMap (fun _ h => by cases h) (fun _ _ _ h => by cases h) (by simpa using top))
      case map X =>
        unfold «nested?/2» at h
        simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at h
        have sub : Erlang.erlang.«-/2» (.integer ↑(d + 1)) (.integer 1) = .ok (.integer ↑d) := by
          rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
        rw [sub, Lynx.Except.ok_bind] at h
        exact Or.inl (Or.inr ⟨X, rfl, nest_map (nested_spec t d) X h⟩)
      case tuple ts =>
        obtain ⟨l⟩ := ts
        exact absurd h (notMap (fun _ h => by cases h) notNode (fun h => by cases h))
      all_goals exact absurd h (notMap (fun _ h => by cases h) notNode (fun h => by cases h))

/-- Each field `negatable_fields?/2` accepts. -/
theorem negatable_fields_spec (hE : NestedOk E depth) (es : List (Term × Term))
    (valid : «negatable_fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) ∨
      (p.1 = .atom "fun" ∧ FunField p.2 ∧ ArityBdds p.2) ∨
      (p.1 = .atom "list" ∧ LField E p.2) ∨ (p.1 = .atom "tuple" ∧ TupleField E p.2) ∨
      (p.1 = .atom "map" ∧ MapField E p.2) := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    simp only [List.map_cons, Term.list, «negatable_fields?/2», Term.true, Lynx.Except.andAlso_eq_true] at valid
    have head : (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
        (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
        (k = .atom "fun" ∧ FunField w ∧ ArityBdds w) ∨
        (k = .atom "list" ∧ LField E w) ∨ (k = .atom "tuple" ∧ TupleField E w) ∨ (k = .atom "map" ∧ MapField E w) := by
      have field := valid.1
      have fallback : «nested_field?/2» (.tuple #[k, w]) depth = .ok Term.true →
          (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
            (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
            (k = .atom "fun" ∧ FunField w ∧ ArityBdds w) ∨ (k = .atom "list" ∧ LField E w) ∨
            (k = .atom "tuple" ∧ TupleField E w) ∨ (k = .atom "map" ∧ MapField E w) := fun h => by
        rcases nested_field_spec hE k w h with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.funField⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      unfold «negatable_field?/2» at field
      simp only at field
      split at field
      · rename_i tag arities shape
        simp at shape
        obtain ⟨rfl, rfl⟩ := shape
        simp only [Lynx.Except.guard, Lynx.Except.tryWith] at field
        split at field
        · rename_i member
          refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
          cases arities <;> simp [Erlang.erlang.«is_map/1», Lynx.Except.andAlso] at field
          rename_i R
          have bdds : ArityBdds (.tuple #[tag, .map R]) := by
            intro t R' e
            simp at e
            obtain ⟨-, rfl⟩ := e
            exact arity_bdds_map R (by simpa [Erlang.maps.«to_list/1»] using field)
          by_cases u : tag = .atom "union"
          · exact ⟨⟨Bool.true, R, by simp [u]⟩, bdds⟩
          · by_cases n : tag = .atom "negation"
            · exact ⟨⟨Bool.false, R, by simp [n]⟩, bdds⟩
            · simp [isMember, u, n] at member
        · exact fallback (by simpa using field)
      · exact fallback field
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih valid.2 p member

theorem negatable_map (t : Term) (depth : Nat) (descr : Term)
    (valid : «negatable?/2» descr (.tuple #[.integer depth, t]) = .ok Term.true) :
    descr = .atom "term" ∨ ∃ X, descr = .map X ∧ Negatable (Nest t depth) X := by
  cases descr
  case atom name =>
    by_cases top : name = "term"
    · exact Or.inl (by rw [top])
    · simp [«negatable?/2», top] at valid
  all_goals try (simp [«negatable?/2»] at valid; done)
  rename_i X
  refine Or.inr ?_
  simp [«negatable?/2», Term.true] at valid
  simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at valid
  have each := negatable_fields_spec (nested_spec t depth) (mapEntries X) valid
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  have key : ∀ {q : Term} {name : String}, compareExact (fuel q (.atom name)) q (.atom name) = .eq → q = .atom name :=
    fun e => (compareExact_eq_atom _ _).mp e
  refine ⟨X, rfl, ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?atomU,
    fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_⟩⟩
  case atomU =>
    obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f.2 S e | (simp at qp)
  · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
    obtain ⟨p, mp, qp, -⟩ := entry q w lookup
    rcases each p mp with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> rw [k] at qp <;> simp [key qp]
  all_goals
    obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f | exact f.1 | exact f.2 | (simp at qp)

/-- A list BDD of other literals is not a top literal itself. -/
theorem not_top_leaf {x : Term} (wx : Bdd ListOk x) : ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"] := by
  intro k e
  subst e
  rcases wx.shape with h | h | ⟨k', x', y', h⟩ | ⟨h', lit, c, u, d, h⟩ <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact Bdd.leaf_iff.mp wx ⟨_, rfl⟩

/-- The negation of a list type. -/
theorem list_negation (k : Int) (x : Term) (field : ListField x) :
    (Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer k, .atom "term", .atom "term"]) x =
      .ok (.atom "bdd_bot")) ∨
    (Bdd ListOk x ∧ ∃ y, Elixir.Module.Types.Descr.«list_difference/2»
        (.tuple #[.integer k, .atom "term", .atom "term"]) x = .ok y ∧
      Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x) := by
  rcases field with ⟨k', rfl⟩ | wx
  · left; simp [Elixir.Module.Types.Descr.«list_difference/2»]
  · right
    obtain ⟨y, run, keep, sem⟩ := neg_ok wx
    refine ⟨wx, y, ?_, keep _ wx, sem⟩
    have nt := not_top_leaf wx
    unfold Elixir.Module.Types.Descr.«list_difference/2»
    split
    · exact (nt _ rfl).elim
    · exact run
    · next h₁ h₂ => first | exact (h₁ _ rfl).elim | exact (h₁ _ _ rfl).elim | exact absurd rfl (h₁ _) | simp_all

/-- The intersection of list types of other literals. -/
theorem list_intersection_bdd {x y : Term} (wx : Bdd ListOk x) (wy : Bdd ListOk y) :
    Elixir.Module.Types.Descr.«list_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_intersection/2»
  split
  · exact (not_top_leaf wx _ rfl).elim
  · exact (not_top_leaf wy _ rfl).elim
  · rfl

/-- What remains of a list or tuple type and its negation. -/
def Gone (K : Nat) (q w : Term) : Prop :=
  (q = .atom "list" ∧ Bdd ListOk w ∧ Unsat w) ∨ (q = .atom "tuple" ∧ EmptyTuple K w) ∨
    (q = .atom "map" ∧ EmptyMap K w)

theorem Gone.congr {K : Nat} {q k w : Term} (e : compareExact (fuel q k) q k = .eq) (gone : Gone K k w) : Gone K q w := by
  rcases gone with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨(compareExact_eq_atom _ _).mp e, h⟩
  · exact Or.inr (Or.inl ⟨(compareExact_eq_atom _ _).mp e, h⟩)
  · exact Or.inr (Or.inr ⟨(compareExact_eq_atom _ _).mp e, h⟩)

/-- Types holding only what remains of list and tuple types and their negations are empty. -/
theorem empty_gone {K m : Nat} (hm : K + 2 ≤ m) (I : List (Term × Term))
    (only : ∀ q w, mapLookup I q = some w → Gone K q w) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) (.map I) = .ok Term.true := by
  have absent : ∀ name, name ≠ "list" → name ≠ "tuple" → name ≠ "map" →
      mapLookup I (.atom name) = Option.none := by
    intro name nl nt nm
    cases h : mapLookup I (.atom name) with
    | none => rfl
    | some w => rcases only _ w h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> simp at e <;> simp_all
  have none : ∀ name, name ≠ "list" → name ≠ "tuple" → name ≠ "map" →
      I.any (fun e => compareExact (fuel (.atom name) e.1) (.atom name) e.1 == .eq) = Bool.false := by
    intro name nl nt nm
    have := absent name nl nt nm
    rw [Bool.eq_false_iff]
    intro hany
    obtain ⟨e, me, he⟩ := List.any_eq_true.mp hany
    have := (mapLookup_isSome I (.atom name)).mpr ⟨e, me, by simpa using he⟩
    simp_all
  have anyKey : ∀ name, (I.any fun e => compareExact (fuel (.atom name) e.1) (.atom name) e.1 == .eq) =
      (mapLookup I (.atom name)).isSome := by
    intro name
    rw [Bool.eq_iff_iff, mapLookup_isSome]
    simp
  simp only [Elixir.Module.Types.Descr.«empty?/1»]
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [getMapKeys_single, absent "dynamic" (by decide) (by decide) (by decide), Erlang.erlang.«==/2»,
    Erlang.erlang.«is_map_key/2», none "atom" (by decide) (by decide) (by decide),
    none "bitmap" (by decide) (by decide) (by decide), none "fun" (by decide) (by decide) (by decide),
    Term.true, Term.false]
  by_cases empty : I = []
  · simp [empty]
  simp only [empty, ite_false, anyKey]
  simp [Erlang.erlang.«not/1»]
  have tupleOk : ∀ r, mapLookup I (.atom "tuple") = some r →
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) r (.map []) = .ok (.atom "true") := fun r h => by
    rcases only _ r h with ⟨e, -⟩ | ⟨-, gone⟩ | ⟨e, -⟩
    · simp at e
    · exact gone m [] (by omega)
    · simp at e
  have mapOk : ∀ r, mapLookup I (.atom "map") = some r →
      Elixir.Module.Types.Descr.«map_empty?/2» (D m) r (.map []) = .ok (.atom "true") := fun r h => by
    rcases only _ r h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, gone⟩
    · simp at e
    · simp at e
    · exact gone m [] hm
  have listOk : ∀ r, mapLookup I (.atom "list") = some r →
      Elixir.Module.Types.Descr.«list_empty?/2» (D m) r (.map []) = .ok (.atom "true") := fun r h => by
    rcases only _ r h with ⟨-, wr, unsat⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact list_empty_unsat _ wr unsat []
    · simp at e
    · simp at e
  cases ht : mapLookup I (.atom "tuple") <;> cases hm : mapLookup I (.atom "map") <;>
    cases hl : mapLookup I (.atom "list") <;>
    first
      | (simp [tupleOk _ ht, mapOk _ hm, listOk _ hl]; done)
      | (simp [tupleOk _ ht, mapOk _ hm]; done)
      | (simp [tupleOk _ ht, listOk _ hl]; done)
      | (simp [mapOk _ hm, listOk _ hl]; done)
      | (simp [tupleOk _ ht]; done)
      | (simp [mapOk _ hm]; done)
      | (simp [listOk _ hl]; done)
      | (simp; done)
