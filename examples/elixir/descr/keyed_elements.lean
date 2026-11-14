namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Nested types of the specification whose literals are keyed are element types of their level. -/

/-- All literals of a BDD satisfy `Q`. -/
def AllLits (Q : Term → Prop) : Term → Prop
  | .tuple ⟨[_, lit, c, u, d]⟩ => Q lit ∧ AllLits Q c ∧ AllLits Q u ∧ AllLits Q d
  | .tuple ⟨[k, x, y]⟩ => Q (.tuple #[k, x, y])
  | _ => True

theorem bdd_allLits {ok Q : Term → Prop} {w : Term} (wb : Bdd ok w) (all : AllLits Q w) :
    Bdd (fun t => ok t ∧ Q t) w := by
  revert all
  refine Bdd.induction (P := fun ok w => AllLits Q w → Bdd (fun t => ok t ∧ Q t) w) ?_ ?_ ?_ ?_ ok w wb
  · intro _ _; exact Bdd.top
  · intro _ _; exact Bdd.bot
  · intro ok k x y okl all
    exact Bdd.leaf_iff.mpr ⟨okl, by simpa [AllLits] using all⟩
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id all
    simp only [AllLits] at all
    obtain ⟨ql, ac, au, ad⟩ := all
    have mono : ∀ {x}, Bdd (fun t => Above ok lit t ∧ Q t) x → Bdd (Above (fun t => ok t ∧ Q t) lit) x :=
      fun hx => hx.mono fun t ⟨⟨o, l⟩, q⟩ => ⟨⟨o, q⟩, l⟩
    exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, ql⟩, mono (ic ac), mono (iu au), mono (id ad)⟩

/-- Keyed tuple literals whose elements satisfy `P`. -/
def TQ (P : Term → Prop) (t : Term) : Prop :=
  KeyOk t ∧ ∀ (k : Int) (tag : String) (l : List Term), t = .tuple #[.integer k, .atom tag, Term.list l] → ∀ e ∈ l, P e

/-- Keyed map literals with atom keys in order whose field types satisfy `P`. -/
def MQ (P : Term → Prop) (t : Term) : Prop :=
  KeyOk t ∧ ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    l.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) ∧
    (∀ e ∈ l, (∃ s : String, e.1 = .atom s) ∧ ∀ u o, e.2 = .tuple #[u, boolAtom o] → P u) ∧
    ∀ dl, tag = fieldsTerm dl → DomsV P dl

/-- List literals whose element and tail types satisfy `P`. -/
def LQ (P : Term → Prop) (t : Term) : Prop := ∀ (k : Int) (a b : Term), t = .tuple #[.integer k, a, b] → P a ∧ P b

/-- Function literals whose argument and return types satisfy `P`. -/
def FLQ (P : Term → Prop) (t : Term) : Prop :=
  ∀ (k : Term) (args : List Term) (ret : Term), t = .tuple #[k, Term.list args, ret] → (∀ a ∈ args, P a) ∧ P ret

/-- Function types whose arities are natural numbers, at least one in unions, with literals of types `P`. -/
def FunK (P : Term → Prop) (w : Term) : Prop :=
  ∃ (tag : Term) (R : List (Term × Term)), w = .tuple #[tag, .map R] ∧ (tag = .atom "union" → R ≠ []) ∧
    NatKeys R ∧ ∀ q v, mapLookup R q = some v → AllLits (FLQ P) v

/-- The literal invariants the optimized operations expect of the fields of a type whose literals hold types `P`:
keyed tuple and map literals, map literals with atom keys in order, and, for element types, function types of
natural arities, at least one in unions. -/
structure KeyedF (P : Term → Prop) (el : Bool) (X : List (Term × Term)) : Prop where
  funs : el = Bool.true → ∀ w, mapLookup X (.atom "fun") = some w → FunK P w
  tuples : ∀ w, mapLookup X (.atom "tuple") = some w → AllLits (TQ P) w
  maps : ∀ w, mapLookup X (.atom "map") = some w → AllLits (MQ P) w
  lists : ∀ w, mapLookup X (.atom "list") = some w → AllLits (LQ P) w

/-- Keyed element types at each nesting depth. -/
def Keyed : Nat → Term → Prop
  | 0, _ => True
  | d + 1, e => e = .atom "term" ∨ (∃ a b c, e = .tuple #[a, b, c]) ∨ ∃ X, e = .map X ∧ KeyedF (Keyed d) Bool.true X

section
variable {E P E' : Term → Prop}

theorem tfield_of (conv : ∀ e, E e → P e → E' e) {w : Term} (tf : TupleField E w)
    (keys : AllLits (fun t => KeyOk t ∧ ∀ (k : Int) (tag : String) (l : List Term),
      t = .tuple #[.integer k, .atom tag, Term.list l] → ∀ e ∈ l, P e) w) : TField E' w := by
  rcases tf with top | b
  · exact Or.inl top
  refine Or.inr ((bdd_allLits b keys).mono fun t ⟨⟨⟨k, tag, l, e, g, els⟩, nt⟩, key, pe⟩ => ?_)
  subst e
  exact ⟨⟨⟨k, tag, l, rfl, g, fun x mx => conv x (els x mx) (pe k tag l rfl x mx)⟩, nt⟩, key⟩

/-- Nested function types with natural arities, at least one in unions, and literals of types `P`, are function
types of element types. -/
theorem funA_of (conv : ∀ e, E e → P e → E' e) {w : Term} (ff : FField E w) (fk : FunK P w) : FunA E' w := by
  obtain ⟨pos, R, rfl, bR⟩ := ff
  obtain ⟨tag, R', e, ne, nk, lits⟩ := fk
  have e₀ := congrArg (fun a : Term => match a with | .tuple ⟨[x, _]⟩ => x | _ => .nil) e
  have e₁ := congrArg (fun a : Term => match a with | .tuple ⟨[_, y]⟩ => y | _ => .nil) e
  simp only [Term.map.injEq] at e₀ e₁
  subst e₀ e₁
  refine ⟨pos, R, rfl, fun hp => ne (by subst hp; rfl), fun q v hv => ?_, nk⟩
  refine (bdd_allLits (bR q v hv) (lits q v hv)).mono fun t ⟨⟨n, hq, k, args, ret, et, len, ha, hr⟩, fl⟩ => ?_
  obtain ⟨pa, pr⟩ := fl _ _ _ et
  exact ⟨n.toNat, by rw [hq]; congr; omega, k, args, ret, et, by omega, fun a ma => conv a (ha a ma) (pa a ma),
    conv ret hr pr⟩

theorem lf_of (conv : ∀ e, E e → P e → E' e) (hterm : E' (.atom "term")) {w : Term} (lf : LField E w)
    (keys : AllLits (fun t => ∀ (k : Int) (a b : Term), t = .tuple #[.integer k, a, b] → P a ∧ P b) w) :
    LF E' w := by
  rcases lf with ⟨k, rfl⟩ | b
  · exact Bdd.leaf_iff.mpr ⟨k, _, _, rfl, hterm, hterm⟩
  refine (bdd_allLits b keys).mono fun t ⟨⟨_, k, a, c, e, ha, hc⟩, pe⟩ => ?_
  subst e
  obtain ⟨pa, pc⟩ := pe k a c rfl
  exact ⟨k, a, c, rfl, conv a ha pa, conv c hc pc⟩

theorem mfield_of (conv : ∀ e, E e → P e → E' e) {w : Term} (mf : MapField E w) (keys : AllLits (MQ P) w) :
    MField E' w := by
  rcases mf with top | b
  · exact Or.inl top
  refine Or.inr ((bdd_allLits b keys).mono fun t ⟨⟨⟨k, tag, l, e, g, fv⟩, nt⟩, key, pe⟩ => ?_)
  subst e
  obtain ⟨sorted, each, doms⟩ := pe k tag l rfl
  refine ⟨⟨k, tag, l, rfl, ?_, fun x mx => ⟨(each x mx).1, ?_⟩, sorted⟩, nt, key⟩
  · rcases g with rfl | rfl | ⟨dl, rfl, hdl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨dk, dp⟩ := doms dl rfl
      exact Or.inr (Or.inr ⟨dl, rfl, fun e me => ⟨(dk e me).1, conv _ (hdl e me) (dk e me).2⟩, dp⟩)
  · obtain ⟨u, o, eu, hu⟩ := fv x mx
    exact ⟨u, o, eu, conv u hu ((each x mx).2 u o eu)⟩

end

/-- Flat types are types of the bottom level. -/
theorem lelem_deg0 {t e : Term} (h : LElem e) :
    DEG FunTop (OField (PureLit t)) (FieldOk "list") (FieldOk "map") e := by
  rcases h with rfl | ⟨M, rfl, bM⟩
  · exact Or.inl rfl
  refine Or.inr ⟨M, rfl, fun q hq => ?_, fun name w hw => ?_⟩
  · rcases bM.keys q hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
  · rcases bM.keys (.atom name) (by rw [hw]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨rfl, bM.bitmap w hw⟩
    · exact Or.inr (Or.inl ⟨rfl, bM.atom w hw |>.1, by
        obtain ⟨q, hq⟩ := (bM.atom w hw).2; exact ⟨q, by simpa [amem, hw] using hq⟩⟩)
    · have := bM.top "fun" w (by decide) (by decide) hw
      simp [topValue] at this
      exact Or.inr (Or.inr (Or.inl ⟨rfl, this.symm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨by decide, by decide,
        bM.top "list" w (by decide) (by decide) hw⟩)⟩)))
    · have := bM.top "tuple" w (by decide) (by decide) hw
      simp [topValue] at this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, this.symm⟩⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨by decide, by decide,
        bM.top "map" w (by decide) (by decide) hw⟩)⟩))))

/-- Keyed nested types of the specification are element types of their level. -/
theorem nest_level (t : Term) : ∀ (d : Nat) (e : Term), Nest t d e → Keyed d e → (level t d).E e
  | 0, _, h, _ => by
    rcases h with h | h
    · exact Or.inl (lelem_deg0 (elem_lelem h))
    · exact Or.inr h
  | d + 1, _, h, k => by
    rcases h with h | h
    rotate_left
    · exact Or.inr (by rw [level_nd]; exact h)
    rcases h with rfl | ⟨X, rfl, v⟩
    · exact Or.inl (Or.inl rfl)
    obtain ⟨X', e, kf⟩ := (k.resolve_left (by simp)).resolve_left (by simp)
    simp only [Term.map.injEq] at e
    subst e
    have conv : ∀ e, Nest t d e → Keyed d e → (level t d).E e := nest_level t d
    refine Or.inl (Or.inr ⟨X, rfl, fun q hq => ?_, fun name w h => ?_⟩)
    · rcases v.keys q hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
    · rcases v.keys (.atom name) (by rw [h]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
        subst e
      · exact Or.inl ⟨rfl, v.bitmap w h⟩
      · obtain ⟨p, S, rfl, set⟩ := v.atom w h
        exact Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, atom_nonempty p S fun hp => v.atomUnion S (by subst hp; simpa using h)⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, funA_of conv (v.funs w h) (kf.funs rfl w h)⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, lf_of conv (level t d).ef.term (v.lists w h) (kf.lists w h)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tfield_of conv (v.tuples w h) (kf.tuples w h)⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, mfield_of conv (v.maps w h) (kf.maps w h)⟩))))

/-- Keyed negatable types are top-level types over the element types of their depth. -/
theorem negatable_tc (t : Term) (d : Nat) {X : List (Term × Term)} (v : Negatable (Nest t d) X)
    (kf : KeyedF (Keyed d) Bool.false X) : TCF (level t d) (.map X) := by
  have conv : ∀ e, Nest t d e → Keyed d e → (level t d).E e := nest_level t d
  refine Or.inr ⟨X, rfl, fun q hq => ?_, fun name w h => ?_⟩
  · rcases v.keys q hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
  · rcases v.keys (.atom name) (by rw [h]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨rfl, v.bitmap w h⟩
    · obtain ⟨p, S, rfl, set⟩ := v.atom w h
      exact Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, atom_nonempty p S fun hp => v.atomUnion S (by subst hp; simpa using h)⟩)
    · obtain ⟨pos, R, rfl⟩ := v.funs w h
      exact Or.inr (Or.inr (Or.inl ⟨rfl, pos, R, rfl, fun q x hx => v.arities _ h _ R rfl q x hx⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, lf_of conv (level t d).ef.term (v.lists w h) (kf.lists w h)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tfield_of conv (v.tuples w h) (kf.tuples w h)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, mfield_of conv (v.maps w h) (kf.maps w h)⟩))))

end Elixir.STTDescrProofsTest.Nest
