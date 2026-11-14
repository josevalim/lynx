namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- Element types at a nesting level, with their values. -/
structure Level : Type 1 where
  nd : Term
  E : Term → Prop
  V : Type
  den : Term → V → Prop
  tl : V → Prop
  K : Nat
  ef : EF nd E V den tl K
  none : E (.map [])
  hasT : ∀ {e}, IsT nd e → E e

theorem keyOf_neg (t : Term) : keyOf t < 0 := by
  obtain ⟨h, run, lt⟩ := Erlang.erlang.phash2_range (Term.list [.atom "term", t])
  simp only [keyOf, run]
  omega

theorem expN_descr {nd : Term} {TF LF MF : Term → Prop} {e : Term} (tf : TF (litN e (keyOf nd))) :
    DEG Fn TF LF MF (expN e (keyOf nd)) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w hw => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
    by_cases t : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp t⟩
    · by_cases a : compareExact (fuel q (.atom "atom")) q (.atom "atom") = .eq
      · exact ⟨"atom", by simp [names], (compareExact_eq_atom _ _).mp a⟩
      · simp [t, a] at h
  · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq] at hw
    by_cases t : name = "tuple"
    · subst t; simp at hw; subst hw; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tf⟩))))
    · by_cases a : name = "atom"
      · subst a; simp at hw; subst hw
        exact Or.inr (Or.inl ⟨rfl, ⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩,
          .atom "nil", by simp [amemV, mapLookup]⟩)
      · simp [t, a] at hw

theorem DEG.notT {nd : Term} {TF LF MF : Term → Prop} {a : Term} (ha : DEG Fn TF LF MF a) : ¬IsT nd a := by
  rcases ha with rfl | ⟨X, rfl, -⟩
  · exact isT_term
  · exact isT_map

theorem nodeOk0 (nd : Term) : NodeOk nd (DEG FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map")) :=
  ⟨fun he => expN_descr (Or.inr (Bdd.leaf_iff.mpr ⟨_, he, rfl⟩)), DEG.notT⟩

theorem nodeOk_DE {nd : Term} {E : Term → Prop} (hterm : E (.atom "term")) (hasT : ∀ {e}, IsT nd e → E e) :
    NodeOk nd (DE E) := by
  refine ⟨fun {e} he => expN_descr (Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨keyOf nd, "closed", [.atom "term", e], rfl,
    Or.inr rfl, fun x mx => ?_⟩, fun ⟨k, h⟩ => by simp [Term.list] at h⟩, fun k tag l h => ?_⟩)), DEG.notT⟩
  · simp at mx; rcases mx with h | h <;> subst h; exact hterm; exact hasT he
  · obtain ⟨e₁, e₂, -⟩ := tuple3_inj h
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨fun _ => keyOf_neg nd, fun h => by simp at h⟩

/-- The element types of each level, with the node `t`. -/
def level (t : Term) : Nat → Level
  | 0 => ⟨t, DEN t (DEG FunTop (OField (PureLit t)) (FieldOk "list") (FieldOk "map")), PtG Resp Resp Resp FVT, denN t denD, tlD,
      23, addNode (ef_gen (step0 t) (fuse0 t)) (nodeOk0 t), Or.inl (Or.inr ⟨[], rfl, descrC_nil⟩), fun h => Or.inr h⟩
  | n + 1 =>
    let L := level t n
    ⟨L.nd, DEN L.nd (DE L.E), PtD L.E L.den L.tl (FVal L.E L.den), denN L.nd denD, tlD, L.K + 24,
      addNode (ef_step L.ef L.none)
      (nodeOk_DE L.ef.term L.hasT), Or.inl de_none, fun h => Or.inr h⟩

theorem level_nd (t : Term) : ∀ n, (level t n).nd = t
  | 0 => rfl
  | n + 1 => level_nd t n

end Elixir.STTDescrProofsTest.Nest
