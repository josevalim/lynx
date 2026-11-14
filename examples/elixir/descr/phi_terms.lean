namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The terms `phi/5` works on, and the sets they stand for. -/

section
variable {V : Type} (den : Term → V → Prop)

/-- Flagged arguments, as `phi/5` keeps them: a list of `{flag, type}`. -/
def encA (args : List (Bool × Term)) : Term := Term.list (args.map fun p => .tuple #[boolAtom p.1, p.2])

/-- The flagged return, `{flag, type}`. -/
def encR (r : Bool × Term) : Term := .tuple #[boolAtom r.1, r.2]

/-- Positive arrows, as BDD leaves `{key, arguments, return}`. -/
def encP (P : List (Term × List Term × Term)) : Term :=
  Term.list (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2])

def semA (args : List (Bool × Term)) : List (Bool × (V → Prop)) := args.map fun p => (p.1, den p.2)
def semR (r : Bool × Term) : Bool × (V → Prop) := (r.1, den r.2)
def semP (P : List (Term × List Term × Term)) : List (FunSem.Arrow V) := P.map fun p => (p.2.1.map den, den p.2.2)

end

/-- Lists whose elements are equal by comparison, pairwise. -/
inductive CmpEq : List Term → List Term → Prop
  | nil : CmpEq [] []
  | cons {a b : Term} {as bs : List Term} : Term.compare (Term.fuel a b) a b = .eq → CmpEq as bs → CmpEq (a :: as) (b :: bs)

theorem list_cmp : ∀ (xs ys : List Term), Term.compare (Term.fuel (Term.list xs) (Term.list ys)) (Term.list xs) (Term.list ys) = .eq → CmpEq xs ys
  | [], [], _ => .nil
  | x :: xs, ys, e => by
    obtain ⟨y, ys', h, ex, es⟩ := cons_cmp e
    cases ys with
    | nil => simp [Term.list] at h
    | cons y' ys =>
      simp only [Term.list, Term.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .cons ex (list_cmp xs ys es)
  | [], y :: ys, e => by
    have := (nil_compare_eq (Term.list (y :: ys))).mp e
    simp [Term.list] at this

theorem boolAtom_cmp {b b' : Bool} (e : Term.compare (Term.fuel (boolAtom b) (boolAtom b')) (boolAtom b) (boolAtom b') = .eq) : b = b' := by
  have := atom_cmp e
  cases b <;> cases b' <;> simp_all [boolAtom]

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- Element types equal by comparison stand for the same set. -/
def DenCongr (E : Term → Prop) (den : Term → V → Prop) : Prop :=
  ∀ {a a'}, E a → E a' → Term.compare (Term.fuel a a') a a' = .eq → den a = den a'

theorem semA_f2 (cg : DenCongr E den) : ∀ {args args' : List (Bool × Term)}, (∀ p ∈ args, E p.2) →
    (∀ p ∈ args', E p.2) →
    CmpEq (args.map fun p => .tuple #[boolAtom p.1, p.2]) (args'.map fun p => .tuple #[boolAtom p.1, p.2]) →
      semA den args = semA den args'
  | [], [], _, _, _ => rfl
  | p :: args, p' :: args', h, h', f => by
    simp only [List.map] at f
    obtain _ | ⟨e₀, f⟩ := f
    obtain ⟨eb, ea⟩ := tuple2_cmp e₀
    have tail := semA_f2 cg (fun q mq => h q (by simp [mq])) (fun q mq => h' q (by simp [mq])) f
    simp only [semA, List.map_cons] at tail ⊢
    rw [boolAtom_cmp eb, cg (h p (by simp)) (h' p' (by simp)) ea, tail]
  | [], _ :: _, _, _, f => by simp only [List.map] at f; cases f
  | _ :: _, [], _, _, f => by simp only [List.map] at f; cases f

theorem semA_cmp (cg : DenCongr E den) {args args' : List (Bool × Term)} (h : ∀ p ∈ args, E p.2)
    (h' : ∀ p ∈ args', E p.2) (e : Term.compare (Term.fuel (encA args) (encA args')) (encA args) (encA args') = .eq) : semA den args = semA den args' :=
  semA_f2 cg h h' (list_cmp _ _ e)

theorem map_den_f2 (cg : DenCongr E den) : ∀ {us us' : List Term}, (∀ u ∈ us, E u) → (∀ u ∈ us', E u) →
    CmpEq us us' → us.map den = us'.map den
  | [], [], _, _, _ => rfl
  | u :: us, u' :: us', h, h', .cons e f => by
    simp only [List.map_cons]
    rw [cg (h u (by simp)) (h' u' (by simp)) e,
      map_den_f2 cg (fun q mq => h q (by simp [mq])) (fun q mq => h' q (by simp [mq])) f]

theorem semP_f2 (cg : DenCongr E den) : ∀ {P P' : List (Term × List Term × Term)},
    (∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2) → (∀ p ∈ P', (∀ u ∈ p.2.1, E u) ∧ E p.2.2) →
    CmpEq (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (P'.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) →
      semP den P = semP den P'
  | [], [], _, _, _ => rfl
  | p :: P, p' :: P', h, h', f => by
    simp only [List.map] at f
    obtain _ | ⟨e₀, f⟩ := f
    obtain ⟨b₀, b₁, b₂, eq, -, e₁, e₂⟩ := tuple3_cmp e₀
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eq
    obtain ⟨-, rfl, rfl, -⟩ := eq
    have tail := semP_f2 cg (fun q mq => h q (by simp [mq])) (fun q mq => h' q (by simp [mq])) f
    simp only [semP, List.map_cons] at tail ⊢
    rw [map_den_f2 cg (h p (by simp)).1 (h' p' (by simp)).1 (list_cmp _ _ e₁),
      cg (h p (by simp)).2 (h' p' (by simp)).2 e₂, tail]
  | [], _ :: _, _, _, f => by simp only [List.map] at f; cases f
  | _ :: _, [], _, _, f => by simp only [List.map] at f; cases f

theorem semP_cmp (cg : DenCongr E den) {P P' : List (Term × List Term × Term)}
    (h : ∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2) (h' : ∀ p ∈ P', (∀ u ∈ p.2.1, E u) ∧ E p.2.2)
    (e : Term.compare (Term.fuel (encP P) (encP P')) (encP P) (encP P') = .eq) : semP den P = semP den P' :=
  semP_f2 cg h h' (list_cmp _ _ e)

end

end Elixir.STTDescrProofsTest.Nest
