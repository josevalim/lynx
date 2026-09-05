import Lynx.Term

namespace Lynx

/-! A contract accepts exactly when its translated Elixir expression returns `true`. -/
def Accepted (outcome : Outcome Term) : Prop :=
  outcome = .value Term.true

instance (outcome : Outcome Term) : Decidable (Accepted outcome) :=
  inferInstanceAs (Decidable (outcome = .value Term.true))

/-!
An expectation must accept at least one input. This is part of verification,
not an optional diagnostic: otherwise every implication below could be true
without checking the implementation.
-/
def Covered {Args : Type} (expects : Args → Outcome Term) : Prop :=
  ∃ input, Accepted (expects input)

/-!
The expected domain is nonempty, and for every accepted input the function
must return normally and its actual result must satisfy the guarantee. `Args`
is a Lean argument container.
-/
def Satisfies {Args : Type}
    (function : Args → Outcome Term)
    (expects : Args → Outcome Term)
    (ensures : Args → Term → Outcome Term) : Prop :=
  Covered expects ∧
    ∀ input,
      Accepted (expects input) →
      ∃ result,
        function input = .value result ∧
        Accepted (ensures input result)

/-- A property has a nonempty explicit domain and no implicit returned value. -/
def Property {Args : Type}
    (expects expression : Args → Outcome Term) : Prop :=
  Covered expects ∧
    ∀ args, Accepted (expects args) → Accepted (expression args)

/-- Source location of a translated clause. Lines use the source file's one-based numbering. -/
structure SourceLabel where
  file : String
  line : Nat
deriving Repr, DecidableEq

instance : ToString SourceLabel where
  toString source := s!"{source.file}:{source.line}"

/-- Attach source metadata to any proposition without changing its logical meaning. -/
def WithSourceLabel (_source : SourceLabel) (proposition : Prop) : Prop := proposition

/-- Named Elixir `ensures` clauses share one required expectation-coverage proof
and are each checked against the same function outcome. -/
def EnsuresClauses {Args : Type} (function expects : Args → Outcome Term)
    (clauses : List (SourceLabel × (Args → Term → Outcome Term))) : Prop :=
  Covered expects ∧ clauses.foldr (fun (source, ensures) rest =>
    WithSourceLabel source (∀ input, Accepted (expects input) →
      ∃ result, function input = .value result ∧ Accepted (ensures input result)) ∧ rest) True

abbrev accepts := Accepted
abbrev SatisfiesUnary := @Satisfies Term

end Lynx
