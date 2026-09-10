import Lynx.Term

/-! Internal proposition vocabulary for Lynx's tactic and translated contracts.
This module is not a supported library API. -/

namespace Lynx

/-! Contract expressions are observations of an environment snapshot. Their
own state changes are discarded; only a normal return of exactly `true` accepts. -/
def Accepted (computation : Result) (env : Environment := {}) : Prop :=
  ∃ final, computation env = .ok Term.true final

/-!
An expectation must accept at least one input/environment pair. This is part of verification,
not an optional diagnostic: otherwise every implication below could be true
without checking the implementation.
-/
def Covered {Args : Type} (expects : Args → Result) : Prop :=
  ∃ initial : Args × Environment, Accepted (expects initial.1) initial.2

/-!
The expected domain is nonempty, and for every accepted input and initial
environment the function must return normally. The guarantee observes its
actual result and final environment. `Args` is a Lean argument container.
-/
def Satisfies {Args : Type}
    (function : Args → Result)
    (expects : Args → Result)
    (ensures : Args → Term → Result) : Prop :=
  Covered expects ∧
    ∀ input env,
      Accepted (expects input) env →
      ∃ result final,
        function input env = .ok result final ∧
        Accepted (ensures input result) final

/-- A property has a nonempty explicit domain and no implicit returned value. -/
def Property {Args : Type}
    (expects expression : Args → Result) : Prop :=
  Covered expects ∧
    ∀ args env, Accepted (expects args) env → Accepted (expression args) env

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
def EnsuresClauses {Args : Type} (function expects : Args → Result)
    (clauses : List (SourceLabel × (Args → Term → Result))) : Prop :=
  Covered expects ∧ clauses.foldr (fun (source, ensures) rest =>
    WithSourceLabel source (∀ input env, Accepted (expects input) env →
      ∃ result final, function input env = .ok result final ∧
        Accepted (ensures input result) final) ∧ rest) True

end Lynx
