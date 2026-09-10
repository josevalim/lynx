module

public import Std

public section

namespace Lynx

inductive Term where
  | integer : Int → Term
  | atom : String → Term
  | tuple : Array Term → Term
  | map : List (Term × Term) → Term
  | nil : Term
  | cons : Term → Term → Term
deriving Repr

inductive Exception where
  | error : Term → Exception
  | throw : Term → Exception
  | exit : Term → Exception
deriving Repr

structure Environment where
  pdict : List (Term × Term) := []
deriving Repr, Inhabited

abbrev Result (α : Type := Term) := EStateM Exception Environment α

/-- Run a computation in a fresh environment. -/
def run (computation : Result α) : EStateM.Result Exception Environment α :=
  EStateM.run computation {}

namespace Result

@[expose] def ok (value : α) : Result α := pure value

@[expose] def error (exception : Exception) : Result α := throw exception

@[simp] theorem ok_apply (value : α) (env : Environment) :
    ok value env = .ok value env := rfl

@[simp] theorem error_apply (exception : Exception) (env : Environment) :
    (error exception : Result α) env = .error exception env := rfl

@[simp] theorem pure_apply (value : α) (env : Environment) :
    (pure value : Result α) env = .ok value env := rfl

@[simp] theorem throw_apply (exception : Exception) (env : Environment) :
    (throw exception : Result α) env = .error exception env := rfl

@[simp] theorem get_apply (env : Environment) :
    (get : Result Environment) env = .ok env env := rfl

@[simp] theorem set_apply (next env : Environment) :
    (set next : Result PUnit) env = .ok .unit next := rfl

@[simp] theorem modify_apply (update : Environment → Environment) (env : Environment) :
    (modify update : Result PUnit) env = .ok .unit (update env) := rfl

@[simp] theorem bind_apply (computation : Result α) (next : α → Result β) (env : Environment) :
    (computation >>= next) env =
      match computation env with
      | .ok value updated => next value updated
      | .error exception updated => .error exception updated := by
  simp only [Bind.bind, EStateM.bind]
  cases computation env <;> rfl

/-- A computation neither reads nor changes the environment. -/
def IsPure (computation : Result α) : Prop :=
  ∀ reference env,
    match computation reference with
    | .ok value _ => computation env = .ok value env
    | .error exception _ => computation env = .error exception env

@[simp] theorem isPure_ok (value : α) : IsPure (ok value) := by
  intro reference env
  rfl

@[simp] theorem isPure_error (exception : Exception) :
    IsPure (error exception : Result α) := by
  intro reference env
  rfl

@[simp↓] theorem IsPure.bind (computation : Result α) (next : α → Result β)
    (computationPure : IsPure computation) (nextPure : ∀ value, IsPure (next value)) :
    IsPure (computation >>= next) := by
  intro reference env
  cases outcome : computation reference with
  | ok value final =>
      have current := computationPure reference env
      rw [outcome] at current
      simp only at current ⊢
      rw [bind_apply, bind_apply, outcome, current]
      exact nextPure value final env
  | error exception final =>
      have current := computationPure reference env
      rw [outcome] at current
      simp only at current ⊢
      rw [bind_apply, bind_apply, outcome, current]

@[simp] theorem IsPure.ok_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (value : α) :
    computation env = .ok value final ↔ computation = ok value ∧ env = final := by
  constructor
  · intro accepted
    have preserved := pure env env
    rw [accepted] at preserved
    have finalEq : final = env := EStateM.Result.ok.inj preserved |>.2
    refine ⟨?_, finalEq.symm⟩
    funext current
    have outcome := pure env current
    rw [accepted] at outcome
    exact outcome
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem IsPure.error_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (exception : Exception) :
    computation env = .error exception final ↔
      computation = error exception ∧ env = final := by
  constructor
  · intro failed
    have preserved := pure env env
    rw [failed] at preserved
    have finalEq : final = env := EStateM.Result.error.inj preserved |>.2
    refine ⟨?_, finalEq.symm⟩
    funext current
    have outcome := pure env current
    rw [failed] at outcome
    exact outcome
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem ok_inj (a b : α) : (ok a : Result α) = ok b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Lynx.run h
    exact EStateM.Result.ok.inj this |>.1
  · rintro rfl; rfl

@[simp] theorem ok_ne_error (value : α) (exception : Exception) :
    (ok value : Result α) ≠ error exception := by
  intro h
  have := congrArg Lynx.run h
  cases this

@[simp] theorem error_ne_ok (exception : Exception) (value : α) :
    (error exception : Result α) ≠ ok value := Ne.symm (ok_ne_error value exception)

@[simp] theorem error_inj (a b : Exception) :
    (error a : Result α) = error b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Lynx.run h
    exact EStateM.Result.error.inj this |>.1
  · rintro rfl; rfl

end Result

-- Computation-facing simplification rules for translated code.
-- The generic monad laws are supplied by the LawfulMonad instance.
@[simp] theorem Result.ok_bind (value : α) (next : α → Result β) :
    (Result.ok value >>= next) = next value := rfl

@[simp] theorem Result.error_bind (exception : Exception) (next : α → Result β) :
    (Result.error exception >>= next) = .error exception := rfl

@[simp] theorem Result.throw_eq (exception : Exception) :
    (throw exception : Result α) = .error exception := rfl

end Lynx
