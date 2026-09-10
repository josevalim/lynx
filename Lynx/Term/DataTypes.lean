import Std

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

namespace Result

/-- Run a computation, starting with an empty environment unless supplied. -/
def run (computation : Result α) (env : Environment := {}) :
    EStateM.Result Exception Environment α := EStateM.run computation env

@[simp] theorem run_eq (computation : Result α) (env : Environment) :
    run computation env = computation env := rfl

def ok (value : α) : Result α := pure value

def error (exception : Exception) : Result α := throw exception

@[simp] theorem run_ok (value : α) (env : Environment) :
    run (ok value) env = .ok value env := rfl

@[simp] theorem run_error (exception : Exception) (env : Environment) :
    run (error exception : Result α) env = .error exception env := rfl

@[simp] theorem run_bind (computation : Result α) (next : α → Result β) (env : Environment) :
    run (computation >>= next) env =
      match run computation env with
      | .ok value updated => run (next value) updated
      | .error exception updated => .error exception updated := by
  simp only [run, EStateM.run, Bind.bind, EStateM.bind]
  cases computation env <;> rfl

@[simp] theorem run_pure (value : α) (env : Environment) :
    run (pure value : Result α) env = .ok value env := rfl

@[simp] theorem run_throw (exception : Exception) (env : Environment) :
    run (throw exception : Result α) env = .error exception env := rfl

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
  exact run_bind computation next env

/-- Replace the final state of an outcome while retaining its value or exception. -/
def rebase (outcome : EStateM.Result Exception Environment α) (env : Environment) :
    EStateM.Result Exception Environment α :=
  match outcome with
  | .ok value _ => .ok value env
  | .error exception _ => .error exception env

@[simp] theorem rebase_ok (value : α) (previous env : Environment) :
    rebase (.ok value previous) env = .ok value env := rfl

@[simp] theorem rebase_error (exception : Exception) (previous env : Environment) :
    rebase (.error exception previous : EStateM.Result Exception Environment α) env =
      .error exception env := rfl

/-- A computation neither reads nor changes the environment. -/
def IsPure (computation : Result α) : Prop :=
  ∀ reference env, computation env = rebase (computation reference) env

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
  rw [bind_apply, bind_apply, computationPure reference env]
  cases outcome : computation reference with
  | ok value final =>
      simp only [rebase]
      exact nextPure value final env
  | error exception final => rfl

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
    rw [pure env current, accepted]
    rfl
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
    rw [pure env current, failed]
    rfl
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem ok_inj (a b : α) : (ok a : Result α) = ok b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun computation => run computation {}) h
    exact EStateM.Result.ok.inj this |>.1
  · rintro rfl; rfl

@[simp] theorem ok_ne_error (value : α) (exception : Exception) :
    (ok value : Result α) ≠ error exception := by
  intro h
  have := congrArg (fun computation => run computation {}) h
  simp at this

@[simp] theorem error_ne_ok (exception : Exception) (value : α) :
    (error exception : Result α) ≠ ok value := Ne.symm (ok_ne_error value exception)

@[simp] theorem error_inj (a b : Exception) :
    (error a : Result α) = error b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun computation => run computation {}) h
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
