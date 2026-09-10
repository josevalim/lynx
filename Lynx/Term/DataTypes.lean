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
