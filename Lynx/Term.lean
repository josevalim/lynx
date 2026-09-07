namespace Lynx

inductive Term where
  | integer : Int → Term
  | atom : String → Term
  | nil : Term
  | cons : Term → Term → Term
deriving Repr, DecidableEq

namespace Term

def «true» : Term :=
  .atom "true"

def «false» : Term :=
  .atom "false"

end Term

inductive Exception where
  | error : Term → Exception
  | throw : Term → Exception
  | exit : Term → Exception
deriving Repr, DecidableEq

/-- An Erlang computation: `.ok` returns a value; `.error` carries an Erlang
exception (which itself distinguishes error, throw, and exit). The success type
defaults to `Term`; generic monadic helpers can use `Result α`. -/
inductive Result (α : Type := Term) where
  | error : Exception → Result α
  | ok : α → Result α
deriving Repr

-- `@Result` suppresses the default argument when a type constructor is needed.
instance : Monad @Result where
  pure := .ok
  bind outcome next :=
    match outcome with
    | .ok value => next value
    | .error exception => .error exception

instance : LawfulMonad @Result := LawfulMonad.mk'
  (id_map := fun outcome => by cases outcome <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun outcome _ _ => by cases outcome <;> rfl)

instance : MonadExceptOf Exception @Result where
  throw := .error
  tryCatch outcome handler :=
    match outcome with
    | .ok value => .ok value
    | .error exception => handler exception

instance [DecidableEq α] : DecidableEq (Result α)
  | .ok left, .ok right => decidable_of_iff (left = right) ⟨congrArg Result.ok, Result.ok.inj⟩
  | .error left, .error right =>
    decidable_of_iff (left = right) ⟨congrArg Result.error, Result.error.inj⟩
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

-- Constructor-facing simplification rules for translated code. The generic
-- monad laws are supplied by the LawfulMonad instance.
@[simp] theorem Result.ok_bind (value : α) (next : α → Result β) :
    (Result.ok value >>= next) = next value := rfl

@[simp] theorem Result.error_bind (exception : Exception) (next : α → Result β) :
    (Result.error exception >>= next) = .error exception := rfl

@[simp] theorem Result.throw_eq (exception : Exception) :
    (throw exception : Result α) = .error exception := rfl

end Lynx
