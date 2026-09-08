import Std

/-! Erlang term and outcome datatypes. Equality and ordering are defined downstream. -/
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

-- Constructor-facing simplification rules for translated code. The generic
-- monad laws are supplied by the LawfulMonad instance.
@[simp] theorem Result.ok_bind (value : α) (next : α → Result β) :
    (Result.ok value >>= next) = next value := rfl

@[simp] theorem Result.error_bind (exception : Exception) (next : α → Result β) :
    (Result.error exception >>= next) = .error exception := rfl

@[simp] theorem Result.throw_eq (exception : Exception) :
    (throw exception : Result α) = .error exception := rfl

end Lynx
