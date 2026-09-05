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

inductive Outcome (α : Type) where
  | value : α → Outcome α
  | raised : Exception → Outcome α
deriving Repr, DecidableEq

instance : Monad Outcome where
  pure := .value
  bind outcome next :=
    match outcome with
    | .value value => next value
    | .raised exception => .raised exception

instance : MonadExceptOf Exception Outcome where
  throw := .raised
  tryCatch outcome handler :=
    match outcome with
    | .value value => .value value
    | .raised exception => handler exception

@[simp] theorem Outcome.value_bind
    (value : α) (next : α → Outcome β) :
    (Outcome.value value >>= next) = next value :=
  rfl

@[simp] theorem Outcome.raised_bind
    (exception : Exception) (next : α → Outcome β) :
    (Outcome.raised exception >>= next) = .raised exception :=
  rfl

@[simp] theorem Outcome.throw_eq (exception : Exception) :
    (throw exception : Outcome α) = .raised exception :=
  rfl

end Lynx
