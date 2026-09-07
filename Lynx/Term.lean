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
exception (which itself distinguishes error, throw, and exit). Monad operations
and their laws are inherited from `Except`. -/
abbrev Result := Except Exception Term

instance : DecidableEq Result
  | .ok left, .ok right => decidable_of_iff (left = right) ⟨congrArg Except.ok, Except.ok.inj⟩
  | .error left, .error right =>
    decidable_of_iff (left = right) ⟨congrArg Except.error, Except.error.inj⟩
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

-- Constructor-facing simplification rules for translated code. The monad
-- instances and generic laws themselves come from `Except`.
@[simp] theorem Result.ok_bind (value : α) (next : α → Except Exception β) :
    (Except.ok value >>= next) = next value := rfl

@[simp] theorem Result.error_bind (exception : Exception) (next : α → Except Exception β) :
    (Except.error exception >>= next) = .error exception := rfl

@[simp] theorem Result.throw_eq (exception : Exception) :
    (throw exception : Except Exception α) = .error exception := rfl

end Lynx
