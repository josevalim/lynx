namespace Lynx

/-!
Runtime Elixir values used by our first semantic fragment.

Elixir lists are not a special host-language `List Term`. They are constructed
from `nil` and cons cells. Consequently, this type can also represent improper
lists such as `[1 | 2]`.
-/

inductive Term where
  | integer : Int → Term
  | atom : String → Term
  | nil : Term
  | cons : Term → Term → Term
deriving Repr, DecidableEq

inductive Exception where
  | error : Term → Exception
  | throw : Term → Exception
  | exit : Term → Exception
deriving Repr, DecidableEq

inductive Outcome where
  | value : Term → Outcome
  | raised : Exception → Outcome
deriving Repr, DecidableEq

end Lynx
