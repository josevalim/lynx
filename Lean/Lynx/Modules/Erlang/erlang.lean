module

public import Lynx.Modules.Erlang.erlang.Guards
public import Lynx.Modules.Erlang.erlang.Process
public import Lynx.Modules.Erlang.erlang.Exceptions
public import Lynx.Modules.Erlang.erlang.Conversions

public section

namespace Erlang.erlang

open Lynx

private def properList? : Term → Option (List Term)
  | .nil => some []
  | .cons head tail => (properList? tail).map (head :: ·)
  | _ => none

/-- Dynamically apply a function to an Erlang list of arguments. Internal
application uses an array and does not retain the source list encoding. It
returns `Except` when the program's function values do. -/
def «apply/2» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m] [Dispatch m]
    (dispatcher : Dispatcher) (function arguments : Term) : m Term :=
  match properList? arguments with
  | none => throw (.error (.atom "badarg"))
  | some decoded => Dispatch.dispatch dispatcher function decoded.toArray

end Erlang.erlang
