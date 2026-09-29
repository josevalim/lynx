module

public import Erlang.erlang.Guards
public import Erlang.erlang.Process

public section

namespace Erlang.erlang

open Lynx

private def properList? : Term → Option (List Term)
  | .nil => some []
  | .cons head tail => (properList? tail).map (head :: ·)
  | _ => none

/-- Dynamically apply a function to an Erlang list of arguments. Internal
application uses an array and does not retain the source list encoding. -/
def «apply/2» (function arguments : Term) : Result :=
  match properList? arguments with
  | none => .error (.error (.atom "badarg"))
  | some decoded => Term.apply function decoded.toArray

end Erlang.erlang
