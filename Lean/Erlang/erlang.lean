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
  | some decoded =>
      match function with
      | .function _ arity _ =>
          if decoded.length = arity then
            .apply function decoded.toArray fun
              | .ok value => .ok value
              | .error exception => .error exception
          else
            .error (.error (.tuple #[.atom "badarity", .tuple #[function, arguments]]))
      | _ => .error (.error (.tuple #[.atom "badfun", function]))

end Erlang.erlang
