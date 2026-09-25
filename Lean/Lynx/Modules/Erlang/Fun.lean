module

public import Lynx.Term

public section

/-! Helpers for calls whose translated Lean signature includes the program-local
function table.

The translator must rewrite calls to every function in this module during
compilation so they receive the generated program's function table. Any future
function with the same requirement must be added here.
-/

namespace Lynx.Modules.Erlang

open Lynx

/-- Spawn a zero-arity function term. Resolution and arity validation happen in
the caller before the child is scheduled. `Result.bind` captures the caller
continuation for scheduling. -/
def spawn_1 (table : Term.FunTable) (child : Term) : Result :=
  match Term.fetchFun table child with
  | some (implementation, 0) =>
      .spawn (implementation #[]) fun pid => .ok (.pid pid)
  | _ => .error (.error (.atom "badarg"))

private def properList? : Term → Option (List Term)
  | .nil => some []
  | .cons head tail => (properList? tail).map (head :: ·)
  | _ => none

/-- Dynamically apply a function to an Erlang list of arguments. Internal
application uses an array and does not retain the source list encoding. -/
def apply_2 (table : Term.FunTable) (function arguments : Term) : Result :=
  match properList? arguments with
  | none => .error (.error (.atom "badarg"))
  | some decoded =>
      match Term.fetchFun table function with
      | none => .error (.error (.tuple #[.atom "badfun", function]))
      | some (implementation, arity) =>
          if decoded.length = arity then
            implementation decoded.toArray
          else
            .error (.error
              (.tuple #[.atom "badarity", .tuple #[function, arguments]]))

end Lynx.Modules.Erlang
