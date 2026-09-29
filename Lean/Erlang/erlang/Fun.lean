module

public import Lynx.Term

public section

/-! Helpers for calls whose translated Lean signature includes the program-local
function table.

The translator must rewrite calls to every function in this module during
compilation so they receive the generated program's function table. Any future
function with the same requirement must be added here.

The translator does not generate function tables yet, so `ExportModules.lean`
leaves these functions out of `modules.json` (it only exports functions of type
`Lynx.Term → … → Lynx.Result`). A call such as `erlang:spawn(F)` is therefore
reported as untranslatable instead of producing ill-typed Lean.
-/

namespace Erlang.erlang

open Lynx

/-- Spawn a zero-arity function term. Resolution and arity validation happen in
the caller before the child is scheduled. `Result.bind` captures the caller
continuation for scheduling. -/
def «spawn/1» (table : Term.FunTable) (child : Term) : Result :=
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
def «apply/2» (table : Term.FunTable) (function arguments : Term) : Result :=
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

end Erlang.erlang
