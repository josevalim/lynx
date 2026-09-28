module

public import Lynx.Term

public section

/-! Helpers for calls whose translated Lean signature includes the program-local
function table.

The translator must rewrite calls to every function in this module during
compilation so they receive the generated program's function table. Any future
function with the same requirement must be added here.
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

/-- Dynamic calls are pure when every implementation in the supplied table is pure. -/
@[simp↓] theorem apply_pure (table : Term.FunTable)
    (pure : ∀ implementation ∈ table, ∀ captures arguments,
      Result.IsPure (implementation captures arguments))
    (function arguments : Term) :
    Result.IsPure («apply/2» table function arguments) := by
  unfold «apply/2»
  split
  · simp
  · cases function <;> simp only [Term.fetchFun]
    all_goals try simp
    rename_i id arity captures
    cases h : table[id]? with
    | none => simp
    | some implementation =>
      simp only [Option.map_some]
      split
      · exact pure implementation (Array.mem_of_getElem? h) captures _
      · simp

end Erlang.erlang
