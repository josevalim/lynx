module

public import Lynx.Term

public section

/-! Erlang function values produce dispatch requests resolved by the runner. -/

namespace Erlang.erlang

open Lynx

/-- Request a zero-arity function spawn. The dispatcher validates the table entry
before creating the child; the function body executes in the child's process. -/
def «spawn/1» (child : Term) : Result :=
  match child with
  | .function _ 0 _ => .spawn child fun
      | .ok pid => .ok pid
      | .error exception => .error exception
  | _ => .error (.error (.atom "badarg"))

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

/-- Application has no effects of its own; its implementation is supplied by the program. -/
@[simp↓] theorem apply_neutral (function arguments : Term) :
    Result.IsNeutral («apply/2» function arguments) := by
  unfold «apply/2»
  split
  · simp
  · cases function <;> simp only
    all_goals try simp
    split <;> simp [Result.IsNeutral]
    intro result
    cases result <;> trivial

end Erlang.erlang
