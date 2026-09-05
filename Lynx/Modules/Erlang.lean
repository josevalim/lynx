import Lynx.Contract
import Lynx.Term

namespace Lynx.Modules.Erlang

open Lynx

/-!
Semantics for Erlang built-in functions and operators used by translated
Elixir code.

These functions operate on dynamic `Term` values and return `Outcome`, so their
normal results and runtime errors remain part of the model.
-/

def is_integer : Term → Outcome Term
  | .integer _ => .value Term.true
  | _ => .value Term.false

/-!
Like Erlang and Elixir, this is a shallow test: `nil` and every cons cell are
lists, including an improper list whose tail is not itself a list.
-/
def is_list : Term → Outcome Term
  | .nil => .value Term.true
  | .cons _ _ => .value Term.true
  | _ => .value Term.false

def add : Term → Term → Outcome Term
  | .integer x, .integer y => .value (.integer (x + y))
  | _, _ => throw (.error (.atom "badarith"))

/-! Short-circuiting Boolean conjunction used to model Elixir's `and`. -/
def andalso
    (left : Outcome Term)
    (right : Unit → Outcome Term) : Outcome Term :=
  match left with
  | .value (.atom "true") => right ()
  | .value (.atom "false") => .value Term.false
  | .value _ => .raised (.error (.atom "badarg"))
  | .raised exception => .raised exception

end Lynx.Modules.Erlang
