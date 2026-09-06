import Lynx.Modules.Extensions

namespace LynxTest.Modules.Extensions
open Lynx Lynx.Modules

example : Extensions.is_proper_list .nil = .value (.atom "true") := by rfl

-- Heads can be arbitrary terms, including improper lists themselves.
example (head : Term) :
    Extensions.is_proper_list (.cons head (.cons (.cons .nil (.atom "tail")) .nil)) =
      .value (.atom "true") := by rfl

example (n : Int) :
    Extensions.is_proper_list (.integer n) = .value (.atom "false") := by rfl

example (name : String) :
    Extensions.is_proper_list (.atom name) = .value (.atom "false") := by rfl

-- Inspect the entire outer spine, not just its first cons cell.
example (a b c : Term) :
    Extensions.is_proper_list (.cons a (.cons b (.cons c (.atom "tail")))) =
      .value (.atom "false") := by rfl

example (head : Term) (n : Int) :
    Extensions.is_proper_list (.cons head (.integer n)) =
      .value (.atom "false") := by rfl

example (predicate : Term → Outcome Term) :
    Extensions.is_proper_list_with predicate .nil = .value (.atom "true") := by rfl

example : Extensions.is_proper_list_with Erlang.is_integer
    (.cons (.integer 1) (.cons (.integer 2) .nil)) = .value (.atom "true") := by rfl

example (result : Term) (notTrue : result ≠ .atom "true") :
    Extensions.is_proper_list_with (fun _ => .value result) (.cons .nil .nil) =
      .value (.atom "false") := by
  simp [Extensions.is_proper_list_with, notTrue]

example (exception : Exception) :
    Extensions.is_proper_list_with (fun _ => .raised exception) (.cons .nil .nil) =
      .value (.atom "false") := by rfl

example : Extensions.is_proper_list_with Erlang.is_integer
    (.cons (.integer 1) (.integer 2)) = .value (.atom "false") := by rfl

example (tail : Term) :
    Extensions.is_proper_list_with (fun _ => .value (.atom "false")) (.cons .nil tail) =
      .value (.atom "false") := by rfl

end LynxTest.Modules.Extensions
