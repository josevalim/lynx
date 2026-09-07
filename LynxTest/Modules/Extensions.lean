import Lynx.Modules.Extensions

namespace LynxTest.Modules.Extensions
open Lynx Lynx.Modules

example : Extensions.is_proper_list_1 .nil = .ok (.atom "true") := by rfl

-- Heads can be arbitrary terms, including improper lists themselves.
example (head : Term) :
    Extensions.is_proper_list_1 (.cons head (.cons (.cons .nil (.atom "tail")) .nil)) =
      .ok (.atom "true") := by rfl

example (n : Int) :
    Extensions.is_proper_list_1 (.integer n) = .ok (.atom "false") := by rfl

example (name : String) :
    Extensions.is_proper_list_1 (.atom name) = .ok (.atom "false") := by rfl

-- Inspect the entire outer spine, not just its first cons cell.
example (a b c : Term) :
    Extensions.is_proper_list_1 (.cons a (.cons b (.cons c (.atom "tail")))) =
      .ok (.atom "false") := by rfl

example (head : Term) (n : Int) :
    Extensions.is_proper_list_1 (.cons head (.integer n)) =
      .ok (.atom "false") := by rfl

example (predicate : Term → Result) :
    Extensions.is_proper_list_2 predicate .nil = .ok (.atom "true") := by rfl

example : Extensions.is_proper_list_2 Erlang.is_integer_1
    (.cons (.integer 1) (.cons (.integer 2) .nil)) = .ok (.atom "true") := by rfl

example (result : Term) (notTrue : result ≠ .atom "true") :
    Extensions.is_proper_list_2 (fun _ => .ok result) (.cons .nil .nil) =
      .ok (.atom "false") := by
  simp [Extensions.is_proper_list_2, notTrue]

example (exception : Exception) :
    Extensions.is_proper_list_2 (fun _ => .error exception) (.cons .nil .nil) =
      .ok (.atom "false") := by rfl

example : Extensions.is_proper_list_2 Erlang.is_integer_1
    (.cons (.integer 1) (.integer 2)) = .ok (.atom "false") := by rfl

example (tail : Term) :
    Extensions.is_proper_list_2 (fun _ => .ok (.atom "false")) (.cons .nil tail) =
      .ok (.atom "false") := by rfl

end LynxTest.Modules.Extensions
