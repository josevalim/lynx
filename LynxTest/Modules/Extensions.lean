import Lynx.Modules.Extensions

namespace LynxTest.Modules.Extensions
open Lynx Lynx.Modules

example (predicate : Term → Outcome Term) :
    Extensions.is_proper_list predicate .nil = .value (.atom "true") := by rfl

example : Extensions.is_proper_list Erlang.is_integer
    (.cons (.integer 1) (.cons (.integer 2) .nil)) = .value (.atom "true") := by rfl

example (result : Term) (notTrue : result ≠ .atom "true") :
    Extensions.is_proper_list (fun _ => .value result) (.cons .nil .nil) =
      .value (.atom "false") := by
  simp [Extensions.is_proper_list, notTrue]

example (exception : Exception) :
    Extensions.is_proper_list (fun _ => .raised exception) (.cons .nil .nil) =
      .value (.atom "false") := by rfl

example : Extensions.is_proper_list Erlang.is_integer
    (.cons (.integer 1) (.integer 2)) = .value (.atom "false") := by rfl

example (tail : Term) :
    Extensions.is_proper_list (fun _ => .value (.atom "false")) (.cons .nil tail) =
      .value (.atom "false") := by rfl

end LynxTest.Modules.Extensions
