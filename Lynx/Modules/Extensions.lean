import Lynx.Modules.Erlang.Definitions

namespace Lynx.Modules.Extensions

/-- Traverse the outer list, accepting only a tail ending in nil.
Elements are unrestricted and are not inspected. -/
def is_proper_list : Term → Result
  | .nil => .ok (.atom "true")
  | .cons _ tail => is_proper_list tail
  | _ => .ok (.atom "false")

/-- A proper-list guard: every element must return exactly `.ok (.atom "true")`.
The empty list succeeds. Improper lists, false/non-boolean predicate results,
and raised outcomes return false. Evaluation stops at the first rejection. -/
def is_proper_list_with (predicate : Term → Result) : Term → Result
  | .nil => .ok (.atom "true")
  | .cons head tail =>
    match predicate head with
    | .ok (.atom "true") => is_proper_list_with predicate tail
    | _ => .ok (.atom "false")
  | _ => .ok (.atom "false")

end Lynx.Modules.Extensions
