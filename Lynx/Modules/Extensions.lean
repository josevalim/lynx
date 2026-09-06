import Lynx.Modules.Erlang

namespace Lynx.Modules.Extensions

/-- A proper-list guard: every element must return exactly `.value (.atom "true")`.
The empty list succeeds. Improper lists, false/non-boolean predicate results,
and raised outcomes return false. Evaluation stops at the first rejection. -/
def is_proper_list (predicate : Term → Outcome Term) : Term → Outcome Term
  | .nil => .value (.atom "true")
  | .cons head tail =>
    match predicate head with
    | .value (.atom "true") => is_proper_list predicate tail
    | _ => .value (.atom "false")
  | _ => .value (.atom "false")

end Lynx.Modules.Extensions
