import Lynx.Modules.Erlang

namespace Lynx.Modules.Enum

/-- Operational `Enum.all?/2`, including Elixir truthiness and improper tails. -/
def all (predicate : Term → Outcome Term) : Term → Outcome Term
  | .nil => .value Term.true
  | .cons head tail => do
      let result ← predicate head
      match result with
      | .atom "false" => .value Term.false
      | .nil => .value Term.false
      | _ => all predicate tail
  | _ => throw (.error (.atom "badarg"))

end Lynx.Modules.Enum
