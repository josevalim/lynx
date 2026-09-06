import Lynx

/-!
The Lean definitions below correspond to this Elixir input:

```elixir
expects is_proper_list(list, &is_integer/1)
ensures (result -> is_proper_list(result, &is_integer/1))
def duplicate([]), do: []
def duplicate([head | tail]), do: [head, head | duplicate(tail)]

expects true
ensures (result -> is_integer(result))
def leaves([head | tail]), do: leaves(head) + leaves(tail)
def leaves(_), do: 1
```
-/

namespace LynxTest.Tactic.Recursive
open Lynx Lynx.Modules

def integers (arg : Term) : Outcome Term := Extensions.is_proper_list Erlang.is_integer arg
def listResult (_arg result : Term) : Outcome Term := integers result
def integerResult (_arg result : Term) : Outcome Term := Erlang.is_integer result
def anyInput (_ : Term) : Outcome Term := .value Term.true

/-- Recursive functions may return a recursive constructor rather than a scalar. -/
def duplicate : Term → Outcome Term
  | .nil => .value .nil
  | .cons head tail => do
      let rest ← duplicate tail
      .value (.cons head (.cons head rest))
  | _ => .raised (.error (.atom "function_clause"))

theorem duplicate_contract : Satisfies duplicate integers listResult := by
  lynx_verify

/-- Independent recursive calls may descend through both constructor fields. -/
def leaves : Term → Outcome Term
  | .cons head tail => do
      let left ← leaves head
      let right ← leaves tail
      Erlang.add left right
  | _ => .value (.integer 1)

theorem leaves_contract : Satisfies leaves anyInput integerResult := by
  lynx_verify

end LynxTest.Tactic.Recursive
