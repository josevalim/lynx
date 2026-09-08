import Lynx.Modules.Erlang.Definitions
import Lynx.Term

namespace Lynx.Modules.Extensions

/-- Traverse the outer list, accepting only a tail ending in nil.
Elements are unrestricted and are not inspected. -/
def is_proper_list_1 : Term → Result
  | .nil => .ok (.atom "true")
  | .cons _ tail => is_proper_list_1 tail
  | _ => .ok (.atom "false")

/-- A proper-list guard: every element must return exactly `.ok (.atom "true")`.
The empty list succeeds. Improper lists, false/non-boolean predicate results,
and raised outcomes return false. Evaluation stops at the first rejection. -/
def is_proper_list_2 (predicate : Term → Result) : Term → Result
  | .nil => .ok (.atom "true")
  | .cons head tail =>
    match predicate head with
    | .ok (.atom "true") => is_proper_list_2 predicate tail
    | _ => .ok (.atom "false")
  | _ => .ok (.atom "false")

private def isTrue : Result → Bool
  | .ok value => value.isTrue
  | _ => false

@[simp] private theorem isTrue_iff (result : Result) :
    isTrue result = true ↔ result = .ok (.atom "true") := by
  cases result with
  | error _ => simp [isTrue]
  | ok value => simp [isTrue, Term.true]

/-- A map guard in source argument order: map, then key/value predicate.
Only effective bindings are tested. Nonmaps, false/non-boolean predicate results,
and raised outcomes return false; the empty map succeeds. -/
@[lynx_opaque] def is_map_2 (input : Term) (predicate : Term → Term → Result) : Result :=
  let accepted : Bool := match input with
    | .map entries => Term.Map.all entries
      (fun k v => isTrue (predicate k v))
    | _ => false
  .ok (if accepted then Term.true else Term.false)

@[simp] theorem is_map_2_iff (input : Term) (predicate : Term → Term → Result) :
    is_map_2 input predicate = .ok (.atom "true") ↔
      ∃ entries, input = .map entries ∧
        Term.Map.All (fun k v => predicate k v = .ok (.atom "true")) entries := by
  cases input <;> simp [is_map_2, Term.true, Term.false]

end Lynx.Modules.Extensions
