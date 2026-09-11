import Lynx.Modules.Erlang.Definitions
import Lynx.Tactic

import Lynx.Term
import Lynx.Term.Map

namespace Lynx.Modules.Extensions

private def isTrue (computation : Result) : Result Bool :=
  Result.handle (computation >>= fun value => .ok value.isTrue) fun _ => .ok false

@[simp] private theorem isTrue_ok (value : Term) :
    isTrue (.ok value) = .ok value.isTrue := rfl

/-- Traverse the outer list, accepting only a tail ending in nil.
Elements are unrestricted and are not inspected. -/
#lynx_pure def is_proper_list_1 : Term → Result
  | .nil => .ok (.atom "true")
  | .cons _ tail => is_proper_list_1 tail
  | _ => .ok (.atom "false")

/-- A proper-list guard: every element must return exactly `.ok (.atom "true")`.
The empty list succeeds. Improper lists, false/non-boolean predicate results,
and raised outcomes return false. Evaluation stops at the first rejection. -/
def is_proper_list_2 (predicate : Term → Result) : Term → Result
  | .nil => .ok (.atom "true")
  | .cons head tail => do
    let accepted ← isTrue (predicate head)
    if accepted then is_proper_list_2 predicate tail else .ok (.atom "false")
  | _ => .ok (.atom "false")

@[simp] theorem is_proper_list_2_run_iff (predicate : Term → Term) (input : Term)
    (env final : Environment) :
    is_proper_list_2 (fun value => .ok (predicate value)) input env =
        .ok (.atom "true") final ↔
      is_proper_list_2 (fun value => .ok (predicate value)) input = .ok (.atom "true") ∧
        env = final := by
  induction input with
  | cons head tail _ ih =>
    by_cases h : (predicate head).isTrue = true <;> simp [is_proper_list_2, h, ih]
  | _ => simp [is_proper_list_2]

@[simp] theorem is_proper_list_2_pure (predicate : Term → Term) (input : Term) :
    Result.IsPure (is_proper_list_2 (fun value => .ok (predicate value)) input) := by
  induction input with
  | cons head tail _ ih =>
      by_cases accepted : (predicate head).isTrue = true
      · simpa [is_proper_list_2, isTrue, Result.handle, accepted] using ih
      · simp [is_proper_list_2, isTrue, Result.handle, accepted]
  | _ => simp [is_proper_list_2]

/-- A map guard in source argument order: map, then key/value predicate.
Only effective bindings are tested. Nonmaps, false/non-boolean predicate results,
and raised outcomes return false; the empty map succeeds. -/
@[lynx_opaque] def is_map_2
    (input : Term) (predicate : Term → Term → Result) : Result := do
  let accepted ← match input with
    | .map entries => Term.Map.allM entries (fun k v => isTrue (predicate k v))
    | _ => Result.ok false
  .ok (if accepted then Term.true else Term.false)

@[simp] theorem is_map_2_iff (input : Term) (predicate : Term → Term → Term) :
    is_map_2 input (fun k v => .ok (predicate k v)) = .ok (.atom "true") ↔
      ∃ entries, input = .map entries ∧
        Term.Map.All (fun k v => predicate k v = .atom "true") entries := by
  cases input <;> simp [is_map_2, Term.true, Term.false]

@[simp] theorem is_map_2_pure (input : Term) (predicate : Term → Term → Term) :
    Result.IsPure (is_map_2 input (fun k v => .ok (predicate k v))) := by
  cases input <;> simp [is_map_2, isTrue, Result.handle]

/-- Pure callbacks retain the caller's environment. Stateful callbacks use the
same implementation, but cannot use this pure specification. -/
@[simp] theorem is_map_2_run_iff (input : Term) (predicate : Term → Term → Term)
    (env final : Environment) :
    is_map_2 input (fun k v => .ok (predicate k v)) env =
        .ok (.atom "true") final ↔
      env = final ∧ ∃ entries, input = .map entries ∧
        Term.Map.All (fun k v => predicate k v = .atom "true") entries := by
  cases input <;> simp [is_map_2, Term.true, Term.false, and_comm]

end Lynx.Modules.Extensions
