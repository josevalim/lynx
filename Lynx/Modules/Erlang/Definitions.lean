import Lynx.Tactic
import Lynx.Term.Compare

/-! Executable Erlang operations and their generated state-independence proofs. -/

namespace Lynx.Modules.Erlang

open Lynx

#lynx_pure def is_integer_1 (input : Term) : Result :=
  .ok (match input with | .integer _ => Term.true | _ => Term.false)

/-- Expose the state-preserving callback even when passed without its argument. -/
@[simp] theorem is_integer_1_function :
    is_integer_1 = fun input => Result.ok
      (match input with | .integer _ => Term.true | _ => Term.false) := rfl

#lynx_pure def is_list_1 : Term → Result
  | .nil => .ok Term.true
  | .cons _ _ => .ok Term.true
  | _ => .ok Term.false

#lynx_pure def add_2 : Term → Term → Result
  | .integer x, .integer y => .ok (.integer (x + y))
  | _, _ => throw (.error (.atom "badarith"))

#lynx_pure def equal_2 (left right : Term) : Result :=
  .ok (if Term.compare left right = .eq then Term.true else Term.false)

#lynx_pure def less_than_2 (left right : Term) : Result :=
  .ok (if (Term.compare left right).isLT then Term.true else Term.false)

#lynx_pure def greater_than_2 (left right : Term) : Result :=
  .ok (if (Term.compare left right).isGT then Term.true else Term.false)

#lynx_pure def less_than_or_equal_2 (left right : Term) : Result :=
  .ok (if (Term.compare left right).isLE then Term.true else Term.false)

#lynx_pure def greater_than_or_equal_2 (left right : Term) : Result :=
  .ok (if (Term.compare left right).isGE then Term.true else Term.false)

#lynx_pure @[lynx_opaque] def append_2 : Term → Term → Result
  | .nil, right => .ok right
  | .cons head tail, right => do
      let rest ← append_2 tail right
      .ok (.cons head rest)
  | _, _ => throw (.error (.atom "badarg"))

@[lynx_opaque] def andalso_2
    (left : Result)
    (right : Unit → Result) : Result := fun env =>
  match left env with
  | .ok (.atom "true") next => right () next
  | .ok (.atom "false") next => .ok Term.false next
  | .ok _ next => .error (.error (.atom "badarg")) next
  | .error exception next => .error exception next

/-- Successful short-circuit conjunction records the actual intermediate state.
The right operand may return any term, not just a boolean. For acceptance goals
(`value = true`), simplification also eliminates the false-left branch. -/
@[simp low] theorem andalso_2_run_ok_iff (left : Result) (right : Unit → Result)
    (env final : Environment) (value : Term) :
    andalso_2 left right env = .ok value final ↔
      (left env = .ok (.atom "false") final ∧ value = .atom "false") ∨
      ∃ next, left env = .ok (.atom "true") next ∧
        right () next = .ok value final := by
  unfold andalso_2
  split <;> simp_all [Term.false, eq_comm, and_comm]

end Lynx.Modules.Erlang
