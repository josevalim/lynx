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

private def termList : List Term → Term
  | [] => .nil
  | head :: tail => .cons head (termList tail)

private def pdictFind (key : Term) : List (Term × Term) → Option Term
  | [] => none
  | (stored, value) :: rest =>
      if Term.compare key stored = .eq then some value else pdictFind key rest

private def pdictRemove (key : Term) : List (Term × Term) → List (Term × Term)
  | [] => []
  | entry :: rest =>
      if Term.compare key entry.1 = .eq then pdictRemove key rest
      else entry :: pdictRemove key rest

private def undefinedOr : Option Term → Term
  | some value => value
  | none => .atom "undefined"

/-- Return all process-dictionary bindings. Their order is unspecified by Erlang. -/
def get_0 : Result := do
  let env ← get
  .ok (termList (env.pdict.map fun (key, value) => .tuple #[key, value]))

/-- Return the value stored under `key`, or `undefined`. -/
def get_1 (key : Term) : Result := do
  let env ← get
  .ok (undefinedOr (pdictFind key env.pdict))

/-- Return all process-dictionary keys. Their order is unspecified by Erlang. -/
def get_keys_0 : Result := do
  let env ← get
  .ok (termList (env.pdict.map Prod.fst))

/-- Return all keys associated with a semantically equal value. -/
def get_keys_1 (value : Term) : Result := do
  let env ← get
  .ok (termList (env.pdict.filterMap fun entry =>
    if Term.compare value entry.2 = .eq then some entry.1 else none))

/-- Store a binding and return its previous value, or `undefined`. -/
def put_2 (key value : Term) : Result := do
  let env ← get
  let previous := undefinedOr (pdictFind key env.pdict)
  set { env with pdict := (key, value) :: pdictRemove key env.pdict }
  .ok previous

/-- Return all process-dictionary bindings and clear the dictionary. -/
def erase_0 : Result := do
  let env ← get
  set { env with pdict := [] }
  .ok (termList (env.pdict.map fun (key, value) => .tuple #[key, value]))

/-- Delete `key` and return its previous value, or `undefined`. -/
def erase_1 (key : Term) : Result := do
  let env ← get
  let previous := undefinedOr (pdictFind key env.pdict)
  set { env with pdict := pdictRemove key env.pdict }
  .ok previous

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
