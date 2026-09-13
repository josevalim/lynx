import Lynx.Term
import Lynx.Tactic

/-! Stateless Erlang operators and their generated purity proofs. -/

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

@[simp] theorem append_nil_left (right : Term) :
    append_2 .nil right = .ok right := rfl

@[simp] theorem append_cons (head tail right : Term) :
    append_2 (.cons head tail) right =
      (append_2 tail right >>= fun rest => .ok (.cons head rest)) := rfl

@[lynx_opaque] def andalso_2
    (left : Result)
    (right : Unit → Result) : Result := do
  match ← left with
  | .atom "true" => right ()
  | .atom "false" => .ok Term.false
  | _ => .error (.error (.atom "badarg"))

/-- Successful short-circuit conjunction records the actual intermediate state.
The right operand may return any term, not just a boolean. For acceptance goals
(`value = true`), simplification also eliminates the false-left branch. -/
@[simp low] theorem andalso_2_run_ok_iff (left : Result) (right : Unit → Result)
    (env final : Environment) (value : Term) (pure : Result.IsPure left) :
    andalso_2 left right env = .ok value final ↔
      (left env = .ok (.atom "false") final ∧ value = .atom "false") ∨
      ∃ next, left env = .ok (.atom "true") next ∧
        right () next = .ok value final := by
  unfold andalso_2
  cases left <;> simp_all [Result.IsPure, Term.false, eq_comm, and_comm]
  split <;> simp_all [eq_comm, and_comm]

@[simp low] theorem andalso_2_ok_iff (left : Result) (right : Unit → Result)
    (value : Term) :
    andalso_2 left right = .ok value ↔
      (left = .ok (.atom "false") ∧ value = .atom "false") ∨
      (left = .ok (.atom "true") ∧ right () = .ok value) := by
  cases left <;> simp_all [andalso_2, Term.false, eq_comm, and_comm]
  split <;> simp_all [eq_comm, and_comm]

@[simp] theorem andalso_2_pure (left : Result) (right : Unit → Result)
    (leftPure : Result.IsPure left) (rightPure : Result.IsPure (right ())) :
    Result.IsPure (andalso_2 left right) := by
  unfold andalso_2
  apply Result.IsPure.bind left _ leftPure
  intro value
  cases value <;> simp [Result.IsPure]
  rename_i name
  by_cases isTrue : name = "true"
  · subst name; exact rightPure
  · by_cases isFalse : name = "false"
    · subst name; simp
    · simp [isTrue, isFalse]

end Lynx.Modules.Erlang
