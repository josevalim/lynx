import Lynx.Contract
import Lynx.Modules.Extensions

namespace Lynx.Modules.Erlang

@[simp] theorem append_nil_left_spec (right : Term) :
    append .nil right = .value right := rfl

@[simp] theorem append_cons_spec (head tail right : Term) :
    append (.cons head tail) right =
      (append tail right >>= fun rest => .value (.cons head rest)) := rfl

/-- Appending to a proper list succeeds, with any right-hand tail. -/
theorem append_success_spec (left right : Term)
    (accepted : Extensions.is_proper_list left = .value (.atom "true")) :
    ∃ joined, append left right = .value joined := by
  have reject : ¬ Accepted (.value (.atom "false")) := by decide
  induction left with
  | nil => exact ⟨right, rfl⟩
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih =>
    obtain ⟨joined, returned⟩ := ih accepted
    exact ⟨.cons head joined, by simp only [append, returned, Outcome.bind_value_spec]⟩

@[simp] theorem append_nil_spec (input : Term)
    (accepted : Extensions.is_proper_list input = .value (.atom "true")) :
    append input .nil = .value input := by
  have reject : ¬ Accepted (.value (.atom "false")) := by decide
  induction input with
  | nil => rfl
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih =>
    simp only [append, ih accepted, Outcome.bind_value_spec]

/-- Associativity, preserving the evaluation and exception behavior of append. -/
theorem append_assoc_spec (left right suffix : Term)
    (accepted : Extensions.is_proper_list left = .value (.atom "true")) :
    (append left right >>= fun joined => append joined suffix) =
      (append right suffix >>= append left) := by
  have reject : ¬ Accepted (.value (.atom "false")) := by decide
  induction left with
  | nil => simp only [append, Outcome.bind_value_spec, Outcome.bind_value_right_spec]
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih =>
    simpa only [append, Outcome.bind_assoc_spec, Outcome.bind_value_spec] using
      congrArg (fun outcome => outcome >>= fun rest => Outcome.value (Term.cons head rest)) (ih accepted)

end Lynx.Modules.Erlang
