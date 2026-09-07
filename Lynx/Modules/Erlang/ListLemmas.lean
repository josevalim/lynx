import Lynx.Modules.Extensions

namespace Lynx.Modules.Erlang

@[simp] theorem append_nil_left_spec (right : Term) :
    append .nil right = .ok right := rfl

@[simp] theorem append_cons_spec (head tail right : Term) :
    append (.cons head tail) right =
      (append tail right >>= fun rest => .ok (.cons head rest)) := rfl

/-- Appending to a proper list succeeds, with any right-hand tail. -/
theorem append_success_spec (left right : Term)
    (accepted : Extensions.is_proper_list left = .ok (.atom "true")) :
    ∃ joined, append left right = .ok joined := by
  have reject : (Except.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by decide
  induction left with
  | nil => exact ⟨right, rfl⟩
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih =>
    obtain ⟨joined, returned⟩ := ih accepted
    exact ⟨.cons head joined, by simp only [append, returned, Result.ok_bind]⟩

@[simp] theorem append_nil_spec (input : Term)
    (accepted : Extensions.is_proper_list input = .ok (.atom "true")) :
    append input .nil = .ok input := by
  have reject : (Except.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by decide
  induction input with
  | nil => rfl
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih =>
    simp only [append, ih accepted, Result.ok_bind]

/-- Associativity, preserving the evaluation and exception behavior of append. -/
theorem append_assoc_spec (left right suffix : Term)
    (accepted : Extensions.is_proper_list left = .ok (.atom "true")) :
    (append left right >>= fun joined => append joined suffix) =
      (append right suffix >>= append left) := by
  have reject : (Except.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by decide
  induction left with
  | nil =>
    simp only [append, Result.ok_bind]
    exact (bind_pure (append right suffix)).symm
  | integer _ => exact False.elim (reject accepted)
  | atom _ => exact False.elim (reject accepted)
  | cons head tail _ ih =>
    simpa only [append, bind_assoc, Result.ok_bind] using
      congrArg (fun outcome => outcome >>= fun rest => Except.ok (Term.cons head rest)) (ih accepted)

end Lynx.Modules.Erlang
