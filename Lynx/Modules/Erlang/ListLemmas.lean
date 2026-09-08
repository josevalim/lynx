import Lynx.Modules.Extensions

namespace Lynx.Modules.Erlang

@[simp] theorem append_nil_left (right : Term) :
    append_2 .nil right = .ok right := rfl

@[simp] theorem append_cons (head tail right : Term) :
    append_2 (.cons head tail) right =
      (append_2 tail right >>= fun rest => .ok (.cons head rest)) := rfl

/-- Appending to a proper list succeeds, with any right-hand tail. -/
theorem append_success (left right : Term)
    (accepted : Extensions.is_proper_list_1 left = .ok (.atom "true")) :
    ∃ joined, append_2 left right = .ok joined := by
  have reject : (Result.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by simp
  induction left with
  | nil => exact ⟨right, rfl⟩
  | cons head tail _ ih =>
    obtain ⟨joined, returned⟩ := ih accepted
    exact ⟨.cons head joined, by simp only [append_2, returned, Result.ok_bind]⟩
  | _ => exact False.elim (reject accepted)

@[simp] theorem append_nil (input : Term)
    (accepted : Extensions.is_proper_list_1 input = .ok (.atom "true")) :
    append_2 input .nil = .ok input := by
  have reject : (Result.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by simp
  induction input with
  | nil => rfl
  | cons head tail _ ih =>
    simp only [append_2, ih accepted, Result.ok_bind]
  | _ => exact False.elim (reject accepted)

/-- Associativity, preserving the evaluation and exception behavior of append_2. -/
theorem append_assoc (left right suffix : Term)
    (accepted : Extensions.is_proper_list_1 left = .ok (.atom "true")) :
    (append_2 left right >>= fun joined => append_2 joined suffix) =
      (append_2 right suffix >>= append_2 left) := by
  have reject : (Result.ok (.atom "false") : Result) ≠ .ok (.atom "true") := by simp
  induction left with
  | nil =>
    simp only [append_2, Result.ok_bind]
    exact (bind_pure (append_2 right suffix)).symm
  | cons head tail _ ih =>
    simpa only [append_2, bind_assoc, Result.ok_bind] using
      congrArg (fun outcome => outcome >>= fun rest => Result.ok (Term.cons head rest)) (ih accepted)
  | _ => exact False.elim (reject accepted)

end Lynx.Modules.Erlang
