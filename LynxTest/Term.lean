import Lynx.Term

namespace LynxTest.Term

open Lynx

-- Equality remains computable, including all three Erlang exception classes.
theorem decidable_results :
    (Except.ok .nil : Result) = .ok .nil ∧
    (Except.ok .nil : Result) ≠ .error (.error .nil) ∧
    (Except.error (.error .nil) : Result) ≠ .ok .nil ∧
    (Except.error (.throw .nil) : Result) = .error (.throw .nil) ∧
    (Except.error (.error .nil) : Result) ≠ .error (.throw .nil) ∧
    (Except.error (.throw .nil) : Result) ≠ .error (.exit .nil) := by decide

end LynxTest.Term
