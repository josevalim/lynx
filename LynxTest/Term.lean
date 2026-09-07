import Lynx.Term

namespace LynxTest.Term

open Lynx

example : Result = Result Lynx.Term := rfl

-- Bind can change the success type, while ordinary results default to Term.
theorem generic_result_bind :
    ((pure 7 : Result Nat) >>= fun n => (pure (.integer n) : Result)) =
      .ok (.integer 7) := rfl

theorem generic_result_catch (exception : Exception) (handler : Exception → Result Nat) :
    tryCatch (throw exception : Result Nat) handler = handler exception := rfl

-- Equality remains computable, including all three Erlang exception classes.
theorem decidable_results :
    (Result.ok .nil : Result) = .ok .nil ∧
    (Result.ok .nil : Result) ≠ .error (.error .nil) ∧
    (Result.error (.error .nil) : Result) ≠ .ok .nil ∧
    (Result.error (.throw .nil) : Result) = .error (.throw .nil) ∧
    (Result.error (.error .nil) : Result) ≠ .error (.throw .nil) ∧
    (Result.error (.throw .nil) : Result) ≠ .error (.exit .nil) := by decide

end LynxTest.Term
