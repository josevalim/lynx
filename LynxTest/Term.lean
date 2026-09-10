import LynxTest.ProofAudit
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

-- Constant computations distinguish success and the three Erlang exception classes.
theorem result_constructors :
    (Result.ok .nil : Result) = .ok .nil ∧
    (Result.ok .nil : Result) ≠ .error (.error .nil) ∧
    (Result.error (.error .nil) : Result) ≠ .ok .nil ∧
    (Result.error (.throw .nil) : Result) = .error (.throw .nil) ∧
    (Result.error (.error .nil) : Result) ≠ .error (.throw .nil) ∧
    (Result.error (.throw .nil) : Result) ≠ .error (.exit .nil) ∧
    (Result.error (.error (.tuple #[.atom "badkey", .nil])) : Result) ≠
      .error (.error (.tuple #[.atom "badmap", .nil])) := by simp

end LynxTest.Term

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term
  LynxTest.ProofAudit.checkModule `LynxTest.Term
  LynxTest.ProofAudit.checkModule `Lynx.Term.DataTypes
  LynxTest.ProofAudit.checkModule `Lynx.Term.Induction
