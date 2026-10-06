module

meta import LynxTest.ProofAudit
import all Lynx
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.Compare
import all Lynx.Term.Runner
import all Lynx.Term.Apply
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String
import Lynx.Modules.Erlang.erlang

namespace LynxTest.Term.Try
open Lynx Erlang.erlang

theorem success_binds_multiple_values :
    Result.tryWith (.ok (7, 9) : Result (Nat × Nat))
      (fun (a, b) => .ok (.integer (a + b)))
      (fun _ => .ok (Term.atom "caught")) = .ok (.integer 16) := by rfl

theorem success_binds_no_values :
    Result.tryWith (.ok () : Result Unit)
      (fun _ => .ok (Term.atom "success"))
      (fun _ => .ok (Term.atom "caught")) = .ok (.atom "success") := by rfl

/-- All exception classes expose their class and reason to the handler. -/
theorem exception_bindings (exception : Exception) :
    Result.tryWith (.error exception : Result)
      Result.ok (fun caught => .ok (.tuple #[caught.classTerm, caught.reason])) =
      .ok (.tuple #[exception.classTerm, exception.reason]) := by simp

theorem success_body_is_outside_handler :
    Result.tryWith (.ok (.integer 7))
      (fun value => .error (.throw value)) (fun _ => .ok (Term.atom "caught")) =
      .error (.throw (.integer 7)) := by rfl

theorem handler_exception_propagates :
    Result.tryWith (.error (.error (.atom "protected")) : Result)
      Result.ok (fun _ => .error (.exit (.atom "handler"))) =
      .error (.exit (.atom "handler")) := by rfl

theorem outer_handler_catches_success_body :
    Result.tryWith
      (Result.tryWith (.ok (.integer 7))
        (fun value => .error (.throw value)) (fun _ => .ok (Term.atom "inner")))
      Result.ok (fun exception => .ok exception.reason) = .ok (.integer 7) := by rfl

/-- A handler can decline an exception without changing its class or reason. -/
theorem unmatched_handler_reraises (exception : Exception) :
    Result.tryWith (.error exception : Result) Result.ok
      (fun caught => .error (caught.withReason caught.reason)) = .error exception := by
  cases exception <;> rfl

theorem reraise_preserves_class (exception : Exception) (reason : Term) :
    (exception.withReason reason).classTerm = exception.classTerm ∧
      (exception.withReason reason).reason = reason := by
  cases exception <;> exact ⟨rfl, rfl⟩

theorem stacktrace_is_empty (exception : Exception) : exception.stacktrace = .nil := rfl

/-- State changes in the protected computation remain visible in its handler. -/
theorem protected_effects_survive_failure :
    Lynx.run (Result.tryWith (do
      let _ ← «put/2» (.atom "key") (.atom "protected")
      «throw/1» (.atom "failure"))
      Result.ok (fun exception => do
        let value ← «get/1» (.atom "key")
        pure (.tuple #[exception.classTerm, exception.reason, value]))) =
      .ok (.tuple #[.atom "throw", .atom "failure", .atom "protected"])
        { currentProcess := { pdict := [(.atom "key", .atom "protected")] } } := by cbv

private def cleanup (computation : Result) : Result :=
  Result.tryWith computation
    (fun value => do
      let _ ← «put/2» (.atom "cleanup") (.atom "done")
      pure value)
    (fun exception => do
      let _ ← «put/2» (.atom "cleanup") (.atom "done")
      .error exception)

theorem cleanup_runs_on_success_and_failure :
    Lynx.run (cleanup (.ok (.integer 7))) =
      .ok (.integer 7) { currentProcess := { pdict := [(.atom "cleanup", .atom "done")] } } ∧
    Lynx.run (cleanup (.error (.throw (.atom "failure")))) =
      .error (.throw (.atom "failure"))
        { currentProcess := { pdict := [(.atom "cleanup", .atom "done")] } } := by
  constructor <;> cbv

theorem cleanup_failure_overrides_previous_outcome :
    Result.tryWith (.ok (Term.integer 7))
      (fun _ => «exit/1» (.atom "cleanup")) (fun _ => «exit/1» (.atom "cleanup")) =
      .error (.exit (.atom "cleanup")) ∧
    Result.tryWith (.error (.throw (.atom "failure")) : Result)
      (fun _ => «exit/1» (.atom "cleanup")) (fun _ => «exit/1» (.atom "cleanup")) =
      .error (.exit (.atom "cleanup")) := by constructor <;> rfl

private def failingTable : Term.FunTable := #[
  .effectful fun _ _ => «throw/1» (.atom "dispatched")]

theorem dispatched_exception_is_caught :
    Lynx.run (Result.tryWith (Term.apply (.function 0 0 #[]) #[])
      Result.ok (fun exception => .ok exception.reason)) [] failingTable =
      .ok (.atom "dispatched") {} := by cbv

theorem dispatched_success_body_exception_escapes :
    Lynx.run (Result.tryWith (.ok Term.nil)
      (fun _ => Term.apply (.function 0 0 #[]) #[])
      (fun _ => .ok (Term.atom "caught"))) [] failingTable =
      .error (.throw (.atom "dispatched")) {} := by cbv

theorem exhaustion_is_not_caught :
    Lynx.run (Result.tryWith (Term.apply (.function 0 0 #[]) #[])
      Result.ok (fun _ => .ok (Term.atom "caught"))) [] failingTable 0 =
      .exhausted {} := by cbv

theorem blocking_is_not_caught :
    Lynx.run (Result.tryWith (Result.receive some Result.ok)
      Result.ok (fun _ => .ok (Term.atom "caught"))) = .deadlock {} := by cbv

/-- The protected handler remains installed across a receive suspension. -/
theorem resumed_receive_exception_is_caught :
    Lynx.run (Result.tryWith (do
      let _ ← Result.schedule («send/2» (.pid 1) (.integer 7))
        (fun pid => .ok (Term.pid pid))
      Result.receive some (fun value => .error (.throw value)))
      Result.ok (fun exception => .ok exception.reason)) =
      .ok (.integer 7) { pidCounter := 2 } := by cbv

end LynxTest.Term.Try

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Try
  LynxTest.ProofAudit.checkModule `Lynx.Term.Runner
  LynxTest.ProofAudit.checkModule `Lynx.Term.Apply
