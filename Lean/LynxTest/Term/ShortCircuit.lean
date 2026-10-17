module

meta import LynxTest.ProofAudit
import Lynx
import Lynx.Modules.Erlang.erlang

namespace LynxTest.Term.ShortCircuit
open Lynx

/-- A `true` left operand discards a right operand that would raise. -/
theorem orElse_short_circuits :
    Result.orElse (.ok (.atom "true")) (.error (.error (.atom "badarg"))) =
      .ok (.atom "true") := by rfl

/-- After `false`, the right operand is returned as is, even when not a Boolean. -/
theorem orElse_returns_right :
    Result.orElse (.ok (.atom "false")) (.ok (.integer 1)) = .ok (.integer 1) := by rfl

theorem orElse_rejects_non_boolean :
    Result.orElse (.ok (.integer 1)) (.ok (.atom "true")) =
      .error (.error (.tuple #[.atom "badarg", .integer 1])) := by rfl

theorem orElse_propagates_left_error (exception : Exception) (right : Result) :
    Result.orElse (.error exception) right = .error exception := by simp

/-- A `false` left operand discards a right operand that would raise. -/
theorem andAlso_short_circuits :
    Result.andAlso (.ok (.atom "false")) (.error (.error (.atom "badarg"))) =
      .ok (.atom "false") := by rfl

theorem andAlso_returns_right :
    Result.andAlso (.ok (.atom "true")) (.ok (.integer 1)) = .ok (.integer 1) := by rfl

theorem andAlso_rejects_non_boolean :
    Result.andAlso (.ok (.integer 1)) (.ok (.atom "true")) =
      .error (.error (.tuple #[.atom "badarg", .integer 1])) := by rfl

/-- Runtime requests in the left operand happen before either branch is selected. -/
theorem orElse_keeps_left_requests (next : Environment → Result) (right : Result) :
    Result.orElse (.get next) right = .get fun env => Result.orElse (next env) right := by rfl

/-- Membership compares exactly, like `=:=`: an integer does not match a float. -/
theorem isMember_exact :
    Term.isMember (.integer 1) [.float ⟨false, 1023, 0⟩, .integer 2] = .atom "false" := by simp

/-- A membership test agrees with the chain of comparisons it replaces. -/
theorem isMember_agrees_with_chain (value : Term) :
    Result.ok (Term.isMember value [.integer 1, .integer 2]) =
      Result.orElse (Erlang.erlang.«=:=/2» value (.integer 1))
        (Erlang.erlang.«=:=/2» value (.integer 2)) := by
  simp only [Term.isMember_cons, Term.isMember_nil, Result.orElse_eq, Erlang.erlang.«=:=/2»]
  split <;> split <;> simp_all

end LynxTest.Term.ShortCircuit

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.ShortCircuit
