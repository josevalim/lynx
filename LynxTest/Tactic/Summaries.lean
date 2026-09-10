import Lynx
import LynxTest.ProofAudit

namespace LynxTest.Tactic.Summaries
open Lynx Lynx.Modules
set_option Elab.async false

private def count : Term → Result
  | .nil => .ok (.integer 0)
  | .cons _ tail => do
    let size ← count tail
    Erlang.add_2 (.integer 1) size
  | _ => .error (.error (.atom "function_clause"))

private def properList := Extensions.is_proper_list_1
private def integerResult (_ result : Term) : Result := Erlang.is_integer_1 result
private def anyInput (_ : Term) : Result := .ok Term.true

/-- A speculative proof must not leave cache entries tied to discarded state. -/
theorem backtracking : True := by
  fail_if_success
    have : Satisfies count properList integerResult := by lynx_verify
    fail "discard the speculative proof"
  trivial

theorem count_contract : Satisfies count properList integerResult := by
  lynx_verify

/-- A later proof may reuse the same independently proved, closed summary. -/
theorem repeated_contract : Satisfies count properList integerResult := by
  lynx_verify

/-- A cached return shape cannot justify a wider domain or a stronger result. -/
theorem rejects_stronger_claims : True := by
  fail_if_success
    have : Satisfies count anyInput integerResult := by lynx_verify
  fail_if_success
    have : Satisfies count properList
        (fun _ result => Erlang.equal_2 result (.integer 0)) := by lynx_verify
  trivial

end LynxTest.Tactic.Summaries

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Tactic.Summaries
