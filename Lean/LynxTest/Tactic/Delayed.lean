import LynxTest.ProofAudit
import Lynx

namespace LynxTest.Tactic.Delayed
open Lynx

-- These functions have no opaque annotation or hand-written simplification rules.
#lynx_pure def isCons : Term → Result
  | .cons _ _ => .ok Term.true
  | _ => .ok Term.false

#lynx_pure def first : Term → Result
  | .cons head _ => .ok head
  | _ => .error (.error (.atom "badarg"))

/-- An unknown input must eventually unfold so acceptance can constrain its shape. -/
theorem accepted_input (input : Term) (accepted : Accepted (isCons input)) :
    ∃ head tail, input = .cons head tail ∧ first input = .ok head := by
  lynx_solve

/-- Learned constructor arguments reduce an ordinary call through its equations. -/
theorem known_input (head tail : Term) : first (.cons head tail) = .ok head := by
  lynx_solve

def preserve : Term → Result
  | .integer 0 => .ok (.integer 0)
  | input => .ok input

/-- A target with unknown arguments must still expose its implementation if needed. -/
theorem unknown_target (input : Term) : preserve input = .ok input := by
  lynx_solve

#lynx_pure def isBoolean : Term → Result
  | .atom "true" => .ok Term.true
  | .atom "false" => .ok Term.true
  | _ => .ok Term.false

/-- Fallback unfolding must retain every accepting branch. -/
theorem accepting_alternatives (input : Term) (accepted : Accepted (isBoolean input)) :
    input = .atom "true" ∨ input = .atom "false" := by
  lynx_solve

/-- The smaller prover used for hypothesis premises also needs fallback unfolding. -/
theorem guarded_premise (input : Term) (accepted : Accepted (isBoolean input))
    (claim : Prop) (step : (input = .atom "true" ∨ input = .atom "false") → claim) :
    claim := by
  lynx_solve

/-- Staging cannot turn partial acceptance information into a stronger claim. -/
theorem rejects_stronger_claim : True := by
  fail_if_success
    have : ∀ input, Accepted (isBoolean input) → input = .atom "true" := by
      lynx_solve
  trivial

-- The generic policy must also preserve shared stateful computations.
def rememberFirst (input : Term) : Result := do
  let value ← first input
  let env ← get
  set (env.setPdict [(.atom "first", value)])
  Modules.Erlang.get_1 (.atom "first")

theorem stateful_continuation (head tail : Term) (env : Environment) :
    rememberFirst (.cons head tail) env =
      .ok head (env.setPdict [(.atom "first", head)]) := by
  lynx_solve

end LynxTest.Tactic.Delayed

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Tactic.Delayed
