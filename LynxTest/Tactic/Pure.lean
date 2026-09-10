import Lynx
import LynxTest.ProofAudit

namespace LynxTest.Tactic.Pure
open Lynx

#lynx_pure def classify (input : Term) : Result :=
  .ok (match input with | .integer _ => Term.true | _ => Term.false)

/-- Purity composes through calls already checked by `#lynx_pure`. -/
#lynx_pure def classifyTwice (input : Term) : Result := do
  let first ← classify input
  classify first

/-- Unary structural recursion can be checked automatically. -/
#lynx_pure def proper : Term → Result
  | .nil => .ok Term.true
  | .cons _ tail => proper tail
  | _ => .ok Term.false

theorem execution_reuses_purity (input : Term) (env final : Environment) :
    classifyTwice input env = .ok Term.false final ↔
      classifyTwice input = .ok Term.false ∧ env = final := by
  simp

run_cmd do
  let some doc ← Lean.findSimpleDocString? (← Lean.getEnv) `LynxTest.Tactic.Pure.classifyTwice
    | throwError "classifyTwice documentation was not registered"
  unless doc.startsWith "Purity composes through calls already checked by `#lynx_pure`." do
    throwError "unexpected classifyTwice documentation: {doc}"

end LynxTest.Tactic.Pure

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Tactic.Pure
