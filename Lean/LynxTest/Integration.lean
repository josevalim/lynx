module

meta import LynxTest.ProofAudit
import all LynxTest.Integration.Sum
import all LynxTest.Integration.Reverse
import all LynxTest.Integration.Sets
import all LynxTest.Integration.ProcessDeadlock

/-! Integration audits are separate from the files compiled by the benchmark runner. -/
run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Sum
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Reverse
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Sets
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.ProcessDeadlock
  -- These internal examples need not export their declarations for auditing.
  let declarations ← LynxTest.ProofAudit.moduleDeclarations `LynxTest.Integration.Sets
  let targets ← #[
    `LynxTest.Integration.Sets.union_result,
    `LynxTest.Integration.Sets.union_commutative,
    `LynxTest.Integration.Sets.union_empty].mapM fun target => do
      let some name := declarations.find? (Lean.privateToUserName · == target)
        | throwError "missing integration theorem: {target}"
      pure name
  LynxTest.ProofAudit.checkIndependent targets
