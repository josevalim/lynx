import LynxTest.ProofAudit
import LynxTest.Integration.Sum
import LynxTest.Integration.Reverse
import LynxTest.Integration.Sets
import LynxTest.Integration.ProcessDeadlock

/-! Integration audits are separate from the files compiled by the benchmark runner. -/
run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Sum
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Reverse
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Sets
  -- The expected verification failure intentionally leaves an incomplete declaration.
  LynxTest.ProofAudit.checkDeclaration
    ``LynxTest.Integration.ProcessDeadlock.run_deadlocks
  LynxTest.ProofAudit.checkDeclaration
    ``LynxTest.Integration.ProcessDeadlock.deadlock_violates_contract
  LynxTest.ProofAudit.checkNoDependencies
    ``LynxTest.Integration.Sum.sum_append_property
    #[``LynxTest.Integration.Sum.sum_satisfies_contract]
  -- These internal examples need not export their declarations for auditing.
  let declarations ← LynxTest.ProofAudit.moduleDeclarations `LynxTest.Integration.Sets
  let targets ← #[
    `LynxTest.Integration.Sets.union_satisfies_contract,
    `LynxTest.Integration.Sets.union_commutative,
    `LynxTest.Integration.Sets.union_empty].mapM fun target => do
      let some name := declarations.find? (Lean.privateToUserName · == target)
        | throwError "missing integration theorem: {target}"
      pure name
  LynxTest.ProofAudit.checkIndependent targets
