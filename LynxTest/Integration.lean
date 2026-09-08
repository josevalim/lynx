import LynxTest.ProofAudit
import LynxTest.Integration.Sum
import LynxTest.Integration.Reverse
import LynxTest.Integration.Sets

/-! Integration audits are separate from the files compiled by the benchmark runner. -/
run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Sum
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Reverse
  LynxTest.ProofAudit.checkModule `LynxTest.Integration.Sets
  LynxTest.ProofAudit.checkNoDependencies
    ``LynxTest.Integration.Sum.sum_append_property
    #[``LynxTest.Integration.Sum.sum_satisfies_contract]
  LynxTest.ProofAudit.checkIndependent #[
    ``LynxTest.Integration.Sets.union_satisfies_contract,
    ``LynxTest.Integration.Sets.union_commutative,
    ``LynxTest.Integration.Sets.union_empty]
