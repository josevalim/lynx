import LynxTest.Integration.Sum
import LynxTest.Tactic.Contracts
import LynxTest.Tactic.Recursive

open Lean

/-! Reject `sorryAx` and unexpected axioms in representative generated proofs. -/
run_cmd do
  let theorems := #[
    ``LynxTest.Integration.Sum.sum_satisfies_contract,
    ``LynxTest.Integration.Sum.sum_append_property,
    ``LynxTest.Tactic.Contracts.structure_contract,
    ``LynxTest.Tactic.Contracts.ensures_clauses,
    ``LynxTest.Tactic.Contracts.duplicate_constraints,
    ``LynxTest.Tactic.Contracts.local_implication,
    ``LynxTest.Tactic.Contracts.assumed_coverage,
    ``LynxTest.Tactic.Contracts.andalso_short_circuit,
    ``LynxTest.Tactic.Contracts.andalso_raises,
    ``LynxTest.Tactic.Contracts.andalso_non_boolean,
    ``LynxTest.Tactic.Recursive.duplicate_contract,
    ``LynxTest.Tactic.Recursive.leaves_contract]
  for name in theorems do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"
  let info ← getConstInfo ``LynxTest.Integration.Sum.sum_append_property
  let some proof := info.value? (allowOpaque := true)
    | throwError "expected an ordinary theorem proof"
  if proof.getUsedConstants.contains
      ``LynxTest.Integration.Sum.sum_satisfies_contract then
    throwError "the append proof must synthesize its own implementation facts"
