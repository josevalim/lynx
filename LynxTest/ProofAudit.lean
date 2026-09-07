import LynxTest.Integration.Sum
import LynxTest.Term
import LynxTest.Integration.Reverse
import LynxTest.Modules.Erlang
import LynxTest.Tactic.Contracts
import LynxTest.Tactic.Recursive
import LynxTest.Tactic.Opaque

open Lean

/-! Reject `sorryAx` and unexpected axioms in representative integration,
library, and generated tactic proofs. -/
run_cmd do
  let theorems := #[
    ``Lynx.Modules.Erlang.append_nil_left_spec,
    ``Lynx.Modules.Erlang.append_cons_spec,
    ``LynxTest.Tactic.Opaque.missing_specification,
    ``LynxTest.Tactic.Opaque.through_wrapper,
    ``LynxTest.Tactic.Opaque.rejects_false_claim,
    ``LynxTest.Tactic.Opaque.quantified_premise,
    ``LynxTest.Tactic.Opaque.representation_equality,
    ``LynxTest.Integration.Sum.sum_satisfies_contract,
    ``LynxTest.Integration.Sum.sum_append_property,
    ``LynxTest.Integration.Reverse.reverseAux_proper_spec,
    ``LynxTest.Integration.Reverse.reverseAux_reverse_spec,
    ``LynxTest.Integration.Reverse.reverse_contract_spec,
    ``LynxTest.Integration.Reverse.reverse_involution_spec,
    ``LynxTest.Integration.Reverse.reverseAux_acc_spec,
    ``LynxTest.Integration.Reverse.reverse_append_spec,
    ``Lynx.Modules.Erlang.append_success_spec,
    ``Lynx.Modules.Erlang.append_nil_spec,
    ``Lynx.Modules.Erlang.append_assoc_spec,
    ``LynxTest.Term.decidable_results,
    ``Lynx.Term.compare_eq_spec,
    ``Lynx.Term.compare_swap_spec,
    ``Lynx.Term.compare_le_trans_spec,
    ``Lynx.Term.compare_le_total_spec,
    ``LynxTest.Modules.Erlang.ordered_terms_spec,
    ``LynxTest.Modules.Erlang.reflexive_operators_spec,
    ``LynxTest.Tactic.Contracts.structure_contract,
    ``LynxTest.Tactic.Contracts.ensures_clauses,
    ``LynxTest.Tactic.Contracts.duplicate_constraints,
    ``LynxTest.Tactic.Contracts.local_implication,
    ``LynxTest.Tactic.Contracts.assumed_coverage,
    ``LynxTest.Tactic.Contracts.andalso_short_circuit,
    ``LynxTest.Tactic.Contracts.andalso_raises,
    ``LynxTest.Tactic.Contracts.andalso_non_boolean,
    ``LynxTest.Tactic.Contracts.nil_spec,
    ``LynxTest.Tactic.Contracts.compound_spec,
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
