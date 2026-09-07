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
    ``Lynx.Modules.Erlang.append_nil_left,
    ``Lynx.Modules.Erlang.append_cons,
    ``LynxTest.Tactic.Opaque.missing_specification,
    ``LynxTest.Tactic.Opaque.through_wrapper,
    ``LynxTest.Tactic.Opaque.rejects_false_claim,
    ``LynxTest.Tactic.Opaque.quantified_premise,
    ``LynxTest.Tactic.Opaque.representation_equality,
    ``LynxTest.Integration.Sum.sum_satisfies_contract,
    ``LynxTest.Integration.Sum.sum_append_property,
    ``LynxTest.Integration.Reverse.reverseAux_proper,
    ``LynxTest.Integration.Reverse.reverseAux_reverse,
    ``LynxTest.Integration.Reverse.reverse_contract,
    ``LynxTest.Integration.Reverse.reverse_involution,
    ``LynxTest.Integration.Reverse.reverseAux_acc,
    ``LynxTest.Integration.Reverse.reverse_append,
    ``Lynx.Modules.Erlang.append_success,
    ``Lynx.Modules.Erlang.append_nil,
    ``Lynx.Modules.Erlang.append_assoc,
    ``LynxTest.Term.decidable_results,
    ``Lynx.Term.compare_eq,
    ``Lynx.Term.compare_swap,
    ``Lynx.Term.compare_le_trans,
    ``Lynx.Term.compare_le_total,
    ``LynxTest.Modules.Erlang.ordered_terms,
    ``LynxTest.Modules.Erlang.reflexive_operators,
    ``LynxTest.Tactic.Contracts.structure_contract,
    ``LynxTest.Tactic.Contracts.ensures_clauses,
    ``LynxTest.Tactic.Contracts.duplicate_constraints,
    ``LynxTest.Tactic.Contracts.local_implication,
    ``LynxTest.Tactic.Contracts.assumed_coverage,
    ``LynxTest.Tactic.Contracts.andalso_short_circuit,
    ``LynxTest.Tactic.Contracts.andalso_raises,
    ``LynxTest.Tactic.Contracts.andalso_non_boolean,
    ``LynxTest.Tactic.Contracts.nil,
    ``LynxTest.Tactic.Contracts.compound,
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
