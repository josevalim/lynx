import LynxTest.Integration.Sum
import LynxTest.Integration.Sets
import LynxTest.Modules.Maps
import LynxTest.Modules.Extensions
import LynxTest.Term
import LynxTest.Term.Map
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
    ``LynxTest.Integration.Reverse.reverse_aux_proper,
    ``LynxTest.Integration.Reverse.reverse_aux_reverse,
    ``LynxTest.Integration.Reverse.reverse_contract,
    ``LynxTest.Integration.Reverse.reverse_involution,
    ``LynxTest.Integration.Reverse.reverse_aux_acc,
    ``LynxTest.Integration.Reverse.reverse_append,
    ``Lynx.Modules.Erlang.append_success,
    ``Lynx.Modules.Erlang.append_nil,
    ``Lynx.Modules.Erlang.append_assoc,
    ``Lynx.instEquivBEqTerm,
    ``Lynx.instLawfulMonadResult,
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

/- Audit term, map, guard, and regression theorems as a group.
Sets targets must synthesize their proofs without reusing each other. -/
run_cmd do
  let env ← getEnv
  let prefixes := #["Lynx.Term.", "Lynx.Modules.Maps.", "Lynx.Modules.Extensions.",
    "LynxTest.Term.", "LynxTest.Modules.Erlang.", "LynxTest.Integration.Sets.", "LynxTest.Modules.Maps.", "LynxTest.Modules.Extensions."]
  for (name, info) in env.constants.toList do
    unless prefixes.any (name.toString.startsWith ·) do continue
    let .thmInfo theoremInfo := info | continue
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"
    if name.toString.startsWith "LynxTest.Integration.Sets." then
      for dependency in theoremInfo.value.getUsedConstants do
        if dependency.toString.startsWith "LynxTest.Integration.Sets." then
          if let some (.thmInfo _) := env.find? dependency then
            throwError "integration target {name} reused target {dependency}"
