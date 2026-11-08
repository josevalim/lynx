module

import Lynx.Modules.Erlang.sets
meta import LynxTest.ProofAudit

namespace LynxTest.Modules.Sets
open Lynx

private def a : Term := .atom "a"
private def b : Term := .atom "b"
private def set (elements : List Term) : Term := .map (elements.map (·, .nil))

/-- Version 2 sets combine by membership. -/
theorem membership :
    Erlang.sets.«is_element/2» a (set [a, b]) = .ok Term.true ∧
    Erlang.sets.«is_element/2» a (set [b]) = .ok Term.false ∧
    Erlang.sets.«union/2» (set [a]) (set [b]) = .ok (.map [(b, .nil), (a, .nil)]) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [set, a, b, Erlang.sets.«is_element/2», Erlang.sets.«union/2»,
    Erlang.sets.elements?, Term.mapLookup]

/-- Sizes count shadowed elements once. -/
theorem size :
    Erlang.sets.«size/1» (set [.integer 1, .integer 2, .integer 1]) = .ok (.integer 2) := by
  simp [set, Erlang.sets.«size/1», List.eraseDupsBy, List.eraseDupsBy.loop]
  rfl

/-- Sets are created as version 2 sets, whatever version the options ask for. -/
theorem creation :
    Erlang.sets.«new/1» (Term.list [.tuple #[.atom "version", .integer 1]]) = .ok (set []) ∧
    Erlang.sets.«from_list/2» (Term.list [a, b]) (Term.list [.tuple #[.atom "version", .integer 1]]) =
      .ok (set [a, b]) ∧
    Erlang.sets.«from_list/1» a = .error (.error (.atom "badarg")) := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [Erlang.sets.«from_list/2», Erlang.sets.«from_list/1»]; rfl

/-- Version 1 sets and maps holding other values are not modeled. -/
theorem unmodeled :
    Erlang.sets.«union/2» (.tuple #[.atom "set"]) (set []) = .error .exhausted ∧
    Erlang.sets.«subtract/2» (.map [(a, a)]) (set []) = .error .exhausted := by
  refine ⟨rfl, ?_⟩
  simp [Erlang.sets.«subtract/2», Erlang.sets.elements?, set, a]

end LynxTest.Modules.Sets

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.sets
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Sets
