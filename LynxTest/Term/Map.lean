module

public meta import LynxTest.ProofAudit
import Lynx.Term
import all Lynx.Term
import all Lynx.Term.Compare
import all Lynx.Term.Map
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control

namespace LynxTest.Term.Map
open Lynx Lynx.Term.Map

private def a : Term := .atom "a"
private def b : Term := .atom "b"

theorem empty : Term.emptyMap = .map [] := rfl

/-- Storage keeps insertion history; lookup uses the first matching key. -/
theorem shadowing :
    put a (.integer 2) [(a, .integer 1)] = [(a, .integer 2), (a, .integer 1)] ∧
    find a [(a, .integer 2), (a, .integer 1)] = some (.integer 2) ∧
    find a [(b, .nil), (a, .integer 1)] = some (.integer 1) := by
  simp [put, find, findEntry, a, b]

end LynxTest.Term.Map

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Map
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Map
