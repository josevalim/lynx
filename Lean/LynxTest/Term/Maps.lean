module

import Lynx
meta import LynxTest.ProofAudit
import all Lynx.Term.Compare
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

namespace LynxTest.Term.Maps
open Lynx

private def a : Term := .atom "a"
private def b : Term := .atom "b"
private def one : Term := .integer 1
private def two : Term := .integer 2
private def floatOne : Term.FiniteFloat := ⟨false, 1023, 0⟩

theorem entries_in_requested_order :
    Term.getMapKeys [b, a, b] (.map [(a, one), (b, two)]) =
      [two, one, two] := rfl

theorem entries_shadowed_key :
    Term.getMapKeys [a] (.map [(a, two), (a, one)]) = [two] := rfl

theorem entries_missing_key :
    Term.getMapKeys [a, b] (.map []) =
      [] := rfl

theorem entries_missing_later :
    Term.getMapKeys [a, b] (.map [(a, one)]) =
      [] := rfl

theorem entries_empty (entries : List (Term × Term)) :
    Term.getMapKeys [] (.map entries) = [] := rfl

theorem entries_empty_nonmap :
    Term.getMapKeys [] one = [] := rfl

theorem entries_numeric_keys :
    Term.getMapKeys [.integer 1] (.map [(.float floatOne, one)]) =
      [] := rfl

theorem entries_arity (keys : List Term) (input : Term)
    (nonempty : Term.getMapKeys keys input ≠ []) :
    (Term.getMapKeys keys input).length = keys.length :=
  Term.getMapKeys_arity keys input nonempty

end LynxTest.Term.Maps

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Maps
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Maps
