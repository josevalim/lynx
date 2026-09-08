import LynxTest.ProofAudit
import Lynx.Modules.Erlang
import LynxTest.Term.Compare

namespace LynxTest.Modules.Erlang
open Lynx
open Lynx.Modules.Erlang
open LynxTest.Term.Compare (orderedTerms ordered_terms)

theorem append_lemmas_reexported (head tail right : Term) :
    append_2 (.cons head tail) right =
      (append_2 tail right >>= fun rest => .ok (.cons head rest)) :=
  append_cons head tail right

theorem ordered_operators :
    orderedTerms.Pairwise (fun a b =>
      less_than_2 a b = .ok (.atom "true") ∧
      greater_than_2 a b = .ok (.atom "false") ∧
      less_than_or_equal_2 a b = .ok (.atom "true") ∧
      greater_than_or_equal_2 a b = .ok (.atom "false") ∧
      less_than_2 b a = .ok (.atom "false") ∧
      greater_than_2 b a = .ok (.atom "true") ∧
      less_than_or_equal_2 b a = .ok (.atom "false") ∧
      greater_than_or_equal_2 b a = .ok (.atom "true")) := by
  apply List.Pairwise.imp (R := fun a b => Term.compare a b = .lt ∧ Term.compare b a = .gt)
    (fun {a b} h => ?_) ordered_terms
  simp [less_than_2, greater_than_2, less_than_or_equal_2, greater_than_or_equal_2,
    h.1, h.2, Term.true, Term.false]

theorem reflexive_operators (a : Term) :
    less_than_2 a a = .ok (.atom "false") ∧
    greater_than_2 a a = .ok (.atom "false") ∧
    less_than_or_equal_2 a a = .ok (.atom "true") ∧
    greater_than_or_equal_2 a a = .ok (.atom "true") := by
  simp [less_than_2, greater_than_2, less_than_or_equal_2, greater_than_or_equal_2,
    Term.true, Term.false]


theorem tuple_equality :
    equal_2 (.tuple #[]) (.tuple #[]) = .ok Term.true ∧
    equal_2 (.tuple #[.integer 1]) (.tuple #[.integer 1, .nil]) = .ok Term.false ∧
    equal_2 (.tuple #[.integer 1, .atom "a"])
      (.tuple #[.atom "a", .integer 1]) = .ok Term.false ∧
    equal_2 (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil])
      (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil]) = .ok Term.true ∧
    equal_2 (.tuple #[]) Term.empty_map = .ok Term.false := by
  repeat' first | apply And.intro | rfl

theorem map_equality :
    equal_2 Term.empty_map (Term.map []) = .ok Term.true ∧
    equal_2 (Term.map [(.atom "a", .integer 1), (.atom "b", .integer 2)])
      (Term.map [(.atom "b", .integer 2), (.atom "a", .integer 1)]) = .ok Term.true ∧
    equal_2 (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "a", .integer 2)]) = .ok Term.false ∧
    equal_2 (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "b", .integer 1)]) = .ok Term.false ∧
    equal_2 Term.empty_map (Term.map [(.atom "a", .nil)]) = .ok Term.false ∧
    equal_2 (Term.map [(.tuple #[Term.empty_map], .tuple #[.nil])])
      (Term.map [(.tuple #[Term.map []], .tuple #[.nil])]) = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem semantic_comparison_operators :
    let a := Term.map [(.integer 1, .nil), (.integer 0, .nil)]
    let b := Term.map [(.integer 0, .nil), (.integer 1, .nil), (.integer 1, .integer 99)]
    equal_2 a b = .ok Term.true ∧
    less_than_2 a b = .ok Term.false ∧
    greater_than_2 a b = .ok Term.false ∧
    less_than_or_equal_2 a b = .ok Term.true ∧
    greater_than_or_equal_2 a b = .ok Term.true := by
  repeat' first | apply And.intro | rfl

end LynxTest.Modules.Erlang

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Erlang
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.Definitions
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.ListLemmas
