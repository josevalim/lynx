import LynxTest.ProofAudit
import Lynx.Term

namespace LynxTest.Term.Compare
open Lynx

-- Strictly increasing across every represented category. Tuples compare arity
-- before elements; maps compare size, all keys, then values. Includes nested
-- tuples/maps, Unicode atoms, large integers, improper tails, and list prefixes.
def orderedTerms : List Term := [
  .integer (-1000000000000000000000000000000), .integer (-1), .integer 0,
  .integer 1000000000000000000000000000000,
  .atom "", .atom "a", .atom "aa", .atom "b", .atom "é", .atom "λ", .atom "😀",
  .tuple #[],
  .tuple #[.integer (-1)], .tuple #[.integer 0], .tuple #[.atom "a"],
  .tuple #[.tuple #[]], .tuple #[Term.emptyMap], .tuple #[.nil],
  .tuple #[.integer (-100), .integer 0],
  .tuple #[.integer 0, .integer 0], .tuple #[.integer 0, .integer 1],
  .tuple #[.integer 1, .integer 0],
  Term.emptyMap,
  Term.map [(.integer 0, .integer 0)],
  Term.map [(.integer 0, .integer 1)],
  Term.map [(.integer 1, .integer (-99))],
  Term.map [(.atom "a", .nil)],
  Term.map [(.tuple #[], .nil)],
  Term.map [(Term.emptyMap, .nil)],
  Term.map [(.atom "a", .integer 99), (.atom "b", .integer 0)],
  Term.map [(.atom "a", .integer 0), (.atom "c", .integer 0)],
  Term.map [(.atom "a", .integer 0), (.atom "c", .integer 1)],
  Term.map [(.integer 0, .nil), (.integer 1, .nil), (.integer 2, .nil)],
  .nil,
  .cons (.integer (-1)) .nil,
  .cons (.integer 0) (.integer (-1)),
  .cons (.integer 0) (.atom "a"),
  .cons (.integer 0) .nil,
  .cons (.integer 0) (.cons (.integer 0) .nil),
  .cons (.integer 0) (.cons (.integer 1) .nil),
  .cons (.integer 0) (.cons (.cons (.integer 0) .nil) .nil),
  .cons (.integer 1) .nil,
  .cons (.atom "a") .nil,
  .cons .nil .nil,
  .cons (.cons (.integer 0) .nil) .nil]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem ordered_terms :
    orderedTerms.Pairwise (fun a b =>
      Term.compare a b = .lt ∧ Term.compare b a = .gt) := by decide

/-- Size counts effective keys; key comparison precedes every value comparison. -/
theorem association_list_order :
    let a := Term.atom "a"
    let b := Term.atom "b"
    let c := Term.atom "c"
    Term.compare (.map [(a, .nil), (a, .integer 99)])
      (.map [(b, .nil), (a, .nil)]) = .lt ∧
    Term.compare (.map [(b, .integer 0), (a, .integer 99)])
      (.map [(c, .integer 0), (a, .integer 0)]) = .lt ∧
    Term.compare (.map [(b, .integer 0), (a, .integer 99)])
      (.map [(a, .integer 99), (b, .integer 1)]) = .lt ∧
    Term.compare (.map [(b, .nil), (a, .integer 1), (a, .integer 99)])
      (.map [(a, .integer 1), (b, .nil)]) = .eq := by decide

/-- Comparison reaches map keys and values through every recursive constructor. -/
theorem nested_map_order :
    let x := Term.map [(.integer 1, .nil), (.integer 0, .nil)]
    let y := Term.map [(.integer 0, .nil), (.integer 1, .nil), (.integer 1, .integer 99)]
    Term.compare (.map [(x, .tuple #[.cons y x])])
      (.map [(y, .tuple #[.cons x y])]) = .eq ∧
    Term.compare (.map [(x, .integer 0), (y, .integer 99)])
      (.map [(y, .integer 1)]) = .lt := by decide

/-- Constructor rank and tuple arity decide without comparing children. -/
theorem comparison_short_circuit (a b : Term) :
    Term.compare (.integer 0) (.map [(a,b)]) = .lt ∧
    Term.compare (.tuple #[a,b]) (.tuple #[b]) = .gt ∧
    Term.compare (.map [(a,b)]) (.map []) = .gt := by
  refine ⟨Term.compare_integer_map 0 [(a,b)], ?_, Term.compare_singleton_map_empty a b⟩
  rw [Term.compare_tuple]
  rfl

/-- A decisive head/key comparison makes the tails/values irrelevant. -/
theorem comparison_keys_before_values (k l v w : Term) (h : Term.compare k l = .lt) :
    Term.compare (.cons k v) (.cons l w) = .lt ∧
    Term.compare (.map [(k,v)]) (.map [(l,w)]) = .lt := by
  simp [Term.compare_cons, Term.compare_singleton_map, h]

end LynxTest.Term.Compare

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Compare
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Compare
