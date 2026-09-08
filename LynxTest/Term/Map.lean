import Lynx.Term

namespace LynxTest.Term.Map
open Lynx Lynx.Term.Map

private def a : Term := .atom "a"
private def b : Term := .atom "b"

theorem empty : Term.empty_map = .map [] := rfl

/-- Storage keeps insertion history; lookup uses the first matching key. -/
theorem shadowing :
    put a (.integer 2) [(a, .integer 1)] = [(a, .integer 2), (a, .integer 1)] ∧
    find a [(a, .integer 2), (a, .integer 1)] = some (.integer 2) ∧
    find a [(b, .nil), (a, .integer 1)] = some (.integer 1) := by
  repeat' first | apply And.intro | rfl

/-- Permutations and shadowed bindings do not affect map equality. -/
theorem semantic_equality :
    Term.Equivalent (.map [(a, .integer 1), (b, .nil)])
      (.map [(b, .nil), (a, .integer 1)]) ∧
    Term.Equivalent (.map [(a, .integer 1), (a, .integer 2)])
      (.map [(a, .integer 1)]) ∧
    ¬ Term.Equivalent (.map [(a, .integer 2), (a, .integer 1)])
      (.map [(a, .integer 1)]) := by decide

/-- Nested maps are semantic keys, including inside tuples and improper lists. -/
theorem nested_keys :
    let x := Term.map [(a, .integer 1), (b, .nil)]
    let y := Term.map [(b, .nil), (a, .integer 1), (a, .integer 99)]
    find y [(x, .integer 7), (y, .integer 8)] = some (.integer 7) ∧
    find (.tuple #[y]) [(.tuple #[x], .integer 7)] = some (.integer 7) ∧
    find (.cons y (.atom "tail")) [(.cons x (.atom "tail"), .integer 7)] = some (.integer 7) ∧
    Term.Equivalent (.map [(x, x)]) (.map [(y, y)]) := by
  repeat' first | apply And.intro | rfl

/-- Semantic BEq deliberately does not imply equality of Lean representations. -/
theorem semantic_beq :
    let x := Term.map [(a, .nil), (b, .nil)]
    let y := Term.map [(b, .nil), (a, .nil)]
    (x == y) = true ∧ x ≠ y := by
  refine ⟨rfl, ?_⟩
  simp [a, b]

end LynxTest.Term.Map
