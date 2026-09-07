import Lynx.Modules.Erlang

namespace LynxTest.Modules.Erlang
open Lynx
open Lynx.Modules.Erlang

theorem append_lemmas_reexported (head tail right : Term) :
    append_2 (.cons head tail) right =
      (append_2 tail right >>= fun rest => .ok (.cons head rest)) :=
  append_cons head tail right

-- Strictly increasing in Erlang term order. Includes Unicode atoms, large
-- integers, improper tails, prefixes, and nested lists.
def orderedTerms : List Term := [
  .integer (-1000000000000000000000000000000), .integer (-1), .integer 0,
  .integer 1000000000000000000000000000000,
  .atom "", .atom "a", .atom "aa", .atom "b", .atom "é", .atom "λ", .atom "😀",
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

theorem ordered_terms :
    orderedTerms.Pairwise (fun a b =>
      Term.compare a b = .lt ∧ Term.compare b a = .gt ∧
      less_than_2 a b = .ok (.atom "true") ∧
      greater_than_2 a b = .ok (.atom "false") ∧
      less_than_or_equal_2 a b = .ok (.atom "true") ∧
      greater_than_or_equal_2 a b = .ok (.atom "false") ∧
      less_than_2 b a = .ok (.atom "false") ∧
      greater_than_2 b a = .ok (.atom "true") ∧
      less_than_or_equal_2 b a = .ok (.atom "false") ∧
      greater_than_or_equal_2 b a = .ok (.atom "true")) := by decide

theorem reflexive_operators (a : Term) :
    less_than_2 a a = .ok (.atom "false") ∧
    greater_than_2 a a = .ok (.atom "false") ∧
    less_than_or_equal_2 a a = .ok (.atom "true") ∧
    greater_than_or_equal_2 a a = .ok (.atom "true") := by
  have self := (Term.compare_eq a a).mpr rfl
  simp [less_than_2, greater_than_2, less_than_or_equal_2, greater_than_or_equal_2, self,
    Term.true, Term.false]


end LynxTest.Modules.Erlang
