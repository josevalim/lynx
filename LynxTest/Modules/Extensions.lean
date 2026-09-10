import LynxTest.ProofAudit
import Lynx.Modules.Extensions

namespace LynxTest.Modules.Extensions
open Lynx Lynx.Modules

example : Extensions.is_proper_list_1 .nil = .ok (.atom "true") := by rfl

-- Heads can be arbitrary terms, including improper lists themselves.
example (head : Term) :
    Extensions.is_proper_list_1 (.cons head (.cons (.cons .nil (.atom "tail")) .nil)) =
      .ok (.atom "true") := by rfl

example (n : Int) :
    Extensions.is_proper_list_1 (.integer n) = .ok (.atom "false") := by rfl

example (name : String) :
    Extensions.is_proper_list_1 (.atom name) = .ok (.atom "false") := by rfl

-- Inspect the entire outer spine, not just its first cons cell.
example (a b c : Term) :
    Extensions.is_proper_list_1 (.cons a (.cons b (.cons c (.atom "tail")))) =
      .ok (.atom "false") := by rfl

example (head : Term) (n : Int) :
    Extensions.is_proper_list_1 (.cons head (.integer n)) =
      .ok (.atom "false") := by rfl

example (predicate : Term → Result) :
    Extensions.is_proper_list_2 predicate .nil = .ok (.atom "true") := by rfl

example : Extensions.is_proper_list_2 Erlang.is_integer_1
    (.cons (.integer 1) (.cons (.integer 2) .nil)) = .ok (.atom "true") := by rfl

example (result : Term) (notTrue : result ≠ .atom "true") :
    Extensions.is_proper_list_2 (fun _ => .ok result) (.cons .nil .nil) =
      .ok (.atom "false") := by
  simp [Extensions.is_proper_list_2, Term.true, notTrue]

example (exception : Exception) :
    Extensions.is_proper_list_2 (fun _ => .error exception) (.cons .nil .nil) =
      .ok (.atom "false") := by rfl

example : Extensions.is_proper_list_2 Erlang.is_integer_1
    (.cons (.integer 1) (.integer 2)) = .ok (.atom "false") := by rfl

example (tail : Term) :
    Extensions.is_proper_list_2 (fun _ => .ok (.atom "false")) (.cons .nil tail) =
      .ok (.atom "false") := by rfl

private def bindings : Term := .map [(.integer 1, Term.nil), (.integer 2, Term.nil)]

theorem map_guard_empty (predicate : Term → Term → Result) :
    Extensions.is_map_2 Term.empty_map predicate = .ok Term.true := rfl

theorem map_guard_key_value :
    Extensions.is_map_2 bindings (fun key value =>
      Erlang.andalso_2 (Erlang.is_integer_1 key) (fun _ => Erlang.equal_2 value .nil)) =
      .ok Term.true ∧
    Extensions.is_map_2 bindings (fun key value => Erlang.equal_2 key value) =
      .ok Term.false := by
  repeat' first | apply And.intro | rfl

theorem map_guard_rejections :
    Extensions.is_map_2 bindings (fun _ _ => .ok Term.false) = .ok Term.false ∧
    Extensions.is_map_2 bindings (fun _ _ => .ok (.integer 1)) = .ok Term.false ∧
    Extensions.is_map_2 bindings (fun _ _ => .ok (.atom "yes")) = .ok Term.false ∧
    Extensions.is_map_2 .nil (fun _ _ => .ok Term.true) = .ok Term.false ∧
    Extensions.is_map_2 (.tuple #[]) (fun _ _ => .ok Term.true) = .ok Term.false ∧
    Extensions.is_map_2 (.map [(.nil, .nil), (.nil, .nil)]) (fun _ _ => .ok Term.false) =
      .ok Term.false := by
  repeat' first | apply And.intro | rfl

theorem map_guard_exception (exception : Exception) :
    Extensions.is_map_2 bindings (fun _ _ => .error exception) = .ok Term.false := rfl

/-- A rejection on the first binding makes the remaining predicate result irrelevant. -/
theorem map_guard_short_circuit (later : Result) :
    Extensions.is_map_2 bindings (fun key _ =>
      if key == .integer 1 then .ok Term.false else later) = .ok Term.false := rfl

theorem map_guard_checks_every_binding :
    Extensions.is_map_2 bindings (fun key _ => Erlang.equal_2 key (.integer 1)) =
      .ok Term.false := by
  repeat' first | apply And.intro | rfl

/-- Shadowed non-set values and exception-producing bindings are never tested. -/
theorem map_guard_shadowing :
    Extensions.is_map_2 (.map [(.nil, .nil), (.nil, .integer 1)])
      (fun _ v => Erlang.equal_2 v .nil) = .ok Term.true ∧
    Extensions.is_map_2 (.map [(.nil, .integer 1), (.nil, .nil)])
      (fun _ v => Erlang.equal_2 v .nil) = .ok Term.false ∧
    Extensions.is_map_2
      (.map [(.map [(.nil, .nil)], .nil), (.map [(.nil, .nil), (.nil, .integer 1)], .integer 1)])
      (fun _ v => if v == .nil then .ok Term.true else .error (.throw v)) = .ok Term.true := by
  repeat' first | apply And.intro | rfl

end LynxTest.Modules.Extensions

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Extensions
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Extensions
