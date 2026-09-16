module

meta import LynxTest.ProofAudit
import Lynx.Modules.Erlang
import LynxTest.Term.Compare
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.FiniteFloat
import all Lynx.Term.Compare
import all Lynx.Term.Runner
import all Lynx.Modules.Erlang.Fun
import all Lynx.Modules.Erlang.Process
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

namespace LynxTest.Modules.Erlang
open Lynx
open Lynx.Modules.Erlang
open LynxTest.Term.Compare (orderedTerms ordered_terms)

private def identityFun : Term.Fun
  | #[value] => .ok value
  | _ => .error (.error (.atom "unexpected_arguments"))

private def firstFun : Term.Fun
  | #[left, _] => .ok left
  | _ => .error (.error (.atom "unexpected_arguments"))

private def rememberSelf : Result := do
  let pid ← self_0
  let _ ← put_2 (.atom "pid") pid
  .ok pid

private def rememberSelfFun : Term.Fun
  | #[] => rememberSelf
  | _ => .error (.error (.atom "unexpected_arguments"))

private def functions : Term.FunTable := #[identityFun, firstFun, rememberSelfFun]

private def floatOne : Term.FiniteFloat :=
  ⟨false, 1023, 0⟩

private def floatOneAndHalf : Term.FiniteFloat :=
  ⟨false, 1023, 2 ^ 51⟩

-- Elixir: <<>>, <<1::1>>, <<1::7>>, <<1>>, <<1, 1::1>>.
-- Partial bytes store their meaningful bits at the most significant end.
private def bitstrings : List Term := [
  .bitstring ⟨#[]⟩ 0, .bitstring ⟨#[128]⟩ 1,
  .bitstring ⟨#[2]⟩ 7, .bitstring ⟨#[1]⟩ 0,
  .bitstring ⟨#[1, 128]⟩ 1]

theorem bitstring_guards :
    bitstrings.map is_binary_1 =
      [.ok Term.true, .ok Term.false, .ok Term.false, .ok Term.true, .ok Term.false] ∧
    bitstrings.map is_bitstring_1 = List.replicate 5 (.ok Term.true) ∧
    bitstrings.map bit_size_1 =
      [.ok (.integer 0), .ok (.integer 1), .ok (.integer 7),
       .ok (.integer 8), .ok (.integer 9)] ∧
    bitstrings.map byte_size_1 =
      [.ok (.integer 0), .ok (.integer 1), .ok (.integer 1),
       .ok (.integer 1), .ok (.integer 2)] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem all_partial_byte_sizes :
    ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8)).map
      (fun bits => bit_size_1 (.bitstring ⟨#[255, 255]⟩ bits)) =
    [16, 9, 10, 11, 12, 13, 14, 15].map (fun n => .ok (.integer n)) := rfl

theorem non_bitstrings_rejected (input : Term)
    (h : ∀ bytes bits, input ≠ .bitstring bytes bits) :
    is_binary_1 input = .ok Term.false ∧
    is_bitstring_1 input = .ok Term.false ∧
    bit_size_1 input = .error (.error (.atom "badarg")) ∧
    byte_size_1 input = .error (.error (.atom "badarg")) := by
  cases input <;> simp_all [is_binary_1, is_bitstring_1, bit_size_1, byte_size_1]

theorem bitstring_comparison :
    -- A proper prefix sorts first; significant bits take precedence over length.
    less_than_2 (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[128]⟩ 0) = .ok Term.true ∧
    greater_than_2 (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[127]⟩ 0) = .ok Term.true ∧
    less_than_2 (.cons (.integer 1) .nil) (.bitstring ⟨#[]⟩ 0) = .ok Term.true ∧
    -- Padding is ignored by ordinary and exact equality.
    equal_2 (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[255]⟩ 1) = .ok Term.true ∧
    exact_equal_2 (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[255]⟩ 1) = .ok Term.true ∧
    exact_equal_2 (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[128]⟩ 2) = .ok Term.false ∧
    exact_equal_2 (.map [(.bitstring ⟨#[128]⟩ 1, .integer 42)])
      (.map [(.bitstring ⟨#[255]⟩ 1, .integer 42)]) = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem empty_bitstring_ignores_count (bits : Fin 8) :
    is_binary_1 (.bitstring ⟨#[]⟩ bits) = .ok Term.true ∧
    bit_size_1 (.bitstring ⟨#[]⟩ bits) = .ok (.integer 0) ∧
    byte_size_1 (.bitstring ⟨#[]⟩ bits) = .ok (.integer 0) := by
  exact ⟨rfl, rfl, rfl⟩

private theorem floatOne_toRat : floatOne.toRat = 1 := by
  simp [floatOne, Term.FiniteFloat.toRat, Term.FiniteFloat.magnitude]
  change (4503599627370496 : Rat) * 2 ^ (-52 : Int) = 1
  rw [show (-52 : Int) = -(52 : Int) by rfl, Rat.zpow_neg]
  change (2 : Rat) ^ (52 : Nat) * ((2 : Rat) ^ (52 : Nat))⁻¹ = 1
  exact Rat.mul_inv_cancel _ (by decide)

theorem fetch_fun :
    (Term.fetchFun functions (.function 0 1)).map Prod.snd = some 1 ∧
    Term.fetchFun functions (.function 3 0) = none ∧
    Term.fetchFun functions .nil = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem dynamic_apply_2 :
    apply_2 functions (.function 0 1) (.cons (.integer 7) .nil) = .ok (.integer 7) ∧
    apply_2 functions (.function 1 2)
      (.cons (.atom "left") (.cons (.atom "right") .nil)) = .ok (.atom "left") ∧
    apply_2 functions (.function 0 1) (.cons (.integer 7) (.atom "improper")) =
      .error (.error (.atom "badarg")) := by
  exact ⟨rfl, rfl, rfl⟩

theorem dynamic_apply_2_errors :
    apply_2 functions (.atom "not_a_fun") .nil =
        .error (.error (.tuple #[.atom "badfun", .atom "not_a_fun"])) ∧
    apply_2 functions (.function 9 0) .nil =
        .error (.error (.tuple #[.atom "badfun", .function 9 0])) ∧
    apply_2 functions (.function 0 1) .nil =
        .error (.error (.tuple #[.atom "badarity", .tuple #[.function 0 1, .nil]])) := by
  exact ⟨rfl, rfl, rfl⟩

theorem float_equality_guards :
    is_float_1 (.float floatOneAndHalf) = .ok Term.true ∧
    equal_2 (.integer 1) (.float floatOne) = .ok Term.true ∧
    not_equal_2 (.integer 1) (.float floatOne) = .ok Term.false ∧
    exact_equal_2 (.integer 1) (.float floatOne) = .ok Term.false ∧
    exact_not_equal_2 (.integer 1) (.float floatOne) = .ok Term.true := by
  simp [is_float_1, equal_2, not_equal_2, exact_equal_2, exact_not_equal_2,
    floatOne_toRat]

theorem append_reduces (head tail right : Term) :
    append_2 (.cons head tail) right =
      (append_2 tail right >>= fun rest => .ok (.cons head rest)) :=
  rfl

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

/-- Callers remain in direct style even when the helper they invoke spawns. -/
private def spawnFromHelper : Result :=
  spawn_1 functions (.function 2 0)

private def spawnCaller : Result := do
  let childPid ← spawnFromHelper
  let parentPid ← rememberSelf
  pure (.tuple #[childPid, parentPid])

theorem spawn_schedules_child_or_parent_first :
    let final : Environment := {
      pidCounter := 2
      currentProcess := { pdict := [(.atom "pid", .pid 1)] } }
    Lynx.run spawnCaller [.spawned] =
      .ok (.tuple #[.pid 2, .pid 1]) final ∧
    Lynx.run spawnCaller [.current] =
      .ok (.tuple #[.pid 2, .pid 1]) final := by
  exact ⟨rfl, rfl⟩

private def nestedSpawnFun : Term.Fun
  | #[] => spawn_1 functions (.function 2 0)
  | _ => .error (.error (.atom "unexpected_arguments"))

private def nestedSpawnCaller : Result :=
  spawn_1 #[nestedSpawnFun] (.function 0 0)

theorem completed_nested_processes_are_removed :
    let final : Environment := { pidCounter := 3 }
    Lynx.run nestedSpawnCaller [.spawned, .spawned] =
      .ok (.pid 2) final ∧
    Lynx.run nestedSpawnCaller [.current, .current] =
      .ok (.pid 2) final := by
  exact ⟨rfl, rfl⟩

theorem spawn_rejects_invalid_fun :
    spawn_1 functions (.atom "not_a_fun") = .error (.error (.atom "badarg")) ∧
    spawn_1 functions (.function 9 0) = .error (.error (.atom "badarg")) ∧
    spawn_1 functions (.function 0 1) = .error (.error (.atom "badarg")) := by
  exact ⟨rfl, rfl, rfl⟩

theorem tuple_equality :
    equal_2 (.tuple #[]) (.tuple #[]) = .ok Term.true ∧
    equal_2 (.tuple #[.integer 1]) (.tuple #[.integer 1, .nil]) = .ok Term.false ∧
    equal_2 (.tuple #[.integer 1, .atom "a"])
      (.tuple #[.atom "a", .integer 1]) = .ok Term.false ∧
    equal_2 (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil])
      (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil]) = .ok Term.true ∧
    equal_2 (.tuple #[]) Term.emptyMap = .ok Term.false := by
  repeat' first | apply And.intro | rfl

theorem map_equality :
    equal_2 Term.emptyMap (Term.map []) = .ok Term.true ∧
    equal_2 (Term.map [(.atom "a", .integer 1), (.atom "b", .integer 2)])
      (Term.map [(.atom "b", .integer 2), (.atom "a", .integer 1)]) = .ok Term.true ∧
    equal_2 (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "a", .integer 2)]) = .ok Term.false ∧
    equal_2 (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "b", .integer 1)]) = .ok Term.false ∧
    equal_2 Term.emptyMap (Term.map [(.atom "a", .nil)]) = .ok Term.false ∧
    equal_2 (Term.map [(.tuple #[Term.emptyMap], .tuple #[.nil])])
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

theorem process_dictionary_empty :
    Lynx.run get_0 = .ok .nil {} ∧
    Lynx.run (get_1 (.atom "missing")) = .ok (.atom "undefined") {} ∧
    Lynx.run get_keys_0 = .ok .nil {} ∧
    Lynx.run erase_0 = .ok .nil {} := by
  repeat' first | apply And.intro | rfl

theorem process_dictionary_put_replace_erase :
    Lynx.run (do
      let missing ← put_2 (.atom "key") (.integer 1)
      let previous ← put_2 (.atom "key") (.integer 2)
      let found ← get_1 (.atom "key")
      let erased ← erase_1 (.atom "key")
      let absent ← get_1 (.atom "key")
      Result.ok (Term.tuple #[missing, previous, found, erased, absent])) =
      .ok (Term.tuple #[.atom "undefined", .integer 1, .integer 2,
        .integer 2, .atom "undefined"]) {} := by
  rfl

theorem process_dictionary_numeric_types_are_distinct :
    Lynx.run (do
      let _ ← put_2 (.integer 1) (.atom "integer")
      let _ ← put_2 (.float floatOne) (.atom "float")
      let integer ← get_1 (.integer 1)
      let float ← get_1 (.float floatOne)
      Result.ok (Term.tuple #[integer, float])) =
      .ok (Term.tuple #[.atom "integer", .atom "float"])
        { currentProcess := { pdict :=
            [(.float floatOne, .atom "float"), (.integer 1, .atom "integer")] } } := by
  rfl

theorem process_dictionary_queries :
    let env : Environment := {
      currentProcess := { pdict := [(.atom "a", .integer 1), (.atom "b", .integer 1)] } }
    get_0 env = .ok (.cons (.tuple #[.atom "a", .integer 1])
      (.cons (.tuple #[.atom "b", .integer 1]) .nil)) env ∧
    get_keys_0 env = .ok (.cons (.atom "a") (.cons (.atom "b") .nil)) env ∧
    get_keys_1 (.integer 1) env =
      .ok (.cons (.atom "a") (.cons (.atom "b") .nil)) env ∧
    erase_0 env = .ok (.cons (.tuple #[.atom "a", .integer 1])
      (.cons (.tuple #[.atom "b", .integer 1]) .nil)) {} := by
  repeat' first | apply And.intro | rfl

end LynxTest.Modules.Erlang

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Erlang
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.Fun
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.Guards
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.Process
