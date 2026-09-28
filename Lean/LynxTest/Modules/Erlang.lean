module

meta import LynxTest.ProofAudit
import Erlang.erlang
import LynxTest.Term.Compare
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.FiniteFloat
import all Lynx.Term.Compare
import all Lynx.Term.Runner
import all Erlang.erlang.Guards
import all Erlang.erlang.Fun
import all Erlang.erlang.Process
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

namespace LynxTest.Modules.Erlang
open Lynx
open Erlang.erlang
open LynxTest.Term.Compare (orderedTerms ordered_terms)

private def identityFun : Term.Fun
  | #[value] => .ok value
  | _ => .error (.error (.atom "unexpected_arguments"))

private def firstFun : Term.Fun
  | #[left, _] => .ok left
  | _ => .error (.error (.atom "unexpected_arguments"))

private def rememberSelf : Result := do
  let pid ← «self/0»
  let _ ← «put/2» (.atom "pid") pid
  .ok pid

private def rememberSelfFun : Term.Fun
  | #[] => rememberSelf
  | _ => .error (.error (.atom "unexpected_arguments"))

private def functions : Term.FunTable := #[identityFun, firstFun, rememberSelfFun]

private def floatOne : Term.FiniteFloat :=
  ⟨false, 1023, 0⟩

private def floatOneAndHalf : Term.FiniteFloat :=
  ⟨false, 1023, 2 ^ 51⟩

theorem nonfinite_float_results_rejected :
    Term.FiniteFloat.ofModel (Float.Model.ofBits 0x7ff0000000000000) = none ∧
    Term.FiniteFloat.ofModel (Float.Model.ofBits 0xfff0000000000000) = none ∧
    Term.FiniteFloat.ofModel (Float.Model.ofBits 0x7ff8000000000001) = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem addition_numeric_types :
    «+/2» (.integer 2) (.integer 3) = .ok (.integer 5) ∧
    «+/2» (.float floatOne) (.float floatOneAndHalf) =
      .ok (.float ⟨false, 1024, 2 ^ 50⟩) ∧
    «+/2» (.integer 1) (.float floatOneAndHalf) =
      .ok (.float ⟨false, 1024, 2 ^ 50⟩) ∧
    «+/2» (.float floatOneAndHalf) (.integer 1) =
      .ok (.float ⟨false, 1024, 2 ^ 50⟩) ∧
    «+/2» (.float floatOneAndHalf) (.integer (-2)) =
      .ok (.float ⟨true, 1022, 0⟩) := by
  repeat' first | apply And.intro | rfl

-- Halfway sums choose the even significand; rounding may carry into the exponent.
theorem addition_rounding :
    «+/2» (.float ⟨false, 1023, 0⟩) (.float ⟨false, 970, 0⟩) =
      .ok (.float ⟨false, 1023, 0⟩) ∧
    «+/2» (.float ⟨false, 1023, 1⟩) (.float ⟨false, 970, 0⟩) =
      .ok (.float ⟨false, 1023, 2⟩) ∧
    «+/2» (.float ⟨false, 1023, 2 ^ 52 - 1⟩) (.float ⟨false, 970, 0⟩) =
      .ok (.float ⟨false, 1024, 0⟩) ∧
    -- Integer conversion rounds before addition, rather than rounding the exact sum.
    «+/2» (.integer (2 ^ 53 + 1)) (.float floatOne) =
      .ok (.float ⟨false, 1076, 0⟩) ∧
    «+/2» (.float ⟨true, 1076, 0⟩) (.integer (2 ^ 53 + 1)) =
      .ok (.float ⟨false, 0, 0⟩) := by
  repeat' first | apply And.intro | rfl

theorem addition_subnormals_and_zero :
    «+/2» (.float ⟨false, 0, 1⟩) (.float ⟨false, 0, 1⟩) =
      .ok (.float ⟨false, 0, 2⟩) ∧
    «+/2» (.float ⟨false, 0, 2 ^ 52 - 1⟩) (.float ⟨false, 0, 1⟩) =
      .ok (.float ⟨false, 1, 0⟩) ∧
    «+/2» (.float ⟨false, 1, 0⟩) (.float ⟨true, 0, 2 ^ 52 - 1⟩) =
      .ok (.float ⟨false, 0, 1⟩) ∧
    «+/2» (.float ⟨true, 0, 0⟩) (.float ⟨true, 0, 0⟩) =
      .ok (.float ⟨true, 0, 0⟩) ∧
    «+/2» (.float ⟨true, 0, 0⟩) (.float ⟨false, 0, 0⟩) =
      .ok (.float ⟨false, 0, 0⟩) ∧
    «+/2» (.integer 0) (.float ⟨true, 0, 0⟩) =
      .ok (.float ⟨false, 0, 0⟩) := by
  repeat' first | apply And.intro | rfl

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 4096 in
theorem addition_overflow :
    «+/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.float ⟨false, 2046, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    «+/2» (.float ⟨true, 2046, 2 ^ 52 - 1⟩) (.float ⟨true, 2046, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    -- Rounding at the overflow boundary, and a sum just below it.
    «+/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.float ⟨false, 1993, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    «+/2» (.float ⟨false, 2046, 2 ^ 52 - 1⟩) (.float ⟨false, 1992, 0⟩) =
      .ok (.float ⟨false, 2046, 2 ^ 52 - 1⟩) ∧
    -- Conversion must fail even if exact addition would cancel the large integer.
    «+/2» (.integer (2 ^ 1024)) (.float ⟨true, 2046, 0⟩) =
      .error (.error (.atom "badarith")) ∧
    «+/2» (.float ⟨false, 2046, 0⟩) (.integer (-(2 ^ 1024))) =
      .error (.error (.atom "badarith")) := by
  repeat' first | apply And.intro | rfl

theorem addition_rejects_nonnumeric (input other : Term)
    (hi : ∀ n, input ≠ .integer n) (hf : ∀ f, input ≠ .float f) :
    «+/2» input other = .error (.error (.atom "badarith")) ∧
    «+/2» other input = .error (.error (.atom "badarith")) := by
  cases input <;> cases other <;> simp_all [«+/2»]

-- Elixir: <<>>, <<1::1>>, <<1::7>>, <<1>>, <<1, 1::1>>.
-- Partial bytes store their meaningful bits at the most significant end.
private def bitstrings : List Term := [
  .bitstring ⟨#[]⟩ 0, .bitstring ⟨#[128]⟩ 1,
  .bitstring ⟨#[2]⟩ 7, .bitstring ⟨#[1]⟩ 0,
  .bitstring ⟨#[1, 128]⟩ 1]

theorem bitstring_guards :
    bitstrings.map «is_binary/1» =
      [.ok Term.true, .ok Term.false, .ok Term.false, .ok Term.true, .ok Term.false] ∧
    bitstrings.map «is_bitstring/1» = List.replicate 5 (.ok Term.true) ∧
    bitstrings.map «bit_size/1» =
      [.ok (.integer 0), .ok (.integer 1), .ok (.integer 7),
       .ok (.integer 8), .ok (.integer 9)] ∧
    bitstrings.map «byte_size/1» =
      [.ok (.integer 0), .ok (.integer 1), .ok (.integer 1),
       .ok (.integer 1), .ok (.integer 2)] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem all_partial_byte_sizes :
    ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8)).map
      (fun bits => «bit_size/1» (.bitstring ⟨#[255, 255]⟩ bits)) =
    [16, 9, 10, 11, 12, 13, 14, 15].map (fun n => .ok (.integer n)) := rfl

theorem non_bitstrings_rejected (input : Term)
    (h : ∀ bytes bits, input ≠ .bitstring bytes bits) :
    «is_binary/1» input = .ok Term.false ∧
    «is_bitstring/1» input = .ok Term.false ∧
    «bit_size/1» input = .error (.error (.atom "badarg")) ∧
    «byte_size/1» input = .error (.error (.atom "badarg")) := by
  cases input <;> simp_all [«is_binary/1», «is_bitstring/1», «bit_size/1», «byte_size/1»]

theorem bitstring_comparison :
    -- A proper prefix sorts first; significant bits take precedence over length.
    «</2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[128]⟩ 0) = .ok Term.true ∧
    «>/2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[127]⟩ 0) = .ok Term.true ∧
    «</2» (.cons (.integer 1) .nil) (.bitstring ⟨#[]⟩ 0) = .ok Term.true ∧
    -- Padding is ignored by ordinary and exact equality.
    «==/2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[255]⟩ 1) = .ok Term.true ∧
    «=:=/2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[255]⟩ 1) = .ok Term.true ∧
    «=:=/2» (.bitstring ⟨#[128]⟩ 1) (.bitstring ⟨#[128]⟩ 2) = .ok Term.false ∧
    «=:=/2» (.map [(.bitstring ⟨#[128]⟩ 1, .integer 42)])
      (.map [(.bitstring ⟨#[255]⟩ 1, .integer 42)]) = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem empty_bitstring_ignores_count (bits : Fin 8) :
    «is_binary/1» (.bitstring ⟨#[]⟩ bits) = .ok Term.true ∧
    «bit_size/1» (.bitstring ⟨#[]⟩ bits) = .ok (.integer 0) ∧
    «byte_size/1» (.bitstring ⟨#[]⟩ bits) = .ok (.integer 0) := by
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
    «apply/2» functions (.function 0 1) (.cons (.integer 7) .nil) = .ok (.integer 7) ∧
    «apply/2» functions (.function 1 2)
      (.cons (.atom "left") (.cons (.atom "right") .nil)) = .ok (.atom "left") ∧
    «apply/2» functions (.function 0 1) (.cons (.integer 7) (.atom "improper")) =
      .error (.error (.atom "badarg")) := by
  exact ⟨rfl, rfl, rfl⟩

theorem dynamic_apply_2_errors :
    «apply/2» functions (.atom "not_a_fun") .nil =
        .error (.error (.tuple #[.atom "badfun", .atom "not_a_fun"])) ∧
    «apply/2» functions (.function 9 0) .nil =
        .error (.error (.tuple #[.atom "badfun", .function 9 0])) ∧
    «apply/2» functions (.function 0 1) .nil =
        .error (.error (.tuple #[.atom "badarity", .tuple #[.function 0 1, .nil]])) := by
  exact ⟨rfl, rfl, rfl⟩

theorem float_equality_guards :
    «is_float/1» (.float floatOneAndHalf) = .ok Term.true ∧
    «==/2» (.integer 1) (.float floatOne) = .ok Term.true ∧
    «/=/2» (.integer 1) (.float floatOne) = .ok Term.false ∧
    «=:=/2» (.integer 1) (.float floatOne) = .ok Term.false ∧
    «=/=/2» (.integer 1) (.float floatOne) = .ok Term.true := by
  simp [«is_float/1», «==/2», «/=/2», «=:=/2», «=/=/2»,
    floatOne_toRat]

theorem append_reduces (head tail right : Term) :
    «++/2» (.cons head tail) right =
      («++/2» tail right >>= fun rest => .ok (.cons head rest)) :=
  rfl

theorem ordered_operators :
    orderedTerms.Pairwise (fun a b =>
      «</2» a b = .ok (.atom "true") ∧
      «>/2» a b = .ok (.atom "false") ∧
      «=</2» a b = .ok (.atom "true") ∧
      «>=/2» a b = .ok (.atom "false") ∧
      «</2» b a = .ok (.atom "false") ∧
      «>/2» b a = .ok (.atom "true") ∧
      «=</2» b a = .ok (.atom "false") ∧
      «>=/2» b a = .ok (.atom "true")) := by
  apply List.Pairwise.imp (R := fun a b => Term.compare a b = .lt ∧ Term.compare b a = .gt)
    (fun {a b} h => ?_) ordered_terms
  simp [«</2», «>/2», «=</2», «>=/2»,
    h.1, h.2, Term.true, Term.false]

theorem reflexive_operators (a : Term) :
    «</2» a a = .ok (.atom "false") ∧
    «>/2» a a = .ok (.atom "false") ∧
    «=</2» a a = .ok (.atom "true") ∧
    «>=/2» a a = .ok (.atom "true") := by
  simp [«</2», «>/2», «=</2», «>=/2»,
    Term.true, Term.false]

/-- Callers remain in direct style even when the helper they invoke spawns. -/
private def spawnFromHelper : Result :=
  «spawn/1» functions (.function 2 0)

private def spawnCaller : Result := do
  let childPid ← spawnFromHelper
  let parentPid ← rememberSelf
  pure (.tuple #[childPid, parentPid])

theorem spawn_schedules_child_or_parent_first :
    let final : Environment := {
      pidCounter := 2
      currentProcess := { pdict := [(.atom "pid", .pid 1)] } }
    Lynx.run spawnCaller [.swap 2] =
      .ok (.tuple #[.pid 2, .pid 1]) final ∧
    Lynx.run spawnCaller [.current] =
      .ok (.tuple #[.pid 2, .pid 1]) final := by
  rw [show spawnCaller = Result.spawn rememberSelf (fun childPid => do
    let parentPid ← rememberSelf
    pure (.tuple #[.pid childPid, parentPid])) from rfl]
  cbv

private def nestedSpawnFun : Term.Fun
  | #[] => «spawn/1» functions (.function 2 0)
  | _ => .error (.error (.atom "unexpected_arguments"))

private def nestedSpawnCaller : Result :=
  «spawn/1» #[nestedSpawnFun] (.function 0 0)

theorem completed_nested_processes_are_removed :
    let final : Environment := { pidCounter := 3 }
    Lynx.run nestedSpawnCaller [.swap 2, .swap 3] =
      .ok (.pid 2) final ∧
    Lynx.run nestedSpawnCaller [.current, .current] =
      .ok (.pid 2) final := by
  rw [show nestedSpawnCaller =
    Result.spawn (Result.spawn rememberSelf (fun pid => .ok (.pid pid)))
      (fun pid => .ok (.pid pid)) from rfl]
  cbv

theorem spawn_rejects_invalid_fun :
    «spawn/1» functions (.atom "not_a_fun") = .error (.error (.atom "badarg")) ∧
    «spawn/1» functions (.function 9 0) = .error (.error (.atom "badarg")) ∧
    «spawn/1» functions (.function 0 1) = .error (.error (.atom "badarg")) := by
  exact ⟨rfl, rfl, rfl⟩

theorem tuple_equality :
    «==/2» (.tuple #[]) (.tuple #[]) = .ok Term.true ∧
    «==/2» (.tuple #[.integer 1]) (.tuple #[.integer 1, .nil]) = .ok Term.false ∧
    «==/2» (.tuple #[.integer 1, .atom "a"])
      (.tuple #[.atom "a", .integer 1]) = .ok Term.false ∧
    «==/2» (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil])
      (.tuple #[.tuple #[.nil], .cons (.atom "a") .nil]) = .ok Term.true ∧
    «==/2» (.tuple #[]) Term.emptyMap = .ok Term.false := by
  repeat' first | apply And.intro | rfl

theorem map_equality :
    «==/2» Term.emptyMap (Term.map []) = .ok Term.true ∧
    «==/2» (Term.map [(.atom "a", .integer 1), (.atom "b", .integer 2)])
      (Term.map [(.atom "b", .integer 2), (.atom "a", .integer 1)]) = .ok Term.true ∧
    «==/2» (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "a", .integer 2)]) = .ok Term.false ∧
    «==/2» (Term.map [(.atom "a", .integer 1)])
      (Term.map [(.atom "b", .integer 1)]) = .ok Term.false ∧
    «==/2» Term.emptyMap (Term.map [(.atom "a", .nil)]) = .ok Term.false ∧
    «==/2» (Term.map [(.tuple #[Term.emptyMap], .tuple #[.nil])])
      (Term.map [(.tuple #[Term.map []], .tuple #[.nil])]) = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem semantic_comparison_operators :
    let a := Term.map [(.integer 1, .nil), (.integer 0, .nil)]
    let b := Term.map [(.integer 0, .nil), (.integer 1, .nil), (.integer 1, .integer 99)]
    «==/2» a b = .ok Term.true ∧
    «</2» a b = .ok Term.false ∧
    «>/2» a b = .ok Term.false ∧
    «=</2» a b = .ok Term.true ∧
    «>=/2» a b = .ok Term.true := by
  repeat' first | apply And.intro | rfl

theorem process_dictionary_empty :
    Lynx.run «get/0» = .ok .nil {} ∧
    Lynx.run («get/1» (.atom "missing")) = .ok (.atom "undefined") {} ∧
    Lynx.run «get_keys/0» = .ok .nil {} ∧
    Lynx.run «erase/0» = .ok .nil {} := by
  repeat' first | apply And.intro | rfl

theorem process_dictionary_put_replace_erase :
    Lynx.run (do
      let missing ← «put/2» (.atom "key") (.integer 1)
      let previous ← «put/2» (.atom "key") (.integer 2)
      let found ← «get/1» (.atom "key")
      let erased ← «erase/1» (.atom "key")
      let absent ← «get/1» (.atom "key")
      Result.ok (Term.tuple #[missing, previous, found, erased, absent])) =
      .ok (Term.tuple #[.atom "undefined", .integer 1, .integer 2,
        .integer 2, .atom "undefined"]) {} := by
  rfl

theorem process_dictionary_numeric_types_are_distinct :
    Lynx.run (do
      let _ ← «put/2» (.integer 1) (.atom "integer")
      let _ ← «put/2» (.float floatOne) (.atom "float")
      let integer ← «get/1» (.integer 1)
      let float ← «get/1» (.float floatOne)
      Result.ok (Term.tuple #[integer, float])) =
      .ok (Term.tuple #[.atom "integer", .atom "float"])
        { currentProcess := { pdict :=
            [(.float floatOne, .atom "float"), (.integer 1, .atom "integer")] } } := by
  rfl

theorem process_dictionary_queries :
    let env : Environment := {
      currentProcess := { pdict := [(.atom "a", .integer 1), (.atom "b", .integer 1)] } }
    «get/0» env = .ok (.cons (.tuple #[.atom "a", .integer 1])
      (.cons (.tuple #[.atom "b", .integer 1]) .nil)) env ∧
    «get_keys/0» env = .ok (.cons (.atom "a") (.cons (.atom "b") .nil)) env ∧
    «get_keys/1» (.integer 1) env =
      .ok (.cons (.atom "a") (.cons (.atom "b") .nil)) env ∧
    «erase/0» env = .ok (.cons (.tuple #[.atom "a", .integer 1])
      (.cons (.tuple #[.atom "b", .integer 1]) .nil)) {} := by
  repeat' first | apply And.intro | rfl

end LynxTest.Modules.Erlang

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Erlang
  LynxTest.ProofAudit.checkModule `Erlang.erlang.Fun
  LynxTest.ProofAudit.checkModule `Erlang.erlang.Guards
  LynxTest.ProofAudit.checkModule `Erlang.erlang.Process
