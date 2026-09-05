import Lynx

namespace LynxTest.Tactic.Contracts
open Lynx Lynx.Modules

structure Arguments where
  input : Term
  ignored : Term

def identity (args : Arguments) : Outcome Term := .value args.input
def always (_ : Arguments) : Outcome Term := .value Term.true
def unchanged (args : Arguments) (result : Term) : Outcome Term :=
  Erlang.equal result args.input

/-- Generated argument structures are unpacked before verification. -/
theorem structure_contract : Satisfies identity always unchanged := by
  lynx_verify

def addPair (args : Term × Term) : Outcome Term := Erlang.add args.1 args.2

def twoIntegers (args : Term × Term) : Outcome Term :=
  Erlang.andalso (Erlang.is_integer args.1) (fun _ => Erlang.is_integer args.2)

def numberResult (_ : Term × Term) (result : Term) : Outcome Term :=
  Erlang.is_integer result

def agrees (args : Term × Term) (result : Term) : Outcome Term := do
  let expected ← addPair args
  Erlang.equal result expected

/-- Named ensures clauses share one coverage condition. -/
theorem ensures_clauses :
    EnsuresClauses addPair twoIntegers
      [({ file := "add.ex", line := 3 }, numberResult),
       ({ file := "add.ex", line := 4 }, agrees)] := by
  lynx_verify

/-- VC generation retains source labels and exposes the original behavior. -/
theorem source_labeled_vcs :
    WithSourceLabel { file := "add.ex", line := 3 }
      (Satisfies addPair twoIntegers numberResult) := by
  lynx_vcgen
  case «add.ex:3».coverage => exact ⟨(.integer 0, .integer 0), rfl⟩
  case «add.ex:3» =>
    rename_i left right accepted
    guard_target = ∃ result, addPair (left, right) = .value result ∧
      Accepted (numberResult (left, right) result)
    lynx_solve

/-- Solving one branch does not discard sibling goals. -/
theorem sibling_goal : Satisfies identity always unchanged ∧ True := by
  constructor
  · lynx_verify
  · trivial

/-- Normalizing duplicate facts must retain a usable proof of the constraint. -/
theorem duplicate_constraints (input : Term)
    (_first _second : Accepted (Erlang.is_integer input)) :
    Accepted (Erlang.is_integer input) := by
  lynx_solve

/-- Quantified facts are applied after proving their premises. -/
theorem local_implication (p q : Prop) (step : p → q) (premise : p) : q := by
  lynx_solve

/-- Coverage still uses hypotheses when direct evaluation cannot decide it. -/
theorem assumed_coverage (expects : Term → Outcome Term)
    (accepted : Accepted (expects (.integer 0))) : Covered expects := by
  lynx_solve

/-- Match reasoning retains the executable short-circuit rules. -/
theorem andalso_short_circuit (right : Unit → Outcome Term) :
    Erlang.andalso (.value Term.false) right = .value Term.false := by
  lynx_solve

theorem andalso_raises (right : Unit → Outcome Term) (exception : Exception) :
    Erlang.andalso (.raised exception) right = .raised exception := by
  lynx_solve

theorem andalso_non_boolean (right : Unit → Outcome Term) (value : Int) :
    Erlang.andalso (.value (.integer value)) right =
      .raised (.error (.atom "badarg")) := by
  lynx_solve

/-- Acceptance eliminates the non-nil branch. -/
theorem nil_spec (input : Term)
    (accepted : Accepted (match input with
      | .nil => Outcome.value (Term.atom "true")
      | _ => .value (.atom "false"))) : input = .nil := by
  lynx_solve

/-- Splitting a computation preserves its connection to its input. -/
theorem compound_spec (input : Term) (probe : Term → Outcome Term)
    (accepted : Accepted (match probe input with
      | .value (.atom "true") => Outcome.value (Term.atom "true")
      | _ => .value (.atom "false"))) :
    probe input = .value (.atom "true") := by
  lynx_solve

end LynxTest.Tactic.Contracts
