import Erlang.erlang
import LynxTest.ProofAudit
import Lynx

namespace LynxTest.Tactic.Contracts
open Lynx

structure Arguments where
  input : Term
  ignored : Term

def identity (args : Arguments) : Result := .ok args.input
def always (_ : Arguments) : Result := .ok Term.true
def unchanged (args : Arguments) (result : Term) : Result :=
  Erlang.erlang.«==/2» result args.input

/-- Generated argument structures are unpacked before verification. -/
theorem structure_contract : Satisfies identity always unchanged := by
  lynx_verify

def addPair (args : Term × Term) : Result := Erlang.erlang.«+/2» args.1 args.2

def twoIntegers (args : Term × Term) : Result := do
  match ← Erlang.erlang.«is_integer/1» args.1 with
  | .atom "true" => Erlang.erlang.«is_integer/1» args.2
  | .atom "false" => .ok Term.false
  | _ => throw (.error (.atom "badarg"))

def numberResult (_ : Term × Term) (result : Term) : Result :=
  Erlang.erlang.«is_integer/1» result

def agrees (args : Term × Term) (result : Term) : Result := do
  let expected ← addPair args
  Erlang.erlang.«==/2» result expected

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
  case «add.ex:3».coverage => exact ⟨((.integer 0, .integer 0), {}), {}, rfl⟩
  case «add.ex:3» =>
    rename_i env left right accepted
    guard_target = ∃ result final, addPair (left, right) env = .ok result final ∧
      Accepted (numberResult (left, right) result) final
    lynx_solve

/-- Solving one branch does not discard sibling goals. -/
theorem sibling_goal : Satisfies identity always unchanged ∧ True := by
  constructor
  · lynx_verify
  · trivial

/-- Normalizing duplicate facts must retain a usable proof of the constraint. -/
theorem duplicate_constraints (input : Term)
    (_first _second : Accepted (Erlang.erlang.«is_integer/1» input)) :
    Accepted (Erlang.erlang.«is_integer/1» input) := by
  lynx_solve

/-- Quantified facts are applied after proving their premises. -/
theorem local_implication (p q : Prop) (step : p → q) (premise : p) : q := by
  lynx_solve

/-- Coverage still uses hypotheses when direct evaluation cannot decide it. -/
theorem assumed_coverage (expects : Term → Result)
    (accepted : Accepted (expects (.integer 0))) : Covered expects := by
  lynx_solve

private def shortCircuit (left : Result) (right : Unit → Result) : Result := do
  match ← left with
  | .atom "true" => right ()
  | .atom "false" => .ok Term.false
  | _ => throw (.error (.atom "badarg"))

/-- Match reasoning retains the executable short-circuit rules. -/
theorem short_circuit_false (right : Unit → Result) :
    shortCircuit (.ok Term.false) right = .ok Term.false := by
  lynx_solve

theorem short_circuit_raises (right : Unit → Result) (exception : Exception) :
    shortCircuit (.error exception) right = .error exception := by
  lynx_solve

theorem short_circuit_non_boolean (right : Unit → Result) (value : Int) :
    shortCircuit (.ok (.integer value)) right =
      .error (.error (.atom "badarg")) := by
  lynx_solve

/-- Literal matches retain the left constraint and reject every unsuccessful branch.
The right computation may change state; acceptance observes its actual outcome. -/
theorem accepted_short_circuit (left right : Result) (env : Environment)
    (leftPure : Result.IsPure left)
    (accepted : Accepted (do
      match ← left with
      | .atom "true" => right
      | .atom "false" => .ok Term.false
      | _ => throw (.error (.atom "badarg"))) env) :
    left = .ok Term.true ∧ Accepted right env := by
  lynx_solve

/-- Splitting a literal match recreates the affected hypothesis; rejected
alternatives must still close when another hypothesis depends on it. -/
theorem dependent_match (input : Term)
    (accepted : Accepted (match input with
      | .atom "allowed" => Result.ok Term.true
      | .atom "denied" => .ok Term.false
      | _ => throw (.error (.atom "badarg"))))
    (predicate : (accepted = accepted) → Prop)
    (_dependent : predicate rfl) : input = .atom "allowed" := by
  lynx_solve

/-- Acceptance eliminates the non-nil branch. -/
theorem nil (input : Term)
    (accepted : Accepted (match input with
      | .nil => Result.ok (Term.atom "true")
      | _ => .ok (.atom "false"))) : input = .nil := by
  lynx_solve

/-- Splitting a computation preserves its connection to its input. -/
theorem compound (input : Term) (probe : Term → Result)
    (env : Environment)
    (pure : Result.IsPure (probe input))
    (accepted : Accepted (do
      let value ← probe input
      Erlang.erlang.«==/2» value (.atom "true")) env) :
    Accepted (probe input) env := by
  lynx_solve

end LynxTest.Tactic.Contracts

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Tactic.Contracts
