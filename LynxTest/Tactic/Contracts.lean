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

end LynxTest.Tactic.Contracts
