import Lynx

open Lean.Elab.Command
open Lynx Lynx.Modules

set_option Elab.async false

/-- Measure elaboration, including tactic execution, but not imported modules. -/
elab "#bench " label:str declaration:command : command => do
  let start ← IO.monoNanosNow
  elabCommand declaration
  Lean.logInfo m!"LYNX_BENCH {label.getString} {(← IO.monoNanosNow) - start}ns"

namespace LynxBench

def sumTerm : Term → Outcome Term
  | .nil => .value (.integer 0)
  | .cons x xs => do
      let subtotal ← sumTerm xs
      Erlang.add x subtotal
  | _ => throw (.error (.atom "function_clause"))

def sumExpects (arg : Term) : Outcome Term :=
  Extensions.is_proper_list Erlang.is_integer arg

def sumEnsures (_arg result : Term) : Outcome Term :=
  Erlang.is_integer result

def appendExpects (args : Term × Term) : Outcome Term :=
  Erlang.andalso (sumExpects args.1) (fun _ => sumExpects args.2)

def appendExpression (args : Term × Term) : Outcome Term := do
  let left ← sumTerm args.1
  let right ← sumTerm args.2
  let total ← Erlang.add left right
  let joined ← Erlang.append args.1 args.2
  let combined ← sumTerm joined
  Erlang.equal total combined

end LynxBench
