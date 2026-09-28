module

public import Lynx.Term.DataTypes
public import Lynx.Term.Compare
public import Lynx.Term.Runner
public import Lynx.Term.Induction

namespace Lynx

/-- Run a complete process tree from a fresh runtime using the supplied
scheduler choices.
An `ok` or `error` outcome means every spawned process has finished.
`deadlock` means the modeled process tree is stuck. -/
public def run (computation : Result α) (schedule : List ScheduleChoice := []) : Outcome α :=
  computation.run { schedule }

end Lynx

namespace Lynx.Term

/-- Executable implementation of a function term. Arguments use a Lean array,
avoiding Erlang-list encoding at internal call sites. -/
public abbrev Fun := Array Term → Result

/-- Program-local function implementations indexed by `Term.function` IDs.
Each entry receives the captured values before the invocation arguments. -/
public abbrev FunTable := Array (Array Term → Fun)

/-- Adapt a lifted closure body, rejecting malformed capture or argument arrays. -/
public def FunTable.entry (captureCount arity : Nat)
    (body : Array Term → Array Term → Result) (captures arguments : Array Term) : Result :=
  if captures.size = captureCount ∧ arguments.size = arity then
    body captures arguments
  else
    .error (.error (.atom "badarg"))

@[simp↓] public theorem FunTable.entry_pure (captureCount arity : Nat)
    (body : Array Term → Array Term → Result)
    (pure : ∀ captures arguments, Result.IsPure (body captures arguments))
    (captures arguments : Array Term) :
    Result.IsPure (FunTable.entry captureCount arity body captures arguments) := by
  unfold FunTable.entry
  split <;> simp_all

/-- Resolve a function term to its implementation and declared arity. -/
@[expose] public def fetchFun (table : FunTable) : Term → Option (Fun × Nat)
  | .function id arity captures => table[id]?.map (fun implementation => (implementation captures, arity))
  | _ => none

/-- Empty Erlang map literal. -/
@[expose, simp] public def emptyMap : Term := .map []

@[expose] public def «true» : Term := .atom "true"
@[expose] public def «false» : Term := .atom "false"

/-- Recognize the Erlang boolean atom `true`. -/
@[expose] public def isTrue : Term → Bool
  | .atom name => name == "true"
  | _ => .false

/-- Recognize the Erlang boolean atom `false`. -/
@[expose] public def isFalse : Term → Bool
  | .atom name => name == "false"
  | _ => .false

/-- Recognize Erlang maps. -/
@[expose] public def isMap : Term → Bool
  | .map _ => .true
  | _ => .false

@[simp] public theorem isTrue_iff (value : Term) : isTrue value = .true ↔ value = Term.true := by
  cases value <;> simp [isTrue, Term.true]

@[simp] public theorem isFalse_iff (value : Term) : isFalse value = .true ↔ value = Term.false := by
  cases value <;> simp [isFalse, Term.false]

@[simp] public theorem isMap_iff (value : Term) :
    isMap value = .true ↔ ∃ entries, value = .map entries := by
  cases value <;> simp [isMap]

end Lynx.Term
