module

public import Lynx.Term.DataTypes
public import Lynx.Term.Compare
import all Lynx.Term.Induction

namespace Lynx.Term

/-- Empty Erlang map literal. -/
@[expose] public def emptyMap : Term := .map []

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

@[simp] public theorem isTrue_iff (value : Term) : isTrue value = .true ↔ value = Term.true := by
  cases value <;> simp [isTrue, Term.true]

@[simp] public theorem isFalse_iff (value : Term) : isFalse value = .true ↔ value = Term.false := by
  cases value <;> simp [isFalse, Term.false]

end Lynx.Term
