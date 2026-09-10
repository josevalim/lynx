import Lynx.Term.DataTypes
import Lynx.Term.Induction
import Lynx.Term.Compare
import Lynx.Term.Map

namespace Lynx.Term

/-- Empty Erlang map literal. -/
def emptyMap : Term := .map []

def «true» : Term := .atom "true"
def «false» : Term := .atom "false"

/-- Recognize the Erlang boolean atom `true`. -/
def isTrue : Term → Bool
  | .atom name => name == "true"
  | _ => .false

/-- Recognize the Erlang boolean atom `false`. -/
def isFalse : Term → Bool
  | .atom name => name == "false"
  | _ => .false

@[simp] theorem isTrue_iff (value : Term) : isTrue value = .true ↔ value = Term.true := by
  cases value <;> simp [isTrue, Term.true]

@[simp] theorem isFalse_iff (value : Term) : isFalse value = .true ↔ value = Term.false := by
  cases value <;> simp [isFalse, Term.false]

end Lynx.Term
