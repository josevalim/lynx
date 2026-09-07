import LynxTest.Integration.Sum

namespace LynxTest.Tactic.Failures
open Lynx Lynx.Modules LynxTest.Integration.Sum

def anyInput (_ : Term) : Result := .ok Term.true
def zero (_ : Term) : Result := .ok (.integer 0)
def falseEnsures (_ _ : Term) : Result := .ok Term.false
def raises (_ : Term) : Result := .error (.error (.atom "boom"))

/--
error: unsolved goals
case «bad.ex:3»
input✝ : Term
⊢ False
-/
#guard_msgs in
theorem rejects_false_guarantee : WithSourceLabel { file := "bad.ex", line := 3 }
    (Satisfies zero anyInput falseEnsures) := by
  lynx_verify

theorem false_contract : ¬ Satisfies sumTerm sumExpects falseEnsures := by
  intro contract
  have failure := contract.2 .nil rfl
  simp [sumTerm, Accepted, falseEnsures, Term.true, Term.false] at failure

/-- error: lynx: could not prove that `expects` accepts any input; it may be empty or unsupported by automatic coverage -/
#guard_msgs in
theorem rejects_uncovered_expectation : Satisfies raises raises falseEnsures := by
  lynx_verify

def onlySpecial (input : Term) : Result := Erlang.equal_2 input (.atom "special")

-- A valid domain outside automatic candidates fails explicitly rather than vacuously.
/-- error: lynx: could not prove that `expects` accepts any input; it may be empty or unsupported by automatic coverage -/
#guard_msgs in
theorem reports_unsupported_coverage : Satisfies zero onlySpecial sumEnsures := by
  lynx_verify

/-- Lean integrations can discharge an unsupported coverage condition directly. -/
theorem manual_coverage : Satisfies zero onlySpecial sumEnsures := by
  lynx_vcgen
  case coverage => exact ⟨.atom "special", rfl⟩
  case ensures => lynx_solve

def badCall (_ : Term) : Result := do
  let result ← sumTerm (.integer 0)
  Erlang.equal_2 result (.integer 0)

-- A property may not assume the expectation of a function it calls.
/--
error: unsolved goals
case «bad.ex:20»
args✝ : Term
⊢ False
-/
#guard_msgs in
theorem rejects_unjustified_call_domain : WithSourceLabel { file := "bad.ex", line := 20 }
    (Property anyInput badCall) := by
  lynx_verify

theorem bad_call_property : ¬ Property anyInput badCall := by
  intro property
  have failure := property.2 .nil rfl
  simp [badCall, sumTerm, Accepted] at failure

end LynxTest.Tactic.Failures
