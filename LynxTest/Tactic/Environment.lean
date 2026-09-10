import Lynx
import LynxTest.ProofAudit

/-! Execution-state regression tests. These use Lean's state operations directly;
no Erlang process-dictionary operations are introduced by this migration. -/
namespace LynxTest.Tactic.Environment
open Lynx Lynx.Modules

private def record (key value : Term) : Result := do
  modify fun env => { env with pdict := (key, value) :: env.pdict }
  pure value

private def readFirst : Result := do
  let env ← get
  pure (match env.pdict with | (_, value) :: _ => value | [] => .atom "undefined")

theorem default_environment : Lynx.run (pure .nil : Result) = .ok .nil {} := rfl

/-- Coverage infers the actual returned state, which need not be empty. -/
theorem stateful_coverage : Covered (fun value : Term => do
    let _ ← record .nil value
    pure Term.true) := by
  lynx_solve

/-- An unchanged local outcome equation must stay active after normalization. -/
theorem known_outcome (computation : Result) (env final : Environment)
    (returned : computation env = .ok (.integer 7) final) :
    Accepted (do Erlang.equal_2 (← computation) (.integer 7)) env := by
  lynx_solve

theorem pure_preserves_environment (env : Environment) (a b : Int) :
    Erlang.add_2 (.integer a) (.integer b) env =
      .ok (.integer (a + b)) env := rfl

theorem bind_threads_state (env : Environment) (key value : Term) :
    (do let _ ← record key value; readFirst) env =
      .ok value { env with pdict := (key, value) :: env.pdict } := rfl

theorem exception_retains_state (env : Environment) (key value : Term) (exception : Exception) :
    (do let _ ← record key value; throw exception : Result) env =
      .error exception { env with pdict := (key, value) :: env.pdict } := rfl

theorem handler_sees_updated_state (env : Environment) (key value : Term) (exception : Exception) :
    (tryCatch (do let _ ← record key value; throw exception : Result)
      (fun _ => readFirst)) env =
      .ok value { env with pdict := (key, value) :: env.pdict } := rfl

theorem higher_order_threads_state (env : Environment) (a b : Term) :
    (List.mapM (fun value => do
      let before ← readFirst
      let _ ← record .nil value
      pure before) [a, b]) env =
      .ok [match env.pdict with | (_, value) :: _ => value | [] => .atom "undefined", a]
        { env with pdict := (.nil, b) :: (.nil, a) :: env.pdict } := rfl

theorem guard_callback_threads_state (env : Environment) (a b : Term) :
    (Extensions.is_proper_list_2
      (fun value => do let _ ← record .nil value; pure Term.true)
      (.cons a (.cons b .nil))) env =
      .ok Term.true { env with pdict := (.nil, b) :: (.nil, a) :: env.pdict } := rfl

theorem guard_rejection_retains_state (env : Environment) (value : Term) :
    (Extensions.is_proper_list_2
      (fun value => do let _ ← record .nil value; throw (.throw value))
      (.cons value .nil)) env =
      .ok Term.false { env with pdict := (.nil, value) :: env.pdict } := rfl

theorem map_callback_threads_state (env : Environment) :
    (Extensions.is_map_2 (.map [(.integer 1, .integer 10), (.integer 2, .integer 20)])
      (fun key value => do let _ ← record key value; pure Term.true)) env =
      .ok Term.true
        { env with pdict := (.integer 2, .integer 20) :: (.integer 1, .integer 10) :: env.pdict } := rfl

theorem short_circuit_retains_state (env : Environment) (value : Term) :
    (Erlang.andalso_2
      (do let _ ← record .nil value; pure Term.false)
      (fun _ => record .nil (.atom "unreachable"))) env =
      .ok Term.false { env with pdict := (.nil, value) :: env.pdict } := rfl

private def rememberList : Term → Result
  | .nil => pure .nil
  | .cons head tail => do
    let _ ← record .nil head
    rememberList tail
  | _ => throw (.error (.atom "function_clause"))

/-- Recursive hypotheses must apply to the updated, not just initial, state. -/
theorem stateful_recursive_contract : Satisfies rememberList Extensions.is_proper_list_1
    (fun _ result => Erlang.equal_2 result .nil) := by
  lynx_verify

private def anyInput (_ : Term) : Result := pure Term.true

/-- Abstracting short-circuit guards must not restrict the right result to booleans. -/
theorem short_circuit_nonboolean_contract :
    Satisfies (fun value => Erlang.andalso_2 (.ok Term.true) (fun _ => record .nil value))
      anyInput (fun input result => Erlang.equal_2 input result) := by
  lynx_verify

private def remember (value : Term) : Result := record .nil value
private def remembered (_input result : Term) : Result := do
  Erlang.equal_2 (← readFirst) result

/-- Guarantees observe the environment returned by the implementation. -/
theorem stateful_contract : Satisfies remember anyInput remembered := by
  lynx_verify

/-- Expectations observe a snapshot; their effects do not initialize the function. -/
private def snapshotExpects (input : Term) : Result := do
  let accepted ← Erlang.equal_2 input (← readFirst)
  let _ ← record .nil (.atom "expectation")
  pure accepted

theorem expectation_snapshot : Satisfies (fun _ => readFirst) snapshotExpects
    (fun input result => Erlang.equal_2 input result) := by
  lynx_vcgen
  case coverage =>
    exact ⟨(.atom "undefined", {}), { pdict := [(.nil, .atom "expectation")] }, rfl⟩
  case ensures => lynx_solve

/-- A computation that happens to work from empty state is not enough. -/
theorem checks_nonempty_initial_state :
    ¬ Satisfies (fun _ => readFirst) anyInput
      (fun _ result => Erlang.equal_2 result (.atom "undefined")) := by
  intro contract
  have failed := contract.2 .nil { pdict := [(.nil, .integer 7)] }
    ⟨{ pdict := [(.nil, .integer 7)] }, rfl⟩
  simp [Accepted, readFirst, Erlang.equal_2, Pure.pure, EStateM.pure, Term.true, Term.false] at failed

theorem observes_state_in_property : Property anyInput (fun input => do
    let _ ← remember input
    remembered input input) := by
  lynx_verify

end LynxTest.Tactic.Environment

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Tactic.Environment
