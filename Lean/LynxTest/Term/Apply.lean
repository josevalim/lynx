module

meta import LynxTest.ProofAudit
import Lynx
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.Apply
import all Lynx.Term.Runner

namespace LynxTest.Term.Apply
open Lynx

private def call (id : Nat) (args : Array Term := #[]) : Result :=
  .apply (.function id args.size #[]) args fun
    | .ok value => .ok value
    | .error exception => .error exception

private def countdown : Term.FunTable := #[.effectful fun _ (args : Array Term) =>
  match args[0]? with
  | some (Term.integer n) =>
      if n ≤ 0 then .ok (.integer 0) else call 0 #[.integer (n - 1)]
  | _ => .error (.error (.atom "badarg"))]

/-- A recursive table requires no recursive Lean definition or cyclic import. -/
theorem recursive_dispatch :
    (call 0 #[.integer 3]).runWith countdown 4 {} = .ok (.integer 0) {} ∧
    (call 0 #[.integer 3]).runWith countdown 3 {} = .exhausted {} := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

private def constant : Term.FunTable := #[.effectful fun _ _ => .ok (.integer 7)]

private def pureFunctions : Term.FunTable := #[
  .pure fun captures arguments =>
    match captures.toList, arguments.toList with
    | [.integer captured], [.integer argument] => .ok (.integer (captured + argument))
    | _, _ => .error (.throw (.atom "bad_input")),
  .effectful fun _ _ => .get fun env => .ok (.pid env.currentPid)
]

/-- Ordinary application dispatches pure closures, including captures and exceptions. -/
theorem pure_calls :
    (Term.apply (.function 0 1 #[.integer 10]) #[.integer 7]).runWith pureFunctions 0 {} =
      .ok (.integer 17) {} ∧
    (Term.apply (.function 0 1 #[]) #[.integer 7]).runWith pureFunctions 0 {} =
      .error (.throw (.atom "bad_input")) {} ∧
    (Term.apply (.function 0 1 #[]) #[]).runWith pureFunctions 0 {} =
      .error (.error (.tuple #[.atom "badarity", .tuple #[.function 0 1 #[], .nil]])) {} ∧
    (Term.apply (.function 9 0 #[]) #[]).runWith pureFunctions 0 {} =
      .error (.error (.tuple #[.atom "badfun", .function 9 0 #[]])) {} ∧
    (Term.apply (.atom "not_a_fun") #[]).runWith pureFunctions 0 {} =
      .error (.error (.tuple #[.atom "badfun", .atom "not_a_fun"])) {} := by
  repeat' apply And.intro
  all_goals cbv

/-- The process runner uses the same pure bodies without a dispatch budget. -/
theorem pure_dispatch_without_depth :
    (Term.apply (.function 0 1 #[.integer 10]) #[.integer 7]).runWith pureFunctions 0 {} =
      .ok (.integer 17) {} ∧
    (Result.handle (Term.apply (.function 0 1 #[]) #[.integer 7])
      (fun _ => .ok (.atom "caught"))).runWith pureFunctions 0 {} =
      .ok (.atom "caught") {} := by
  constructor <;> cbv

/-- An effectful entry remains a request until executed by the runner. -/
theorem effectful_call :
    (Term.apply (.function 1 0 #[]) #[]).runWith pureFunctions 1 {} =
      .ok (.pid 1) {} ∧
    (Term.apply (.function 1 0 #[]) #[]).runWith pureFunctions 0 {} =
      .exhausted {} := by
  constructor <;> cbv

/-- Sequential calls reuse the depth budget after returning. -/
theorem sequential_dispatch :
    (do let _ ← call 0; call 0).runWith constant 1 {} = .ok (.integer 7) {} ∧
    (call 0).runWith constant 0 {} = .exhausted {} ∧
    (call 1).runWith constant 0 {} =
      .error (.error (.tuple #[.atom "badfun", .function 1 0 #[]])) {} := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

private def failing : Term.FunTable := #[.effectful fun _ _ => .error (.throw (.integer 9))]

/-- Exceptions raised inside dispatched code reach the caller's handler. -/
theorem catch_dispatched_exception :
    (Result.handle (call 0) (fun _ => .ok (.integer 42))).runWith failing 1 {} =
      .ok (.integer 42) {} := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

/-- Exhaustion cannot be caught as an Erlang exception. -/
theorem exhaustion_is_not_an_exception :
    (Result.handle (call 0) (fun _ => .ok (.integer 42))).runWith failing 0 {} =
      .exhausted {} := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

private def stateful : Term.FunTable := #[.effectful fun _ _ =>
  .get fun env => .set { env with currentProcess.pdict := [(.atom "key", .integer 1)] }
    (.ok (.integer 7))]

/-- Dispatch preserves state changes for the caller's continuation. -/
theorem dispatched_state :
    (do let _ ← call 0; getThe Environment).runWith stateful 1 {} =
      .ok { currentProcess.pdict := [(.atom "key", .integer 1)] }
        { currentProcess.pdict := [(.atom "key", .integer 1)] } := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

/-- The same program table is available in children without adding a scheduling boundary. -/
theorem spawned_dispatch :
    (Result.schedule (call 0) fun _ => .receive .infinity (fun _ value => some value) (fun value => .ok (value.getD .nil))).runWith
      #[.effectful fun _ _ => .send 1 (.integer 7) (.ok .nil)] 1 {} =
      .ok (.integer 7) { pidCounter := 2 } := by cbv

private def spawn (id : Nat) : Result :=
  .spawn (.function id 0 #[]) fun
    | .ok pid => .ok pid
    | .error exception => .error exception

/-- Pure bodies may be spawned; this still creates a child and a scheduling boundary. -/
theorem pure_spawn_without_depth :
    (spawn 0).runWith #[.pure fun _ _ => .ok (.integer 7)] 0 {} =
      .ok (.pid 2) { pidCounter := 2 } := by cbv

/-- Invalid IDs fail in the caller without allocating a child. Exceptions raised
by a valid child do not reach the caller's exception handler. -/
theorem spawn_exception_boundaries :
    (Result.handle (spawn 9) (fun _ => .ok (.atom "caught"))).runWith failing 1 {} =
      .ok (.atom "caught") {} ∧
    (Result.handle (spawn 0) (fun _ => .ok (.atom "caught"))).runWith failing 1 {} =
      .ok (.pid 2) { pidCounter := 2 } := by
  constructor <;> cbv

/-- Recursive spawning consumes dispatch depth rather than resetting the budget
for each new process. -/
theorem recursive_spawn_exhausts :
    match (spawn 0).runWith #[.effectful fun _ _ => spawn 0] 3 {} with
    | .exhausted env => env.pidCounter = 4
    | _ => False := by cbv

end LynxTest.Term.Apply

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Apply
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Apply
