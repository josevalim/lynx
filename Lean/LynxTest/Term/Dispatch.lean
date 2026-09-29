module

meta import LynxTest.ProofAudit
import Lynx
import all Lynx.Term.DataTypes
import all Lynx.Term.Dispatch
import all Lynx.Term.Runner

namespace LynxTest.Term.Dispatch
open Lynx

private def call (id : Nat) (args : Array Term := #[]) : Result :=
  .apply (.function id args.size #[]) args fun
    | .ok value => .ok value
    | .error exception => .error exception

private def countdown : Term.FunTable := #[fun _ (args : Array Term) =>
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

private def constant : Term.FunTable := #[fun _ _ => .ok (.integer 7)]

/-- Sequential calls reuse the depth budget after returning. -/
theorem sequential_dispatch :
    (do let _ ← call 0; call 0).runWith constant 1 {} = .ok (.integer 7) {} ∧
    (call 0).runWith constant 0 {} = .exhausted {} ∧
    (call 1).runWith constant 0 {} =
      .error (.error (.tuple #[.atom "badfun", .function 1 0 #[]])) {} := by
  repeat' apply And.intro
  all_goals first | exact rfl | (cbv <;> rfl)

private def failing : Term.FunTable := #[fun _ _ => .error (.throw (.integer 9))]

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

private def stateful : Term.FunTable := #[fun _ _ =>
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
    (Result.schedule (call 0) fun _ => .receive (fun value => some value) .ok).runWith
      #[fun _ _ => .send 1 (.integer 7) (.ok .nil)] 1 {} =
      .ok (.integer 7) { pidCounter := 2 } := by cbv

private def spawn (id : Nat) : Result :=
  .spawn (.function id 0 #[]) fun
    | .ok pid => .ok pid
    | .error exception => .error exception

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
    match (spawn 0).runWith #[fun _ _ => spawn 0] 3 {} with
    | .exhausted env => env.pidCounter = 4
    | _ => False := by cbv

end LynxTest.Term.Dispatch

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Dispatch
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Dispatch
