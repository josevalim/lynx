/-
defmodule ProcessDeadlock do
  expects true
  ensures (result -> result == :ok)

  def run do
    spawn(fn ->
      receive do
        :ping -> :ok
      end
    end)

    receive do
      :pong -> :ok
    end
  end
end
-/
import LynxTest.Bench

namespace LynxTest.Integration.ProcessDeadlock
open Lynx Lynx.Modules
set_option Elab.async false

private def receiveAtom (name : String) : Result :=
  .receive (fun message => match message with
    | .atom found => if found == name then some message else none
    | _ => none) .ok

def worker_0 : Result := do
  let _ ← receiveAtom "ping"
  .ok (.atom "ok")

private def workerFun : Term.Fun
  | #[] => worker_0
  | _ => .error (.error (.atom "unexpected_arguments"))

private def functions : Term.FunTable := #[workerFun]

def run_0 : Result := do
  let _ ← Erlang.spawn_1 functions (.function 0 0)
  let _ ← receiveAtom "pong"
  .ok (.atom "ok")

def runExpects (_ : Unit) : Result := .ok Term.true

def runEnsures (_ : Unit) (result : Term) : Result :=
  Erlang.equal_2 result (.atom "ok")

private def runFunction (_ : Unit) : Result := run_0

/- The guarded diagnostic asserts that verification reaches and rejects the
deadlock outcome, rather than merely failing for an unspecified reason. -/
/--
case «process_deadlock.ex:5».deadlock
-/
#guard_msgs (error, substring := true) in
theorem verifier_rejects_deadlocking_contract :
    WithSourceLabel { file := "process_deadlock.ex", line := 5 }
      (Satisfies runFunction runExpects runEnsures) := by
  lynx_verify

/-- The parent waits for `pong` while its child waits for `ping`; neither process
sends a message, so the whole process tree is stuck. -/
theorem run_deadlocks :
    Lynx.run run_0 = .deadlock { pidCounter := 2, processes := [(2, {})] } := by
  rw [show run_0 = Result.spawn worker_0 (fun _ => do
    let _ ← receiveAtom "pong"
    .ok (.atom "ok")) from rfl]
  cbv

/-- The deadlock is a counterexample to the translated function contract. -/
theorem deadlock_violates_contract :
    ¬ Satisfies runFunction runExpects runEnsures := by
  intro contract
  obtain ⟨result, final, returned, _⟩ := contract.2 () {} ⟨{}, rfl⟩
  rw [show runFunction () = run_0 from rfl] at returned
  have stuck := run_deadlocks
  change run_0 {} = _ at returned
  change run_0 {} = _ at stuck
  rw [stuck] at returned
  cases returned

end LynxTest.Integration.ProcessDeadlock
