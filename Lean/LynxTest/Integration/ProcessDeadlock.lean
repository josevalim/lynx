module

/-
defmodule ProcessDeadlock do
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
import Lynx.Modules.Erlang.erlang
import all Lynx.Term
import all Lynx.Term.Runner
import all Lynx.Term.Apply
import LynxTest.Bench

namespace LynxTest.Integration.ProcessDeadlock
open Lynx
set_option Elab.async false

private def receiveAtom (name : String) : Result :=
  .receive (fun message => match message with
    | .atom found => if found == name then some message else none
    | _ => none) .ok

def worker_0 : Result := do
  let _ ← receiveAtom "ping"
  .ok (.atom "ok")

private def workerFun (args : Array Term) : Result :=
  match args.toList with
  | [] => worker_0
  | _ => .error (.error (.atom "unexpected_arguments"))

private def functions : Term.FunTable := #[.effectful fun _ => workerFun]

def run_0 : Result := do
  let _ ← Erlang.erlang.«spawn/1» (.function 0 0 #[])
  let _ ← receiveAtom "pong"
  .ok (.atom "ok")

private def runFunction : Result := Result.resolve functions 1 run_0

/-- The parent waits for `pong` while its child waits for `ping`; neither process
sends a message, so the whole process tree is stuck. -/
theorem run_deadlocks :
    Lynx.run runFunction = .deadlock { pidCounter := 2, processes := [(2, {})] } := by
  cbv

/- law run_returns(), expects: (result -> result == :ok)
   The execution below is a counterexample: it deadlocks. -/
theorem deadlock_prevents_return :
    ¬ ∃ result final, runFunction {} = .ok result final := by
  intro ⟨result, final, returned⟩
  have stuck := run_deadlocks
  change runFunction {} = _ at stuck
  rw [stuck] at returned
  cases returned

end LynxTest.Integration.ProcessDeadlock
