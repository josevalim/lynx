module

import Lynx.Modules.Erlang.erlang
import Lynx.Modules.Erlang.lists
meta import LynxTest.ProofAudit
import Lynx
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.Compare
import all Lynx.Term.Dispatch
import all Lynx.Term.Runner
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

/-! Links, monitors, aliases, and exit signals between local processes. -/

namespace LynxTest.Modules.Signals
open Lynx Erlang.erlang

private def receiveAny : Result :=
  .receive .infinity (fun _ message => some message) fun
    | some message => .ok message
    | none => .ok .nil

/-- Receive a queued message, or `timeout` when there is none. -/
private def poll : Result :=
  .receive .immediate (fun _ message => some message) fun
    | some message => .ok message
    | none => .ok (.atom "timeout")

/-- Spawned processes: one returns, one raises, and one waits for a message. -/
private def functions : Term.FunTable := [
  { module := "test", name := "raises", arity := 0, entry := .effectful fun _ _ _ =>
      .error (.error (.atom "boom")) },
  { module := "test", name := "returns", arity := 0, entry := .effectful fun _ _ _ => .ok .nil },
  { module := "test", name := "waits", arity := 0, entry := .effectful fun _ _ _ => receiveAny }]

private def dispatcher : Dispatcher := Dispatcher.ofTable functions 1

private def returns : Term := .function "test" "returns" 0 #[]
private def raises : Term := .function "test" "raises" 0 #[]
private def waits : Term := .function "test" "waits" 0 #[]

/-- Accept exactly one outcome, for proofs over every schedule. -/
private def only (expected : Outcome Term) (actual : Outcome Term) : Bool :=
  match expected, actual with
  | .ok expected, .ok actual => Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | .error (.exit expected), .error (.exit actual) => Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | .error (.error expected), .error (.error actual) => Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | .deadlock, .deadlock => true
  | _, _ => false

private def down (reference : List Nat) (processId : PID) (reason : Term) : Term :=
  .tuple #[.atom "DOWN", .reference reference, .atom "process", .pid processId, reason]

/-- A monitor reports how the process ended, whatever the schedule. -/
theorem monitor_reports_normal_exit :
    Concurrent.check (only (.ok (down [1] [1] (.atom "normal")))) 32 (.start {} (do
      let _ ← «spawn_monitor/1» dispatcher returns
      receiveAny)) = true := by cbv

theorem monitor_reports_raised_reason :
    Concurrent.check (only (.ok (down [1] [1] (.tuple #[.atom "boom", .nil])))) 32 (.start {} (do
      let _ ← «spawn_monitor/1» dispatcher raises
      receiveAny)) = true := by cbv

/-- Monitoring a process that does not exist reports `noproc` at once. -/
theorem monitor_missing_process :
    Lynx.sequential (do
      let _ ← «monitor/2» dispatcher (.atom "process") (.pid [99])
      receiveAny) = .ok (down [1] [99] (.atom "noproc")) := by cbv

/-- Flushing removes the monitor's `DOWN` message. -/
theorem demonitor_flushes_down :
    Lynx.sequential (do
      let reference ← «monitor/2» dispatcher (.atom "process") (.pid [99])
      let _ ← «demonitor/2» dispatcher reference (.cons (.atom "flush") .nil)
      poll) = .ok (.atom "timeout") := by cbv

/-- Flushing removes only the oldest message shaped like a `DOWN` message,
which is not necessarily the `DOWN` message itself. -/
theorem demonitor_flushes_oldest_monitor_message :
    Lynx.sequential (do
      let reference ← «monitor/2» dispatcher (.atom "process") (.pid [99])
      let self ← «self/0» dispatcher
      let _ ← «send/2» dispatcher self (.tuple #[.atom "other", reference, .nil, .nil, .nil])
      let _ ← «demonitor/2» dispatcher reference (.cons (.atom "flush") .nil)
      poll) = .ok (.tuple #[.atom "other", .reference [1], .nil, .nil, .nil]) := by cbv

/-- An active monitor has not delivered its `DOWN` message, so flushing it
leaves the mailbox alone, even messages of the same shape. -/
theorem demonitor_active_does_not_flush :
    Concurrent.check (only (.ok (.tuple #[.atom "other", .reference [1], .nil, .nil, .nil])))
      32 (.start {} (do
        let child ← «spawn/1» dispatcher waits
        let reference ← «monitor/2» dispatcher (.atom "process") child
        let self ← «self/0» dispatcher
        let _ ← «send/2» dispatcher self (.tuple #[.atom "other", reference, .nil, .nil, .nil])
        let _ ← «demonitor/2» dispatcher reference (.cons (.atom "flush") .nil)
        let message ← poll
        let _ ← «send/2» dispatcher child (.atom "stop")
        pure message)) = true := by cbv

/-- A linked process that raises takes its linked parent down with its reason. -/
theorem linked_crash_kills_parent :
    Concurrent.check (only (.error (.exit (.tuple #[.atom "boom", .nil])))) 32 (.start {} (do
      let _ ← «spawn_link/1» dispatcher raises
      receiveAny)) = true := by cbv

/-- A normal exit does not affect linked processes. -/
theorem linked_normal_exit_is_ignored :
    Concurrent.check (only (.ok (.atom "done"))) 32 (.start {} (do
      let _ ← «spawn_link/1» dispatcher returns
      pure (.atom "done"))) = true := by cbv

/-- Trapping exits turns the signal into a message. -/
theorem trapped_exit_is_a_message :
    Concurrent.check (only (.ok (.tuple #[.atom "EXIT", .pid [1], .tuple #[.atom "boom", .nil]])))
      32 (.start {} (do
        let _ ← «process_flag/2» dispatcher (.atom "trap_exit") (.atom "true")
        let _ ← «spawn_link/1» dispatcher raises
        receiveAny)) = true := by cbv

/-- A root killed by a signal reports the environment it last had: the
process dictionary it filled before its linked child raised. -/
theorem killed_root_keeps_environment :
    let run := (do
      let _ ← «put/2» dispatcher (.atom "key") (.integer 1)
      let _ ← «spawn_link/1» dispatcher raises
      receiveAny : Result).run {} []
    run.1 = .error (.exit (.tuple #[.atom "boom", .nil])) ∧
      run.2.pdict = [(.atom "key", .integer 1)] := by
  cbv

/-- `kill` cannot be trapped, and monitors report it as `killed`. -/
theorem kill_cannot_be_trapped :
    Concurrent.check (only (.ok (down [1] [1] (.atom "killed")))) 32 (.start {} (do
      let child ← «spawn_monitor/1» dispatcher waits
      match child with
      | .tuple ⟨[pid, _]⟩ =>
        let _ ← «exit/2» dispatcher pid (.atom "kill")
        receiveAny
      | _ => pure .nil)) = true := by cbv

/-- Exit signals with reason `normal` are ignored by processes that do not trap
exits, so the child keeps waiting until it is told to stop. -/
theorem normal_exit_signal_is_ignored :
    Concurrent.check (only (.ok (down [1] [1] (.atom "normal")))) 32 (.start {} (do
      let child ← «spawn_monitor/1» dispatcher waits
      match child with
      | .tuple ⟨[pid, _]⟩ =>
        let _ ← «exit/2» dispatcher pid (.atom "normal")
        let _ ← «send/2» dispatcher pid (.atom "stop")
        receiveAny
      | _ => pure .nil)) = true := by cbv

/-- An alias delivers to its owner until the monitor ends. -/
theorem alias_ends_with_demonitor :
    Concurrent.check (only (.ok (.tuple #[.atom "hello", .atom "timeout"]))) 32 (.start {} (do
      let child ← «spawn/1» dispatcher waits
      let alias ← «monitor/3» dispatcher (.atom "process") child
        (.cons (.tuple #[.atom "alias", .atom "demonitor"]) .nil)
      let _ ← «send/2» dispatcher alias (.atom "hello")
      let first ← receiveAny
      let _ ← «demonitor/1» dispatcher alias
      let _ ← «send/2» dispatcher alias (.atom "again")
      let second ← poll
      let _ ← «send/2» dispatcher child (.atom "stop")
      pure (.tuple #[first, second]))) = true := by cbv

/-- Linking to a process that does not exist raises `noproc`. -/
theorem link_to_missing_process :
    Lynx.sequential («link/1» dispatcher (.pid [99])) = .error (.error (.atom "noproc")) := by
  cbv

theorem liveness :
    Lynx.sequential (do
      let alive ← «is_process_alive/1» dispatcher (.pid [])
      let missing ← «is_process_alive/1» dispatcher (.pid [99])
      let name ← «process_info/2» dispatcher (.pid []) (.atom "registered_name")
      let gone ← «process_info/2» dispatcher (.pid [99]) (.atom "registered_name")
      pure (Term.tuple #[alive, missing, name, gone])) =
      .ok (.tuple #[.atom "true", .atom "false", .nil, .atom "undefined"]) := by cbv

theorem raise_classes :
    «raise/3» (.atom "throw") (.atom "value") .nil = .error (.throw (.atom "value")) ∧
    «raise/3» (.atom "exit") (.atom "value") .nil = .error (.exit (.atom "value")) ∧
    «raise/3» (.atom "error") (.atom "value") (.atom "stack") =
      .error (.error (.atom "badarg")) := by
  refine ⟨rfl, rfl, rfl⟩

theorem keyfind_finds_first_match :
    Erlang.lists.«keyfind/3» (.atom "b") (.integer 1)
        (.cons (.atom "skipped") (.cons (.tuple #[.atom "a", .integer 1])
          (.cons (.tuple #[.atom "b", .integer 2]) .nil))) =
      .ok (.tuple #[.atom "b", .integer 2]) ∧
    Erlang.lists.«keyfind/3» (.atom "c") (.integer 1) (.cons (.tuple #[.atom "a"]) .nil) =
      .ok (.atom "false") := by
  constructor <;> cbv

/-! Signals that do nothing when they arrive, which `check` takes alone. -/

/-- The root waits for a message, holding the records `[]` maps to, with its first child
`[1]` already ended, and `signal` in transit from `source` to `target`. -/
private def waitingWith (root : Concurrent.ProcessState) (source target : PID)
    (signal : Concurrent.Signal) : Concurrent.Config Term :=
  .running
    { processes := fun processId => if processId == [] then some root else none
      inTransit := [⟨source, target, signal⟩] }
    [([], .root receiveAny)] none false

/-- A `DOWN` of a monitor that was removed, and a message to an alias that was removed. -/
theorem inactive_reference_is_forced :
    (waitingWith { refCounter := 1 } [1] [] (.down [1] (.atom "normal"))).forced =
      some (.deliver [1] []) ∧
    (waitingWith { refCounter := 1 } [1] [] (.aliasMessage [1] (.atom "hello"))).forced =
      some (.deliver [1] []) := by
  constructor <;> cbv

/-- A `DOWN` of an active monitor, or of a reference the receiver has not allocated yet
(a later monitor may receive it), does something. -/
theorem active_reference_is_not_forced :
    (waitingWith { refCounter := 1, monitoring := [([1], [1])] } [1] []
      (.down [1] (.atom "normal"))).forced = none ∧
    (waitingWith {} [1] [] (.down [1] (.atom "normal"))).forced = none := by
  constructor <;> cbv

/-- A message to a process that ended is dropped, but a link to it answers with an exit
signal, and a message to a process not spawned yet may still reach it. -/
theorem ended_process_is_forced :
    (waitingWith { children := 1 } [] [1] (.message (.atom "hello"))).forced =
      some (.bounce [] [1]) ∧
    (waitingWith { children := 1 } [] [1] .link).forced = none ∧
    (waitingWith {} [] [1] (.message (.atom "hello"))).forced = none := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

end LynxTest.Modules.Signals

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Modules.Signals
