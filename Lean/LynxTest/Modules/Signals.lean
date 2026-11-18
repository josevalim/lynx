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

/-- A child that sends itself `alma` with `exit/2`, then tells the root it survived. -/
private def suicide : Result := do
  let me ← «self/0» dispatcher
  let _ ← «exit/2» dispatcher me (.atom "alma")
  «send/2» dispatcher (.pid []) (.atom "survived")

private def suicides : Term := .function "test" "suicides" 0 #[]
private def suicidal : Dispatcher := Dispatcher.ofTable [
  { module := "test", name := "suicides", arity := 0, entry := .effectful fun _ _ _ =>
      suicide }] 1

private def returns : Term := .function "test" "returns" 0 #[]
private def raises : Term := .function "test" "raises" 0 #[]
private def waits : Term := .function "test" "waits" 0 #[]

/-- Accept exactly one outcome, for proofs over every schedule. -/
private def only (expected : Outcome Term) (actual : Outcome Term) : Bool :=
  match expected, actual with
  | .ok expected, .ok actual => Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | .error (.exit expected), .error (.exit actual) => Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | .error (.error expected), .error (.error actual) => Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | .error .exhausted, .error .exhausted => true
  | .deadlock, .deadlock => true
  | _, _ => false

private def down (reference : List Nat) (processId : PID) (reason : Term) : Term :=
  .tuple #[.atom "DOWN", .reference reference, .atom "process", .pid processId, reason]

/-- A monitor reports how the process ended, whatever the schedule. -/
theorem monitor_reports_normal_exit :
    Concurrent.check (only (.ok (down [1] [1] (.atom "normal")))) 32 (.start {} (do
      let _ ← «spawn_monitor/1» dispatcher returns
      receiveAny)) = true := by decide +kernel

theorem monitor_reports_raised_reason :
    Concurrent.check (only (.ok (down [1] [1] (.tuple #[.atom "boom", .nil])))) 32 (.start {} (do
      let _ ← «spawn_monitor/1» dispatcher raises
      receiveAny)) = true := by decide +kernel

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
        pure message)) = true := by decide +kernel

/-- A linked process that raises takes its linked parent down with its reason. -/
theorem linked_crash_kills_parent :
    Concurrent.check (only (.error (.exit (.tuple #[.atom "boom", .nil])))) 32 (.start {} (do
      let _ ← «spawn_link/1» dispatcher raises
      receiveAny)) = true := by decide +kernel

/-- A normal exit does not affect linked processes. -/
theorem linked_normal_exit_is_ignored :
    Concurrent.check (only (.ok (.atom "done"))) 32 (.start {} (do
      let _ ← «spawn_link/1» dispatcher returns
      pure (.atom "done"))) = true := by decide +kernel

/-- Trapping exits turns the signal into a message. -/
theorem trapped_exit_is_a_message :
    Concurrent.check (only (.ok (.tuple #[.atom "EXIT", .pid [1], .tuple #[.atom "boom", .nil]])))
      32 (.start {} (do
        let _ ← «process_flag/2» dispatcher (.atom "trap_exit") (.atom "true")
        let _ ← «spawn_link/1» dispatcher raises
        receiveAny)) = true := by decide +kernel

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
      | _ => pure .nil)) = true := by decide +kernel

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
      | _ => pure .nil)) = true := by decide +kernel

/-- With `exit/2`, a process sending itself `normal` ends at once with it,
unless it traps exits. -/
theorem exit_self_normal_ends :
    Concurrent.check (only (.error (.exit (.atom "normal")))) 32 (.start {} (do
      let me ← «self/0» dispatcher
      let _ ← «exit/2» dispatcher me (.atom "normal")
      pure (.atom "survived"))) = true := by decide +kernel

/-- With `exit/2`, a process sending itself `kill` ends at once, even trapping exits. -/
theorem exit_self_kill_ends_trapping :
    Concurrent.check (only (.error (.exit (.atom "killed")))) 32 (.start {} (do
      let _ ← «process_flag/2» dispatcher (.atom "trap_exit") (.atom "true")
      let me ← «self/0» dispatcher
      let _ ← «exit/2» dispatcher me (.atom "kill")
      pure (.atom "survived"))) = true := by decide +kernel

/-- A child ending on its own `exit/2` signal never reports that it survived:
its trapping parent gets its reason. -/
theorem exit_self_ends_before_returning :
    Concurrent.check (only (.ok (.tuple #[.atom "EXIT", .pid [1], .atom "alma"]))) 32 (.start {} (do
      let _ ← «process_flag/2» dispatcher (.atom "trap_exit") (.atom "true")
      let _ ← «spawn_link/1» suicidal suicides
      receiveAny)) = true := by decide +kernel

/-- Accept either of two outcomes. -/
private def either (first second : Outcome Term) (actual : Outcome Term) : Bool :=
  only first actual || only second actual

/-- A process trapping its own `exit/2` signal handles it later, against its flags
by then: as an `EXIT` message if it handled it before clearing `trap_exit`, and
exiting otherwise. -/
theorem exit_self_trapped_is_handled_later :
    Concurrent.check (either (.ok (.tuple #[.atom "EXIT", .pid [], .atom "alma"])) (.error (.exit (.atom "alma"))))
      32 (.start {} (do
        let _ ← «process_flag/2» dispatcher (.atom "trap_exit") (.atom "true")
        let me ← «self/0» dispatcher
        let _ ← «exit/2» dispatcher me (.atom "alma")
        let _ ← «process_flag/2» dispatcher (.atom "trap_exit") (.atom "false")
        poll)) = true := by decide +kernel

/-- A process handles its own `exit_signal/2` signal later: it may return before. -/
theorem exit_signal_self_is_handled_later :
    Concurrent.check (either (.ok (.atom "survived")) (.error (.exit (.atom "alma")))) 32 (.start {} (do
      let me ← «self/0» dispatcher
      let _ ← «exit_signal/2» dispatcher me (.atom "alma")
      pure (.atom "survived"))) = true := by decide +kernel

/-- A `receive … after 0` handles everything queued first, so a process sending
itself `exit_signal/2` never times out. -/
theorem exit_signal_self_ends_before_timeout :
    Concurrent.check (only (.error (.exit (.atom "alma")))) 32 (.start {} (do
      let me ← «self/0» dispatcher
      let _ ← «exit_signal/2» dispatcher me (.atom "alma")
      poll)) = true := by decide +kernel

/-- Exit signals to aliases are not modeled. -/
theorem exit_alias_is_exhausted :
    Concurrent.check (only (.error .exhausted)) 32 (.start {} (do
      let _ ← «exit/2» dispatcher (.reference [0]) (.atom "alma")
      pure .nil)) = true ∧
    Concurrent.check (only (.error .exhausted)) 32 (.start {} (do
      let _ ← «exit_signal/2» dispatcher (.reference [0]) (.atom "alma")
      pure .nil)) = true := by decide +kernel

/-- `exit_signal/2` sends other processes the signals `exit/2` does. -/
theorem exit_signal_to_others :
    Concurrent.check (only (.ok (down [1] [1] (.atom "normal")))) 32 (.start {} (do
      let child ← «spawn_monitor/1» dispatcher waits
      match child with
      | .tuple ⟨[pid, _]⟩ =>
        let _ ← «exit_signal/2» dispatcher pid (.atom "normal")
        let _ ← «send/2» dispatcher pid (.atom "stop")
        receiveAny
      | _ => pure .nil)) = true ∧
    Concurrent.check (only (.ok (down [1] [1] (.atom "killed")))) 32 (.start {} (do
      let child ← «spawn_monitor/1» dispatcher waits
      match child with
      | .tuple ⟨[pid, _]⟩ =>
        let _ ← «exit_signal/2» dispatcher pid (.atom "kill")
        receiveAny
      | _ => pure .nil)) = true := by decide +kernel

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
      pure (.tuple #[first, second]))) = true := by decide +kernel

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

/-- Receive a message, or `timeout` once the timer expires. -/
private def receiveWithin : Result :=
  .receive .finite (fun _ message => some message) fun
    | some message => .ok message
    | none => .ok (.atom "timeout")

/-- A positive timeout starts once the process handled what was queued, so a
message queued before the receive is received. -/
theorem receive_takes_queued_message :
    Concurrent.check (only (.ok (.atom "hello"))) 32 (.start {} (do
      let me ← «self/0» dispatcher
      let _ ← «send/2» dispatcher me (.atom "hello")
      receiveWithin)) = true := by decide +kernel

/-- An exit signal queued from a linked process that crashed acts on the link
it finds when handled: relinking while trapping exits after unlinking makes
it arrive as an `EXIT` message, unless the child handled the unlink first. -/
private def relinks : Result := do
  let _ ← «process_flag/2» dispatcher (.atom "trap_exit") (.atom "true")
  let child ← «spawn_link/1» dispatcher raises
  let _ ← «unlink/1» dispatcher child
  let _ ← «link/1» dispatcher child
  receiveAny

theorem relink_acts_on_queued_exit :
    Concurrent.check (either (.ok (.tuple #[.atom "EXIT", .pid [1], .atom "noproc"]))
      (.ok (.tuple #[.atom "EXIT", .pid [1], .tuple #[.atom "boom", .nil]]))) 64 (.start {} relinks) = true := by
  decide +kernel

theorem relink_may_receive_crash :
    (match Concurrent.counterexample (only (.ok (.tuple #[.atom "EXIT", .pid [1], .atom "noproc"]))) 64
        (.start {} relinks) with
      | some (_, .rejected (.ok result)) =>
          Term.compareExact (Term.fuel result (.tuple #[.atom "EXIT", .pid [1], .tuple #[.atom "boom", .nil]])) result
            (.tuple #[.atom "EXIT", .pid [1], .tuple #[.atom "boom", .nil]]) == .eq
      | _ => false) = true := by decide +kernel

end LynxTest.Modules.Signals

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Modules.Signals
