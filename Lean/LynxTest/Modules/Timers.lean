module

import Lynx.Modules.Erlang.erlang
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

/-! Timers, which the scheduler expires and whose messages it delivers in later
steps of its choosing. -/

namespace LynxTest.Modules.Timers
open Lynx Erlang.erlang

private def receiveAny : Result :=
  .receive .infinity (fun _ message => some message) fun
    | some message => .ok message
    | none => .ok .nil

/-- Receive a message, or `timeout` once the scheduler expires the receive. -/
private def receiveOrTimeout : Result :=
  .receive .finite (fun _ message => some message) fun
    | some message => .ok message
    | none => .ok (.atom "timeout")

private def functions : Term.FunTable := [
  { module := "test", name := "returns", arity := 0, entry := .effectful fun _ _ _ => .ok .nil },
  { module := "test", name := "waits", arity := 0, entry := .effectful fun _ _ _ => receiveAny }]

private def dispatcher : Dispatcher := Dispatcher.ofTable functions 1

private def returns : Term := .function "test" "returns" 0 #[]
private def waits : Term := .function "test" "waits" 0 #[]

/-- Accept any of the given results, for proofs over every schedule. -/
private def oneOf (expected : List Term) : Outcome Term → Bool
  | .ok actual => expected.any (Term.exactCompare · actual == .eq)
  | _ => false

private def tick : Term := .atom "tick"

/-- Start a timer sending `tick` to the caller. -/
private def startTick : Result := do
  let self ← «self/0» dispatcher
  «send_after/3» dispatcher (.integer 10) self tick

/-- A timer delivers its message, whatever the schedule. -/
theorem timer_delivers :
    Concurrent.check (oneOf [tick]) 32 (.start {} (do
      let _ ← startTick
      receiveAny)) = true := by cbv

/-- Results of canceling the timer and then waiting for its message: either
it was canceled with some milliseconds left, so the message never arrives, or
it expired, so its message arrives. -/
private def canceled : List Term :=
  .tuple #[.atom "false", tick] ::
    (List.range 11).map fun left => .tuple #[.integer (.ofNat left), .atom "timeout"]

theorem cancel_stops_or_message_arrives :
    Concurrent.check (oneOf canceled) 64 (.start {} (do
      let timer ← startTick
      let canceled ← «cancel_timer/1» dispatcher timer
      let message ← match canceled with
        | .atom "false" => receiveAny
        | _ => receiveOrTimeout
      .ok (.tuple #[canceled, message]))) = true := by cbv

/-- The milliseconds left may be none, before the timer expires. -/
theorem cancel_reports_no_time_left :
    (match Concurrent.counterexample (oneOf (canceled.erase (.tuple #[.integer 0, .atom "timeout"])))
        64 (.start {} (do
        let timer ← startTick
        let canceled ← «cancel_timer/1» dispatcher timer
        let message ← match canceled with
          | .atom "false" => receiveAny
          | _ => receiveOrTimeout
        .ok (.tuple #[canceled, message]))) with
      | some (_, .rejected (.ok result)) =>
          Term.exactCompare result (.tuple #[.integer 0, .atom "timeout"]) == .eq
      | _ => false) = true := by cbv

/-- Replying `false` does not mean the message arrived: it may still be on its
way, so waiting with a timeout may miss it. -/
theorem cancel_false_before_delivery :
    (match Concurrent.counterexample (oneOf canceled) 64 (.start {} (do
          let timer ← startTick
          let canceled ← «cancel_timer/1» dispatcher timer
          let message ← receiveOrTimeout
          .ok (.tuple #[canceled, message]))) with
      | some (_, .rejected (.ok result)) =>
          Term.exactCompare result (.tuple #[.atom "false", .atom "timeout"]) == .eq
      | _ => false) = true := by cbv

/-- A timer can only be canceled once. -/
theorem cancel_twice :
    Concurrent.check (oneOf [.atom "false"]) 32 (.start {} (do
      let timer ← startTick
      let _ ← «cancel_timer/1» dispatcher timer
      «cancel_timer/1» dispatcher timer)) = true := by cbv

/-- Timers of a process that exited report `false`, as OTP cancels them, whether
it exited before or after the timer started. -/
theorem cancel_after_destination_exits :
    Concurrent.check (oneOf [.atom "false"]) 32 (.start {} (do
      let spawned ← «spawn_monitor/1» dispatcher returns
      let _ ← receiveAny
      match spawned with
      | .tuple ⟨[pid, _]⟩ => do
          let timer ← «send_after/3» dispatcher (.integer 10) pid tick
          «cancel_timer/1» dispatcher timer
      | _ => .ok .nil)) = true := by cbv

theorem cancel_after_destination_exits_later :
    Concurrent.check (oneOf [.atom "false"]) 32 (.start {} (do
      let spawned ← «spawn_monitor/1» dispatcher waits
      match spawned with
      | .tuple ⟨[pid, _]⟩ => do
          let timer ← «send_after/3» dispatcher (.integer 10) pid tick
          let _ ← «exit/2» dispatcher pid (.atom "kill")
          let _ ← receiveAny
          «cancel_timer/1» dispatcher timer
      | _ => .ok .nil)) = true := by cbv

/-- Other references are not timers. -/
theorem cancel_other_reference :
    Lynx.sequential (do
      let reference ← «make_ref/0» dispatcher
      «cancel_timer/1» dispatcher reference) = .ok (.atom "false") := by cbv

theorem cancel_badarg :
    Lynx.sequential («cancel_timer/1» dispatcher (.atom "timer")) =
      .error (.error (.atom "badarg")) := by cbv

theorem send_after_negative_time :
    Lynx.sequential («send_after/3» dispatcher (.integer (-1)) (.pid []) tick) =
      .error (.error (.atom "badarg")) := by cbv

/-- Relative times are the default, and the last `abs` option wins; absolute
times are not modeled. -/
theorem send_after_options :
    Concurrent.check (oneOf [tick]) 32 (.start {} (do
      let self ← «self/0» dispatcher
      let options := Term.list [.tuple #[.atom "abs", .atom "true"], .tuple #[.atom "abs", .atom "false"]]
      let _ ← «send_after/4» dispatcher (.integer 10) self tick options
      receiveAny)) = true ∧
    Lynx.sequential («send_after/4» dispatcher (.integer 10) (.pid []) tick
      (.list [.tuple #[.atom "abs", .atom "false"], .tuple #[.atom "abs", .atom "true"]])) =
      .error .exhausted ∧
    Lynx.sequential («send_after/4» dispatcher (.integer 10) (.pid []) tick
      (.list [.atom "abs"])) = .error (.error (.atom "badarg")) ∧
    Lynx.sequential («send_after/4» dispatcher (.integer 10) (.pid []) tick
      (.list [.tuple #[.atom "info", .atom "true"]])) = .error (.error (.atom "badarg")) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

/-- Times outside 64 bits are rejected; whether longer times are accepted
depends on OTP's clock, so they are not modeled. -/
theorem send_after_long_times :
    Lynx.sequential («send_after/3» dispatcher (.integer (2 ^ 63)) (.pid []) tick) =
      .error (.error (.atom "badarg")) ∧
    Lynx.sequential («send_after/3» dispatcher (.integer (2 ^ 32)) (.pid []) tick) =
      .error .exhausted ∧
    Lynx.sequential («send_after/3» dispatcher (.integer 10) (.reference [1]) tick) =
      .error (.error (.atom "badarg")) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

end LynxTest.Modules.Timers
