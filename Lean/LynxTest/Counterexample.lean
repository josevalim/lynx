module

import Lynx
import Lynx.Runner.Elab
import Lynx.Modules.Erlang.erlang
-- The search runs the runtime in the interpreter, which needs its compiled code.
meta import Lynx.Modules.Erlang.erlang

/-! Counterexample search for concurrent checks. -/

namespace LynxTest.Counterexample
open Lynx Erlang.erlang

/-- Receive a queued message, or `timeout` when there is none. -/
private def poll : Result :=
  .receive .immediate (fun _ message => some message) fun
    | some message => .ok message
    | none => .ok (.atom "timeout")

/-- A child that sends `hello` to the PID it captured. -/
private def functions : Term.FunTable := [
  { module := "test", name := "greet", arity := 0, entry := .effectful fun dispatcher captures _ =>
      match captures.toList with
      | [parent] => «send/2» dispatcher parent (.atom "hello")
      | _ => .error .exhausted }]

private def dispatcher : Dispatcher := Dispatcher.ofTable functions 1

/-- The parent polls for the child's message, which may not have arrived yet. -/
private def race : Result := do
  let self ← «self/0» dispatcher
  let _ ← «spawn/1» dispatcher (.function "test" "greet" 0 #[self])
  poll

private def hello : Outcome Term → Bool
  | .ok (.atom "hello") => true
  | _ => false

private def answered : Outcome Term → Bool
  | .ok (.atom "hello") | .ok (.atom "timeout") => true
  | _ => false

/--
error: Found a schedule where the program returns timeout:
  1. <0> spawns <0.1>
  2. <0> times out waiting for a message
  3. <0> exits with normal
  4. <0.1> sends hello to <0>
  5. <0.1> exits with normal
-/
#guard_msgs in
example : Concurrent.check hello 32 (.start {} race) = true := by
  lynx_counterexample
  cbv

/-- Without a counterexample, the goal is left for the kernel to prove. -/
example : Concurrent.check answered 32 (.start {} race) = true := by
  lynx_counterexample
  cbv

/--
error: Found a schedule that takes more than 4 steps; increase the depth:
  1. <0> spawns <0.1>
  2. <0> times out waiting for a message
-/
#guard_msgs in
example : Concurrent.check answered 4 (.start {} race) = true := by
  lynx_counterexample
  cbv

/-- Laws state checks from some call depth on, which the search takes to be zero. -/
private def deep (depth : Nat) : Result := do
  let self ← «self/0» (Dispatcher.ofTable functions depth)
  let _ ← «spawn/1» (Dispatcher.ofTable functions depth) (.function "test" "greet" 0 #[self])
  poll

/--
error: Found a schedule where the program returns timeout:
  1. <0> spawns <0.1>
  2. <0> times out waiting for a message
  3. <0> exits with normal
  4. <0.1> sends hello to <0>
  5. <0.1> exits with normal
where depth = 0
-/
#guard_msgs in
example (depth : Nat) : Concurrent.check hello 32 (.start {} (deep (depth + 1))) = true := by
  lynx_counterexample
  sorry

/-- error: lynx_counterexample runs closed programs, but this one depends on [message] -/
#guard_msgs in
example (message : Term) :
    Concurrent.check hello 32 (.start {} (pure message : Result)) = true := by
  lynx_counterexample
  sorry

end LynxTest.Counterexample
