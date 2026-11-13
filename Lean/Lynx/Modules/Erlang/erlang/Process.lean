module

public import Lynx.Term

public section

/-! Erlang process identity, local messaging, and process-dictionary operations.
Like every computation that is not pure, they receive the program's dispatcher,
which only spawning uses. -/

namespace Lynx.Term

/-- Whether monitor options create an alias. Aliases are only modeled with
`demonitor`, and tags are not modeled; neither returns. -/
@[expose] def monitorAlias : List Term → Except Exception Bool
  | [] => .ok Bool.false
  | .tuple ⟨[.atom "alias", .atom "demonitor"]⟩ :: rest => (monitorAlias rest).map fun _ => Bool.true
  | .tuple ⟨[.atom "alias", .atom "explicit_unalias"]⟩ :: _ => .error .exhausted
  | .tuple ⟨[.atom "alias", .atom "reply_demonitor"]⟩ :: _ => .error .exhausted
  | .tuple ⟨[.atom "tag", _]⟩ :: _ => .error .exhausted
  | _ :: _ => .error (.error (.atom "badarg"))

/-- Whether to flush a `DOWN` message and whether to report if the monitor was
found. -/
@[expose] def demonitorOptions : List Term → Option (Bool × Bool)
  | [] => some (Bool.false, Bool.false)
  | .atom "flush" :: rest => (demonitorOptions rest).map fun (_, info) => (Bool.true, info)
  | .atom "info" :: rest => (demonitorOptions rest).map fun (flush, _) => (flush, Bool.true)
  | _ :: _ => none

/-- Whether `send_after/4` options request an absolute time. The last `abs`
option wins, as in OTP. -/
@[expose] def timerAbsolute (absolute : Bool := Bool.false) : List Term → Option Bool
  | [] => some absolute
  | .tuple ⟨[.atom "abs", .atom "false"]⟩ :: rest => timerAbsolute Bool.false rest
  | .tuple ⟨[.atom "abs", .atom "true"]⟩ :: rest => timerAbsolute Bool.true rest
  | _ :: _ => none

/-- Start a timer sending `message` to a local PID, replying its reference.
OTP rejects negative times and those outside 64 bits, and accepts others while
they end before its monotonic clock does, centuries after it starts. Times up
to 2^32 - 1 milliseconds are modeled as accepted; longer ones and registered
names do not return. -/
@[expose] def sendAfter (time destination message : Term) : Result :=
  match time with
  | .integer duration =>
      if duration < 0 || duration ≥ 2 ^ 63 then .error (.error (.atom "badarg")) else
      match destination with
      | .pid target =>
          if duration > 4294967295 then .error .exhausted else
          .request (.startTimer target message duration.toNat) .ok
      | .atom _ => .error .exhausted
      | _ => .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

end Lynx.Term

namespace Erlang.erlang

open Lynx

/-- Allocate a reference unique within this runtime: the process's PID extended
with its own allocation count. Allocation preserves process state and does not
introduce a scheduler boundary. -/
@[expose] def «make_ref/0» (_ : Dispatcher) : Result := do
  let env ← get
  let id := env.refCounter + 1
  set { env with refCounter := id }
  .ok (.reference (env.currentPid ++ [id]))

@[simp] theorem make_ref_apply (dispatcher : Dispatcher) (env : Environment) :
    «make_ref/0» dispatcher env =
      (.ok (.reference (env.currentPid ++ [env.refCounter + 1])), { env with refCounter := env.refCounter + 1 }) := by
  change (Result.get fun initial => Result.set
    { initial with refCounter := initial.refCounter + 1 }
    (.ok (Term.reference (initial.currentPid ++ [initial.refCounter + 1])))) env = _
  simp

@[simp] theorem make_ref_bind_apply (dispatcher : Dispatcher) (next : Term → Result α)
    (env : Environment) :
    («make_ref/0» dispatcher >>= next) env =
      next (.reference (env.currentPid ++ [env.refCounter + 1])) { env with refCounter := env.refCounter + 1 } := by
  change (Result.get fun initial => Result.set
    { initial with refCounter := initial.refCounter + 1 }
    (next (.reference (initial.currentPid ++ [initial.refCounter + 1])))) env = _
  simp

/-- Spawn a zero-arity function value. Its body executes in the child's process,
which reports calling a function value the table does not contain. -/
@[expose] def «spawn/1» (dispatcher : Dispatcher) (child : Term) : Result :=
  match child with
  | .function _ _ 0 _ => .schedule {} (dispatcher.call child #[]) fun pid => .ok (.pid pid)
  | _ => .error (.error (.atom "badarg"))

/-- Return the PID of the process running the current computation. -/
@[expose] def «self/0» (_ : Dispatcher) : Result := do
  let env ← get
  .ok (.pid env.currentPid)

@[simp] theorem self_readOnly (dispatcher : Dispatcher) :
    Result.IsReadOnly («self/0» dispatcher) := by
  change ∀ env : Environment, Result.IsReadOnly (.ok (Term.pid env.currentPid))
  intro env
  trivial

/-- Send to a local PID or an alias and return the message. A nonexistent or
terminated PID, or an inactive alias, silently discards the message. Registered
names and remote destinations are not modeled. Sending is a scheduler boundary,
even to self or a dead PID. -/
@[expose] def «send/2» (_ : Dispatcher) (destination message : Term) : Result :=
  match destination with
  | .pid pid => .send pid message (.ok message)
  | .reference alias => .request (.sendAlias alias message) .ok
  | _ => .error (.error (.atom "badarg"))

/-- Spawn a zero-arity function value linked to the caller, in the same step. -/
@[expose] def «spawn_link/1» (dispatcher : Dispatcher) (child : Term) : Result :=
  match child with
  | .function _ _ 0 _ =>
      .schedule { link := true } (dispatcher.call child #[]) fun pid => .ok (.pid pid)
  | _ => .error (.error (.atom "badarg"))

/-- Spawn a zero-arity function value monitored by the caller, in the same step.
The monitor's reference is the caller's next one. -/
@[expose] def «spawn_monitor/1» (dispatcher : Dispatcher) (child : Term) : Result :=
  match child with
  | .function _ _ 0 _ =>
      .schedule { monitor := true } (dispatcher.call child #[]) fun pid => do
        let env ← get
        .ok (.tuple #[.pid pid, .reference (env.currentPid ++ [env.refCounter])])
  | _ => .error (.error (.atom "badarg"))

/-- Monitor a process. Monitoring a process that does not exist sends its
`DOWN` message at once, with reason `noproc`. Registered names are not
modeled and do not return. -/
@[expose] def «monitor/2» (_ : Dispatcher) (kind target : Term) : Result :=
  match kind, target with
  | .atom "process", .pid pid => .request (.monitor pid false) .ok
  | .atom "process", .atom _ => .error .exhausted
  | _, _ => .error (.error (.atom "badarg"))

/-- Monitor a process with options. With `{alias, demonitor}`, the reference
also receives messages for the caller until the monitor ends. -/
@[expose] def «monitor/3» (_ : Dispatcher) (kind target options : Term) : Result :=
  match kind, target, (Term.properList? options).map Term.monitorAlias with
  | .atom "process", .pid pid, some (.ok alias) => .request (.monitor pid alias) .ok
  | .atom "process", .atom _, some (.ok _) => .error .exhausted
  | _, _, some (.error .exhausted) => .error .exhausted
  | _, _, _ => .error (.error (.atom "badarg"))

/-- End a monitor and its alias. -/
@[expose] def «demonitor/1» (_ : Dispatcher) (reference : Term) : Result :=
  match reference with
  | .reference id => .request (.demonitor id false) fun _ => .ok (.atom "true")
  | _ => .error (.error (.atom "badarg"))

/-- End a monitor and its alias. When the monitor was no longer active, `flush`
removes the oldest `{_, Reference, _, _, _}` message from the mailbox, usually
its `DOWN` message. `info` returns whether the monitor was still active. -/
@[expose] def «demonitor/2» (_ : Dispatcher) (reference options : Term) : Result :=
  match reference, (Term.properList? options).bind Term.demonitorOptions with
  | .reference id, some (flush, info) =>
      .request (.demonitor id flush) fun found => .ok (if info = true then found else .atom "true")
  | _, _ => .error (.error (.atom "badarg"))

/-- Send `message` once a timer of `time` milliseconds fires, replying the
timer's reference. When it fires, and when its message then arrives, are the
scheduler's choices. -/
@[expose] def «send_after/3» (_ : Dispatcher) (time destination message : Term) : Result :=
  Term.sendAfter time destination message

/-- Like `send_after/3`. Absolute times are not modeled and do not return. -/
@[expose] def «send_after/4» (_ : Dispatcher) (time destination message options : Term) : Result :=
  match (Term.properList? options).bind (Term.timerAbsolute Bool.false) with
  | some false => Term.sendAfter time destination message
  | some true => .error .exhausted
  | none => .error (.error (.atom "badarg"))

/-- Cancel a timer, replying the milliseconds left, any number up to its
duration as elapsed time is not modeled, or `false` once it expired, was
canceled, or its destination exited. An expired timer's message may still be
on its way. Timers paused by the debugger are not modeled. -/
@[expose] def «cancel_timer/1» (_ : Dispatcher) (reference : Term) : Result :=
  match reference with
  | .reference id => .request (.cancelTimer id) .ok
  | _ => .error (.error (.atom "badarg"))

/-- Link to a process. Linking to a process that does not exist raises
`noproc`, unless the caller traps exits and receives an `EXIT` message. -/
@[expose] def «link/1» (_ : Dispatcher) (target : Term) : Result :=
  match target with
  | .pid pid => .request (.link pid) fun reply =>
      match reply with
      | .atom "noproc" => .error (.error (.atom "noproc"))
      | reply => .ok reply
  | _ => .error (.error (.atom "badarg"))

@[expose] def «unlink/1» (_ : Dispatcher) (target : Term) : Result :=
  match target with
  | .pid pid => .request (.unlink pid) .ok
  | _ => .error (.error (.atom "badarg"))

/-- Send an exit signal. `kill` cannot be trapped, and `normal` is ignored
unless the target traps exits or is the caller. The target acts on the signal
when it arrives; the caller acts on its own at once. -/
@[expose] def «exit/2» (_ : Dispatcher) (target reason : Term) : Result :=
  match target with
  | .pid pid => .request (.exit pid reason) .ok
  | _ => .error (.error (.atom "badarg"))

/-- Set whether exit signals arrive as `EXIT` messages, returning the previous
value. Other flags are not modeled and do not return. -/
@[expose] def «process_flag/2» (_ : Dispatcher) (flag value : Term) : Result :=
  match flag, value with
  | .atom "trap_exit", .atom "true" => .request (.trapExit true) .ok
  | .atom "trap_exit", .atom "false" => .request (.trapExit false) .ok
  | .atom "trap_exit", _ => .error (.error (.atom "badarg"))
  | _, _ => .error .exhausted

@[expose] def «is_process_alive/1» (_ : Dispatcher) (target : Term) : Result :=
  match target with
  | .pid pid => .request (.alive pid) .ok
  | _ => .error (.error (.atom "badarg"))

/-- Process information. Only `registered_name` is modeled: processes have no
registered names, so it is `[]` for live processes. Other items do not return. -/
@[expose] def «process_info/2» (_ : Dispatcher) (target item : Term) : Result :=
  match target, item with
  | .pid pid, .atom "registered_name" => .request (.alive pid) fun alive =>
      .ok (match alive with
        | .atom "true" => .nil
        | _ => .atom "undefined")
  | .pid _, _ => .error .exhausted
  | _, _ => .error (.error (.atom "badarg"))

/-- Return all process-dictionary bindings. Their order is unspecified by Erlang.erlang. -/
@[expose] def «get/0» (_ : Dispatcher) : Result := do
  let env ← get
  .ok ((env.pdict.map fun (key, value) => Term.tuple #[key, value]).foldr Term.cons Term.nil)

/-- Return the value stored under `key`, or `undefined`. -/
@[expose] def «get/1» (_ : Dispatcher) (key : Term) : Result := do
  let env ← get
  .ok ((env.pdict.findSome? fun (stored, value) =>
    if Term.compareExact (Term.fuel key stored) key stored = .eq then some value else none).getD (.atom "undefined"))

/-- Return all process-dictionary keys. Their order is unspecified by Erlang.erlang. -/
@[expose] def «get_keys/0» (_ : Dispatcher) : Result := do
  let env ← get
  .ok ((env.pdict.map Prod.fst).foldr Term.cons Term.nil)

/-- Return all keys associated with a semantically equal value. -/
@[expose] def «get_keys/1» (_ : Dispatcher) (value : Term) : Result := do
  let env ← get
  .ok ((env.pdict.filterMap fun entry =>
    if Term.compareExact (Term.fuel value entry.2) value entry.2 = .eq then some entry.1 else none).foldr Term.cons Term.nil)

/-- Store a binding and return its previous value, or `undefined`. -/
@[expose] def «put/2» (_ : Dispatcher) (key value : Term) : Result := do
  let env ← get
  let previous := (env.pdict.findSome? fun (stored, value) =>
    if Term.compareExact (Term.fuel key stored) key stored = .eq then some value else none).getD (.atom "undefined")
  set { env with pdict := (key, value) :: env.pdict.filter fun entry =>
    Term.compareExact (Term.fuel key entry.1) key entry.1 != Ordering.eq }
  .ok previous

/-- Return all process-dictionary bindings and clear the dictionary. -/
@[expose] def «erase/0» (_ : Dispatcher) : Result := do
  let env ← get
  set { env with pdict := [] }
  .ok ((env.pdict.map fun (key, value) => Term.tuple #[key, value]).foldr Term.cons Term.nil)

/-- Delete `key` and return its previous value. -/
@[expose] def «erase/1» (_ : Dispatcher) (key : Term) : Result := do
  let env ← get
  let previous := (env.pdict.findSome? fun (stored, value) =>
    if Term.compareExact (Term.fuel key stored) key stored = .eq then some value else none).getD (.atom "undefined")
  set { env with pdict := env.pdict.filter fun entry => Term.compareExact (Term.fuel key entry.1) key entry.1 != Ordering.eq }
  .ok previous

end Erlang.erlang
