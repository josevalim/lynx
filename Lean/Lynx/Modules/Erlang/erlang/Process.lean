module

public import Lynx.Term

public section

/-! Erlang process identity, local messaging, and process-dictionary operations. -/

namespace Erlang.erlang

open Lynx

/-- Request a zero-arity function spawn. The dispatcher validates the table entry
before creating the child; the function body executes in the child's process. -/
@[expose] def «spawn/1» (child : Term) : Result :=
  match child with
  | .function _ 0 _ => .spawn child fun
      | .ok pid => .ok pid
      | .error exception => .error exception
  | _ => .error (.error (.atom "badarg"))

/-- Return the PID of the process running the current computation. -/
@[expose] def «self/0» : Result := do
  let env ← get
  .ok (.pid env.currentPid)

/-- Send to a local PID and return the message. A nonexistent or terminated
PID silently discards the message. Registered names and remote destinations
are not modeled. Sending is a scheduler boundary, even to self or a dead PID. -/
@[expose] def «send/2» (destination message : Term) : Result :=
  match destination with
  | .pid pid => .send pid message (.ok message)
  | _ => .error (.error (.atom "badarg"))

/-- Return all process-dictionary bindings. Their order is unspecified by Erlang.erlang. -/
@[expose] def «get/0» : Result := do
  let env ← get
  .ok ((env.pdict.map fun (key, value) => Term.tuple #[key, value]).foldr Term.cons Term.nil)

/-- Return the value stored under `key`, or `undefined`. -/
@[expose] def «get/1» (key : Term) : Result := do
  let env ← get
  .ok ((env.pdict.findSome? fun (stored, value) =>
    if Term.exactCompare key stored = .eq then some value else none).getD (.atom "undefined"))

/-- Return all process-dictionary keys. Their order is unspecified by Erlang.erlang. -/
@[expose] def «get_keys/0» : Result := do
  let env ← get
  .ok ((env.pdict.map Prod.fst).foldr Term.cons Term.nil)

/-- Return all keys associated with a semantically equal value. -/
@[expose] def «get_keys/1» (value : Term) : Result := do
  let env ← get
  .ok ((env.pdict.filterMap fun entry =>
    if Term.exactCompare value entry.2 = .eq then some entry.1 else none).foldr Term.cons Term.nil)

/-- Store a binding and return its previous value, or `undefined`. -/
@[expose] def «put/2» (key value : Term) : Result := do
  let env ← get
  let previous := (env.pdict.findSome? fun (stored, value) =>
    if Term.exactCompare key stored = .eq then some value else none).getD (.atom "undefined")
  set (env.setPdict ((key, value) :: env.pdict.filter fun entry => Term.exactCompare key entry.1 != .eq))
  .ok previous

/-- Return all process-dictionary bindings and clear the dictionary. -/
@[expose] def «erase/0» : Result := do
  let env ← get
  set (env.setPdict [])
  .ok ((env.pdict.map fun (key, value) => Term.tuple #[key, value]).foldr Term.cons Term.nil)

/-- Delete `key` and return its previous value. -/
@[expose] def «erase/1» (key : Term) : Result := do
  let env ← get
  let previous := (env.pdict.findSome? fun (stored, value) =>
    if Term.exactCompare key stored = .eq then some value else none).getD (.atom "undefined")
  set (env.setPdict (env.pdict.filter fun entry => Term.exactCompare key entry.1 != .eq))
  .ok previous

end Erlang.erlang
