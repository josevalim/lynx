module

public import Lynx.Term

public section

/-! Erlang process identity, local messaging, and process-dictionary operations.
Like every computation that is not pure, they receive the program's dispatcher,
which only spawning uses. -/

namespace Erlang.erlang

open Lynx

/-- Allocate a reference unique within this runtime, independently of PIDs.
Allocation preserves process state and does not introduce a scheduler boundary. -/
@[expose] def «make_ref/0» (_ : Dispatcher) : Result := do
  let env ← get
  let id := env.refCounter + 1
  set { env with refCounter := id }
  .ok (.reference id)

@[simp] theorem make_ref_apply (dispatcher : Dispatcher) (env : Environment) :
    «make_ref/0» dispatcher env =
      (.ok (.reference (env.refCounter + 1)), { env with refCounter := env.refCounter + 1 }) := by
  change (Result.get fun initial => Result.set
    { initial with refCounter := initial.refCounter + 1 }
    (.ok (Term.reference (initial.refCounter + 1)))) env = _
  simp

@[simp] theorem make_ref_bind_apply (dispatcher : Dispatcher) (next : Term → Result α)
    (env : Environment) :
    («make_ref/0» dispatcher >>= next) env =
      next (.reference (env.refCounter + 1)) { env with refCounter := env.refCounter + 1 } := by
  change (Result.get fun initial => Result.set
    { initial with refCounter := initial.refCounter + 1 }
    (next (.reference (initial.refCounter + 1)))) env = _
  simp

/-- Spawn a zero-arity function value. Its body executes in the child's process,
which reports calling a function value the table does not contain. -/
@[expose] def «spawn/1» (dispatcher : Dispatcher) (child : Term) : Result :=
  match child with
  | .function _ 0 _ => .schedule (dispatcher.call child #[]) fun pid => .ok (.pid pid)
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

/-- Send to a local PID and return the message. A nonexistent or terminated
PID silently discards the message. Registered names and remote destinations
are not modeled. Sending is a scheduler boundary, even to self or a dead PID. -/
@[expose] def «send/2» (_ : Dispatcher) (destination message : Term) : Result :=
  match destination with
  | .pid pid => .send pid message (.ok message)
  | _ => .error (.error (.atom "badarg"))

/-- Return all process-dictionary bindings. Their order is unspecified by Erlang.erlang. -/
@[expose] def «get/0» (_ : Dispatcher) : Result := do
  let env ← get
  .ok ((env.pdict.map fun (key, value) => Term.tuple #[key, value]).foldr Term.cons Term.nil)

/-- Return the value stored under `key`, or `undefined`. -/
@[expose] def «get/1» (_ : Dispatcher) (key : Term) : Result := do
  let env ← get
  .ok ((env.pdict.findSome? fun (stored, value) =>
    if Term.exactCompare key stored = .eq then some value else none).getD (.atom "undefined"))

/-- Return all process-dictionary keys. Their order is unspecified by Erlang.erlang. -/
@[expose] def «get_keys/0» (_ : Dispatcher) : Result := do
  let env ← get
  .ok ((env.pdict.map Prod.fst).foldr Term.cons Term.nil)

/-- Return all keys associated with a semantically equal value. -/
@[expose] def «get_keys/1» (_ : Dispatcher) (value : Term) : Result := do
  let env ← get
  .ok ((env.pdict.filterMap fun entry =>
    if Term.exactCompare value entry.2 = .eq then some entry.1 else none).foldr Term.cons Term.nil)

/-- Store a binding and return its previous value, or `undefined`. -/
@[expose] def «put/2» (_ : Dispatcher) (key value : Term) : Result := do
  let env ← get
  let previous := (env.pdict.findSome? fun (stored, value) =>
    if Term.exactCompare key stored = .eq then some value else none).getD (.atom "undefined")
  set (env.setPdict ((key, value) :: env.pdict.filter fun entry => Term.exactCompare key entry.1 != .eq))
  .ok previous

/-- Return all process-dictionary bindings and clear the dictionary. -/
@[expose] def «erase/0» (_ : Dispatcher) : Result := do
  let env ← get
  set (env.setPdict [])
  .ok ((env.pdict.map fun (key, value) => Term.tuple #[key, value]).foldr Term.cons Term.nil)

/-- Delete `key` and return its previous value. -/
@[expose] def «erase/1» (_ : Dispatcher) (key : Term) : Result := do
  let env ← get
  let previous := (env.pdict.findSome? fun (stored, value) =>
    if Term.exactCompare key stored = .eq then some value else none).getD (.atom "undefined")
  set (env.setPdict (env.pdict.filter fun entry => Term.exactCompare key entry.1 != .eq))
  .ok previous

end Erlang.erlang
