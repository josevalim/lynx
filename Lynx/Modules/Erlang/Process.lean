import Lynx.Term

/-! Erlang process identity and process-dictionary operations. -/

namespace Lynx.Modules.Erlang

open Lynx

/-- Return the PID of the process running the current computation. -/
def self_0 : Result := do
  let env ← get
  .ok (.pid env.currentPid)

private def termList : List Term → Term
  | [] => .nil
  | head :: tail => .cons head (termList tail)

private def pdictFind (key : Term) : List (Term × Term) → Option Term
  | [] => none
  | (stored, value) :: rest =>
      if Term.exactCompare key stored = .eq then some value else pdictFind key rest

private def pdictRemove (key : Term) : List (Term × Term) → List (Term × Term)
  | [] => []
  | entry :: rest =>
      if Term.exactCompare key entry.1 = .eq then pdictRemove key rest
      else entry :: pdictRemove key rest

private def undefinedOr : Option Term → Term
  | some value => value
  | none => .atom "undefined"

/-- Return all process-dictionary bindings. Their order is unspecified by Erlang. -/
def get_0 : Result := do
  let env ← get
  .ok (termList (env.pdict.map fun (key, value) => .tuple #[key, value]))

/-- Return the value stored under `key`, or `undefined`. -/
def get_1 (key : Term) : Result := do
  let env ← get
  .ok (undefinedOr (pdictFind key env.pdict))

/-- Return all process-dictionary keys. Their order is unspecified by Erlang. -/
def get_keys_0 : Result := do
  let env ← get
  .ok (termList (env.pdict.map Prod.fst))

/-- Return all keys associated with a semantically equal value. -/
def get_keys_1 (value : Term) : Result := do
  let env ← get
  .ok (termList (env.pdict.filterMap fun entry =>
    if Term.exactCompare value entry.2 = .eq then some entry.1 else none))

/-- Store a binding and return its previous value, or `undefined`. -/
def put_2 (key value : Term) : Result := do
  let env ← get
  let previous := undefinedOr (pdictFind key env.pdict)
  set (env.setPdict ((key, value) :: pdictRemove key env.pdict))
  .ok previous

/-- Return all process-dictionary bindings and clear the dictionary. -/
def erase_0 : Result := do
  let env ← get
  set (env.setPdict [])
  .ok (termList (env.pdict.map fun (key, value) => .tuple #[key, value]))

/-- Delete `key` and return its previous value. -/
def erase_1 (key : Term) : Result := do
  let env ← get
  let previous := undefinedOr (pdictFind key env.pdict)
  set (env.setPdict (pdictRemove key env.pdict))
  .ok previous

end Lynx.Modules.Erlang
