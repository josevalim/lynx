module

import Lynx.Modules.Erlang.erlang
import Lynx.Modules.Erlang.persistent_term
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

/-! Persistent terms, which every process shares. Updates become visible in a
step of their own, while their process is suspended, even after it exits. -/

namespace LynxTest.Modules.PersistentTerm
open Lynx Erlang Erlang.erlang

private def receiveAny : Result :=
  .receive .infinity (fun _ message => some message) fun
    | some message => .ok message
    | none => .ok .nil

private def key : Term := .atom "key"
private def undefined : Term := .atom "undefined"

/-- Read the key, or `undefined`. -/
private def read (dispatcher : Dispatcher) : Result := persistent_term.«get/2» dispatcher key undefined

/-- Children: one reads the key and sends it to the root, one stores `one`,
one stores `two`, each telling the root when done, and one stores `one` and
then waits. -/
private def functions : Term.FunTable := [
  { module := "test", name := "reads", arity := 0, entry := .effectful fun dispatcher _ _ => do
      let value ← read dispatcher
      «send/2» dispatcher (.pid []) value },
  { module := "test", name := "stores_one", arity := 0, entry := .effectful fun dispatcher _ _ => do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
      «send/2» dispatcher (.pid []) (.atom "done") },
  { module := "test", name := "stores_two", arity := 0, entry := .effectful fun dispatcher _ _ => do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "two")
      «send/2» dispatcher (.pid []) (.atom "done") },
  { module := "test", name := "stores_and_waits", arity := 0, entry := .effectful fun dispatcher _ _ => do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
      receiveAny }]

private def dispatcher : Dispatcher := Dispatcher.ofTable functions 1

private def reads : Term := .function "test" "reads" 0 #[]
private def storesOne : Term := .function "test" "stores_one" 0 #[]
private def storesTwo : Term := .function "test" "stores_two" 0 #[]
private def storesAndWaits : Term := .function "test" "stores_and_waits" 0 #[]

/-- Accept exactly one outcome, for proofs over every schedule. -/
private def only (expected : Outcome Term) (actual : Outcome Term) : Bool :=
  match expected, actual with
  | .ok expected, .ok actual => Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | .error (.error expected), .error (.error actual) =>
      Term.compareExact (Term.fuel expected actual) expected actual == .eq
  | _, _ => false

/-- Accept any of the given results. -/
private def oneOf (expected : List Term) : Outcome Term → Bool
  | .ok actual => expected.any ((fun a b => Term.compareExact (Term.fuel a b) a b) · actual == .eq)
  | _ => false

/-- Accept exactly one result, to find a run reaching it. -/
private def exactly (expected : Term) : Outcome Term → Bool
  | .ok actual => expected.identical actual
  | _ => false

private theorem eq_of_exactly {expected : Term} {outcome : Outcome Term}
    (accepted : exactly expected outcome = true) : outcome = .ok expected := by
  cases outcome with
  | ok actual => simp only [exactly] at accepted; rw [Term.eq_of_identical accepted]
  | _ => simp [exactly] at accepted

/-! ### One process -/

/-- An update is visible to its process once it returns. -/
theorem put_then_get :
    Concurrent.check (only (.ok (.atom "one"))) 32 (.start {} (do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
      persistent_term.«get/1» dispatcher key)) = true := by decide +kernel

theorem get_missing_raises :
    Concurrent.check (only (.error (.error (.atom "badarg")))) 32 (.start {} (persistent_term.«get/1» dispatcher key)) = true := by
  decide +kernel

theorem get_missing_default :
    Concurrent.check (only (.ok undefined)) 32 (.start {} (read dispatcher)) = true := by decide +kernel

/-- `put_new/2` raises when another value is stored, and returns `ok` for the same one. -/
theorem put_new_other_raises :
    Concurrent.check (only (.error (.error (.atom "badarg")))) 32 (.start {} (do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
      persistent_term.«put_new/2» dispatcher key (.atom "two"))) = true := by decide +kernel

theorem put_new_same :
    Concurrent.check (only (.ok (.tuple #[.atom "ok", .atom "one"]))) 32 (.start {} (do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
      let stored ← persistent_term.«put_new/2» dispatcher key (.atom "one")
      let value ← persistent_term.«get/1» dispatcher key
      pure (.tuple #[stored, value]))) = true := by decide +kernel

theorem erase_reports :
    Concurrent.check (only (.ok (.tuple #[.atom "true", undefined, .atom "false"]))) 32 (.start {} (do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
      let erased ← persistent_term.«erase/1» dispatcher key
      let value ← read dispatcher
      let again ← persistent_term.«erase/1» dispatcher key
      pure (.tuple #[erased, value, again]))) = true := by decide +kernel

/-! ### Races -/

/-- A reader racing an update reads either value, and both are reachable. -/
private def racingRead : Result := do
  let _ ← «spawn/1» dispatcher reads
  let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
  receiveAny

theorem racing_read :
    Concurrent.check (oneOf [undefined, .atom "one"]) 32 (.start {} racingRead) = true := by decide +kernel

theorem racing_read_old : Lynx.reachable racingRead (.ok undefined) :=
  Lynx.reachable_of_witness racingRead (exactly undefined) 32 (fun _ _ => 0) (by decide +kernel)
    fun _ => eq_of_exactly

theorem racing_read_new : Lynx.reachable racingRead (.ok (.atom "one")) :=
  Lynx.reachable_of_witness racingRead (exactly (.atom "one")) 32 (fun _ _ => 0) (by decide +kernel)
    fun _ => eq_of_exactly

/-- A process spawned after an update returned reads it. -/
theorem read_after_put :
    Concurrent.check (only (.ok (.atom "one"))) 32 (.start {} (do
      let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
      let _ ← «spawn/1» dispatcher reads
      receiveAny)) = true := by decide +kernel

/-- Two updates of the same key take turns, in either order. -/
private def racingPuts : Result := do
  let _ ← «spawn/1» dispatcher storesOne
  let _ ← «spawn/1» dispatcher storesTwo
  let _ ← receiveAny
  let _ ← receiveAny
  persistent_term.«get/1» dispatcher key

theorem racing_puts :
    Concurrent.check (oneOf [.atom "one", .atom "two"]) 64 (.start {} racingPuts) = true := by decide +kernel

theorem racing_puts_one : Lynx.reachable racingPuts (.ok (.atom "one")) :=
  Lynx.reachable_of_witness racingPuts (exactly (.atom "one")) 64 (fun _ _ => 0) (by decide +kernel)
    fun _ => eq_of_exactly

theorem racing_puts_two : Lynx.reachable racingPuts (.ok (.atom "two")) :=
  Lynx.reachable_of_witness racingPuts (exactly (.atom "two")) 64 (fun _ _ => 0) (by decide +kernel)
    fun _ => eq_of_exactly

/-- A process may be killed while its update is staged, which still becomes
visible: a run reaches its `DOWN`, then a read finding no value, then a read
finding the update, as OTP still makes the update visible
(`release_update_permission` in `erl_bif_persistent.c` skips resuming an
exiting updater). -/
private def killedWhileStaged : Result := do
  let _ ← «spawn_monitor/1» dispatcher storesAndWaits
  let _ ← «exit/2» dispatcher (.pid [1]) (.atom "kill")
  let _ ← receiveAny
  let before ← read dispatcher
  let after ← read dispatcher
  pure (.tuple #[before, after])

theorem killed_while_staged :
    Lynx.reachable killedWhileStaged (.ok (.tuple #[undefined, .atom "one"])) :=
  Lynx.reachable_of_witness killedWhileStaged (exactly (.tuple #[undefined, .atom "one"])) 64 (fun _ _ => 0)
    (by decide +kernel) fun _ => eq_of_exactly

/-- `put_new/2` on a missing key stores the value. -/
theorem put_new_missing :
    Concurrent.check (only (.ok (.tuple #[.atom "ok", .atom "one"]))) 32 (.start {} (do
      let stored ← persistent_term.«put_new/2» dispatcher key (.atom "one")
      let value ← persistent_term.«get/1» dispatcher key
      pure (.tuple #[stored, value]))) = true := by decide +kernel

/-- A reader racing an erase reads either value, and both are reachable. -/
private def racingErase : Result := do
  let _ ← persistent_term.«put/2» dispatcher key (.atom "one")
  let _ ← «spawn/1» dispatcher reads
  let _ ← persistent_term.«erase/1» dispatcher key
  receiveAny

theorem racing_erase :
    Concurrent.check (oneOf [undefined, .atom "one"]) 32 (.start {} racingErase) = true := by decide +kernel

theorem racing_erase_old : Lynx.reachable racingErase (.ok (.atom "one")) :=
  Lynx.reachable_of_witness racingErase (exactly (.atom "one")) 32 (fun _ _ => 0) (by decide +kernel)
    fun _ => eq_of_exactly

theorem racing_erase_new : Lynx.reachable racingErase (.ok undefined) :=
  Lynx.reachable_of_witness racingErase (exactly undefined) 32 (fun _ _ => 0) (by decide +kernel)
    fun _ => eq_of_exactly

/-- An erase racing another process's update takes turns with it: it erases
the update, after which a read finds nothing, or finds no value, after which a
read finds nothing or the update. Erasing never returns before an update it
saw is visible. -/
theorem erase_takes_turns :
    Concurrent.check (oneOf [.tuple #[.atom "false", .atom "one"], .tuple #[.atom "false", undefined],
      .tuple #[.atom "true", undefined]]) 64
      (.start {} (do
        let _ ← «spawn/1» dispatcher storesOne
        let erased ← persistent_term.«erase/1» dispatcher key
        let value ← read dispatcher
        let _ ← receiveAny
        pure (.tuple #[erased, value]))) = true := by decide +kernel

end LynxTest.Modules.PersistentTerm

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Modules.PersistentTerm
