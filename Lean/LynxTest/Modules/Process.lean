module

meta import LynxTest.ProofAudit
import Lynx
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.Compare
import all Lynx.Term.Runner
import all Lynx.Modules.Erlang.Process
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

namespace LynxTest.Modules.Process
open Lynx Lynx.Modules.Erlang

private def receiveAny : Result := .receive some .ok

private def receiveAtom (name : String) : Result :=
  .receive (fun message => match message with
    | .atom found => if found == name then some message else none
    | _ => none) .ok

private def returned (outcome : Outcome Term) : Option Term :=
  match outcome with
  | .ok value _ => some value
  | _ => none

private def mailbox (outcome : Outcome Term) : List Term :=
  match outcome with
  | .ok _ env | .error _ env | .deadlock env => env.currentProcess.mailbox

/-- Sending returns its argument and appends behind existing messages. -/
theorem send_to_self :
    Lynx.run (send_2 (.pid 1) (.integer 7)) =
      .ok (.integer 7) { currentProcess := { mailbox := [.integer 7] } } := by cbv

theorem send_rejects_non_pid :
    send_2 (.integer 1) .nil = .error (.error (.atom "badarg")) := by cbv

theorem send_to_missing_pid :
    Lynx.run (send_2 (.pid 99) (.integer 7)) = .ok (.integer 7) {} := by cbv

/-- A dictionary update must not erase pending messages. -/
theorem dictionary_preserves_mailbox :
    returned (Lynx.run (do
      let _ ← send_2 (.pid 1) (.integer 7)
      let _ ← put_2 (.atom "key") (.integer 8)
      receiveAny)) = some (.integer 7) := by cbv

/-- Skip unmatched messages and preserve their order on either side of the match. -/
theorem selective_receive_preserves_unmatched :
    (receiveAtom "wanted") { currentProcess := {
      mailbox := [.integer 1, .atom "wanted", .integer 2, .atom "wanted"] } } =
    .ok (.atom "wanted") { currentProcess := {
      mailbox := [.integer 1, .integer 2, .atom "wanted"] } } := by cbv

/-- Selectors can bind values and encode ordered clauses, not just predicates. -/
theorem receive_bindings_and_clause_priority :
    let computation : Result := .receive (fun message => match message with
      | .integer n => some (n + 1)
      | _ => some 0) (fun n => .ok (.integer n))
    computation { currentProcess := { mailbox := [.integer 7] } } =
      .ok (.integer 8) {} := by cbv

private def handshake : Result := do
  let child ← Result.spawn (do
    let _ ← receiveAtom "start"
    send_2 (.pid 1) (.atom "done")) (fun pid => .ok (Term.pid pid))
  let _ ← send_2 child (.atom "start")
  receiveAtom "done"

/-- Either process can block first, and both resume with their own state. -/
theorem blocked_processes_resume :
    Lynx.run handshake [.swap 2] = .ok (.atom "done") { pidCounter := 2 } ∧
    Lynx.run handshake [.current] = .ok (.atom "done") { pidCounter := 2 } := by
  cbv

private def interleavedSends : Result := do
  let _ ← Result.spawn (send_2 (.pid 1) (.atom "child")) (fun pid => .ok (Term.pid pid))
  let _ ← send_2 (.pid 1) (.atom "first")
  let _ ← send_2 (.pid 1) (.atom "second")
  let first ← receiveAny
  let second ← receiveAny
  let third ← receiveAny
  pure (.tuple #[first, second, third])

/-- Only the choice after the first send changes: the child runs between the
parent's two sends, despite the parent winning the spawn decision. -/
theorem send_is_a_scheduling_boundary :
    returned (Lynx.run interleavedSends [.current, .current]) =
      some (.tuple #[.atom "first", .atom "second", .atom "child"]) ∧
    returned (Lynx.run interleavedSends [.current, .swap 2]) =
      some (.tuple #[.atom "first", .atom "child", .atom "second"]) := by
  cbv

private def twoSenders : Result := do
  let _ ← Result.spawn (send_2 (.pid 1) (.atom "left")) (fun pid => .ok (Term.pid pid))
  let _ ← Result.spawn (send_2 (.pid 1) (.atom "right")) (fun pid => .ok (Term.pid pid))
  let first ← receiveAny
  let second ← receiveAny
  pure (.tuple #[first, second])

/-- With three processes, swap can select either worker at the same boundary. -/
theorem swap_selects_the_named_process :
    returned (Lynx.run twoSenders [.current, .swap 2]) =
      some (.tuple #[.atom "left", .atom "right"]) ∧
    returned (Lynx.run twoSenders [.current, .swap 3]) =
      some (.tuple #[.atom "right", .atom "left"]) := by
  cbv

/-- An unavailable PID choice must not strand runnable processes. -/
theorem invalid_schedule_falls_back :
    returned (Lynx.run interleavedSends [.swap 999]) =
      some (.tuple #[.atom "first", .atom "second", .atom "child"]) := by cbv

/-- Empty receive blocks, rather than raising or returning a fabricated value. -/
theorem empty_receive_deadlocks : Lynx.run receiveAny = .deadlock {} := by cbv

theorem nonmatching_receive_deadlocks :
    (receiveAtom "wanted") { currentProcess := { mailbox := [.integer 7] } } =
      .deadlock { currentProcess := { mailbox := [.integer 7] } } := by cbv

/-- Whole-tree completion cannot hide a child that is still waiting. -/
theorem blocked_child_prevents_completion :
    Lynx.run (Result.spawn receiveAny (fun _ => .ok (Term.atom "done"))) =
      .deadlock { pidCounter := 2, processes := [(2, {})] } := by cbv

/-- A receive cannot be recovered by an exception handler when no message matches. -/
theorem blocking_is_not_an_exception :
    Lynx.run (tryCatch receiveAny (fun _ => .ok (.atom "caught"))) = .deadlock {} := by cbv

/-- A selected receive body still raises in the receiving process. -/
theorem receive_body_exception_is_caught :
    returned (Lynx.run (do
      let _ ← send_2 (.pid 1) (.integer 7)
      tryCatch (Result.receive some (fun _ => .error (.error (.atom "failure"))))
        (fun _ => .ok (.atom "caught")))) = some (.atom "caught") := by cbv

/-- A child finishing first disappears; sending to its old PID creates no state. -/
theorem terminated_child_is_not_revived :
    Lynx.run (do
      let child ← Result.spawn (.ok .nil) (fun pid => .ok (Term.pid pid))
      send_2 child (.atom "ignored")) [.swap 2] =
      .ok (.atom "ignored") { pidCounter := 2 } := by cbv

/-- Root termination also closes its mailbox while the remaining children finish. -/
theorem terminated_root_discards_late_messages :
    mailbox (Lynx.run (Result.spawn (send_2 (.pid 1) (.atom "late"))
      (fun _ => .ok .nil))) = [] := by cbv

/-- Child exceptions do not become exceptions in the unlinked parent. -/
theorem child_exception_is_isolated :
    Lynx.run (Result.spawn (.error (.error (.atom "failure")))
      (fun _ => .ok (Term.atom "done"))) [.swap 2] =
      .ok (.atom "done") { pidCounter := 2 } := by cbv

private def isolatedDictionaries : Result := do
  let _ ← put_2 (.atom "key") (.atom "parent")
  let child ← Result.spawn (do
    let _ ← put_2 (.atom "key") (.atom "child")
    let _ ← receiveAtom "start"
    send_2 (.pid 1) (← get_1 (.atom "key"))) (fun pid => .ok (Term.pid pid))
  let _ ← send_2 child (.atom "start")
  let reply ← receiveAny
  let own ← get_1 (.atom "key")
  pure (.tuple #[own, reply])

theorem suspended_processes_keep_their_dictionaries :
    returned (Lynx.run isolatedDictionaries [.swap 2]) =
      some (.tuple #[.atom "parent", .atom "child"]) := by cbv

private def receiveBoundary : Result := do
  let _ ← Result.spawn (do
    let _ ← receiveAtom "start"
    send_2 (.pid 1) (.atom "child")) (fun pid => .ok (Term.pid pid))
  let _ ← send_2 (.pid 2) (.atom "start")
  let _ ← send_2 (.pid 1) (.atom "ready")
  let _ ← receiveAtom "ready"
  let _ ← send_2 (.pid 1) (.atom "parent")
  receiveAny

theorem successful_receive_is_a_scheduling_boundary :
    returned (Lynx.run receiveBoundary []) = some (.atom "parent") ∧
    returned (Lynx.run receiveBoundary
      [.current, .current, .current, .swap 2]) = some (.atom "child") := by
  cbv

/-- Selecting a blocked process falls back without discarding its continuation. -/
theorem waiting_schedule_choice_falls_back :
    Lynx.run handshake [.swap 2, .swap 1] =
      .ok (.atom "done") { pidCounter := 2 } := by cbv

/-- The solver must treat the added outcomes as known constructors rather than
repeatedly splitting them as if they were unevaluated computations. -/
theorem deadlock_cannot_accept (computation : Result) (env final : Environment)
    (stuck : computation env = .deadlock final) : ¬ Accepted computation env := by
  lynx_solve

private def sends : Nat → Result
  | 0 => .ok .nil
  | n + 1 => .send 99 .nil (sends n)

open Lynx.Term.Runner in
private theorem sends_execute (n : Nat) :
    execute 1 (save {}) (.process 1 (sends n) some) none 1 = .ok .nil {} := by
  induction n with
  | zero => cbv
  | succ n ih =>
    rw [execute]
    change execute 1 (save {}) (.process 1 (sends n) some) none 1 = .ok .nil {}
    exact ih

/-- Any finite number of sends completes, with no fixed execution cutoff. -/
theorem arbitrarily_many_sends (n : Nat) : Lynx.run (sends n) = .ok .nil {} := by
  cases n with
  | zero => rfl
  | succ n => exact sends_execute (n + 1)

end LynxTest.Modules.Process

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Modules.Process

run_cmd LynxTest.ProofAudit.checkModule `Lynx.Term.Runner
run_cmd LynxTest.ProofAudit.checkModule `Lynx.Term.DataTypes
