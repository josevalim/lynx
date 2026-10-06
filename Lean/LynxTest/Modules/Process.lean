module

import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit
import Lynx
import all Lynx.Term
import all Lynx.Term.DataTypes
import all Lynx.Term.Compare
import all Lynx.Term.Runner
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

namespace LynxTest.Modules.Process
open Lynx Erlang.erlang

private def receiveBlocking (select : Term → Option β) (next : β → Result) : Result :=
  .receive .infinity (fun _ => select) (fun
    | some value => next value
    | none => .ok .nil)

private def receiveAny : Result := receiveBlocking some .ok

private def receiveAtom (name : String) : Result :=
  receiveBlocking (fun message => match message with
    | .atom found => if found == name then some message else none
    | _ => none) .ok

private def returned (outcome : Outcome Term) : Option Term :=
  match outcome with
  | .ok value _ => some value
  | _ => none

private def mailbox (outcome : Outcome Term) : List Term :=
  match outcome with
  | .ok _ env | .error _ env | .deadlock env | .exhausted env => env.currentProcess.mailbox

/-- Sending returns its argument and appends behind existing messages. -/
theorem send_to_self :
    Lynx.run («send/2» (.pid 1) (.integer 7)) =
      .ok (.integer 7) { currentProcess := { mailbox := [.integer 7] } } := by cbv

theorem send_rejects_non_pid :
    «send/2» (.integer 1) .nil = .error (.error (.atom "badarg")) := by cbv

theorem send_to_missing_pid :
    Lynx.run («send/2» (.pid 99) (.integer 7)) = .ok (.integer 7) {} := by cbv

/-- A dictionary update must not erase pending messages. -/
theorem dictionary_preserves_mailbox :
    returned (Lynx.run (do
      let _ ← «send/2» (.pid 1) (.integer 7)
      let _ ← «put/2» (.atom "key") (.integer 8)
      receiveAny)) = some (.integer 7) := by cbv

/-- Skip unmatched messages and preserve their order on either side of the match. -/
theorem selective_receive_preserves_unmatched :
    (receiveAtom "wanted") { currentProcess := {
      mailbox := [.integer 1, .atom "wanted", .integer 2, .atom "wanted"] } } =
    .ok (.atom "wanted") { currentProcess := {
      mailbox := [.integer 1, .integer 2, .atom "wanted"] } } := by cbv

/-- Selectors can bind values and encode ordered clauses, not just predicates. -/
theorem receive_bindings_and_clause_priority :
    let computation : Result := receiveBlocking (fun message => match message with
      | .integer n => some (n + 1)
      | _ => some 0) (fun n => .ok (.integer n))
    computation { currentProcess := { mailbox := [.integer 7] } } =
      .ok (.integer 8) {} := by cbv

private def receiveTimed (duration : Term) : Result :=
  Result.receiveWith duration (fun _ message => match message with
    | .atom "wanted" => some message
    | _ => none) (fun
      | some value => .ok value
      | none => .ok (.atom "timeout"))

/-- A poll scans past rejected messages and consumes only its first match. -/
theorem zero_timeout_scans_mailbox :
    (receiveTimed (.integer 0)) { currentProcess := {
      mailbox := [.integer 1, .atom "wanted", .integer 2] } } =
    .ok (.atom "wanted") { currentProcess := { mailbox := [.integer 1, .integer 2] } } := by cbv

theorem zero_timeout_preserves_unmatched :
    (receiveTimed (.integer 0)) { currentProcess := { mailbox := [.integer 1] } } =
    .ok (.atom "timeout") { currentProcess := { mailbox := [.integer 1] } } := by cbv

theorem infinity_never_expires :
    (receiveTimed (.atom "infinity")) { schedule := [.timeout 1] } = .deadlock {} := by cbv

/-- Timeout validation precedes scanning, even with a queued match. -/
theorem timeout_validation_precedes_scan :
    (receiveTimed (.atom "invalid")) { currentProcess := { mailbox := [.atom "wanted"] } } =
      .error (.error (.atom "timeout_value")) { currentProcess := { mailbox := [.atom "wanted"] } } ∧
    Lynx.run (receiveTimed (.atom "invalid")) = .error (.error (.atom "timeout_value")) {} ∧
    Lynx.run (receiveTimed (.integer (-1))) = .error (.error (.atom "timeout_value")) {} ∧
    Lynx.run (receiveTimed (.integer 4294967296)) = .error (.error (.atom "timeout_value")) {} := by
  repeat' apply And.intro
  all_goals cbv

/-- With no runnable sender, finite receives expire without an execution budget. -/
theorem finite_timeout_progress :
    Lynx.run (receiveTimed (.integer 1)) = .ok (.atom "timeout") {} ∧
    Lynx.run (receiveTimed (.integer 10000)) = .ok (.atom "timeout") {} := by cbv

private def timeoutRace : Result := do
  let _ ← Result.schedule («send/2» (.pid 1) (.atom "wanted")) (fun pid => .ok (Term.pid pid))
  receiveTimed (.integer 10)

/-- Blocking consumes a choice: the same program can receive or time out first. -/
theorem timeout_is_a_scheduler_choice :
    returned (Lynx.run timeoutRace [.current, .swap 2]) = some (.atom "wanted") ∧
    returned (Lynx.run timeoutRace [.current, .timeout 1]) = some (.atom "timeout") := by cbv

/-- Timer choices target waiting children as well as the root process. -/
theorem timeout_can_expire_child :
    Lynx.run (do
      let _ ← Result.schedule (do
        let value ← receiveTimed (.integer 10)
        «send/2» (.pid 1) value) (fun processId => .ok (Term.pid processId))
      receiveAny) [.current, .timeout 2] = .ok (.atom "timeout") { pidCounter := 2 } := by cbv

/-- A timeout choice cannot discard a matching message already in the queue. -/
theorem queued_match_precedes_timeout_choice :
    (receiveTimed (.integer 10)) {
      currentProcess := { mailbox := [.atom "wanted"] }
      schedule := [.timeout 1] } = .ok (.atom "wanted") {} := by cbv

/-- Timeout exceptions and bodies remain covered by the receiving caller's handler. -/
theorem timeout_handler_scope :
    returned (Lynx.run (tryCatch (receiveTimed (.integer (-1)))
      (fun _ => .ok (.atom "caught")))) = some (.atom "caught") ∧
    returned (Lynx.run (tryCatch
      (Result.receiveWith (.integer 0) (β := Unit) (fun _ _ => none) (fun _ =>
        .error (.error (.atom "failure"))))
      (fun _ => .ok (.atom "caught")))) = some (.atom "caught") := by cbv

/-- Guard reads use the receiver's state while the scheduler scans other PIDs. -/
private def receiveSelf : Result :=
  Result.receiveWith (.atom "infinity") (fun env message =>
    match Result.toExceptRead (do
      let receiver ← «self/0»
      «=:=/2» message receiver) env (by simp) with
    | .ok (.atom "true") => some message
    | _ => none) (fun reply => .ok (reply.getD .nil))

theorem guard_reads_waiting_child_identity :
    Lynx.run (do
      let child ← Result.schedule (do
        let value ← receiveSelf
        «send/2» (.pid 1) value) (fun pid => .ok (Term.pid pid))
      let _ ← «send/2» child child
      receiveAny) [.swap 2] = .ok (.pid 2) { pidCounter := 2 } := by cbv

private def receiveFalse : Result :=
  Result.receiveWith (.integer 0) (fun env message =>
    match Result.toExceptRead (Result.tryWith («not/1» message)
      Result.ok (fun _ => .ok Term.false)) env
      (by simp (config := { maxDischargeDepth := 64 })) with
    | .ok (.atom "true") => some message
    | _ => none) (fun reply => .ok (reply.getD (.atom "timeout")))

/-- General try catches guard errors; both errors and false guards reject a
message without consuming it, and scanning continues to the next candidate. -/
theorem guard_errors_and_false_preserve_messages :
    receiveFalse { currentProcess := {
      mailbox := [.integer 7, .atom "true", .atom "false", .atom "tail"] } } =
    .ok (.atom "false") { currentProcess := {
      mailbox := [.integer 7, .atom "true", .atom "tail"] } } := by cbv

theorem guard_cannot_perform_process_effects :
    ¬ Result.IsReadOnly («send/2» (.pid 1) .nil) ∧
    ¬ Result.IsReadOnly («put/2» (.atom "key") .nil) := by
  constructor
  · cbv
  · intro readOnly
    exact readOnly {}

theorem try_success_body_is_outside_handler :
    Lynx.run (Result.tryWith (.ok (.integer 7))
      (fun value => .error (.throw value)) (fun _ => .ok (Term.atom "caught"))) =
      .error (.throw (.integer 7)) {} := by cbv

theorem try_handler_exception_propagates :
    Lynx.run (Result.tryWith (.error (.error (.atom "protected")) : Result)
      Result.ok (fun _ => .error (.exit (.atom "handler")))) =
      .error (.exit (.atom "handler")) {} := by cbv

private def handshake : Result := do
  let child ← Result.schedule (do
    let _ ← receiveAtom "start"
    «send/2» (.pid 1) (.atom "done")) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» child (.atom "start")
  receiveAtom "done"

/-- Either process can block first, and both resume with their own state. -/
theorem blocked_processes_resume :
    Lynx.run handshake [.swap 2] = .ok (.atom "done") { pidCounter := 2 } ∧
    Lynx.run handshake [.current] = .ok (.atom "done") { pidCounter := 2 } := by
  cbv

private def interleavedSends : Result := do
  let _ ← Result.schedule («send/2» (.pid 1) (.atom "child")) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» (.pid 1) (.atom "first")
  let _ ← «send/2» (.pid 1) (.atom "second")
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
  let _ ← Result.schedule («send/2» (.pid 1) (.atom "left")) (fun pid => .ok (Term.pid pid))
  let _ ← Result.schedule («send/2» (.pid 1) (.atom "right")) (fun pid => .ok (Term.pid pid))
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
    Lynx.run (Result.schedule receiveAny (fun _ => .ok (Term.atom "done"))) =
      .deadlock { pidCounter := 2, processes := [(2, {})] } := by cbv

/-- A receive cannot be recovered by an exception handler when no message matches. -/
theorem blocking_is_not_an_exception :
    Lynx.run (tryCatch receiveAny (fun _ => .ok (.atom "caught"))) = .deadlock {} := by cbv

/-- A selected receive body still raises in the receiving process. -/
theorem receive_body_exception_is_caught :
    returned (Lynx.run (do
      let _ ← «send/2» (.pid 1) (.integer 7)
      tryCatch (receiveBlocking some (fun _ => .error (.error (.atom "failure"))))
        (fun _ => .ok (.atom "caught")))) = some (.atom "caught") := by cbv

/-- A child finishing first disappears; sending to its old PID creates no state. -/
theorem terminated_child_is_not_revived :
    Lynx.run (do
      let child ← Result.schedule (.ok .nil) (fun pid => .ok (Term.pid pid))
      «send/2» child (.atom "ignored")) [.swap 2] =
      .ok (.atom "ignored") { pidCounter := 2 } := by cbv

/-- Root termination also closes its mailbox while the remaining children finish. -/
theorem terminated_root_discards_late_messages :
    mailbox (Lynx.run (Result.schedule («send/2» (.pid 1) (.atom "late"))
      (fun _ => .ok .nil))) = [] := by cbv

/-- Child exceptions do not become exceptions in the unlinked parent. -/
theorem child_exception_is_isolated :
    Lynx.run (Result.schedule (.error (.error (.atom "failure")))
      (fun _ => .ok (Term.atom "done"))) [.swap 2] =
      .ok (.atom "done") { pidCounter := 2 } := by cbv

private def isolatedDictionaries : Result := do
  let _ ← «put/2» (.atom "key") (.atom "parent")
  let child ← Result.schedule (do
    let _ ← «put/2» (.atom "key") (.atom "child")
    let _ ← receiveAtom "start"
    «send/2» (.pid 1) (← «get/1» (.atom "key"))) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» child (.atom "start")
  let reply ← receiveAny
  let own ← «get/1» (.atom "key")
  pure (.tuple #[own, reply])

theorem suspended_processes_keep_their_dictionaries :
    returned (Lynx.run isolatedDictionaries [.swap 2]) =
      some (.tuple #[.atom "parent", .atom "child"]) := by cbv

private def receiveBoundary : Result := do
  let _ ← Result.schedule (do
    let _ ← receiveAtom "start"
    «send/2» (.pid 1) (.atom "child")) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» (.pid 2) (.atom "start")
  let _ ← «send/2» (.pid 1) (.atom "ready")
  let _ ← receiveAtom "ready"
  let _ ← «send/2» (.pid 1) (.atom "parent")
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

/-- A deadlocked computation cannot have a successful return. -/
theorem deadlock_cannot_accept (computation : Result) (env final : Environment)
    (stuck : computation env = .deadlock final) :
    ¬ ∃ value returnedEnv, computation env = .ok value returnedEnv := by
  rintro ⟨value, returnedEnv, returned⟩
  rw [stuck] at returned
  cases returned

private def sends : Nat → Result
  | 0 => .ok .nil
  | n + 1 => .send 99 .nil (sends n)

open Lynx.Term.Runner in
private theorem sends_execute (n : Nat) :
    execute 1 (save {}) (.process 1 (sends n) some) none .current = .ok .nil {} := by
  induction n with
  | zero => cbv
  | succ n ih =>
    rw [execute, choose]
    change execute 1 (save {}) (.process 1 (sends n) some) none .current = .ok .nil {}
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

run_cmd LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang.Exceptions
