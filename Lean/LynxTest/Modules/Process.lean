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

/-- These operations make no dynamic calls. -/
private def noFunctions : Dispatcher := Dispatcher.ofTable [] 0

theorem error_reason (reason arguments : Term) :
    «error/2» reason arguments = .error (.error reason) := by rfl

theorem error_caught (reason arguments : Term) :
    Result.handle (Result.ofExcept («error/2» reason arguments)) (fun
      | .error value => .ok value
      | exception => .error exception) =
      .ok reason := by
  rfl

private def receiveBlocking (select : Term → Option β) (next : β → Result) : Result :=
  .receive .infinity (fun _ => select) (fun
    | some value => next value
    | none => .ok .nil)

private def receiveAny : Result := receiveBlocking some .ok

private def receiveAtom (name : String) : Result :=
  receiveBlocking (fun message => match message with
    | .atom found => if found == name then some message else none
    | _ => none) .ok

/-- Queue messages in the root's mailbox, then run the computation. -/
private def queued (messages : List Term) (computation : Result) : Result :=
  messages.foldr (fun message next => .send [] message next) computation

/-- Consume up to `count` queued messages without blocking, as a list. -/
private def drain : Nat → Result
  | 0 => .ok .nil
  | count + 1 => .receive .immediate (fun _ message => some message) fun
      | some message => do
        let rest ← drain count
        pure (.cons message rest)
      | none => .ok .nil

/-- The computation's value and the messages it leaves in the mailbox. -/
private def leaving (computation : Result) : Result := do
  let value ← computation
  let rest ← drain 8
  pure (.tuple #[value, rest])

private def list (items : List Term) : Term := items.foldr .cons .nil

/-- Allocation changes only the reference counter, for any initial environment. -/
theorem make_ref_preserves_process_state (env : Environment) :
    («make_ref/0» noFunctions) env =
      (.ok (.reference (env.currentPid ++ [env.refCounter + 1])),
        { env with refCounter := env.refCounter + 1 }) := by simp

/-- The process's previously allocated identities lie below the next reference. -/
theorem make_ref_fresh (env : Environment) (previous : Nat)
    (allocated : previous ≤ env.refCounter) :
    Term.reference (env.currentPid ++ [env.refCounter + 1]) ≠
      .reference (env.currentPid ++ [previous]) := by
  intro equal
  simp at equal
  omega

theorem successive_references_are_distinct (env : Environment) :
    (do
      let first ← («make_ref/0» noFunctions)
      let second ← («make_ref/0» noFunctions)
      Result.ofExcept («=:=/2» first second)) env =
    (.ok Term.false, { env with refCounter := env.refCounter + 2 }) := by
  simp [«=:=/2», Nat.add_assoc]

theorem reference_type_guard (input : Term) :
    «is_reference/1» input = .ok Term.true ↔ ∃ id, input = .reference id := by
  cases input <;> simp [«is_reference/1», Term.true, Term.false]

theorem make_ref_is_effectful :
    ¬ Result.IsReadOnly («make_ref/0» noFunctions) ∧ ¬ Result.IsPure («make_ref/0» noFunctions) := by
  constructor
  · intro readOnly
    exact readOnly {}
  · intro pure
    exact (show ¬ Result.IsReadOnly («make_ref/0» noFunctions) from fun readOnly => readOnly {})
      (Result.IsPure.readOnly _ pure)

/-- Dictionary writes must preserve allocation state between calls. -/
theorem dictionary_preserves_reference_counter :
    Result.run (do
      let first ← («make_ref/0» noFunctions)
      let _ ← «put/2» noFunctions (.atom "key") first
      let second ← («make_ref/0» noFunctions)
      pure (Term.tuple #[first, second])) {} =
    (.ok (.tuple #[.reference [1], .reference [2]]), {
      refCounter := 2, pdict := [(.atom "key", .reference [1])] }) := by cbv

private def referenceExchange : Result := do
  let first ← («make_ref/0» noFunctions)
  let _ ← Result.schedule {} (do
    let ref ← («make_ref/0» noFunctions)
    «send/2» noFunctions (.pid []) ref) (fun pid => .ok (Term.pid pid))
  let second ← («make_ref/0» noFunctions)
  let child ← receiveAny
  pure (.tuple #[first, second, child])

/-- Each process allocates references under its own PID, so they are unique
across processes and do not depend on the schedule. -/
theorem references_are_unique_across_processes :
    Result.run referenceExchange {} [.swap [1]] =
      (.ok (.tuple #[.reference [1], .reference [2], .reference [1, 1]]), { refCounter := 2 }) ∧
    Result.run referenceExchange {} [.current] =
      (.ok (.tuple #[.reference [1], .reference [2], .reference [1, 1]]), { refCounter := 2 }) := by
  cbv

/-- Sending returns its argument and appends behind existing messages. -/
theorem send_to_self :
    Lynx.sequential (leaving («send/2» noFunctions (.pid []) (.integer 7))) =
      .ok (.tuple #[.integer 7, list [.integer 7]]) := by cbv

theorem send_rejects_non_pid :
    «send/2» noFunctions (.integer 1) .nil = .error (.error (.atom "badarg")) := by cbv

theorem send_to_missing_pid :
    Lynx.sequential («send/2» noFunctions (.pid [99]) (.integer 7)) = .ok (.integer 7) := by cbv

/-- A dictionary update must not erase pending messages. -/
theorem dictionary_preserves_mailbox :
    Lynx.sequential (do
      let _ ← «send/2» noFunctions (.pid []) (.integer 7)
      let _ ← «put/2» noFunctions (.atom "key") (.integer 8)
      receiveAny) = .ok (.integer 7) := by cbv

/-- Skip unmatched messages and preserve their order on either side of the match. -/
theorem selective_receive_preserves_unmatched :
    Lynx.sequential (queued [.integer 1, .atom "wanted", .integer 2, .atom "wanted"]
      (leaving (receiveAtom "wanted"))) =
    .ok (.tuple #[.atom "wanted", list [.integer 1, .integer 2, .atom "wanted"]]) := by cbv

/-- Selectors can bind values and encode ordered clauses, not just predicates. -/
theorem receive_bindings_and_clause_priority :
    let computation : Result := receiveBlocking (fun message => match message with
      | .integer n => some (n + 1)
      | _ => some 0) (fun n => .ok (.integer n))
    Lynx.sequential (queued [.integer 7] computation) = .ok (.integer 8) := by cbv

private def receiveTimed (duration : Term) : Result :=
  Result.receiveWith duration (fun _ message => match message with
    | .atom "wanted" => some message
    | _ => none) (fun
      | some value => .ok value
      | none => .ok (.atom "timeout"))

/-- A poll scans past rejected messages and consumes only its first match. -/
theorem zero_timeout_scans_mailbox :
    Lynx.sequential (queued [.integer 1, .atom "wanted", .integer 2]
      (leaving (receiveTimed (.integer 0)))) =
    .ok (.tuple #[.atom "wanted", list [.integer 1, .integer 2]]) := by cbv

theorem zero_timeout_preserves_unmatched :
    Lynx.sequential (queued [.integer 1] (leaving (receiveTimed (.integer 0)))) =
    .ok (.tuple #[.atom "timeout", list [.integer 1]]) := by cbv

theorem infinity_never_expires :
    Result.run (receiveTimed (.atom "infinity")) {} [.timeout []] = (.deadlock, {}) := by cbv

/-- Timeout validation precedes scanning, even with a queued match. -/
theorem timeout_validation_precedes_scan :
    Lynx.sequential (queued [.atom "wanted"]
      (leaving (tryCatch (receiveTimed (.atom "invalid")) fun _ => .ok (.atom "caught")))) =
      .ok (.tuple #[.atom "caught", list [.atom "wanted"]]) ∧
    Lynx.sequential (receiveTimed (.atom "invalid")) = .error (.error (.atom "timeout_value")) ∧
    Lynx.sequential (receiveTimed (.integer (-1))) = .error (.error (.atom "timeout_value")) ∧
    Lynx.sequential (receiveTimed (.integer 4294967296)) =
      .error (.error (.atom "timeout_value")) := by
  repeat' apply And.intro
  all_goals cbv

/-- With no runnable sender, finite receives expire without an execution budget. -/
theorem finite_timeout_progress :
    Lynx.sequential (receiveTimed (.integer 1)) = .ok (.atom "timeout") ∧
    Lynx.sequential (receiveTimed (.integer 10000)) = .ok (.atom "timeout") := by cbv

private def timeoutRace : Result := do
  let _ ← Result.schedule {} («send/2» noFunctions (.pid []) (.atom "wanted")) (fun pid => .ok (Term.pid pid))
  receiveTimed (.integer 10)

/-- Blocking consumes a choice: the same program can receive or time out first. -/
theorem timeout_is_a_scheduler_choice :
    (timeoutRace.run {} [.current, .swap [1]]).1 = .ok (.atom "wanted") ∧
    (timeoutRace.run {} [.current, .timeout []]).1 = .ok (.atom "timeout") := by cbv

/-- Timer choices target waiting children as well as the root process. -/
theorem timeout_can_expire_child :
    Result.run (do
      let _ ← Result.schedule {} (do
        let value ← receiveTimed (.integer 10)
        «send/2» noFunctions (.pid []) value) (fun processId => .ok (Term.pid processId))
      receiveAny) {} [.current, .timeout [1]] = (.ok (.atom "timeout"), {}) := by cbv

/-- A timeout choice cannot discard a matching message already in the queue. -/
theorem queued_match_precedes_timeout_choice :
    ((queued [.atom "wanted"] (receiveTimed (.integer 10))).run {} [.timeout []]).1 =
      .ok (.atom "wanted") := by cbv

/-- Timeout exceptions and bodies remain covered by the receiving caller's handler. -/
theorem timeout_handler_scope :
    Lynx.sequential (tryCatch (receiveTimed (.integer (-1)))
      (fun _ => .ok (.atom "caught"))) = .ok (Term.atom "caught") ∧
    Lynx.sequential (tryCatch
      (Result.receiveWith (.integer 0) (β := Unit) (fun _ _ => none) (fun _ =>
        .error (.error (.atom "failure"))))
      (fun _ => .ok (.atom "caught"))) = .ok (Term.atom "caught") := by cbv

/-- Guard reads use the receiver's state while the scheduler scans other PIDs. -/
private def receiveSelf : Result :=
  Result.receiveWith (.atom "infinity") (fun env message =>
    match Result.toExceptRead (do
      let receiver ← («self/0» noFunctions)
      Result.ofExcept («=:=/2» message receiver)) env (by simp) with
    | .ok (.atom "true") => some message
    | _ => none) (fun reply => .ok (reply.getD .nil))

theorem guard_reads_waiting_child_identity :
    Result.run (do
      let child ← Result.schedule {} (do
        let value ← receiveSelf
        «send/2» noFunctions (.pid []) value) (fun pid => .ok (Term.pid pid))
      let _ ← «send/2» noFunctions child child
      receiveAny) {} [.swap [1]] = (.ok (.pid [1]), {}) := by cbv

private def receiveFalse : Result :=
  Result.receiveWith (.integer 0) (fun env message =>
    match Result.toExceptRead (Result.tryWith (Result.ofExcept («not/1» message))
      Result.ok (fun _ => .ok Term.false)) env
      (by simp (config := { maxDischargeDepth := 64 })) with
    | .ok (.atom "true") => some message
    | _ => none) (fun reply => .ok (reply.getD (.atom "timeout")))

/-- General try catches guard errors; both errors and false guards reject a
message without consuming it, and scanning continues to the next candidate. -/
theorem guard_errors_and_false_preserve_messages :
    Lynx.sequential (queued [.integer 7, .atom "true", .atom "false", .atom "tail"]
      (leaving receiveFalse)) =
    .ok (.tuple #[.atom "false", list [.integer 7, .atom "true", .atom "tail"]]) := by cbv

theorem guard_cannot_perform_process_effects :
    ¬ Result.IsReadOnly («send/2» noFunctions (.pid []) .nil) ∧
    ¬ Result.IsReadOnly («put/2» noFunctions (.atom "key") .nil) := by
  constructor
  · cbv
  · intro readOnly
    exact readOnly {}

theorem try_success_body_is_outside_handler :
    Lynx.sequential (Result.tryWith (.ok (.integer 7))
      (fun value => .error (.throw value)) (fun _ => .ok (Term.atom "caught"))) =
      .error (.throw (.integer 7)) := by cbv

theorem try_handler_exception_propagates :
    Lynx.sequential (Result.tryWith (.error (.error (.atom "protected")) : Result)
      Result.ok (fun _ => .error (.exit (.atom "handler")))) =
      .error (.exit (.atom "handler")) := by cbv

private def handshake : Result := do
  let child ← Result.schedule {} (do
    let _ ← receiveAtom "start"
    «send/2» noFunctions (.pid []) (.atom "done")) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» noFunctions child (.atom "start")
  receiveAtom "done"

/-- Either process can block first, and both resume with their own state. -/
theorem blocked_processes_resume :
    Result.run handshake {} [.swap [1]] = (.ok (.atom "done"), {}) ∧
    Result.run handshake {} [.current] = (.ok (.atom "done"), {}) := by
  cbv

private def interleavedSends : Result := do
  let _ ← Result.schedule {} («send/2» noFunctions (.pid []) (.atom "child")) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» noFunctions (.pid []) (.atom "first")
  let _ ← «send/2» noFunctions (.pid []) (.atom "second")
  let first ← receiveAny
  let second ← receiveAny
  let third ← receiveAny
  pure (.tuple #[first, second, third])

/-- Only the choice after the first send changes: the child runs between the
parent's two sends, despite the parent winning the spawn decision. -/
theorem send_is_a_scheduling_boundary :
    (interleavedSends.run {} [.current, .current]).1 =
      .ok (.tuple #[.atom "first", .atom "second", .atom "child"]) ∧
    (interleavedSends.run {} [.current, .swap [1]]).1 =
      .ok (.tuple #[.atom "first", .atom "child", .atom "second"]) := by
  cbv

private def twoSenders : Result := do
  let _ ← Result.schedule {} («send/2» noFunctions (.pid []) (.atom "left")) (fun pid => .ok (Term.pid pid))
  let _ ← Result.schedule {} («send/2» noFunctions (.pid []) (.atom "right")) (fun pid => .ok (Term.pid pid))
  let first ← receiveAny
  let second ← receiveAny
  pure (.tuple #[first, second])

/-- With three processes, swap can select either worker at the same boundary. -/
theorem swap_selects_the_named_process :
    (twoSenders.run {} [.current, .swap [1]]).1 =
      .ok (.tuple #[.atom "left", .atom "right"]) ∧
    (twoSenders.run {} [.current, .swap [2]]).1 =
      .ok (.tuple #[.atom "right", .atom "left"]) := by
  cbv

/-- An unavailable PID choice must not strand runnable processes. -/
theorem invalid_schedule_falls_back :
    (interleavedSends.run {} [.swap [999]]).1 =
      .ok (.tuple #[.atom "first", .atom "second", .atom "child"]) := by cbv

/-- Empty receive blocks, rather than raising or returning a fabricated value. -/
theorem empty_receive_deadlocks : Lynx.sequential receiveAny = .deadlock := by cbv

theorem nonmatching_receive_deadlocks :
    Lynx.sequential (queued [.integer 7] (receiveAtom "wanted")) = .deadlock := by cbv

/-- Whole-tree completion cannot hide a child that is still waiting. -/
theorem blocked_child_prevents_completion :
    Result.run (Result.schedule {} receiveAny (fun _ => .ok (Term.atom "done"))) {} =
      (.deadlock, {}) := by cbv

/-- A receive cannot be recovered by an exception handler when no message matches. -/
theorem blocking_is_not_an_exception :
    Lynx.sequential (tryCatch receiveAny (fun _ => .ok (.atom "caught"))) = .deadlock := by cbv

/-- A selected receive body still raises in the receiving process. -/
theorem receive_body_exception_is_caught :
    Lynx.sequential (do
      let _ ← «send/2» noFunctions (.pid []) (.integer 7)
      tryCatch (receiveBlocking some (fun _ => .error (.error (.atom "failure"))))
        (fun _ => .ok (.atom "caught"))) = .ok (Term.atom "caught") := by cbv

/-- A child finishing first disappears; sending to its old PID creates no state. -/
theorem terminated_child_is_not_revived :
    Result.run (do
      let child ← Result.schedule {} (.ok .nil) (fun pid => .ok (Term.pid pid))
      «send/2» noFunctions child (.atom "ignored")) {} [.swap [1]] =
      (.ok (.atom "ignored"), {}) := by cbv

/-- Root termination also closes its mailbox: a late message neither revives
the root nor blocks the remaining children, in any run. -/
theorem terminated_root_discards_late_messages :
    Lynx.concurrent (Result.schedule {} («send/2» noFunctions (.pid []) (.atom "late"))
      (fun _ => .ok Term.nil)) (.ok Term.nil) :=
  concurrent_of_check _ (fun | .ok .nil => true | _ => false) 16 (fun _ => by cbv)
    fun result accepted => by split at accepted <;> simp_all

/-- Child exceptions do not become exceptions in the unlinked parent. -/
theorem child_exception_is_isolated :
    Result.run (Result.schedule {} (.error (.error (.atom "failure")))
      (fun _ => .ok (Term.atom "done"))) {} [.swap [1]] =
      (.ok (.atom "done"), {}) := by cbv

private def isolatedDictionaries : Result := do
  let _ ← «put/2» noFunctions (.atom "key") (.atom "parent")
  let child ← Result.schedule {} (do
    let _ ← «put/2» noFunctions (.atom "key") (.atom "child")
    let _ ← receiveAtom "start"
    «send/2» noFunctions (.pid []) (← «get/1» noFunctions (.atom "key"))) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» noFunctions child (.atom "start")
  let reply ← receiveAny
  let own ← «get/1» noFunctions (.atom "key")
  pure (.tuple #[own, reply])

theorem suspended_processes_keep_their_dictionaries :
    (isolatedDictionaries.run {} [.swap [1]]).1 =
      .ok (.tuple #[.atom "parent", .atom "child"]) := by cbv

private def receiveBoundary : Result := do
  let _ ← Result.schedule {} (do
    let _ ← receiveAtom "start"
    «send/2» noFunctions (.pid []) (.atom "child")) (fun pid => .ok (Term.pid pid))
  let _ ← «send/2» noFunctions (.pid [1]) (.atom "start")
  let _ ← «send/2» noFunctions (.pid []) (.atom "ready")
  let _ ← receiveAtom "ready"
  let _ ← «send/2» noFunctions (.pid []) (.atom "parent")
  receiveAny

theorem successful_receive_is_a_scheduling_boundary :
    (receiveBoundary.run {} []).1 = .ok (.atom "parent") ∧
    (receiveBoundary.run {} [.current, .current, .current, .swap [1]]).1 = .ok (.atom "child") := by
  cbv

/-- Selecting a blocked process falls back without discarding its continuation. -/
theorem waiting_schedule_choice_falls_back :
    Result.run handshake {} [.swap [1], .swap []] =
      (.ok (.atom "done"), {}) := by cbv

/-! Exploring every interleaving proves outcomes for every run, and so for all
scheduler choices, not only for the schedules listed above. -/

theorem handshake_every_run : Lynx.concurrent handshake (.ok (.atom "done")) :=
  concurrent_of_check handshake (fun | .ok (.atom "done") => true | _ => false) 32 (fun _ => by cbv)
    fun result accepted => by split at accepted <;> simp_all

/-- Both delivery orders are possible, and no other outcome is. -/
theorem two_senders_every_run {events : List Concurrent.Event} {last : Concurrent.Config Term}
    {outcome : Outcome Term} (run : Concurrent.Run (.start {} twoSenders) events last)
    (terminal : Concurrent.Terminal last outcome) :
    outcome = .ok (.tuple #[.atom "left", .atom "right"]) ∨
    outcome = .ok (.tuple #[.atom "right", .atom "left"]) := by
  have checked := Concurrent.check_sound (accept := fun
      | .ok (.tuple ⟨[.atom "left", .atom "right"]⟩) => true
      | .ok (.tuple ⟨[.atom "right", .atom "left"]⟩) => true
      | _ => false) (depth := 32) (by cbv) run terminal
  split at checked
  · exact .inl rfl
  · exact .inr rfl
  · contradiction

/-- Exploration reaches both delivery orders, so a single order is not provable. -/
theorem two_senders_check_rejects_one_order :
    Concurrent.check (fun
      | .ok (.tuple ⟨[.atom "left", .atom "right"]⟩) => true
      | _ => false) 32 (.start {} twoSenders) = false := by cbv

/-- A deadlocked computation cannot have a successful return. -/
theorem deadlock_cannot_accept (computation : Result) (env final : Environment)
    (stuck : computation env = (.deadlock, final)) :
    ¬ ∃ value returnedEnv, computation env = (.ok value, returnedEnv) := by
  rintro ⟨value, returnedEnv, returned⟩
  rw [stuck] at returned
  cases returned

private def sends : Nat → Result
  | 0 => .ok .nil
  | n + 1 => .send [99] .nil (sends n)

open Lynx.Term.Runner Lynx.Concurrent in
private theorem sends_execute (n : Nat) :
    execute [] (State.initial {}) (.process [] (sends n) some) none false [] .current [] = (.ok .nil, {}) := by
  induction n with
  | zero => cbv
  | succ n ih =>
    rw [execute, choose]
    change execute [] (State.initial {}) (.process [] (sends n) some) none false [] .current [] = (.ok .nil, {})
    exact ih

/-- Any finite number of sends completes, with no fixed execution cutoff. -/
theorem arbitrarily_many_sends (n : Nat) : Lynx.sequential (sends n) = .ok .nil := by
  cases n with
  | zero => rfl
  | succ n => exact congrArg Prod.fst (sends_execute (n + 1))

end LynxTest.Modules.Process

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Modules.Process

run_cmd LynxTest.ProofAudit.checkModule `Lynx.Term.Runner
run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Reduction
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Confluence
run_cmd LynxTest.ProofAudit.checkModule `Lynx.Term.DataTypes

run_cmd LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang.Exceptions
