module

public import Lynx

@[expose] public section

open Lynx Lynx.Concurrent

namespace ServerProof

/-- The root sends requests to the server, which replies to the root. -/
def talk (sender receiver : PID) : Prop :=
  (sender = [] ∧ receiver = [1]) ∨ (sender = [1] ∧ receiver = [])

theorem single : Concurrent.Single talk := by
  refine ⟨?_, ?_⟩
  · intro sender sender' receiver talks talks'
    rcases talks with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases talks' with ⟨same, other⟩ | ⟨same, other⟩ <;>
      first | exact same.symm | simp at other
  · intro sender receiver talks
    rcases talks with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- What the server replies for a list of integers. -/
def doubled : Term → Term
  | .cons (.integer n) rest => .cons (.integer (n * 2)) (doubled rest)
  | other => other

/-- The requests queued at the server for a list. -/
def requests : Term → List Entry
  | .cons x rest => ⟨[], .message (.tuple #[.atom "request", x])⟩ :: requests rest
  | _ => []

/-- A queue of messages from processes. -/
def Messages (queue : List Entry) : Prop :=
  ∀ entry ∈ queue, (∃ message, entry.signal = .message message) ∧ entry.source ≠ clock

theorem requests_quiet (xs : Term) : Messages (requests xs) := by
  induction xs using requests.induct with
  | case1 x rest ih =>
    simp only [Messages, requests, List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨⟨_, rfl⟩, by simp [clock]⟩, ih⟩
  | case2 xs notCons => cases xs <;> simp_all [requests, Messages]

/-- The length of a list term, which bounds the steps of each phase. -/
def len : Term → Nat
  | .cons _ rest => len rest + 1
  | _ => 0

/-- A record of a process that only queues messages and handles them into its mailbox. -/
theorem quiet_record {children : Nat} {queue : List Entry} {mailbox : List Term}
    (messages : Messages queue) : ({ children, queue, mailbox } : ProcessState).Quiet :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, messages⟩

theorem messages_nil : Messages [] := by simp [Messages]

theorem messages_request {rest : List Entry} (message : Term) (messages : Messages rest) :
    Messages (⟨[], .message message⟩ :: rest) := by
  simp only [Messages, List.mem_cons, forall_eq_or_imp]
  exact ⟨⟨⟨_, rfl⟩, by simp [clock]⟩, messages⟩

theorem messages_reply (message : Term) : Messages [⟨[1], .message message⟩] := by simp [Messages, clock]

theorem normalize_two {first second : PID} {record record' : ProcessState} {timers : List Timer}
    {elapsed : PID → Nat → Nat} (quiet : record.Quiet) (quiet' : record'.Quiet) :
    ({ processes := [(first, record), (second, record')], timers, elapsed } : State).normalize =
      { processes := [(first, record), (second, record')], timers, elapsed } :=
  State.normalize_of_quiet (by simp [quiet, quiet'])

theorem root_server : @BEq.beq (List Nat) Kernel.pidBEq [1] [] = false := rfl

theorem messages_append {sent : List Entry} (message : Term) (messages : Messages sent) :
    Messages (sent ++ [⟨[], .message message⟩]) := by
  intro entry mem
  simp only [List.mem_append, List.mem_singleton] at mem
  rcases mem with mem | rfl
  · exact messages entry mem
  · exact ⟨⟨_, rfl⟩, by simp [clock]⟩

end ServerProof
