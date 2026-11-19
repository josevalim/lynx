module

public import Lynx.Term.DataTypes
public import Lynx.Concurrent.Kernel

/-! Interleaving semantics of local processes, as a labelled transition system.

`Lynx.Result.run` executes one interleaving chosen by its scheduler choices.
This module describes every interleaving instead: `Config.successors` lists the
steps of a configuration, a `Step` is one of them, and a `Run` collects the
`Event`s of consecutive steps as a trace. Concurrent laws are stated over these
runs (`Lynx.concurrent`).

Parity with OTP's behaviour is fundamental: every run OTP can take must be a
run here, and every reply must be one OTP can give, as modeled from OTP's
source rather than its documentation. A law proven here only says something
about a program on OTP as far as this holds, so precision may be traded for
proof performance, but never parity.

Processes affect each other only through signals, modeled after OTP's (`erts`
in OTP 30): messages, exit signals, links, monitors, `DOWN` messages, and
`is_process_alive` requests and replies. A sender puts a signal in its
receiver's queue at once, so a process's queue holds the signals of all senders
in the order they were sent, its own included. The receiver handles them one at
a time, in that order, against its state at that time, at any point of its own
computation. A `receive` only sees messages already handled; it times out at
once only after handling everything queued. Queues are causal as OTP's are with
on-heap message queues: with `message_queue_data` `off_heap`, OTP may buffer
signals per sender and reorder signals from different senders, which is not
modeled.

A process ends in phases: it stops being alive, then sends exit signals to its
links in any order and `DOWN` messages to its watchers in order, one at a time,
then answers the requests still queued, one at a time. Monitor signals wait, as OTP's scheduler parks them,
until their sender is scheduled out or signals the same process again. A
parked monitor signal of a process that ends, or of a monitor it removes, is
dropped: its target would only remove the monitor again, and a `DOWN` it
answers with only reaches a process that drops it.

The scheduler owns the `State` of every process. A running process only
observes and replaces its own `Environment`: its identity, its process
dictionary, and the reference allocator. A process that does not return ends,
and the run's outcome is then `Exception.exhausted`. -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-- The sender of timer messages. Children are numbered from one, so no
process has this PID. -/
@[expose] def clock : PID := [0]

/-- A signal from one process to another. -/
inductive Signal where
  | message (message : Term)
  /-- A message to an alias, dropped unless the alias is active when it is handled. -/
  | aliasMessage (alias : List Nat) (message : Term)
  /-- An exit signal, from a link or from `exit/2`. `normalKills`: the signal of
  an `exit/2` to the sender itself, which `normal` does not spare. -/
  | exit (reason : Term) (linked : Bool) (normalKills : Bool)
  | link
  /-- Remove a link; the receiver acknowledges with the same id. -/
  | unlink (id : Nat)
  | unlinkAck (id : Nat)
  /-- Start monitoring the receiver. -/
  | monitor (reference : List Nat)
  /-- The monitored process ended, so the monitor ends with a `DOWN` message. -/
  | down (reference : List Nat) (reason : Term)
  /-- An `is_process_alive` request, answered with a `reply`. -/
  | isAlive
  | reply (value : Term)
  /-- A marker a process sends itself to handle everything queued before it. -/
  | flush
deriving Repr

/-- A signal in a process's queue, with its sender. -/
structure Entry where
  source : PID
  signal : Signal
deriving Repr

/-- What a process that ended has left to send: exit signals to its links,
then `DOWN` messages to its watchers, then answers to its queued requests. -/
structure Exiting where
  reason : Term
  links : List PID
  downs : List (List Nat × PID)
deriving Repr

/-- The scheduler's record of a process. Each process allocates its own
references and child PIDs, so allocation does not depend on how processes
interleave. -/
structure ProcessState where
  /-- Signals not handled yet, oldest first. -/
  queue : List Entry := []
  /-- Messages handled, which `receive` scans. -/
  mailbox : List Term := []
  pdict : List (Term × Term) := []
  /-- Number of references the process allocated, forgotten once it ends. -/
  refCounter : Nat := 0
  /-- Number of processes the process spawned. -/
  children : Nat := 0
  /-- Linked processes; `some id` while this process unlinks with that id. -/
  links : List (PID × Option Nat) := []
  /-- Monitors on this process: each reference and the process that watches. -/
  monitors : List (List Nat × PID) := []
  /-- Monitors this process holds: each reference and the process it watches. -/
  monitoring : List (List Nat × PID) := []
  /-- Monitor references that are also destinations for this process. -/
  aliases : List (List Nat) := []
  /-- Whether exit signals arrive as messages. -/
  trapExit : Bool := false
  /-- Number of timers the process canceled before they fired. -/
  cancels : Nat := 0
  /-- Number of unlinks the process started. -/
  unlinks : Nat := 0
  /-- A monitor signal waiting for the process to be scheduled out: its target and reference. -/
  parked : Option (PID × List Nat) := none
  /-- The processes whose `normal` link exit removed a link when it was sent
  rather than handled, in PID order. This is only exact while the process does
  not start trapping exits, or link to the process again, before it would
  have handled the exit: before it handles the `normal` `DOWN` the same
  process sends after its link exits. A process that ended is gone before it
  sends its link exits (`ERTS_CONTINUE_EXIT_FREE` in OTP), so nothing else
  shows the exit was handled: a peer may see the process gone and time out a
  receive with the exit still on its way. -/
  eagerExits : List PID := []
  /-- Set once the process ended. -/
  exiting : Option Exiting := none
deriving Repr, Inhabited

/-- A timer that sends a message to a process. Elapsed time is not modeled:
it fires at any point, so its duration is only what canceling it reports. -/
structure Timer where
  /-- The reference `send_after` replies, allocated by the process starting it. -/
  reference : List Nat
  destination : PID
  message : Term
  duration : Nat
deriving Repr

/-- The runtime shared by all processes of a run. -/
structure State where
  /-- The records of processes that are alive or still ending, in the order of their PIDs. -/
  processes : List (PID × ProcessState) := []
  /-- Timers yet to fire, in the order of their references. -/
  timers : List Timer := []
  /-- The milliseconds elapsed when a process cancels a timer, by how many
  timers it canceled before. Elapsed time is not modeled: a run starts with any
  of these, and nothing changes them. -/
  elapsed : PID → Nat → Nat := fun _ _ => 0

/-- Whether one PID comes before another, comparing their paths. -/
@[expose] def pidBefore : PID → PID → Bool
  | [], _ :: _ => true
  | _, [] => false
  | first :: rest, first' :: rest' => first < first' || (first == first' && pidBefore rest rest')

/-- Insert a record in PID order. -/
@[expose] def insertSorted (processId : PID) (process : ProcessState) :
    List (PID × ProcessState) → List (PID × ProcessState)
  | [] => [(processId, process)]
  | (other, record) :: rest =>
      if pidBefore processId other then (processId, process) :: (other, record) :: rest
      else (other, record) :: insertSorted processId process rest

/-- Replace the record of a process, keeping the records in PID order, so the
state does not depend on the order in which processes were created. -/
@[expose] def insertRecord (processId : PID) (process : ProcessState)
    (records : List (PID × ProcessState)) : List (PID × ProcessState) :=
  insertSorted processId process (Kernel.filter (·.1 != processId) records)

/-- The record of a process, if it is alive or still ending. -/
@[expose] def State.record (state : State) (processId : PID) : Option ProcessState :=
  Kernel.lookup processId state.processes

/-- The record of a process, empty when there is none. -/
@[expose] def State.process (state : State) (processId : PID) : ProcessState :=
  (state.record processId).getD {}

/-- Replace the record of a process. -/
@[expose] def State.set (state : State) (processId : PID) (process : ProcessState) : State :=
  { state with processes := insertRecord processId process state.processes }

/-- Remove the record of a process. -/
@[expose] def State.remove (state : State) (processId : PID) : State :=
  { state with processes := Kernel.filter (·.1 != processId) state.processes }

/-- Change the record of a process that has one. -/
@[expose] def State.modify (state : State) (processId : PID)
    (change : ProcessState → ProcessState) : State :=
  match state.record processId with
  | some process => state.set processId (change process)
  | none => state

/-- Whether a process is alive: it has a record and has not ended. -/
@[expose] def State.alive (state : State) (processId : PID) : Bool :=
  match state.record processId with
  | some process => process.exiting.isNone
  | none => false

/-- What the process observes when it runs, including in receive guards. -/
@[expose] def State.view (state : State) (processId : PID) : Environment :=
  let process := state.process processId
  { currentPid := processId, refCounter := process.refCounter, pdict := process.pdict }

/-- Keep what the process left in its environment. Its identity is not stored,
and its reference counter never goes back, so references stay unique. -/
@[expose] def State.store (state : State) (processId : PID) (env : Environment) : State :=
  state.modify processId fun process =>
    { process with pdict := env.pdict, refCounter := max process.refCounter env.refCounter }

/-- Append a handled message to a mailbox. -/
@[expose] def State.append (state : State) (processId : PID) (message : Term) : State :=
  state.modify processId fun process =>
    { process with mailbox := Kernel.append process.mailbox [message] }

/-- Allocate the next reference of a process. -/
@[expose] def State.allocate (state : State) (processId : PID) : List Nat × State :=
  (Kernel.append processId [(state.process processId).refCounter + 1],
    state.modify processId fun process => { process with refCounter := process.refCounter + 1 })

/-- The reason a process exits with when it raises. Stack traces are not recorded. -/
@[expose] def exitReason : Exception → Term
  | .error reason => .tuple #[reason, .nil]
  | .throw value => .tuple #[.tuple #[.atom "nocatch", value], .nil]
  | .exit reason => reason
  | .exhausted => .atom "exhausted"

/-- Whether an exit reason is `normal`, which links ignore. -/
@[expose] def isNormal : Term → Bool
  | .atom "normal" => true
  | _ => false

/-- Whether an exit reason cannot be trapped. -/
@[expose] def isKill : Term → Bool
  | .atom "kill" => true
  | _ => false

/-- Whether a message has the shape `{_, Reference, _, _, _}` of a monitor's
`DOWN` message, which flushing a monitor removes. -/
@[expose] def isMonitorMessage (reference : List Nat) : Term → Bool
  | .tuple ⟨[_, .reference found, _, _, _]⟩ => found == reference
  | _ => false

/-- Whether a process can never be alive again: it ended, or never existed. -/
@[expose] def State.gone (state : State) (processId : PID) : Bool := !state.alive processId

/-- Whether a reference was allocated by a process, which therefore holds every
monitor and alias it will ever hold with it. -/
@[expose] def State.allocated (state : State) (owner : PID) (reference : List Nat) : Bool :=
  reference.dropLast == owner && match reference.getLast? with
    | some count => 1 ≤ count && count ≤ (state.process owner).refCounter
    | none => false

/-- A queued signal that does nothing when handled, now or later: a `DOWN` of a
monitor or a message to an alias its receiver no longer holds, or a request
from a process that is gone. An acknowledgement of an unlink is handled even
when it no longer matches a link, which then does nothing. -/
@[expose] def State.inertEntry (state : State) (processId : PID) (entry : Entry) : Bool :=
  let process := state.process processId
  match entry.signal with
  | .down reference _ => state.allocated processId reference &&
      !Kernel.any process.monitoring (·.1 == reference)
  | .aliasMessage alias _ => state.allocated processId alias &&
      !Kernel.contains process.aliases alias && !Kernel.any process.monitoring (·.1 == alias)
  | .isAlive | .monitor _ => state.gone entry.source
  | _ => false

/-- Whether a receive with a timeout handles a queued signal before it can
time out: it is not inert, nor the message of a timer, which may still be on
its way after `cancel_timer/1` replied that the timer expired. -/
@[expose] def State.awaitedEntry (state : State) (processId : PID) (entry : Entry) : Bool :=
  !(state.inertEntry processId entry || entry.source == clock)

/-- A signal to a process that is gone: the sender falls back as OTP's senders
do. A link is answered with an exit signal `noproc`, a monitor with a `DOWN`
`noproc`, an unlink removes the link at once, and the rest are dropped. -/
@[expose] def State.fallback (state : State) (source target : PID) : Signal → State
  | .link => state.modify source fun process => { process with
      queue := Kernel.append process.queue [{ source := target, signal := .exit (.atom "noproc") true false }] }
  | .monitor reference => state.modify source fun process => { process with
      queue := Kernel.append process.queue [{ source := target, signal := .down reference (.atom "noproc") }] }
  | .unlink _ => state.modify source fun process =>
      { process with links := Kernel.filter (·.1 != target) process.links }
  | .isAlive => state.modify source fun process => { process with
      queue := Kernel.append process.queue [{ source := target, signal := .reply (.atom "false") }] }
  | _ => state

/-- Put a signal in its receiver's queue. -/
@[expose] def State.enqueue (state : State) (source target : PID) (signal : Signal) : State :=
  match state.record target with
  | some process =>
      if process.exiting.isNone then
        state.set target { process with queue := Kernel.append process.queue [{ source, signal }] }
      else state.fallback source target signal
  | none => state.fallback source target signal

/-- Send a parked monitor signal. -/
@[expose] def State.unpark (state : State) (processId : PID) : State :=
  match (state.process processId).parked with
  | some (target, reference) =>
      (state.modify processId fun process => { process with parked := none }).enqueue processId target
        (.monitor reference)
  | none => state

/-- Send a signal. A monitor signal parked for the same target goes first. -/
@[expose] def State.send (state : State) (source target : PID) (signal : Signal) : State :=
  let state := match (state.process source).parked with
    | some (parked, _) => if parked == target then state.unpark source else state
    | none => state
  state.enqueue source target signal

/-- Insert a PID in PID order. -/
@[expose] def insertPid (processId : PID) : List PID → List PID
  | [] => [processId]
  | other :: rest => if pidBefore processId other then processId :: other :: rest
      else other :: insertPid processId rest

/-- Whether the exit signal of a process that ended to a link only removes
the link: it is `normal`, to a live process not trapping exits, which has no
link from the process left to handle. -/
@[expose] def State.eagerLink (state : State) (processId target : PID) (reason : Term) : Bool :=
  isNormal reason && state.alive target && !(state.process target).trapExit &&
    !Kernel.any (state.process target).queue (fun entry => entry.source == processId && entry.signal matches .link)

/-- An exit signal from a link of a process that ended. A `normal` one to a
live process not trapping exits only removes its link, so it is applied when
sent, and the receiver may not start trapping exits before it would have
handled it (`ProcessState.eagerExits`). It is queued instead while the receiver
has yet to handle a link from the process, which would come back otherwise. -/
@[expose] def State.linkExit (state : State) (processId target : PID) (reason : Term) : State :=
  if state.eagerLink processId target reason then
    state.modify target fun process => { process with
      links := Kernel.filter (·.1 != processId) process.links
      eagerExits := insertPid processId process.eagerExits }
  else state.send processId target (.exit reason true false)

/-- A process ends: it is no longer alive, timers sending to it are canceled,
its messages are dropped, and its queue keeps the requests it still answers.
It applies at once the link exits that only remove a link (`State.eagerLink`),
which nothing observes being sent, and has its other links and its watchers
left to signal. -/
@[expose] def State.terminate (state : State) (processId : PID) (reason : Term) : State :=
  let process := state.process processId
  let links := Kernel.foldl (fun links (peer, unlinking) =>
    if unlinking.isNone then insertPid peer links else links) [] process.links
  let queue := Kernel.filter (fun entry => match entry.signal with
    | .link | .monitor _ | .isAlive => true
    | _ => false) process.queue
  let state := { state with timers := Kernel.filter (·.destination != processId) state.timers }
  let state := state.set processId { process with
    mailbox := [], queue, parked := none, exiting := some { reason, links, downs := process.monitors } }
  Kernel.foldl (fun state target => if state.eagerLink processId target reason then
      (state.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
        { exiting with links := Kernel.filter (· != target) exiting.links } }).linkExit processId target reason
    else state) state links

/-- Answer a request queued at a process that ended: a link with an exit
signal `noproc`, a monitor with a `DOWN` `noproc`, and `is_process_alive` with `false`. -/
@[expose] def State.answer (state : State) (processId : PID) (entry : Entry) : State :=
  match entry.signal with
  | .link => state.send processId entry.source (.exit (.atom "noproc") true false)
  | .monitor reference => state.send processId entry.source (.down reference (.atom "noproc"))
  | .isAlive => state.send processId entry.source (.reply (.atom "false"))
  | _ => state

/-- A phase of a process that ended sending an exit signal to one of its links,
in any order: OTP walks the links in an order it leaves undefined, and other
processes run in between. -/
@[expose] def State.linkPhase (state : State) (processId target : PID) : Option State :=
  match state.record processId with
  | some process =>
    match process.exiting with
    | some exiting =>
        if Kernel.contains exiting.links target then
          some ((state.set processId { process with exiting := some { exiting with
            links := Kernel.filter (· != target) exiting.links } }).linkExit processId target exiting.reason)
        else none
    | none => none
  | none => none

/-- The next phase of a process that ended once it signaled its links: a
`DOWN` to a watcher, or answering the oldest request still queued.
Normalization removes the record once nothing is left. -/
@[expose] def State.phase (state : State) (processId : PID) : Option State :=
  match state.record processId with
  | some process =>
    match process.exiting with
    | some exiting =>
      match exiting.links, exiting.downs with
      | _ :: _, _ => none
      | [], (reference, watcher) :: rest =>
          some ((state.set processId { process with exiting := some { exiting with downs := rest } }).send
            processId watcher (.down reference exiting.reason))
      | [], [] =>
          match process.queue with
          | entry :: rest => some ((state.set processId { process with queue := rest }).answer processId entry)
          | [] => none
    | none => none
  | none => none

/-- The links a process that ended has left to signal. -/
@[expose] def State.exitLinks (state : State) (processId : PID) : List PID :=
  match (state.process processId).exiting with
  | some exiting => exiting.links
  | none => []

/-- Every next phase of a process that ended. -/
@[expose] def State.phases (state : State) (processId : PID) : List State :=
  Kernel.append (Kernel.filterMap (state.linkPhase processId) (state.exitLinks processId))
    (match state.phase processId with
      | some next => [next]
      | none => [])

/-! ### Normalization

After every step, what nothing can observe any more is removed, so that steps
whose effects only differ there lead to the same configuration. -/

/-- Whether a queued signal can still be observed: it is not inert, and for a
process that ended its sender is not gone. A link exit from a process that is
gone is kept even without an active link, as linking again before handling it
makes it act. -/
@[expose] def State.keepEntry (state : State) (processId : PID) (process : ProcessState) (entry : Entry) :
    Bool :=
  !(state.inertEntry processId entry || (process.exiting.isSome && state.gone entry.source))

/-- Whether a signal queued at a process that ended is a request it still
answers: a link, a monitor or an `is_process_alive` request from a process
that is not gone. Only requests stay queued when a process ends, and no
signal joins its queue after. -/
@[expose] def State.answersEntry (state : State) (entry : Entry) : Bool :=
  (entry.signal matches .link | .monitor _ | .isAlive) && !state.gone entry.source

/-- A record without what nothing can observe: queued signals that do nothing,
links being removed from processes that are gone, and, for a process that
ended, everything but what it still sends and answers. -/
@[expose] def State.normalizeRecord (state : State) (processId : PID) (process : ProcessState) :
    ProcessState :=
  match process.exiting with
  | some exiting =>
      { queue := Kernel.filter state.answersEntry process.queue
        children := process.children
        exiting := some { exiting with
          links := Kernel.filter (fun target => !state.gone target) exiting.links
          downs := Kernel.filter (fun down => !state.gone down.2) exiting.downs } }
  | none =>
      { process with
        queue := Kernel.filter (state.keepEntry processId process) process.queue
        links := Kernel.filter (fun link => !(link.2.isSome && state.gone link.1)) process.links }

/-- Whether a process that ended has nothing left to send or answer. -/
@[expose] def ProcessState.finished (process : ProcessState) : Bool :=
  match process.exiting with
  | some { links := [], downs := [], .. } => process.queue.isEmpty
  | _ => false

/-- Remove what nothing can observe any more. -/
@[expose] def State.normalize (state : State) : State :=
  let processes := Kernel.map (fun record => (record.1, state.normalizeRecord record.1 record.2))
    state.processes
  { state with processes := Kernel.filter (fun record => !record.2.finished) processes }

/-! ### Requests -/

/-- Add a timer in the order of the references, so the timers do not depend on
the order in which processes started them. -/
@[expose] def insertTimer (timer : Timer) : List Timer → List Timer
  | [] => [timer]
  | head :: rest =>
      if pidBefore timer.reference head.reference then timer :: head :: rest
      else head :: insertTimer timer rest

/-- What a process waits for inside a request: a marker behind the signals
queued before it, a reply from a process, or the exit signal it sent itself. -/
inductive Wait where
  | flush (reply : Term)
  | reply (source : PID)
  | exit
deriving Repr

/-- How a request is answered: at once, by waiting, or by continuing with a computation. -/
inductive Answer (β : Type) : Type 1 where
  | reply (value : Term) (state : State)
  | wait (wait : Wait) (state : State)
  | continue (computation : Result β) (state : State)

/-- Answer a request from a process. -/
@[expose] def State.request (state : State) (processId : PID) (next : Term → Result β) :
    Request → Answer β
  | .monitor target alias =>
      let (reference, state) := state.allocate processId
      if target = processId then .reply (.reference reference) state else
      let state := (state.unpark processId).modify processId fun process =>
        { process with
          monitoring := Kernel.append process.monitoring [(reference, target)]
          aliases := if alias then Kernel.append process.aliases [reference] else process.aliases
          parked := some (target, reference) }
      .reply (.reference reference) state
  | .demonitor reference flush =>
      -- The target only sends a `DOWN` that this process drops, so no signal is
      -- needed. An inactive monitor may have delivered its `DOWN`; flushing it
      -- receives one message of its shape, handling the queue first.
      let active := Kernel.any (state.process processId).monitoring (·.1 == reference)
      let state := state.modify processId fun process =>
        { process with
          monitoring := Kernel.filter (·.1 != reference) process.monitoring
          aliases := Kernel.erase process.aliases reference
          parked := match process.parked with
            | some (_, parked) => if parked == reference then none else process.parked
            | none => none }
      if flush && !active then
        .continue (.receive .immediate (fun _ message =>
          if isMonitorMessage reference message then some () else none) fun _ => next (.atom "false")) state
      else .reply (.atom (if active then "true" else "false")) state
  | .link target =>
      if target = processId then .reply (.atom "true") state else
      let process := state.process processId
      -- The link was removed when its exit was applied as it was sent; OTP
      -- may not have handled the exit yet, and then still holds the link.
      if Kernel.contains process.eagerExits target then .continue (.error .exhausted) state else
      if !state.alive target && !process.trapExit then .reply (.atom "noproc") state else
      match Kernel.lookup target process.links with
      | some none => .reply (.atom "true") state
      | _ =>
          let state := state.modify processId fun process =>
            { process with links := Kernel.append (Kernel.filter (·.1 != target) process.links) [(target, none)] }
          .reply (.atom "true") (state.send processId target .link)
  | .unlink target =>
      if target = processId then .reply (.atom "true") state else
      let process := state.process processId
      match Kernel.lookup target process.links with
      | some none =>
          let id := process.unlinks + 1
          let state := state.modify processId fun process =>
            { process with
              unlinks := id
              links := Kernel.map (fun link => if link.1 == target then (link.1, some id) else link) process.links }
          .reply (.atom "true") (state.send processId target (.unlink id))
      | _ => .reply (.atom "true") state
  | .exit target reason quirk =>
      if target != processId then .reply (.atom "true") (state.send processId target (.exit reason false false))
      else if quirk && (isKill reason || !(state.process processId).trapExit) then
        .wait .exit (state.send processId processId (.exit reason false true))
      else .reply (.atom "true") (state.send processId processId (.exit reason false false))
  | .trapExit enabled =>
      let process := state.process processId
      if enabled && !process.eagerExits.isEmpty then .continue (.error .exhausted) state else
      .reply (.atom (if process.trapExit then "true" else "false"))
        (state.modify processId fun process => { process with trapExit := enabled })
  | .alive target =>
      -- OTP replies `true` at once when the target has no signals queued
      -- (erl_bif_info.c), as the target handling the request at once would.
      -- Here the target always handles it, and a request to a process that is
      -- not alive always flushes, so no step reads whether a queue is empty.
      if target = processId then .reply (.atom "true") state
      else if state.alive target then .wait (.reply target) (state.send processId target .isAlive)
      else .wait (.flush (.atom "false")) (state.enqueue processId processId .flush)
  | .sendAlias alias message =>
      .reply message (state.send processId alias.dropLast (.aliasMessage alias message))
  | .startTimer destination message duration =>
      -- OTP destroys a timer for a process that is not alive at once.
      let (reference, state) := state.allocate processId
      .reply (.reference reference) (if state.alive destination then
        { state with timers := insertTimer { reference, destination, message, duration } state.timers }
        else state)
  | .cancelTimer reference =>
      -- Only a timer yet to fire is canceled. It reports the milliseconds left,
      -- from the time elapsed when it is canceled. Once it fired, its message
      -- may still be queued.
      match Kernel.find? (·.reference == reference) state.timers with
      | some timer =>
          let process := state.process processId
          .reply (.integer (timer.duration - state.elapsed processId process.cancels))
            ({ state with timers := Kernel.filter (·.reference != reference) state.timers }.modify
              processId fun process => { process with cancels := process.cancels + 1 })
      | none => .reply (.atom "false") state

/-- The runtime of a single process continuing from its environment, with the
time elapsed when timers are canceled. -/
@[expose] def State.initial (env : Environment) (elapsed : PID → Nat → Nat := fun _ _ => 0) :
    State :=
  { processes := [(env.currentPid, { pdict := env.pdict, refCounter := env.refCounter })], elapsed }

/-- Spawn a child, linking or monitoring it in the same step. The link replaces
any entry the parent has for the child's PID, which only a program naming that
PID before it exists can have made. -/
@[expose] def State.spawnWith (state : State) (processId : PID) (options : SpawnOptions) :
    PID × State :=
  let process := state.process processId
  let child := Kernel.append processId [process.children + 1]
  let state := (state.set processId { process with children := process.children + 1 }).set child {}
  let state := if options.link then
      (state.modify processId fun process =>
        { process with links := Kernel.append (Kernel.filter (·.1 != child) process.links) [(child, none)] }).modify
          child fun other =>
          { other with links := [(processId, none)] }
    else state
  let state := if options.monitor then
      let (reference, state) := state.allocate processId
      (state.modify processId fun process =>
        { process with monitoring := Kernel.append process.monitoring [(reference, child)] }).modify child
          fun other => { other with monitors := [(reference, processId)] }
    else state
  (child, state)

/-- The first timer of each reference, skipping references already seen. -/
@[expose] def firstOfEach (seen : List (List Nat)) : List Timer → List Timer
  | [] => []
  | timer :: rest =>
      if Kernel.contains seen timer.reference then firstOfEach seen rest
      else timer :: firstOfEach (timer.reference :: seen) rest

/-- The timers that can fire: the first of each reference. -/
@[expose] def State.firing (state : State) : List Timer := firstOfEach [] state.timers

/-- Fire a timer: its message is queued from `clock`. -/
@[expose] def State.fire (state : State) (timer : Timer) : State :=
  { state with timers := Kernel.filter (·.reference != timer.reference) state.timers }.enqueue clock
    timer.destination (.message timer.message)

/-- Select the oldest matching message, preserving all unmatched messages.
Returns the message, the selector's bindings, and the remaining mailbox. -/
@[expose] def selectMessage (select : Term → Option β) : List Term → Option (Term × β × List Term)
  | [] => none
  | message :: rest =>
      match select message with
      | some value => some (message, value, rest)
      | none => (selectMessage select rest).map fun (selected, value, remaining) =>
          (selected, value, message :: remaining)

/-! ### Steps -/

/-- A live process. The root returns the run's value; spawned children return
terms nobody observes. `finish` reports how a result reaches the run's outcome.
A process inside a request that waits has no steps of its own until a signal
it handles resumes it. -/
structure Task (α : Type) : Type 1 where
  {β : Type}
  computation : Result β
  finish : Except Exception β → Option (Except Exception α)
  wait : Option (Wait × (Term → Result β)) := none

/-- The process that started the run. -/
@[expose] def Task.root (computation : Result α) : Task α := ⟨computation, some, none⟩

/-- A spawned process, whose result is discarded. -/
@[expose] def Task.child (computation : Result Term) : Task α := ⟨computation, fun _ => none, none⟩

/-- What a step does, as observed in a trace. -/
inductive Event where
  /-- Read or replace the environment without a process request. -/
  | internal : PID → Event
  /-- The parent spawns a child with the given PID. -/
  | spawn (parent child : PID) : Event
  /-- Send a message to the receiver's queue. -/
  | send (sender receiver : PID) (message : Term) : Event
  /-- Consume a message from the process's own mailbox. -/
  | receive (receiver : PID) (message : Term) : Event
  /-- A receive with a zero or positive timeout resumes without a message. -/
  | timeout : PID → Event
  /-- The process returns, raises, acts on an exit signal, or does not
  return, with its exit reason. -/
  | exit (processId : PID) (reason : Term) : Event
  /-- The scheduler answers a request about other processes, or the process
  starts waiting (`reply` is `none`). -/
  | request (processId : PID) (query : Request) (reply : Option Term) : Event
  /-- A process handles the oldest signal of its queue. -/
  | handle (receiver : PID) (entry : Entry) : Event
  /-- A process that ended sends its next exit signal or `DOWN`, or answers
  its queued requests and leaves. -/
  | phase : PID → Event
  /-- A parked monitor signal is sent. -/
  | unpark : PID → Event
  /-- A timer fires, so its message is queued. -/
  | fire (reference : List Nat) : Event
deriving Repr

/-- One possible step of one process, and the processes that replace it. -/
structure Transition (α : Type) : Type 1 where
  event : Event
  state : State
  /-- Empty when the process ends; otherwise its continuation, followed by
  any process it spawned. -/
  tasks : List (PID × Task α)
  /-- The root's result, when the root ends. -/
  finished : Option (Except Exception α) := none
  /-- The process did not return, so the run's outcome is `Exception.exhausted`. -/
  exhausted : Bool := false

/-- A process ends with a reason, which reaches the run's outcome when it is
the root. -/
@[expose] def Task.ended {γ : Type} (finish : Except Exception γ → Option (Except Exception α))
    (event : Event) (state : State) (processId : PID) (reason : Term) (result : Except Exception γ) :
    Transition α :=
  { event, state := state.terminate processId reason, tasks := [], finished := finish result }

/-- The steps of a process itself: none while blocked or waiting, one
otherwise. A receive without a match and with a timeout steps by timing out,
only with nothing left to handle (`State.awaitedEntry`), which it handles
first. A positive timeout starts once the process waits after handling its
queue, and what is queued after it starts can be taken as queued after it
expires, as sending to a process does not observe whether its timer expired. -/
@[expose] def Task.own (state : State) (processId : PID) : Task α → List (Transition α)
  | ⟨_, _, some _⟩ => []
  | ⟨computation, finish, none⟩ =>
    let view := state.view processId
    let process := state.process processId
    let proceed (event : Event) (state : State) (next : Result _) : Transition α :=
      { event, state, tasks := [(processId, ⟨next, finish, none⟩)] }
    match computation with
    | .error .exhausted =>
        [{ event := .exit processId (.atom "exhausted"), state := state.remove processId
           tasks := [], exhausted := true }]
    | .ok value => [Task.ended finish (.exit processId (.atom "normal")) state processId
        (.atom "normal") (.ok value)]
    | .error exception => [Task.ended finish (.exit processId (exitReason exception)) state processId
        (exitReason exception) (.error exception)]
    | .get next => [proceed (.internal processId) state (next view)]
    | .set updated next => [proceed (.internal processId) (state.store processId updated) next]
    | Result.schedule options child next =>
        let (childPid, spawned) := state.spawnWith processId options
        [{ event := .spawn processId childPid, state := spawned
           tasks := [(processId, ⟨next childPid, finish, none⟩), (childPid, Task.child child)] }]
    | .send destination message next =>
        [proceed (.send processId destination message) (state.send processId destination (.message message))
          next]
    | .receive timeout select next =>
        match selectMessage (select view) process.mailbox with
        | some (message, value, remaining) =>
            [proceed (.receive processId message)
              (state.modify processId fun process => { process with mailbox := remaining })
              (next (some value))]
        | none =>
            let timedOut := proceed (.timeout processId) state (next none)
            match timeout with
            | .infinity => []
            | _ => if Kernel.any process.queue (state.awaitedEntry processId) then [] else [timedOut]
    | .request query next =>
        match state.request processId next query with
        | .reply value state => [proceed (.request processId query (some value)) state (next value)]
        | .continue computation state => [proceed (.request processId query none) state computation]
        | .wait wait state =>
            [{ event := .request processId query none, state
               tasks := [(processId, ⟨computation, finish, some (wait, next)⟩)] }]

/-- How a process acts on an exit signal: the state, and the reason it exits
with, if any. A link exit signal only acts while the link exists and is not
being removed. A process trapping exits receives the signal as an `EXIT`
message, unless it cannot be trapped. Otherwise it exits, ignoring the reason
`normal` unless the signal is its own `exit/2`. -/
@[expose] def State.exitSignal (state : State) (target source : PID) (reason : Term) (linked : Bool)
    (normalKills : Bool) : State × Option Term :=
  let process := state.process target
  let link := Kernel.lookup source process.links
  if linked && link.isNone then (state, none) else
  let state := if linked then
      state.modify target fun process => { process with links := Kernel.filter (·.1 != source) process.links }
    else state
  if linked && link != some none then (state, none)
  else if process.trapExit && !(!linked && isKill reason) then
    (state.append target (.tuple #[.atom "EXIT", .pid source, reason]), none)
  else if isNormal reason && !normalKills then (state, none)
  else (state, some (if !linked && isKill reason then .atom "killed" else reason))

/-- The process handles the oldest signal of its queue: its new state, the
value it resumes with if it was waiting for it, and the reason it exits with, if any. -/
@[expose] def State.handle (state : State) (processId : PID) (waiting : Option Wait) (entry : Entry) :
    State × Option Term × Option Term :=
  let process := state.process processId
  let source := entry.source
  match entry.signal with
  | .message message => (state.append processId message, none, none)
  | .aliasMessage alias message =>
      (if Kernel.contains process.aliases alias then state.append processId message else state, none, none)
  | .exit reason linked normalKills =>
      let (state, exits) := state.exitSignal processId source reason linked normalKills
      (state, none, exits)
  | .link =>
      (if (Kernel.lookup source process.links).isSome then state
        else state.modify processId fun process =>
          { process with links := Kernel.append process.links [(source, none)] }, none, none)
  | .unlink id =>
      let state := if Kernel.lookup source process.links == some none then
          state.modify processId fun process =>
            { process with links := Kernel.filter (·.1 != source) process.links }
        else state
      (state.send processId source (.unlinkAck id), none, none)
  | .unlinkAck id =>
      -- Only the link being removed goes, which a link made again since keeps.
      (if Kernel.lookup source process.links == some (some id) then
        state.modify processId fun process =>
          { process with links := Kernel.filter (fun link => !(link.1 == source && link.2 == some id)) process.links }
        else state, none, none)
  | .monitor reference =>
      (state.modify processId fun process =>
        { process with monitors := Kernel.append process.monitors [(reference, source)] }, none, none)
  | .down reference reason =>
      -- A `normal` `DOWN` follows its sender's link exits, so a link exit it
      -- applied when sent would have been handled.
      let state := if isNormal reason && Kernel.contains process.eagerExits source then
          state.modify processId fun process =>
            { process with eagerExits := Kernel.filter (· != source) process.eagerExits }
        else state
      if Kernel.any process.monitoring (·.1 == reference) then
        ((state.modify processId fun process =>
          { process with monitoring := Kernel.filter (·.1 != reference) process.monitoring
                         aliases := Kernel.erase process.aliases reference }).append processId
          (.tuple #[.atom "DOWN", .reference reference, .atom "process", .pid source, reason]), none, none)
      else (state, none, none)
  | .isAlive => (state.send processId source (.reply (.atom "true")), none, none)
  | .reply value =>
      match waiting with
      | some (.reply expected) => (state, if expected == source then some value else none, none)
      | _ => (state, none, none)
  | .flush =>
      match waiting with
      | some (.flush value) => (state, some value, none)
      | _ => (state, none, none)

/-- The process handles the oldest signal of its queue. -/
@[expose] def Task.handle (state : State) (processId : PID) (task : Task α) : List (Transition α) :=
  let process := state.process processId
  match process.queue with
  | [] => []
  | entry :: rest =>
    let (handled, resumed, exits) :=
      (state.set processId { process with queue := rest }).handle processId (task.wait.map (·.1)) entry
    let event := Event.handle processId entry
    match exits with
    | some reason => [Task.ended task.finish event handled processId reason (.error (.exit reason))]
    | none =>
      match resumed, task with
      | some value, ⟨_, finish, some (_, next)⟩ =>
          [{ event, state := handled, tasks := [(processId, ⟨next value, finish, none⟩)] }]
      | _, _ => [{ event, state := handled, tasks := [(processId, task)] }]

/-- Every step of a process: its own, and handling its oldest signal. -/
@[expose] def Task.transitions (state : State) (processId : PID) (task : Task α) :
    List (Transition α) :=
  Kernel.append (task.own state processId) (task.handle state processId)

/-- Whether a computation starts with a process request, which hands it to the scheduler. -/
@[expose] def isRequest : Result α → Bool
  | Result.schedule .. | .send .. | .receive .. | .request .. => true
  | _ => false

/-- A state of a run. -/
inductive Config (α : Type) : Type 1 where
  /-- Before its first process request, a computation reads and replaces its
  environment directly. The run then starts with the time elapsed when timers
  are canceled, which can be any. -/
  | start (env : Environment) (computation : Result α)
      (elapsed : PID → Nat → Nat := fun _ _ => 0)
  /-- Live processes in tree order, the root's result once it ends, and whether
  some process did not return. -/
  | running (state : State) (tasks : List (PID × Task α))
      (finished : Option (Except Exception α)) (exhausted : Bool)

/-- The configuration a process step leads to. A process that does not return
ends the run, which keeps no records or timers, as nothing observes them. -/
@[expose] def Transition.apply (transition : Transition α) (before after : List (PID × Task α))
    (finished : Option (Except Exception α)) (exhausted : Bool) : Config α :=
  if transition.exhausted then .running { transition.state with processes := [], timers := [] } [] finished true
  else .running transition.state.normalize (Kernel.append (Kernel.append before transition.tasks) after)
    (transition.finished.orElse fun _ => finished) exhausted

/-- Every way to split a list around one element. -/
@[expose] def splits : List γ → List (List γ × γ × List γ)
  | [] => []
  | head :: rest => ([], head, rest) :: Kernel.map (fun (before, item, after) =>
      (head :: before, item, after)) (splits rest)

theorem mem_splits {before after : List γ} {item : γ} :
    (before, item, after) ∈ splits (before ++ item :: after) := by
  induction before with
  | nil => simp [splits]
  | cons head rest ih =>
    simp only [List.cons_append, splits, List.mem_cons, List.mem_map, Kernel.map_eq]
    exact .inr ⟨_, ih, rfl⟩

theorem eq_of_mem_splits {tasks before after : List γ} {item : γ}
    (mem : (before, item, after) ∈ splits tasks) : tasks = before ++ item :: after := by
  induction tasks generalizing before with
  | nil => simp [splits] at mem
  | cons head rest ih =>
    simp only [splits, List.mem_cons, Prod.mk.injEq, List.mem_map, Prod.exists,
        Kernel.map_eq] at mem
    rcases mem with ⟨rfl, rfl, rfl⟩ | ⟨before', item', after', mem, rfl, rfl, rfl⟩
    · rfl
    · simp [ih mem]

/-- Every step of a configuration, with its event: a step of a process, a
phase of a process that ended, a parked monitor signal sent, or a timer firing.
A run that a process did not return from has none. -/
@[expose] def Config.successors : Config α → List (Event × Config α)
  | .start env computation elapsed =>
      match computation with
      | .get next => [(.internal env.currentPid, .start env (next env) elapsed)]
      | .set updated next => [(.internal env.currentPid, .start updated next elapsed)]
      | computation =>
          if isRequest computation then
            [(.internal env.currentPid, .running (State.initial env elapsed)
              [(env.currentPid, Task.root computation)] none false)]
          else []
  | .running _ _ _ true => []
  | .running state tasks finished false =>
      Kernel.append (Kernel.append (Kernel.append
        (Kernel.flatMap (fun (before, (processId, task), after) =>
          Kernel.map (fun transition => (transition.event, transition.apply before after finished false))
            (task.transitions state processId)) (splits tasks))
        (Kernel.flatMap (fun (processId, _) =>
          Kernel.map (fun next => (.phase processId, .running next.normalize tasks finished false))
            (state.phases processId))
          state.processes))
        (Kernel.filterMap (fun (processId, _) =>
          (state.process processId).parked.map fun _ =>
            (.unpark processId, .running (state.unpark processId).normalize tasks finished false))
          state.processes))
        (Kernel.map (fun timer =>
          (.fire timer.reference, .running (state.fire timer).normalize tasks finished false)) state.firing)

/-- A step of a configuration. -/
@[expose] def Step (first : Config α) (event : Event) (next : Config α) : Prop :=
  (event, next) ∈ first.successors

/-- Consecutive steps and the trace of their events. -/
inductive Run {α : Type} : Config α → List Event → Config α → Prop where
  | refl : Run config [] config
  | step : Step first event next → Run next events last → Run first (event :: events) last

/-- The outcome of a configuration without steps. -/
@[expose] def Config.outcome : Config α → Outcome α
  | .start _ (.ok value) _ => .ok value
  | .start _ (.error exception) _ => .error exception
  | .start .. => .deadlock
  | .running _ _ _ true => .error .exhausted
  | .running _ [] (some (.ok value)) false => .ok value
  | .running _ [] (some (.error exception)) false => .error exception
  | .running .. => .deadlock

/-- A configuration without steps, and its outcome: the root's result once
every process ended, `Exception.exhausted` once some process did not return,
and a deadlock otherwise. -/
inductive Terminal {α : Type} : Config α → Outcome α → Prop where
  | stuck (none : config.successors = []) : Terminal config config.outcome

theorem Terminal.successors_eq_nil {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : config.successors = [] := by
  cases terminal with
  | stuck none => exact none

theorem Terminal.outcome_eq {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : config.outcome = outcome := by
  cases terminal; rfl

/-- A property preserved by every step holds after every run. -/
theorem Run.invariant {invariant : Config α → Prop}
    (preserved : ∀ first event next, invariant first → Step first event next → invariant next)
    {first last : Config α} {events : List Event} (run : Run first events last)
    (initial : invariant first) : invariant last := by
  induction run with
  | refl => exact initial
  | step step _ ih => exact ih (preserved _ _ _ initial step)

end Lynx.Concurrent
