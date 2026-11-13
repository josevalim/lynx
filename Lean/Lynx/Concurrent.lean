module

public import Lynx.Term.DataTypes

/-! Interleaving semantics of local processes, as a labelled transition system.

`Lynx.Result.run` executes one interleaving chosen by its scheduler choices.
This module describes every interleaving instead: `Config.successors` lists the
steps of a configuration, a `Step` is one of them, and a `Run` collects the
`Event`s of consecutive steps as a trace. Concurrent laws are stated over these
runs (`Lynx.concurrent`).

Processes affect each other only through signals: messages, exit signals,
links, monitors and `DOWN` messages. As in OTP, a signal is in transit from
its sender until its receiver takes it, and only signals between the same two
processes keep their order. A process sees its own messages at once, as OTP
fetches every queued signal before a receive. Timers send their messages from
`clock`.

The scheduler owns the `State` of every process. A running process only
observes and replaces its own `Environment`: its identity, its process
dictionary, and the reference allocator. A process that does not return ends,
and the run's outcome is then `Exception.exhausted`. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- The scheduler's record of a live process. Each process allocates its own
references and child PIDs, so allocation does not depend on how processes
interleave. -/
structure ProcessState where
  pdict : List (Term × Term) := []
  mailbox : List Term := []
  /-- Number of references the process allocated. -/
  refCounter : Nat := 0
  /-- Number of processes the process spawned. -/
  children : Nat := 0
  /-- Processes linked to this one. -/
  links : List PID := []
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
deriving Repr, Inhabited

/-- The sender of timer messages. Children are numbered from one, so no
process has this PID. -/
@[expose] def clock : PID := [0]

/-- A signal from one process to another. -/
inductive Signal where
  | message (message : Term)
  /-- A message to an alias, dropped unless the alias is active when it arrives. -/
  | aliasMessage (alias : List Nat) (message : Term)
  /-- An exit signal, from a link or from `exit/2`. -/
  | exit (reason : Term) (linked : Bool)
  | link
  | unlink
  /-- Start monitoring the receiver. -/
  | monitor (reference : List Nat)
  /-- The monitored process ended, so the monitor ends with a `DOWN` message. -/
  | down (reference : List Nat) (reason : Term)
deriving Repr

/-- A signal in transit. -/
structure Envelope where
  source : PID
  target : PID
  signal : Signal
deriving Repr

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
  /-- Live processes. Terminated and unknown PIDs have no state. -/
  processes : PID → Option ProcessState := fun _ => none
  /-- Timers yet to fire, oldest first. -/
  timers : List Timer := []
  /-- Signals in transit, oldest first. -/
  inTransit : List Envelope := []
  /-- The milliseconds elapsed when a process cancels a timer, by how many
  timers it canceled before. Elapsed time is not modeled: a run starts with any
  of these, and nothing changes them. -/
  elapsed : PID → Nat → Nat := fun _ _ => 0

/-- Replace the record of one process. -/
@[expose] def State.update (state : State) (processId : PID) (process : Option ProcessState) :
    State :=
  { state with processes := fun candidate =>
      if candidate = processId then process else state.processes candidate }

/-- The record of a process, empty when it is not live. -/
@[expose] def State.process (state : State) (processId : PID) : ProcessState :=
  (state.processes processId).getD {}

/-- Whether a process is live. -/
@[expose] def State.alive (state : State) (processId : PID) : Bool :=
  (state.processes processId).isSome

/-- What the process observes when it runs, including in receive guards. -/
@[expose] def State.view (state : State) (processId : PID) : Environment :=
  let process := state.process processId
  { currentPid := processId, refCounter := process.refCounter, pdict := process.pdict }

/-- Change the record of a live process. -/
@[expose] def State.modify (state : State) (processId : PID)
    (change : ProcessState → ProcessState) : State :=
  match state.processes processId with
  | some process => state.update processId (some (change process))
  | none => state

/-- Keep what the process left in its environment. Its identity is not stored. -/
@[expose] def State.store (state : State) (processId : PID) (env : Environment) : State :=
  state.modify processId fun process =>
    { process with pdict := env.pdict, refCounter := env.refCounter }

/-- Append a message to a live mailbox. -/
@[expose] def State.append (state : State) (processId : PID) (message : Term) : State :=
  state.modify processId fun process => { process with mailbox := process.mailbox ++ [message] }

/-- Send a signal: it is in transit until its receiver takes it. -/
@[expose] def State.emit (state : State) (source target : PID) (signal : Signal) : State :=
  { state with inTransit := state.inTransit ++ [{ source, target, signal }] }

/-- Allocate the next reference of a process. -/
@[expose] def State.allocate (state : State) (processId : PID) : List Nat × State :=
  (processId ++ [(state.process processId).refCounter + 1],
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

/-- Add an element unless the list already has it. -/
@[expose] def insertOnce [BEq γ] (item : γ) (items : List γ) : List γ :=
  if items.contains item then items else items ++ [item]

/-- A process ends: linked processes get exit signals, watchers `DOWN`
signals, and timers sending to it are canceled, as OTP does. -/
@[expose] def State.terminate (state : State) (processId : PID) (reason : Term) : State :=
  let process := state.process processId
  let state := { state.update processId none with
    timers := state.timers.filter (·.destination != processId) }
  let state := process.links.foldl (fun state linked =>
    state.emit processId linked (.exit reason true)) state
  process.monitors.foldl (fun state (reference, watcher) =>
    state.emit processId watcher (.down reference reason)) state

/-- How a live process acts on an exit signal: the state, and the reason it
exits with, if any. A link exit signal only acts while the link exists. A
process trapping exits receives the signal as an `EXIT` message, unless it
cannot be trapped. Otherwise it exits, ignoring the reason `normal`. -/
@[expose] def State.exitSignal (state : State) (target source : PID) (reason : Term)
    (linked : Bool) : State × Option Term :=
  let process := state.process target
  if linked && !process.links.contains source then (state, none) else
  let state := if linked then
      state.modify target fun process => { process with links := process.links.erase source }
    else state
  if !linked && isKill reason then (state, some (.atom "killed"))
  else if process.trapExit then (state.append target (.tuple #[.atom "EXIT", .pid source, reason]), none)
  else if isNormal reason then (state, none)
  else (state, some reason)

/-- A live process takes a signal: the state, and the reason it exits with, if any. -/
@[expose] def State.receive (state : State) (envelope : Envelope) : State × Option Term :=
  let target := envelope.target
  match envelope.signal with
  | .message message => (state.append target message, none)
  | .aliasMessage alias message =>
      (if (state.process target).aliases.contains alias then state.append target message else state,
        none)
  | .exit reason linked => state.exitSignal target envelope.source reason linked
  | .link => (state.modify target fun process =>
      { process with links := insertOnce envelope.source process.links }, none)
  | .unlink => (state.modify target fun process =>
      { process with links := process.links.erase envelope.source }, none)
  | .monitor reference => (state.modify target fun process =>
      { process with monitors := process.monitors ++ [(reference, envelope.source)] }, none)
  | .down reference reason =>
      if (state.process target).monitoring.any (·.1 == reference) then
        ((state.modify target fun process =>
          { process with monitoring := process.monitoring.filter (·.1 != reference)
                         aliases := process.aliases.erase reference }).append target
          (.tuple #[.atom "DOWN", .reference reference, .atom "process", .pid envelope.source,
            reason]), none)
      else (state, none)

/-- A signal reaches a process that is not live: links and monitors are
answered with `noproc`, and the others are dropped. -/
@[expose] def State.bounce (state : State) (envelope : Envelope) : State :=
  match envelope.signal with
  | .link => state.emit envelope.target envelope.source (.exit (.atom "noproc") true)
  | .monitor reference => state.emit envelope.target envelope.source (.down reference (.atom "noproc"))
  | _ => state

/-- The oldest signal of each sender and receiver, each with the other signals
in transit. -/
@[expose] def deliverableFrom (before : List Envelope) (seen : List (PID × PID)) :
    List Envelope → List (Envelope × List Envelope)
  | [] => []
  | envelope :: rest =>
      if seen.contains (envelope.source, envelope.target) then
        deliverableFrom (before ++ [envelope]) seen rest
      else (envelope, before ++ rest) ::
        deliverableFrom (before ++ [envelope]) ((envelope.source, envelope.target) :: seen) rest

/-- The signals that can arrive next, each with the other signals in transit. -/
@[expose] def deliverable (inTransit : List Envelope) : List (Envelope × List Envelope) :=
  deliverableFrom [] [] inTransit

/-- Answer a request from a process: the reply, the state, and the reason the
process exits with, if any. `none` while the request cannot be answered. -/
@[expose] def State.request (state : State) (processId : PID) :
    Request → Option (Term × State × Option Term)
  | .monitor target alias =>
      let (reference, state) := state.allocate processId
      if target = processId then some (.reference reference, state, none) else
      let state := state.modify processId fun process =>
        { process with monitoring := process.monitoring ++ [(reference, target)]
                       aliases := if alias then process.aliases ++ [reference] else process.aliases }
      -- Monitoring a process that does not exist answers at once.
      let state := if state.alive target then state.emit processId target (.monitor reference)
        else state.emit target processId (.down reference (.atom "noproc"))
      some (.reference reference, state, none)
  | .demonitor reference flush =>
      -- The monitored process only sends a `DOWN` that this process drops, as
      -- references are never reused, so no signal is needed. An active
      -- monitor has not delivered its `DOWN` message, so only an inactive one
      -- flushes, removing the oldest message of its shape, as OTP does.
      let active := (state.process processId).monitoring.any (·.1 == reference)
      some (.atom (if active then "true" else "false"), state.modify processId fun process =>
        { process with
            monitoring := process.monitoring.filter (·.1 != reference)
            aliases := process.aliases.erase reference
            mailbox := if flush && !active then process.mailbox.eraseP (isMonitorMessage reference)
              else process.mailbox }, none)
  | .link target =>
      if target = processId then some (.atom "true", state, none)
      else if !state.alive target && !(state.process processId).trapExit then
        some (.atom "noproc", state, none)
      else
        let state := state.modify processId fun process =>
          { process with links := insertOnce target process.links }
        some (.atom "true", if state.alive target then state.emit processId target .link
          else state.emit target processId (.exit (.atom "noproc") true), none)
  | .unlink target =>
      let state := state.modify processId fun process =>
        { process with links := process.links.erase target }
      some (.atom "true", if target = processId then state else state.emit processId target .unlink,
        none)
  | .exit target reason =>
      if target = processId then
        -- A process that sends itself `normal` exits, unless it traps exits.
        if isNormal reason && !(state.process processId).trapExit then
          some (.atom "true", state, some reason)
        else
          let (state, exits) := state.exitSignal processId processId reason false
          some (.atom "true", state, exits)
      else some (.atom "true", state.emit processId target (.exit reason false), none)
  | .trapExit enabled =>
      some (.atom (if (state.process processId).trapExit then "true" else "false"),
        state.modify processId fun process => { process with trapExit := enabled }, none)
  | .alive target =>
      -- OTP answers after the requester's earlier signals reach the target,
      -- and the target's earlier signals reach the requester.
      if target = processId then some (.atom "true", state, none)
      else if state.inTransit.any fun envelope =>
          (envelope.source == processId && envelope.target == target) ||
            (envelope.source == target && envelope.target == processId) then none
      else some (.atom (if state.alive target then "true" else "false"), state, none)
  | .sendAlias alias message =>
      let owner := alias.dropLast
      if owner = processId then
        some (message, if (state.process processId).aliases.contains alias then
          state.append processId message else state, none)
      else some (message, state.emit processId owner (.aliasMessage alias message), none)
  | .startTimer destination message duration =>
      -- OTP destroys a timer for a process that is not alive at once.
      let (reference, state) := state.allocate processId
      some (.reference reference, if state.alive destination then
        { state with timers := state.timers ++ [{ reference, destination, message, duration }] }
        else state, none)
  | .cancelTimer reference =>
      -- Only a timer yet to fire is canceled. It reports the milliseconds left,
      -- from the time elapsed when it is canceled. Once it fired, its message
      -- may still be in transit.
      match state.timers.find? (·.reference == reference) with
      | some timer =>
          let process := state.process processId
          some (.integer (timer.duration - state.elapsed processId process.cancels),
            { state with timers := state.timers.filter (·.reference != reference) }.modify
              processId fun process => { process with cancels := process.cancels + 1 }, none)
      | none => some (.atom "false", state, none)

/-- The runtime of a single process continuing from its environment, with the
time elapsed when timers are canceled. -/
@[expose] def State.initial (env : Environment) (elapsed : PID → Nat → Nat := fun _ _ => 0) :
    State :=
  { processes := fun candidate =>
      if candidate = env.currentPid then
        some { pdict := env.pdict, refCounter := env.refCounter }
      else none
    elapsed }

/-- Allocate the next child of a process, which starts with an empty record. -/
@[expose] def State.spawn (state : State) (processId : PID) : PID × State :=
  let process := state.process processId
  let childPid := processId ++ [process.children + 1]
  (childPid, (state.update processId (some { process with children := process.children + 1 })).update
    childPid (some {}))

/-- Spawn a child, linking or monitoring it in the same step. -/
@[expose] def State.spawnWith (state : State) (processId : PID) (options : SpawnOptions) :
    PID × State :=
  let (child, state) := state.spawn processId
  let state := if options.link then
      (state.modify processId fun process =>
        { process with links := insertOnce child process.links }).modify child fun other =>
          { other with links := [processId] }
    else state
  let state := if options.monitor then
      let (reference, state) := state.allocate processId
      (state.modify processId fun process =>
        { process with monitoring := process.monitoring ++ [(reference, child)] }).modify child
          fun other => { other with monitors := [(reference, processId)] }
    else state
  (child, state)

/-- Fire a timer: its message is in transit. -/
@[expose] def State.fire (state : State) (timer : Timer) : State :=
  { state with timers := state.timers.filter (·.reference != timer.reference) }.emit clock
    timer.destination (.message timer.message)

/-! Steps keep the time elapsed when timers are canceled. -/

@[simp] theorem State.elapsed_update {state : State} {processId : PID}
    {process : Option ProcessState} : (state.update processId process).elapsed = state.elapsed := rfl

@[simp] theorem State.elapsed_modify {state : State} {processId : PID}
    {change : ProcessState → ProcessState} :
    (state.modify processId change).elapsed = state.elapsed := by
  unfold State.modify; split <;> rfl

/-- Select the oldest matching message, preserving all unmatched messages.
Returns the message, the selector's bindings, and the remaining mailbox. -/
@[expose] def selectMessage (select : Term → Option β) : List Term → Option (Term × β × List Term)
  | [] => none
  | message :: rest =>
      match select message with
      | some value => some (message, value, rest)
      | none => (selectMessage select rest).map fun (selected, value, remaining) =>
          (selected, value, message :: remaining)

/-- The message a receive selects is at an index of the mailbox, and stays
selected, leaving the same messages, when more messages arrive. -/
theorem selectMessage_index {select : Term → Option β} {mailbox : List Term}
    {message : Term} {value : β} {remaining : List Term}
    (selected : selectMessage select mailbox = some (message, value, remaining)) :
    ∃ index < mailbox.length, remaining = mailbox.eraseIdx index ∧
      ∀ extra, selectMessage select (mailbox ++ extra) = some (message, value, remaining ++ extra) := by
  induction mailbox generalizing remaining with
  | nil => simp [selectMessage] at selected
  | cons head rest ih =>
    simp only [selectMessage] at selected
    split at selected
    · rename_i matched
      simp only [Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl, rfl⟩ := selected
      exact ⟨0, by simp, by simp, fun extra => by simp [selectMessage, matched]⟩
    · rename_i unmatched
      simp only [Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at selected
      obtain ⟨_, _, remaining', found, rfl, rfl, rfl⟩ := selected
      obtain ⟨index, bound, rfl, extend⟩ := ih found
      exact ⟨index + 1, by simp [bound], by simp, fun extra => by
        simp [selectMessage, unmatched, extend]⟩

/-- A live process. The root returns the run's value; spawned children return
terms nobody observes. `finish` reports how a result reaches the run's outcome. -/
structure Task (α : Type) : Type 1 where
  {β : Type}
  computation : Result β
  finish : Except Exception β → Option (Except Exception α)

/-- The process that started the run. -/
@[expose] def Task.root (computation : Result α) : Task α := ⟨computation, some⟩

/-- A spawned process, whose result is discarded. -/
@[expose] def Task.child (computation : Result Term) : Task α := ⟨computation, fun _ => none⟩

/-- What a step does, as observed in a trace. -/
inductive Event where
  /-- Read or replace the environment without a process request. -/
  | internal : PID → Event
  /-- The parent spawns a child with the given PID. -/
  | spawn (parent child : PID) : Event
  /-- Send a message, which is in transit unless the receiver is the sender. -/
  | send (sender receiver : PID) (message : Term) : Event
  /-- Consume a message from the process's own mailbox. -/
  | receive (receiver : PID) (message : Term) : Event
  /-- A receive with a zero or positive timeout resumes without a message. -/
  | timeout : PID → Event
  /-- The process returns, raises, acts on an exit signal, or does not
  return, with its exit reason. -/
  | exit (processId : PID) (reason : Term) : Event
  /-- The scheduler answers a request about other processes. -/
  | request (processId : PID) (query : Request) (reply : Term) : Event
  /-- A signal in transit reaches its receiver. -/
  | deliver (envelope : Envelope) : Event
  /-- A signal reaches the PID of a process that is not live: links and
  monitors are answered with `noproc`, and other signals are dropped. -/
  | bounce (envelope : Envelope) : Event
  /-- A timer fires, so its message is in transit. -/
  | fire (reference : List Nat) : Event
deriving Repr

/-- One possible step of one process, and the processes that replace it. -/
structure Transition (α : Type) : Type 1 where
  event : Event
  state : State
  /-- Empty when the process ends; otherwise its continuation, followed by
  any process it spawned. -/
  tasks : List (PID × Task α)
  /-- The root's result and final environment, when the root ends. -/
  finished : Option (Except Exception α × Environment) := none
  /-- A positive timeout expired, which is the scheduler's choice. -/
  expired : Bool := false
  /-- The process did not return, so the run's outcome is `Exception.exhausted`. -/
  exhausted : Bool := false

/-- A process ends with a reason, which reaches the run's outcome when it is
the root. -/
@[expose] def Task.ended {γ : Type} (finish : Except Exception γ → Option (Except Exception α))
    (event : Event) (state : State) (processId : PID) (reason : Term) (result : Except Exception γ) :
    Transition α :=
  let view := state.view processId
  { event, state := state.terminate processId reason, tasks := []
    finished := (finish result).map (·, view) }

/-- The steps of a process itself: none while blocked, two for a
positive-timeout receive without a match, one otherwise. -/
@[expose] def Task.own (state : State) (processId : PID) : Task α → List (Transition α)
  | ⟨computation, finish⟩ =>
    let view := state.view processId
    let process := state.process processId
    let proceed (event : Event) (state : State) (next : Result _) : Transition α :=
      { event, state, tasks := [(processId, ⟨next, finish⟩)] }
    match computation with
    | .error .exhausted =>
        [{ event := .exit processId (.atom "exhausted"), state := state.update processId none
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
           tasks := [(processId, ⟨next childPid, finish⟩), (childPid, Task.child child)] }]
    | .send destination message next =>
        -- A process sees its own messages at once.
        let state := if destination = processId then state.append processId message
          else state.emit processId destination (.message message)
        [proceed (.send processId destination message) state next]
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
            | .immediate => [timedOut]
            | .finite => [{ timedOut with expired := true }]
    | .request query next =>
        match state.request processId query with
        | none => []
        | some (reply, answered, none) =>
            [proceed (.request processId query reply) answered (next reply)]
        | some (reply, answered, some reason) =>
            [Task.ended finish (.request processId query reply) answered processId reason
              (.error (.exit reason))]

/-- The signals that can reach a process next, and what each does. -/
@[expose] def Task.deliveries (state : State) (processId : PID) (task : Task α) :
    List (Transition α) :=
  (deliverable state.inTransit).filterMap fun (envelope, rest) =>
    if envelope.target != processId then none else
    let (received, exits) := { state with inTransit := rest }.receive envelope
    some <| match exits with
      | none => { event := .deliver envelope, state := received, tasks := [(processId, task)] }
      | some reason => Task.ended task.finish (.deliver envelope) received processId reason
          (.error (.exit reason))

/-- Every step of a process: its own, and the signals it takes. -/
@[expose] def Task.transitions (state : State) (processId : PID) (task : Task α) :
    List (Transition α) :=
  task.own state processId ++ task.deliveries state processId

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
      (finished : Option (Except Exception α × Environment)) (exhausted : Bool)

/-- The configuration a process step leads to. -/
@[expose] def Transition.apply (transition : Transition α) (before after : List (PID × Task α))
    (finished : Option (Except Exception α × Environment)) (exhausted : Bool) : Config α :=
  .running transition.state (before ++ transition.tasks ++ after)
    (transition.finished.orElse fun _ => finished) (exhausted || transition.exhausted)

/-- Every way to split a list around one element. -/
@[expose] def splits : List γ → List (List γ × γ × List γ)
  | [] => []
  | head :: rest => ([], head, rest) :: (splits rest).map fun (before, item, after) =>
      (head :: before, item, after)

theorem mem_splits {before after : List γ} {item : γ} :
    (before, item, after) ∈ splits (before ++ item :: after) := by
  induction before with
  | nil => simp [splits]
  | cons head rest ih =>
    simp only [List.cons_append, splits, List.mem_cons, List.mem_map]
    exact .inr ⟨_, ih, rfl⟩

theorem eq_of_mem_splits {tasks before after : List γ} {item : γ}
    (mem : (before, item, after) ∈ splits tasks) : tasks = before ++ item :: after := by
  induction tasks generalizing before with
  | nil => simp [splits] at mem
  | cons head rest ih =>
    simp only [splits, List.mem_cons, Prod.mk.injEq, List.mem_map, Prod.exists] at mem
    rcases mem with ⟨rfl, rfl, rfl⟩ | ⟨before', item', after', mem, rfl, rfl, rfl⟩
    · rfl
    · simp [ih mem]

/-- Every step of a configuration, with its event: a step of a process, a
signal reaching a process that is not live, or a timer firing. -/
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
  | .running state tasks finished exhausted =>
      (splits tasks).flatMap (fun (before, (processId, task), after) =>
        (task.transitions state processId).map fun transition =>
          (transition.event, transition.apply before after finished exhausted)) ++
      (deliverable state.inTransit).filterMap (fun (envelope, rest) =>
        if (tasks.lookup envelope.target).isSome then none
        else some (.bounce envelope,
          .running ({ state with inTransit := rest }.bounce envelope) tasks finished exhausted)) ++
      state.timers.map fun timer =>
        (.fire timer.reference, .running (state.fire timer) tasks finished exhausted)

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
  | .running _ [] (some (.ok value, _)) false => .ok value
  | .running _ [] (some (.error exception, _)) false => .error exception
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

/-- A configuration without successors is terminal. -/
theorem Config.terminal_of_successors_eq_nil {config : Config α}
    (stuck : config.successors = []) : Terminal config config.outcome :=
  .stuck stuck

/-- A property preserved by every step holds after every run. -/
theorem Run.invariant {invariant : Config α → Prop}
    (preserved : ∀ first event next, invariant first → Step first event next → invariant next)
    {first last : Config α} {events : List Event} (run : Run first events last)
    (initial : invariant first) : invariant last := by
  induction run with
  | refl => exact initial
  | step step _ ih => exact ih (preserved _ _ _ initial step)

/-! ### Exhaustive exploration

For a closed program, every run can be enumerated: `Config.successors` lists
each step, and `check` follows all of them. Proving `check` by evaluation
establishes a property for every schedule (see `Lynx.concurrent_of_check`). -/

/-- Whether every run from the configuration ends in an accepted outcome,
following at most `depth` steps along each run. -/
@[expose] def check (accept : Outcome α → Bool) : Nat → Config α → Bool
  | 0, _ => false
  | depth + 1, config =>
      match config.successors with
      | [] => accept config.outcome
      | successors => successors.all fun (_, next) => check accept depth next

/-- How a run that `check` rejects fails. -/
inductive Failure (α : Type) where
  /-- The run ends in an outcome that is not accepted. -/
  | rejected : Outcome α → Failure α
  /-- The run takes more steps than the depth allows. -/
  | unfinished : Failure α

/-- The first run that `check` rejects, as the events of its steps and how it
fails. Evaluating it is a fast way to find why a check fails. -/
@[expose] def counterexample (accept : Outcome α → Bool) :
    Nat → Config α → Option (List Event × Failure α)
  | 0, _ => some ([], .unfinished)
  | depth + 1, config =>
      match config.successors with
      | [] => if accept config.outcome then none else some ([], .rejected config.outcome)
      | successors => successors.findSome? fun (event, next) =>
          (counterexample accept depth next).map fun (events, failure) => (event :: events, failure)

/-- Every run of a configuration that `check` accepts ends in an accepted outcome. -/
theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {first last : Config α}
    {events : List Event} {outcome : Outcome α} (checked : check accept depth first = true)
    (run : Run first events last) (terminal : Terminal last outcome) : accept outcome = true := by
  induction run generalizing depth with
  | refl =>
    cases depth with
    | zero => simp [check] at checked
    | succ depth =>
      simp only [check, terminal.successors_eq_nil] at checked
      rw [← terminal.outcome_eq]
      exact checked
  | step step _ ih =>
    cases depth with
    | zero => simp [check] at checked
    | succ depth =>
      simp only [check] at checked
      split at checked
      · rename_i none
        simp [Step, none] at step
      · exact ih (List.all_eq_true.mp checked _ step) terminal

end Lynx.Concurrent
