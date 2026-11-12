module

public import Lynx.Term.DataTypes

/-! Interleaving semantics of local processes, as a labelled transition system.

`Lynx.Result.run` executes one interleaving chosen by its scheduler choices.
This module describes every interleaving instead: a `Step` advances one
process, and a `Run` collects the `Event`s of consecutive steps as a trace.
The runner's soundness theorems show that each run with any scheduler choices
is a `Run` ending in a `Terminal` configuration with the same outcome, so a
property of every terminal configuration holds for every schedule.

The scheduler owns the `State` of every process. A running process only
observes and replaces its own `Environment`: its identity, its process
dictionary, and the reference allocator. It cannot reach another process's
dictionary or mailbox, and replacing its `currentPid` does not change which
process is running. Any live process may take its next step, including between
environment accesses, which affect only that process. A process that does not
return ends, and the run's outcome is then `Exception.exhausted`. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- The scheduler's record of a process that is not running. Each process
allocates its own references and child PIDs, so allocation does not depend on
how processes interleave. -/
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
  /-- The reason of an exit signal the process has yet to act on. The process
  exits with it at its next step, as signals arrive asynchronously. -/
  signal : Option Term := none
deriving Repr, Inhabited

/-- A timer that sends a message to a process. Elapsed time is not modeled: the
scheduler expires it at any point and later delivers its message, so its
duration is only what canceling it reports. -/
structure Timer where
  /-- The reference `send_after` replies, allocated by the process starting it. -/
  reference : List Nat
  destination : PID
  message : Term
  duration : Nat
  /-- Whether it expired, so its message is on its way and canceling it fails. -/
  expired : Bool := false
deriving Repr

/-- The runtime shared by all processes of a run. -/
structure State where
  /-- Live processes. Terminated and unknown PIDs have no state. -/
  processes : PID → Option ProcessState := fun _ => none
  /-- Timers that have yet to deliver their message, oldest first. -/
  timers : List Timer := []

/-- Replace the record of one process. -/
@[expose] def State.update (state : State) (processId : PID) (process : Option ProcessState) :
    State :=
  { state with processes := fun candidate =>
      if candidate = processId then process else state.processes candidate }

/-- The record of a process, empty when it is not live. -/
@[expose] def State.process (state : State) (processId : PID) : ProcessState :=
  (state.processes processId).getD {}

/-- What the process observes when it runs, including in receive guards. -/
@[expose] def State.view (state : State) (processId : PID) : Environment :=
  let process := state.process processId
  { currentPid := processId, refCounter := process.refCounter, pdict := process.pdict }

/-- Keep what the process left in its environment. Its identity is not stored. -/
@[expose] def State.store (state : State) (processId : PID) (env : Environment) : State :=
  state.update processId
    (some { state.process processId with pdict := env.pdict, refCounter := env.refCounter })

/-- Append a message to a live mailbox. Messages to other PIDs are discarded. -/
@[expose] def State.deliver (state : State) (processId : PID) (message : Term) : State :=
  match state.processes processId with
  | some process => state.update processId (some { process with mailbox := process.mailbox ++ [message] })
  | none => state

/-- Change the record of a live process. -/
@[expose] def State.modify (state : State) (processId : PID)
    (change : ProcessState → ProcessState) : State :=
  match state.processes processId with
  | some process => state.update processId (some (change process))
  | none => state

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

/-- Whether a message has the shape `{_, Reference, _, _, _}` of a monitor's
`DOWN` message, which flushing a monitor removes. -/
@[expose] def isMonitorMessage (reference : List Nat) : Term → Bool
  | .tuple ⟨[_, .reference found, _, _, _]⟩ => found == reference
  | _ => false

/-- Record a pending exit reason, unless one is already pending. -/
@[expose] def State.kill (state : State) (processId : PID) (reason : Term) : State :=
  state.modify processId fun process =>
    { process with signal := process.signal.orElse fun _ => some reason }

/-- Deliver an exit signal from a process. A process that traps exits receives
it as an `EXIT` message, unless it cannot be trapped. Otherwise the process
exits, ignoring the reason `normal`. -/
@[expose] def State.signal (state : State) (target sender : PID) (reason : Term)
    (untrappable : Bool) : State :=
  if untrappable then state.kill target (.atom "killed")
  else if (state.process target).trapExit then
    state.deliver target (.tuple #[.atom "EXIT", .pid sender, reason])
  else if isNormal reason then state
  else state.kill target reason

/-- A process exits: each linked process receives an exit signal, and each
monitoring process a `DOWN` message, which ends its monitor and alias. Timers
sending to it are canceled, as OTP does. -/
@[expose] def State.terminate (state : State) (processId : PID) (reason : Term) : State :=
  let process := state.process processId
  let state := { state.update processId none with
    timers := state.timers.filter (·.destination != processId) }
  let state := process.links.foldl (fun state linked =>
    (state.modify linked fun other => { other with links := other.links.erase processId }).signal
      linked processId reason false) state
  process.monitors.foldl (fun state (reference, watcher) =>
    (state.deliver watcher (.tuple #[.atom "DOWN", .reference reference, .atom "process",
      .pid processId, reason])).modify watcher fun other =>
        { other with monitoring := other.monitoring.filter (·.1 != reference)
                     aliases := other.aliases.erase reference }) state

/-- Add an element unless the list already has it. -/
@[expose] def insertOnce [BEq γ] (item : γ) (items : List γ) : List γ :=
  if items.contains item then items else items ++ [item]

/-- Start a monitor from a process, allocating its reference. Monitoring a
process that does not exist delivers its `DOWN` message at once. -/
@[expose] def State.monitor (state : State) (processId target : PID) (alias : Bool) :
    List Nat × State :=
  let reference := processId ++ [(state.process processId).refCounter + 1]
  let state := state.modify processId fun process =>
    { process with refCounter := process.refCounter + 1 }
  match state.processes target with
  | some _ =>
      let state := state.modify target fun watched =>
        { watched with monitors := watched.monitors ++ [(reference, processId)] }
      (reference, state.modify processId fun process =>
        { process with monitoring := process.monitoring ++ [(reference, target)]
                       aliases := if alias then process.aliases ++ [reference] else process.aliases })
  | none =>
      (reference, state.deliver processId (.tuple #[.atom "DOWN", .reference reference,
        .atom "process", .pid target, .atom "noproc"]))

/-- Answer a request from a process. -/
@[expose] def State.request (state : State) (processId : PID) : Request → Term × State
  | .monitor target alias =>
      let (reference, state) := state.monitor processId target alias
      (.reference reference, state)
  | .demonitor reference flush =>
      -- An active monitor has not delivered its `DOWN` message, so only an
      -- inactive one flushes, removing the oldest message of its shape, as OTP does.
      let process := state.process processId
      let active := process.monitoring.any (·.1 == reference)
      let state := process.monitoring.foldl (fun state (found, target) =>
        if found == reference then
          state.modify target fun watched =>
            { watched with monitors := watched.monitors.filter (·.1 != reference) }
        else state) state
      (.atom (if active then "true" else "false"),
        state.modify processId fun process =>
        { process with
            monitoring := process.monitoring.filter (·.1 != reference)
            aliases := process.aliases.erase reference
            mailbox := if flush && !active then process.mailbox.eraseP (isMonitorMessage reference)
              else process.mailbox })
  | .link target =>
      if target = processId then (.atom "true", state) else
      match state.processes target with
      | some _ =>
          (.atom "true", (state.modify processId fun process =>
            { process with links := insertOnce target process.links }).modify target fun other =>
              { other with links := insertOnce processId other.links })
      | none =>
          if (state.process processId).trapExit then
            (.atom "true", state.deliver processId
              (.tuple #[.atom "EXIT", .pid target, .atom "noproc"]))
          else (.atom "noproc", state)
  | .unlink target =>
      (.atom "true", (state.modify processId fun process =>
        { process with links := process.links.erase target }).modify target fun other =>
          { other with links := other.links.erase processId })
  | .exit target reason =>
      -- A process that sends itself `normal` exits, unless it traps exits.
      if target = processId && isNormal reason && !(state.process processId).trapExit then
        (.atom "true", state.kill processId reason)
      else
        (.atom "true", state.signal target processId reason
          (match reason with | .atom "kill" => true | _ => false))
  | .trapExit enabled =>
      (.atom (if (state.process processId).trapExit then "true" else "false"),
        state.modify processId fun process => { process with trapExit := enabled })
  | .alive target =>
      (.atom (if (state.processes target).isSome then "true" else "false"), state)
  | .sendAlias alias message =>
      let owner := alias.dropLast
      if (state.process owner).aliases.contains alias then (message, state.deliver owner message)
      else (message, state)
  | .startTimer destination message duration =>
      -- The reference comes from the requester's own counter, like `make_ref`.
      -- OTP destroys a timer for a process that is not alive at once.
      let reference := processId ++ [(state.process processId).refCounter + 1]
      let state := state.modify processId fun process =>
        { process with refCounter := process.refCounter + 1 }
      (.reference reference, if (state.processes destination).isSome then
        { state with timers := state.timers ++ [{ reference, destination, message, duration }] }
        else state)
  | .cancelTimer reference =>
      -- Only a timer yet to expire is canceled: an expired one, whose message
      -- may still be on its way, and one whose destination exited report `false`.
      match state.timers.find? fun timer => timer.reference == reference && !timer.expired with
      | some timer =>
          (.integer timer.duration,
            { state with timers := state.timers.filter (·.reference != reference) })
      | none => (.atom "false", state)

/-- Every reply a request may get, starting with the one `State.request`
gives. Canceling a timer reports the milliseconds left, which may be any number
up to its duration, as elapsed time is not modeled. -/
@[expose] def replies : Request → Term → List Term
  | .cancelTimer _, .integer (.ofNat duration) =>
      (List.range (duration + 1)).reverse.map fun left => .integer (.ofNat left)
  | _, reply => [reply]

theorem mem_replies (query : Request) (reply : Term) : reply ∈ replies query reply := by
  unfold replies
  split
  · simpa using ⟨_, Nat.lt_succ_self _, rfl⟩
  · simp

/-- The runtime of a single process continuing from its environment. -/
@[expose] def State.initial (env : Environment) : State :=
  { processes := fun candidate =>
      if candidate = env.currentPid then
        some { pdict := env.pdict, refCounter := env.refCounter }
      else none }

/-- A process without links or monitors exits without changing other
processes, when no timer is pending. -/
theorem State.terminate_eq_update {state : State} {processId : PID} {reason : Term}
    (links : (state.process processId).links = [])
    (monitors : (state.process processId).monitors = []) (idle : state.timers = []) :
    state.terminate processId reason = state.update processId none := by
  simp [State.terminate, links, monitors, idle, State.update]

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
  let state := if options.monitor then (state.monitor processId child false).2 else state
  (child, state)

/-! Process operations keep the timers. -/

@[simp] theorem State.timers_update {state : State} {processId : PID}
    {process : Option ProcessState} : (state.update processId process).timers = state.timers := rfl

@[simp] theorem State.timers_modify {state : State} {processId : PID}
    {change : ProcessState → ProcessState} : (state.modify processId change).timers = state.timers := by
  unfold State.modify; split <;> rfl

@[simp] theorem State.timers_deliver {state : State} {processId : PID} {message : Term} :
    (state.deliver processId message).timers = state.timers := by
  unfold State.deliver; split <;> rfl

@[simp] theorem State.timers_store {state : State} {processId : PID} {env : Environment} :
    (state.store processId env).timers = state.timers := rfl

@[simp] theorem State.timers_initial {env : Environment} : (State.initial env).timers = [] := rfl

@[simp] theorem State.timers_spawnWith {state : State} {processId : PID} {options : SpawnOptions} :
    (state.spawnWith processId options).2.timers = state.timers := by
  simp only [State.spawnWith, State.spawn, State.monitor]
  repeat' split
  all_goals simp

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
  /-- Deliver a message into the receiver's mailbox. -/
  | send (sender receiver : PID) (message : Term) : Event
  /-- Consume a message from the process's own mailbox. -/
  | receive (receiver : PID) (message : Term) : Event
  /-- A receive with a zero or positive timeout resumes without a message. -/
  | timeout : PID → Event
  /-- The process returns, raises, receives an exit signal, or does not
  return, with its exit reason. -/
  | exit (processId : PID) (reason : Term) : Event
  /-- The scheduler answers a request about other processes. -/
  | request (processId : PID) (query : Request) (reply : Term) : Event
  /-- A timer expires, so its message is on its way. -/
  | expire (reference : List Nat) : Event
  /-- The message of an expired timer arrives in the receiver's mailbox. -/
  | arrive (receiver : PID) (message : Term) : Event
deriving Repr

/-- Every step of the timers: an armed one expires, or the message of an
expired one arrives. Either may happen at any point, as elapsed time is not
modeled. -/
@[expose] def State.timerSteps (state : State) : List (Event × State) :=
  state.timers.map fun timer =>
    if timer.expired then
      (.arrive timer.destination timer.message,
        { state.deliver timer.destination timer.message with
          timers := state.timers.filter (·.reference != timer.reference) })
    else
      (.expire timer.reference,
        { state with timers := state.timers.map fun other =>
            if other.reference == timer.reference then { other with expired := true } else other })

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

/-- Every step the process can take in this state: none while blocked, two for
a positive-timeout receive without a match, one otherwise. -/
@[expose] def Task.transitions (state : State) (processId : PID) : Task α → List (Transition α)
  | ⟨computation, finish⟩ =>
    let view := state.view processId
    let process := state.process processId
    match process.signal with
    | some reason =>
        [{ event := .exit processId reason, state := state.terminate processId reason, tasks := []
           finished := (finish (.error (.exit reason))).map (·, view) }]
    | none =>
    match computation with
    | .error .exhausted =>
        [{ event := .exit processId (.atom "exhausted"), state := state.update processId none
           tasks := [], exhausted := true }]
    | .ok value =>
        [{ event := .exit processId (.atom "normal")
           state := state.terminate processId (.atom "normal"), tasks := []
           finished := (finish (.ok value)).map (·, view) }]
    | .error exception =>
        [{ event := .exit processId (exitReason exception)
           state := state.terminate processId (exitReason exception), tasks := []
           finished := (finish (.error exception)).map (·, view) }]
    | .get next =>
        [{ event := .internal processId, state
           tasks := [(processId, ⟨next view, finish⟩)] }]
    | .set updated next =>
        [{ event := .internal processId, state := state.store processId updated
           tasks := [(processId, ⟨next, finish⟩)] }]
    | Result.schedule options child next =>
        let (childPid, spawned) := state.spawnWith processId options
        [{ event := .spawn processId childPid, state := spawned
           tasks := [(processId, ⟨next childPid, finish⟩), (childPid, Task.child child)] }]
    | .send destination message next =>
        [{ event := .send processId destination message
           state := state.deliver destination message
           tasks := [(processId, ⟨next, finish⟩)] }]
    | .receive timeout select next =>
        match selectMessage (select view) process.mailbox with
        | some (message, value, remaining) =>
            [{ event := .receive processId message
               state := state.update processId (some { process with mailbox := remaining })
               tasks := [(processId, ⟨next (some value), finish⟩)] }]
        | none =>
            let timedOut : Transition α := {
              event := .timeout processId, state
              tasks := [(processId, ⟨next none, finish⟩)] }
            match timeout with
            | .infinity => []
            | .immediate => [timedOut]
            | .finite => [{ timedOut with expired := true }]
    | .request query next =>
        let (reply, answered) := state.request processId query
        (replies query reply).map fun reply =>
          { event := .request processId query reply, state := answered
            tasks := [(processId, ⟨next reply, finish⟩)] }

/-- Whether a computation starts with a process request, which hands it to the scheduler. -/
@[expose] def isRequest : Result α → Bool
  | Result.schedule .. | .send .. | .receive .. | .request .. => true
  | _ => false

/-- A state of a run. -/
inductive Config (α : Type) : Type 1 where
  /-- Before its first process request, a computation reads and replaces its
  environment directly. -/
  | start (env : Environment) (computation : Result α)
  /-- Live processes in tree order, the root's result once it ends, and whether
  some process did not return. -/
  | running (state : State) (tasks : List (PID × Task α))
      (finished : Option (Except Exception α × Environment)) (exhausted : Bool)

/-- The configuration a process step leads to. -/
@[expose] def Transition.apply (transition : Transition α) (before after : List (PID × Task α))
    (finished : Option (Except Exception α × Environment)) (exhausted : Bool) : Config α :=
  .running transition.state (before ++ transition.tasks ++ after)
    (transition.finished.orElse fun _ => finished) (exhausted || transition.exhausted)

/-- Any live process may take its step. The runner keeps running the current
process after an environment access, which is one of these interleavings. -/
inductive Step {α : Type} : Config α → Event → Config α → Prop where
  | get : Step (.start env (.get next)) (.internal env.currentPid) (.start env (next env))
  | set : Step (.start env (.set updated next)) (.internal env.currentPid) (.start updated next)
  /-- The first request starts the scheduler, with the current process as the root. -/
  | enter (request : isRequest computation = true) :
      Step (.start env computation) (.internal env.currentPid)
        (.running (State.initial env) [(env.currentPid, Task.root computation)] none false)
  | run (split : tasks = before ++ (processId, task) :: after)
      (possible : transition ∈ task.transitions state processId) :
      Step (.running state tasks finished exhausted) transition.event
        (transition.apply before after finished exhausted)
  /-- A timer expires, or the message of an expired one arrives. -/
  | timer (possible : (event, after) ∈ state.timerSteps) :
      Step (.running state tasks finished exhausted) event
        (.running after tasks finished exhausted)

/-- Consecutive steps and the trace of their events. -/
inductive Run {α : Type} : Config α → List Event → Config α → Prop where
  | refl : Run config [] config
  | step : Step first event next → Run next events last → Run first (event :: events) last

/-- A configuration without steps, and the outcome the runner reports for it. -/
inductive Terminal {α : Type} : Config α → Outcome α → Prop where
  | ok : Terminal (.start env (.ok value)) (.ok value)
  | error : Terminal (.start env (.error exception)) (.error exception)
  /-- Some process did not return, and no other process or timer can step. -/
  | exhausted (blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions state processId = []) (idle : state.timers = []) :
      Terminal (.running state tasks finished true) (.error .exhausted)
  | returned (idle : state.timers = []) :
      Terminal (.running state [] (some (.ok value, env)) false) (.ok value)
  | raised (idle : state.timers = []) :
      Terminal (.running state [] (some (.error exception, env)) false) (.error exception)
  /-- Every process is blocked and no timer is pending, or the root never
  produced a result. -/
  | deadlock (blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions state processId = [])
      (pending : tasks = [] → finished = none) (idle : state.timers = []) :
      Terminal (.running state tasks finished false) .deadlock

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
each step, and `check` follows them, taking independent steps first, such as
environment reads and writes, as `Config.reduced` describes, and following one
order of steps that commute, as `explore` describes. Proving `check` by
evaluation establishes a property for every schedule (see
`Lynx.concurrent_of_check`). -/

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

/-- Every step of a configuration, with its event. -/
@[expose] def Config.successors : Config α → List (Event × Config α)
  | .start env computation =>
      match computation with
      | .get next => [(.internal env.currentPid, .start env (next env))]
      | .set updated next => [(.internal env.currentPid, .start updated next)]
      | computation =>
          if isRequest computation then
            [(.internal env.currentPid,
              .running (State.initial env) [(env.currentPid, Task.root computation)] none false)]
          else []
  | .running state tasks finished exhausted =>
      let steps := (splits tasks).flatMap fun (before, (processId, task), after) =>
        (task.transitions state processId).map fun transition =>
          (transition.event, transition.apply before after finished exhausted)
      -- Evaluation skips timer steps when there are no timers, as usual.
      match state.timers with
      | [] => steps
      | _ :: _ => steps ++
          state.timerSteps.map fun (event, after) => (event, .running after tasks finished exhausted)

/-- The steps of the processes, then those of the timers. -/
theorem Config.successors_running {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool} :
    (Config.running state tasks finished exhausted).successors =
      (splits tasks).flatMap (fun (before, (processId, task), after) =>
        (task.transitions state processId).map fun transition =>
          (transition.event, transition.apply before after finished exhausted)) ++
      state.timerSteps.map fun (event, after) => (event, .running after tasks finished exhausted) := by
  simp only [Config.successors]
  split <;> simp_all [State.timerSteps]

theorem Step.mem_successors {first next : Config α} {event : Event}
    (step : Step first event next) : (event, next) ∈ first.successors := by
  cases step with
  | get => simp [Config.successors]
  | set => simp [Config.successors]
  | @enter computation env request =>
    cases computation <;> simp_all [isRequest, Config.successors]
  | run split possible =>
    subst split
    simp only [Config.successors_running, List.mem_append, List.mem_flatMap, Prod.exists,
      List.mem_map]
    exact .inl ⟨_, _, _, _, mem_splits, _, possible, rfl⟩
  | timer possible =>
    simp only [Config.successors_running, List.mem_append, List.mem_map, Prod.exists]
    exact .inr ⟨_, _, possible, rfl⟩

/-- Without timers, there are no timer steps. -/
@[simp] theorem State.timerSteps_eq_nil {state : State} :
    state.timerSteps = [] ↔ state.timers = [] := by
  simp [State.timerSteps]

/-- The outcome of a configuration without steps. -/
@[expose] def Config.outcome : Config α → Outcome α
  | .start _ (.ok value) => .ok value
  | .start _ (.error exception) => .error exception
  | .start _ _ => .deadlock
  | .running _ _ _ true => .error .exhausted
  | .running _ [] (some (.ok value, _)) false => .ok value
  | .running _ [] (some (.error exception, _)) false => .error exception
  | .running .. => .deadlock

theorem Terminal.outcome_eq {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : config.outcome = outcome := by
  cases terminal with
  | deadlock blocked pending =>
    unfold Config.outcome
    split <;> simp_all
  | exhausted => simp [Config.outcome]
  | _ => rfl

theorem Terminal.successors_eq_nil {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : config.successors = [] := by
  cases terminal with
  | deadlock blocked _ idle | exhausted blocked idle =>
    simp only [Config.successors_running, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
      Prod.forall, List.map_eq_nil_iff, State.timerSteps_eq_nil, idle, and_true]
    intro before processId task after mem
    simp [blocked processId task (by rw [eq_of_mem_splits mem]; simp)]
  | returned idle | raised idle => simp [Config.successors_running, splits, idle]
  | _ => simp [Config.successors, isRequest]

theorem Step.of_mem_successors {first next : Config α} {event : Event}
    (mem : (event, next) ∈ first.successors) : Step first event next := by
  cases first with
  | start env computation =>
    cases computation <;> simp only [Config.successors, isRequest, List.mem_singleton,
      Prod.mk.injEq, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at mem
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := mem; first | exact .get | exact .set | exact .enter rfl)
      | (simp at mem)
  | running state tasks finished exhausted =>
    simp only [Config.successors_running, List.mem_append, List.mem_flatMap, List.mem_map,
      Prod.exists, Prod.mk.injEq] at mem
    rcases mem with ⟨before, processId, task, after, split, transition, possible, rfl, rfl⟩ |
      ⟨event, after, possible, rfl, rfl⟩
    · exact .run (eq_of_mem_splits split) possible
    · exact .timer possible

/-! ### Deterministic evaluation

`Config.advance` repeatedly takes the first step of the first process that can
take one. Its runs are ordinary runs, so for programs whose outcome does not
depend on the schedule it evaluates that outcome. -/

/-- Take the first available step, at most `steps` times. -/
@[expose] def Config.advance : Nat → Config α → Config α
  | 0, config => config
  | steps + 1, config =>
      match config.successors with
      | [] => config
      | (_, next) :: _ => advance steps next

@[simp] theorem Config.advance_zero (config : Config α) : config.advance 0 = config := rfl

/-- Configurations without successors stay put, so advancing composes. -/
theorem Config.advance_add (first second : Nat) (config : Config α) :
    config.advance (first + second) = (config.advance first).advance second := by
  induction first generalizing config with
  | zero => simp
  | succ first ih =>
    rw [Nat.add_right_comm, Config.advance, Config.advance]
    split
    · rename_i stuck
      clear ih
      induction second with
      | zero => rfl
      | succ second ih => simp [Config.advance, stuck]
    · exact ih _

theorem Config.advance_succ {config next : Config α} {event : Event}
    {rest : List (Event × Config α)} (steps : Nat)
    (first : config.successors = (event, next) :: rest) :
    config.advance (steps + 1) = next.advance steps := by
  simp [Config.advance, first]

theorem Config.run_advance (steps : Nat) (config : Config α) :
    ∃ events, Run config events (config.advance steps) := by
  induction steps generalizing config with
  | zero => exact ⟨[], .refl⟩
  | succ steps ih =>
    simp only [Config.advance]
    split
    · exact ⟨[], .refl⟩
    · rename_i event next rest found
      have mem : (event, next) ∈ config.successors := by simp [found]
      obtain ⟨events, run⟩ := ih next
      exact ⟨event :: events, .step (Step.of_mem_successors mem) run⟩

/-- A configuration without successors is terminal. -/
theorem Config.terminal_of_successors_eq_nil {config : Config α}
    (stuck : config.successors = []) : Terminal config config.outcome := by
  cases config with
  | start env computation =>
    cases computation with
    | ok => exact .ok
    | error => exact .error
    | _ => simp [Config.successors, isRequest] at stuck
  | running state tasks finished exhausted =>
    simp only [Config.successors_running, List.append_eq_nil_iff, List.map_eq_nil_iff,
      State.timerSteps_eq_nil] at stuck
    obtain ⟨stuck, idle⟩ := stuck
    have blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions state processId = [] := by
      intro processId task mem
      obtain ⟨before, after, rfl⟩ := List.append_of_mem mem
      simp only [List.flatMap_eq_nil_iff, List.map_eq_nil_iff, Prod.forall] at stuck
      exact stuck _ _ _ _ mem_splits
    cases exhausted with
    | true => exact .exhausted blocked idle
    | false =>
      cases tasks with
      | cons => exact .deadlock blocked (by simp) idle
      | nil =>
        rcases finished with _ | ⟨_ | _, _⟩
        · exact .deadlock blocked (fun _ => rfl) idle
        · exact .raised idle
        · exact .returned idle

/-- Whether the next step of a process commutes with the steps of other
processes and timers, without a pending exit signal: reading or replacing its
environment, its dictionary and reference counter, which other processes cannot
inspect, or receiving a message already in its mailbox, which other processes
only append to. -/
@[expose] def Task.independent (state : State) (processId : PID) (task : Task α) : Bool :=
  (state.process processId).signal.isNone &&
    match task.computation with
    | .get _ | .set .. => true
    | .receive _ select _ =>
        (selectMessage (select (state.view processId)) (state.process processId).mailbox).isSome
    | _ => false

/-! ### Footprints

A step reads and writes some locations of the state: fields of processes,
whether processes are alive, and the timers. Steps of different processes whose
footprints do not conflict commute, so `check` follows one of their orders. -/

/-- A field of a process record. -/
inductive Field where
  | pdict | mailbox | refCounter | children | links | monitors | monitoring | aliases | trapExit
  | signal
deriving Repr

/-- The position of a field, to compare fields in evaluation. -/
@[expose] def Field.index : Field → Nat
  | .pdict => 0 | .mailbox => 1 | .refCounter => 2 | .children => 3 | .links => 4
  | .monitors => 5 | .monitoring => 6 | .aliases => 7 | .trapExit => 8 | .signal => 9

instance : BEq Field := ⟨fun first second => first.index == second.index⟩

instance : LawfulBEq Field where
  eq_of_beq {first second} equal := by
    cases first <;> cases second <;> simp_all [BEq.beq, Field.index]
  rfl {field} := by cases field <;> simp [BEq.beq]

instance : DecidableEq Field := fun first second => decidable_of_iff (first == second) beq_iff_eq

/-- Every field. -/
@[expose] def Field.all : List Field :=
  [.pdict, .mailbox, .refCounter, .children, .links, .monitors, .monitoring, .aliases, .trapExit,
    .signal]

theorem Field.mem_all (field : Field) : field ∈ Field.all := by
  cases field <;> simp [Field.all]

/-- A location of the state. -/
inductive Loc where
  | field (processId : PID) (field : Field)
  | alive (processId : PID)
  /-- The timers sending to a process, in order. -/
  | timersTo (processId : PID)
  /-- All timers, in order. -/
  | timers
deriving Repr

/-- Compare locations in evaluation. -/
@[expose] def Loc.beq : Loc → Loc → Bool
  | .field processId name, .field processId' name' => processId == processId' && name == name'
  | .alive processId, .alive processId' => processId == processId'
  | .timersTo processId, .timersTo processId' => processId == processId'
  | .timers, .timers => true
  | _, _ => false

instance : BEq Loc := ⟨Loc.beq⟩

instance : LawfulBEq Loc where
  eq_of_beq {first second} equal := by
    change Loc.beq first second = true at equal
    cases first <;> cases second <;> simp_all [Loc.beq]
  rfl {loc} := by
    change Loc.beq loc loc = true
    cases loc <;> simp [Loc.beq]

instance : DecidableEq Loc := fun first second => decidable_of_iff (first == second) beq_iff_eq

/-- Every location of a process. -/
@[expose] def Loc.process (processId : PID) : List Loc :=
  .alive processId :: Field.all.map (.field processId)

/-- What signaling a process reads. -/
@[expose] def Loc.signaled (target : PID) : List Loc :=
  [.alive target, .field target .trapExit, .field target .signal, .field target .mailbox]

/-- The locations a step reads and those it writes. -/
structure Footprint where
  reads : List Loc
  writes : List Loc

/-- Whether one of two steps writes what the other reads or writes. -/
@[expose] def Footprint.conflicts (first second : Footprint) : Bool :=
  first.writes.any (fun loc => second.reads.contains loc || second.writes.contains loc) ||
    second.writes.any fun loc => first.reads.contains loc

/-- The timers sending to processes, for timers with a reference. -/
@[expose] def State.timersWith (state : State) (reference : List Nat) : List Loc :=
  state.timers.filterMap fun timer =>
    if timer.reference == reference then some (.timersTo timer.destination) else none

/-- What a process exiting reads and writes, besides its own record: linked
processes receive exit signals, watchers `DOWN` messages, and timers sending to
it are canceled. -/
@[expose] def State.exitFootprint (state : State) (processId : PID) (reason : Term) : Footprint :=
  let process := state.process processId
  let timers : List Loc :=
    if state.timers.any (·.destination == processId) then [.timers, .timersTo processId] else []
  { reads := Loc.process processId ++ .timersTo processId :: timers ++
      process.links.flatMap (fun linked => .field linked .links :: Loc.signaled linked) ++
      process.monitors.flatMap fun (_, watcher) =>
        [.alive watcher, .field watcher .mailbox, .field watcher .monitoring, .field watcher .aliases]
    writes := Loc.process processId ++ timers ++
      process.links.flatMap (fun linked =>
        .field linked .links :: .field linked .mailbox ::
          if isNormal reason then [] else [.field linked .signal]) ++
      process.monitors.flatMap fun (_, watcher) =>
        [.field watcher .mailbox, .field watcher .monitoring, .field watcher .aliases] }

/-- What answering a request of a live process reads and writes, besides what
every step of the process reads. -/
@[expose] def Request.footprint (state : State) (processId : PID) (process : ProcessState) :
    Request → Footprint
  | .monitor target alias =>
      let changed : List Loc := if (state.processes target).isSome then
          [.field target .monitors, .field processId .monitoring] ++
            if alias then [.field processId .aliases] else []
        else [.field processId .mailbox]
      { reads := .alive target :: changed, writes := .field processId .refCounter :: changed }
  | .demonitor reference flush =>
      let own : List Loc := [.field processId .monitoring, .field processId .aliases] ++
        if flush && !process.monitoring.any (·.1 == reference) then [.field processId .mailbox]
        else []
      { reads := own ++ process.monitoring.flatMap fun (found, target) =>
          if found == reference then [.alive target, .field target .monitors] else []
        writes := own ++ process.monitoring.flatMap fun (found, target) =>
          if found == reference then [.field target .monitors] else [] }
  | .link target =>
      if target = processId then { reads := [], writes := [] }
      else if (state.processes target).isSome then
        { reads := [.alive target, .field processId .links, .field target .links]
          writes := [.field processId .links, .field target .links] }
      else
        { reads := [.alive target, .field processId .trapExit, .field processId .mailbox]
          writes := [.field processId .mailbox] }
  | .unlink target =>
      { reads := [.alive target, .field processId .links, .field target .links]
        writes := [.field processId .links, .field target .links] }
  | .exit target reason =>
      if target = processId && isNormal reason && !process.trapExit then
        { reads := [.field processId .trapExit], writes := [.field processId .signal] }
      else
        { reads := .field processId .trapExit :: Loc.signaled target
          writes := [.field target .signal, .field target .mailbox] }
  | .trapExit _ => { reads := [.field processId .trapExit], writes := [.field processId .trapExit] }
  | .alive target => { reads := [.alive target], writes := [] }
  | .sendAlias alias _ =>
      let owner := alias.dropLast
      { reads := [.alive owner, .field owner .aliases, .field owner .mailbox]
        writes := [.field owner .mailbox] }
  | .startTimer destination _ _ =>
      let timers : List Loc :=
        if (state.processes destination).isSome then [.timers, .timersTo destination] else []
      { reads := .alive destination :: timers, writes := .field processId .refCounter :: timers }
  | .cancelTimer reference =>
      { reads := [.timers], writes := .timers :: state.timersWith reference }

/-- What the next step of a live process reads and writes, besides what every
step of it reads, or nothing for steps treated as conflicting with every other
step. -/
@[expose] def Task.stepFootprint (state : State) (processId : PID) (process : ProcessState)
    (task : Task α) : Option Footprint :=
  match process.signal with
  | some reason => some (state.exitFootprint processId reason)
  | none =>
  match task.computation with
  | .ok _ => some (state.exitFootprint processId (.atom "normal"))
  | .error .exhausted => some { reads := [], writes := Loc.process processId }
  | .error exception => some (state.exitFootprint processId (exitReason exception))
  | .get _ => some { reads := [], writes := [] }
  | Result.schedule options _ _ =>
      let linked : List Loc := if options.link then [.field processId .links] else []
      let monitored : List Loc := if options.monitor then [.field processId .monitoring] else []
      some { reads := .field processId .children :: linked ++ monitored
             writes := .field processId .children ::
               Loc.process (processId ++ [process.children + 1]) ++ linked ++
               if options.monitor then .field processId .refCounter :: monitored else [] }
  | .send destination _ _ =>
      some { reads := [.alive destination, .field destination .mailbox]
             writes := [.field destination .mailbox] }
  | .receive _ select _ =>
      match selectMessage (select (state.view processId)) process.mailbox with
      | some _ => none
      | none => some { reads := [.field processId .mailbox], writes := [] }
  | .request query _ => some (Request.footprint state processId process query)
  | _ => none

/-- What the next step of a process reads and writes, or nothing for steps
treated as conflicting with every other step, such as steps of a process that
is not live. Every step reads the pending signal and what the process observes. -/
@[expose] def Task.footprint (state : State) (processId : PID) (task : Task α) : Option Footprint :=
  match state.processes processId with
  | none => none
  | some process => (task.stepFootprint state processId process).map fun footprint =>
      { footprint with reads := [.alive processId, .field processId .signal,
          .field processId .pdict, .field processId .refCounter] ++ footprint.reads }

/-- What a step of a timer reads and writes. -/
@[expose] def Timer.footprint (timer : Timer) (state : State) : Footprint :=
  if timer.expired then
    { reads := [.timers, .alive timer.destination, .field timer.destination .mailbox]
      writes := .timers :: .field timer.destination .mailbox :: state.timersWith timer.reference }
  else { reads := [.timers], writes := .timers :: state.timersWith timer.reference }

/-- Names a step across configurations: the step of a process by its place among
the process's steps, or the step of a timer by the timer's place. -/
inductive Key where
  | process (processId : PID) (index : Nat)
  | timer (index : Nat)
deriving Repr

/-- Compare keys in evaluation. -/
@[expose] def Key.beq : Key → Key → Bool
  | .process processId index, .process processId' index' =>
      processId == processId' && index == index'
  | .timer index, .timer index' => index == index'
  | _, _ => false

instance : BEq Key := ⟨Key.beq⟩

instance : LawfulBEq Key where
  eq_of_beq {first second} equal := by
    change Key.beq first second = true at equal
    cases first <;> cases second <;> simp_all [Key.beq]
  rfl {key} := by
    change Key.beq key key = true
    cases key <;> simp [Key.beq]

instance : DecidableEq Key := fun first second => decidable_of_iff (first == second) beq_iff_eq

/-- Every step of a running configuration, with its key, in the order of
`Config.successors`. -/
@[expose] def Config.steps : Config α → List (Key × Event × Config α)
  | .running state tasks finished exhausted =>
      let steps := (splits tasks).flatMap fun (before, (processId, task), after) =>
        (task.transitions state processId).zipIdx.map fun (transition, index) =>
          (.process processId index, transition.event,
            transition.apply before after finished exhausted)
      match state.timers with
      | [] => steps
      | _ :: _ => steps ++ state.timerSteps.zipIdx.map fun ((event, after), index) =>
          (.timer index, event, .running after tasks finished exhausted)
  | .start .. => []

/-- What the step with a key reads and writes. -/
@[expose] def Key.footprint (state : State) (tasks : List (PID × Task α)) : Key → Option Footprint
  | .process processId _ => (tasks.lookup processId).bind (·.footprint state processId)
  | .timer index => state.timers[index]?.map (·.footprint state)

/-- Whether the steps with two keys commute: they belong to different processes
or timers, and their footprints do not conflict. -/
@[expose] def Key.independent (state : State) (tasks : List (PID × Task α)) (first second : Key) :
    Bool :=
  let distinct := match first, second with
    | .process first _, .process second _ => first != second
    | .timer _, .timer _ => false
    | _, _ => true
  distinct && match first.footprint state tasks, second.footprint state tasks with
    | some first, some second => !first.conflicts second
    | _, _ => false

/-- Follow every step not asleep. Each step is followed with the sleeping steps
and the steps followed before it that commute with it asleep: runs taking those
first are covered elsewhere. -/
@[expose] def explore (visit : List Key → Config α → Bool) (independent : Key → Key → Bool)
    (sleep : List Key) : List Key → List (Key × Event × Config α) → Bool
  | _, [] => true
  | done, (key, _, next) :: rest =>
      if sleep.contains key then explore visit independent sleep done rest
      else visit ((sleep ++ done).filter (independent · key)) next &&
        explore visit independent sleep (done ++ [key]) rest

/-- The first rejected run that `explore` finds. -/
@[expose] def exploreFind (visit : List Key → Config α → Option (List Event × β))
    (independent : Key → Key → Bool) (sleep : List Key) :
    List Key → List (Key × Event × Config α) → Option (List Event × β)
  | _, [] => none
  | done, (key, event, next) :: rest =>
      if sleep.contains key then exploreFind visit independent sleep done rest
      else match visit ((sleep ++ done).filter (independent · key)) next with
        | some (events, failure) => some (event :: events, failure)
        | none => exploreFind visit independent sleep (done ++ [key]) rest

/-- The steps `check` follows: only the first process whose next step is
independent when there is one, as every run can take that step first and end
the same way, and otherwise every step. -/
@[expose] def Config.reduced (config : Config α) : List (Event × Config α) :=
  match config with
  | .running state tasks finished exhausted =>
      match (splits tasks).find? (fun (_, (processId, task), _) => task.independent state processId) with
      | some (before, (processId, task), after) =>
          (task.transitions state processId).map fun transition =>
            (transition.event, transition.apply before after finished exhausted)
      | none => config.successors
  | _ => config.successors

/-- Whether every run from the configuration ends in an accepted outcome,
following at most `depth` steps along each run, where runs taking a sleeping
step first are covered elsewhere. Runs that differ only in when a process takes
an independent step are followed once, see `Config.reduced`, and of runs that
differ only in the order of steps that commute, see `Key.independent`, one is
followed, see `explore`. -/
@[expose] def checkFrom (accept : Outcome α → Bool) : Nat → List Key → Config α → Bool
  | 0, _, _ => false
  | depth + 1, sleep, config =>
      match config with
      | .running state tasks _ _ =>
          match (splits tasks).find? (fun (_, (processId, task), _) =>
              task.independent state processId) with
          | some _ => config.reduced.all fun (_, next) => checkFrom accept depth [] next
          | none =>
              match config.steps with
              | [] => accept config.outcome
              | steps => explore (checkFrom accept depth) (Key.independent state tasks) sleep [] steps
      | config =>
          match config.successors with
          | [] => accept config.outcome
          | successors => successors.all fun (_, next) => checkFrom accept depth [] next

/-- Whether every run from the configuration ends in an accepted outcome,
following at most `depth` steps along each run. -/
@[expose] def check (accept : Outcome α → Bool) (depth : Nat) (config : Config α) : Bool :=
  checkFrom accept depth [] config

/-- How a run that `check` rejects fails. -/
inductive Failure (α : Type) where
  /-- The run ends in an outcome that is not accepted. -/
  | rejected : Outcome α → Failure α
  /-- The run takes more steps than the depth allows. -/
  | unfinished : Failure α

/-- The first run that `checkFrom` rejects. -/
@[expose] def counterexampleFrom (accept : Outcome α → Bool) :
    Nat → List Key → Config α → Option (List Event × Failure α)
  | 0, _, _ => some ([], .unfinished)
  | depth + 1, sleep, config =>
      let rejected := if accept config.outcome then none else some ([], .rejected config.outcome)
      let all (successors : List (Event × Config α)) := successors.findSome? fun (event, next) =>
        (counterexampleFrom accept depth [] next).map fun (events, failure) =>
          (event :: events, failure)
      match config with
      | .running state tasks _ _ =>
          match (splits tasks).find? (fun (_, (processId, task), _) =>
              task.independent state processId) with
          | some _ => all config.reduced
          | none =>
              match config.steps with
              | [] => rejected
              | steps => exploreFind (counterexampleFrom accept depth) (Key.independent state tasks)
                  sleep [] steps
      | config =>
          match config.successors with
          | [] => rejected
          | successors => all successors

/-- The first run that `check` rejects, as the events of its steps and how it
fails. Evaluating it is a fast way to find why a check fails. -/
@[expose] def counterexample (accept : Outcome α → Bool) (depth : Nat) (config : Config α) :
    Option (List Event × Failure α) :=
  counterexampleFrom accept depth [] config

theorem explore_eq_true_iff {visit : List Key → Config α → Bool}
    {find : List Key → Config α → Option (List Event × β)} {independent : Key → Key → Bool}
    (same : ∀ sleep next, visit sleep next = true ↔ find sleep next = none)
    (sleep done : List Key) (steps : List (Key × Event × Config α)) :
    explore visit independent sleep done steps = true ↔
      exploreFind find independent sleep done steps = none := by
  induction steps generalizing done with
  | nil => simp [explore, exploreFind]
  | cons step rest ih =>
    obtain ⟨key, event, next⟩ := step
    simp only [explore, exploreFind]
    split
    · exact ih done
    · rw [Bool.and_eq_true, same, ih]
      split <;> simp_all

theorem checkFrom_eq_true_iff (accept : Outcome α → Bool) (depth : Nat) (sleep : List Key)
    (config : Config α) :
    checkFrom accept depth sleep config = true ↔ counterexampleFrom accept depth sleep config = none := by
  induction depth generalizing sleep config with
  | zero => simp [checkFrom, counterexampleFrom]
  | succ depth ih =>
    simp only [checkFrom, counterexampleFrom]
    have all : ∀ successors : List (Event × Config α),
        (successors.all fun (_, next) => checkFrom accept depth [] next) = true ↔
          (successors.findSome? fun (event, next) =>
            (counterexampleFrom accept depth [] next).map fun (events, failure) =>
              (event :: events, failure)) = none := by
      intro successors
      simp only [List.all_eq_true, List.findSome?_eq_none_iff, Option.map_eq_none_iff, ih]
    split
    · split
      · exact all _
      · split
        · split <;> simp_all
        · exact explore_eq_true_iff (fun sleep next => ih sleep next) _ _ _
    · split
      · split <;> simp_all
      · exact all _

theorem check_eq_true_iff (accept : Outcome α → Bool) (depth : Nat) (config : Config α) :
    check accept depth config = true ↔ counterexample accept depth config = none :=
  checkFrom_eq_true_iff accept depth [] config

end Lynx.Concurrent
