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

/-- The runtime shared by all processes of a run. -/
structure State where
  /-- Live processes. Terminated and unknown PIDs have no state. -/
  processes : PID → Option ProcessState := fun _ => none

/-- Replace the record of one process. -/
@[expose] def State.update (state : State) (processId : PID) (process : Option ProcessState) :
    State :=
  { processes := fun candidate =>
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

/-- Whether a message is the `DOWN` message of a monitor. -/
@[expose] def isDown (reference : List Nat) : Term → Bool
  | .tuple ⟨[.atom "DOWN", .reference found, _, _, _]⟩ => found == reference
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
monitoring process a `DOWN` message, which ends its monitor and alias. -/
@[expose] def State.terminate (state : State) (processId : PID) (reason : Term) : State :=
  let process := state.process processId
  let state := state.update processId none
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
      let process := state.process processId
      let state := process.monitoring.foldl (fun state (found, target) =>
        if found == reference then
          state.modify target fun watched =>
            { watched with monitors := watched.monitors.filter (·.1 != reference) }
        else state) state
      (.atom (if process.monitoring.any (·.1 == reference) then "true" else "false"),
        state.modify processId fun process =>
        { process with
            monitoring := process.monitoring.filter (·.1 != reference)
            aliases := process.aliases.erase reference
            mailbox := if flush then process.mailbox.filter (!isDown reference ·)
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

/-- The runtime of a single process continuing from its environment. -/
@[expose] def State.initial (env : Environment) : State :=
  { processes := fun candidate =>
      if candidate = env.currentPid then
        some { pdict := env.pdict, refCounter := env.refCounter }
      else none }

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

/-- Select the oldest matching message, preserving all unmatched messages.
Returns the message, the selector's bindings, and the remaining mailbox. -/
@[expose] def selectMessage (select : Term → Option β) : List Term → Option (Term × β × List Term)
  | [] => none
  | message :: rest =>
      match select message with
      | some value => some (message, value, rest)
      | none => (selectMessage select rest).map fun (selected, value, remaining) =>
          (selected, value, message :: remaining)

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
        [{ event := .request processId query reply, state := answered
           tasks := [(processId, ⟨next reply, finish⟩)] }]

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

/-- Consecutive steps and the trace of their events. -/
inductive Run {α : Type} : Config α → List Event → Config α → Prop where
  | refl : Run config [] config
  | step : Step first event next → Run next events last → Run first (event :: events) last

/-- A configuration without steps, and the outcome the runner reports for it. -/
inductive Terminal {α : Type} : Config α → Outcome α → Prop where
  | ok : Terminal (.start env (.ok value)) (.ok value)
  | error : Terminal (.start env (.error exception)) (.error exception)
  /-- Some process did not return, and no other process can step. -/
  | exhausted (blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions state processId = []) :
      Terminal (.running state tasks finished true) (.error .exhausted)
  | returned : Terminal (.running state [] (some (.ok value, env)) false) (.ok value)
  | raised : Terminal (.running state [] (some (.error exception, env)) false)
      (.error exception)
  /-- Every process is blocked, or the root never produced a result. -/
  | deadlock (blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions state processId = [])
      (pending : tasks = [] → finished = none) :
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
each step, and `check` follows them, taking environment reads first as
`Config.reduced` describes. Proving `check` by evaluation establishes a
property for every schedule (see `Lynx.concurrent_of_check`). -/

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
      (splits tasks).flatMap fun (before, (processId, task), after) =>
        (task.transitions state processId).map fun transition =>
          (transition.event, transition.apply before after finished exhausted)

theorem Step.mem_successors {first next : Config α} {event : Event}
    (step : Step first event next) : (event, next) ∈ first.successors := by
  cases step with
  | get => simp [Config.successors]
  | set => simp [Config.successors]
  | @enter computation env request =>
    cases computation <;> simp_all [isRequest, Config.successors]
  | run split possible =>
    subst split
    simp only [Config.successors, List.mem_flatMap, Prod.exists, List.mem_map]
    exact ⟨_, _, _, _, mem_splits, _, possible, rfl⟩

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
  | deadlock blocked | exhausted blocked =>
    simp only [Config.successors, List.flatMap_eq_nil_iff, Prod.forall]
    intro before processId task after mem
    simp [blocked processId task (by rw [eq_of_mem_splits mem]; simp)]
  | _ => simp [Config.successors, splits, isRequest]

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
    simp only [Config.successors, List.mem_flatMap, List.mem_map, Prod.exists, Prod.mk.injEq] at mem
    obtain ⟨before, processId, task, after, split, transition, possible, rfl, rfl⟩ := mem
    exact .run (eq_of_mem_splits split) possible

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
    have blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions state processId = [] := by
      intro processId task mem
      obtain ⟨before, after, rfl⟩ := List.append_of_mem mem
      simp only [Config.successors, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
        Prod.forall] at stuck
      exact stuck _ _ _ _ mem_splits
    cases exhausted with
    | true => exact .exhausted blocked
    | false =>
      cases tasks with
      | cons => exact .deadlock blocked (by simp)
      | nil =>
        rcases finished with _ | ⟨_ | _, _⟩
        · exact .deadlock blocked (fun _ => rfl)
        · exact .raised
        · exact .returned

/-- Whether a process is about to read its environment, without a pending exit
signal. Steps of other processes cannot change what it reads, and it changes
nothing they observe, so it can step before them. -/
@[expose] def Task.reads (state : State) (processId : PID) (task : Task α) : Bool :=
  (state.process processId).signal.isNone &&
    match task.computation with
    | .get _ => true
    | _ => false

/-- The steps `check` follows: only the first process about to read its
environment when there is one, as every other order of its read reaches the
same configurations, and otherwise every step. -/
@[expose] def Config.reduced (config : Config α) : List (Event × Config α) :=
  match config with
  | .running state tasks finished exhausted =>
      match (splits tasks).find? (fun (_, (processId, task), _) => task.reads state processId) with
      | some (before, (processId, task), after) =>
          (task.transitions state processId).map fun transition =>
            (transition.event, transition.apply before after finished exhausted)
      | none => config.successors
  | _ => config.successors

/-- Whether every run from the configuration ends in an accepted outcome,
following at most `depth` steps along each run. Runs that differ only in when
a process reads its environment are followed once, see `Config.reduced`. -/
@[expose] def check (accept : Outcome α → Bool) : Nat → Config α → Bool
  | 0, _ => false
  | depth + 1, config =>
      match config.reduced with
      | [] => accept config.outcome
      | successors => successors.all fun (_, next) => check accept depth next

end Lynx.Concurrent
