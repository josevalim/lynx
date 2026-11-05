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
process is running. Environment reads and writes are not scheduler
boundaries: after such a step, the same process continues while it can run,
so its local code executes atomically between process requests. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- The scheduler's record of a process that is not running. -/
structure ProcessState where
  pdict : List (Term × Term) := []
  mailbox : List Term := []
deriving Repr, Inhabited

/-- The runtime shared by all processes of a run. -/
structure State where
  /-- Greatest reference identity allocated in this runtime. -/
  refCounter : Nat := 0
  /-- Greatest PID allocated so far. A spawn increments this before allocation. -/
  pidCounter : PID := 1
  /-- Live processes. Terminated and unknown PIDs have no state. -/
  processes : PID → Option ProcessState := fun _ => none

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
  { currentPid := processId, refCounter := state.refCounter
    pdict := (state.process processId).pdict }

/-- Keep what the process left in its environment. Its identity is not stored. -/
@[expose] def State.store (state : State) (processId : PID) (env : Environment) : State :=
  { state.update processId (some { state.process processId with pdict := env.pdict }) with
    refCounter := env.refCounter }

/-- Append a message to a live mailbox. Messages to other PIDs are discarded. -/
@[expose] def State.deliver (state : State) (processId : PID) (message : Term) : State :=
  match state.processes processId with
  | some process => state.update processId (some { process with mailbox := process.mailbox ++ [message] })
  | none => state

/-- The runtime of a single process continuing from its environment. -/
@[expose] def State.initial (env : Environment) : State :=
  { refCounter := env.refCounter, pidCounter := env.currentPid
    processes := fun candidate =>
      if candidate = env.currentPid then some { pdict := env.pdict } else none }

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
  /-- The process returns, raises, or does not return. -/
  | exit : PID → Event
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
  /-- Spawns, sends, and receives are scheduler boundaries. -/
  boundary : Bool := false
  /-- A positive timeout expired, which is the scheduler's choice. -/
  expired : Bool := false
  /-- The process did not return, which ends the whole run. -/
  exhausted : Bool := false

/-- Every step the process can take in this state: none while blocked, two for
a positive-timeout receive without a match, one otherwise. -/
@[expose] def Task.transitions (state : State) (processId : PID) : Task α → List (Transition α)
  | ⟨computation, finish⟩ =>
    let view := state.view processId
    match computation with
    | .error .exhausted =>
        [{ event := .exit processId, state, tasks := [], exhausted := true }]
    | .ok value =>
        [{ event := .exit processId, state := state.update processId none, tasks := []
           finished := (finish (.ok value)).map (·, view) }]
    | .error exception =>
        [{ event := .exit processId, state := state.update processId none, tasks := []
           finished := (finish (.error exception)).map (·, view) }]
    | .get next =>
        [{ event := .internal processId, state
           tasks := [(processId, ⟨next view, finish⟩)] }]
    | .set updated next =>
        [{ event := .internal processId, state := state.store processId updated
           tasks := [(processId, ⟨next, finish⟩)] }]
    | Result.schedule child next =>
        let childPid := state.pidCounter + 1
        [{ event := .spawn processId childPid
           state := { state.update childPid (some {}) with pidCounter := childPid }
           tasks := [(processId, ⟨next childPid, finish⟩), (childPid, Task.child child)]
           boundary := true }]
    | .send destination message next =>
        [{ event := .send processId destination message
           state := state.deliver destination message
           tasks := [(processId, ⟨next, finish⟩)]
           boundary := true }]
    | .receive timeout select next =>
        let process := state.process processId
        match selectMessage (select view) process.mailbox with
        | some (message, value, remaining) =>
            [{ event := .receive processId message
               state := state.update processId (some { process with mailbox := remaining })
               tasks := [(processId, ⟨next (some value), finish⟩)]
               boundary := true }]
        | none =>
            let timedOut : Transition α := {
              event := .timeout processId, state
              tasks := [(processId, ⟨next none, finish⟩)], boundary := true }
            match timeout with
            | .infinity => []
            | .immediate => [timedOut]
            | .finite => [{ timedOut with expired := true }]

/-- Whether a computation starts with a process request, which hands it to the scheduler. -/
@[expose] def isRequest : Result α → Bool
  | Result.schedule .. | .send .. | .receive .. => true
  | _ => false

/-- A state of a run. -/
inductive Config (α : Type) : Type 1 where
  /-- Before its first process request, a computation reads and replaces its
  environment directly. -/
  | start (env : Environment) (computation : Result α)
  /-- Live processes in tree order, the root's result once it ends, and the
  process that must keep running while it is ready, after an environment
  access or exit rather than a scheduler boundary. -/
  | running (state : State) (tasks : List (PID × Task α))
      (finished : Option (Except Exception α × Environment)) (current : Option PID)
  /-- Some process did not return. -/
  | halted

/-- The process can make progress other than by expiring a timeout. -/
@[expose] def Ready (state : State) (tasks : List (PID × Task α)) (processId : PID) : Prop :=
  ∃ task, (processId, task) ∈ tasks ∧
    ∃ transition ∈ task.transitions state processId, transition.expired = false

/-- The current process keeps running while it is ready. Otherwise any process
may take any of its steps. -/
@[expose] def Allowed (state : State) (tasks : List (PID × Task α)) (current : Option PID)
    (processId : PID) (transition : Transition α) : Prop :=
  ∀ running, current = some running → Ready state tasks running →
    processId = running ∧ transition.expired = false

/-- The process that keeps running after a step. -/
@[expose] def Transition.current (transition : Transition α) (processId : PID) : Option PID :=
  if transition.boundary then none else some processId

inductive Step {α : Type} : Config α → Event → Config α → Prop where
  | get : Step (.start env (.get next)) (.internal env.currentPid) (.start env (next env))
  | set : Step (.start env (.set updated next)) (.internal env.currentPid) (.start updated next)
  /-- The first request starts the scheduler, with the current process as the root. -/
  | enter (request : isRequest computation = true) :
      Step (.start env computation) (.internal env.currentPid)
        (.running (State.initial env) [(env.currentPid, Task.root computation)] none
          (some env.currentPid))
  | run (split : tasks = before ++ (processId, task) :: after)
      (possible : transition ∈ task.transitions state processId)
      (allowed : Allowed state tasks current processId transition)
      (returns : transition.exhausted = false) :
      Step (.running state tasks finished current) transition.event
        (.running transition.state (before ++ transition.tasks ++ after)
          (transition.finished.orElse fun _ => finished) (transition.current processId))
  | exhaust (split : tasks = before ++ (processId, task) :: after)
      (possible : transition ∈ task.transitions state processId)
      (allowed : Allowed state tasks current processId transition)
      (exhausted : transition.exhausted = true) :
      Step (.running state tasks finished current) transition.event .halted

/-- Consecutive steps and the trace of their events. -/
inductive Run {α : Type} : Config α → List Event → Config α → Prop where
  | refl : Run config [] config
  | step : Step first event next → Run next events last → Run first (event :: events) last

/-- A configuration without steps, and the outcome the runner reports for it. -/
inductive Terminal {α : Type} : Config α → Outcome α → Prop where
  | ok : Terminal (.start env (.ok value)) (.ok value)
  | error : Terminal (.start env (.error exception)) (.error exception)
  | halted : Terminal .halted (.error .exhausted)
  | returned : Terminal (.running state [] (some (.ok value, env)) current) (.ok value)
  | raised : Terminal (.running state [] (some (.error exception, env)) current)
      (.error exception)
  /-- Every process is blocked, or the root never produced a result. -/
  | deadlock (blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions state processId = [])
      (pending : tasks = [] → finished = none) :
      Terminal (.running state tasks finished current) .deadlock

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
establishes a property for every schedule. -/

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

/-- Decide `Ready`. -/
@[expose] def isReady (state : State) (tasks : List (PID × Task α)) (processId : PID) : Bool :=
  tasks.any fun (candidate, task) => candidate == processId &&
    (task.transitions state candidate).any fun transition => !transition.expired

theorem isReady_iff {state : State} {tasks : List (PID × Task α)} {processId : PID} :
    isReady state tasks processId = true ↔ Ready state tasks processId := by
  simp only [isReady, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    Prod.exists, Ready]
  constructor
  · rintro ⟨_, task, mem, rfl, transition, possible, unexpired⟩
    exact ⟨task, mem, transition, possible, unexpired⟩
  · rintro ⟨task, mem, transition, possible, unexpired⟩
    exact ⟨_, task, mem, rfl, transition, possible, unexpired⟩

/-- The configuration a process step leads to. -/
@[expose] def Transition.apply (transition : Transition α) (processId : PID)
    (before after : List (PID × Task α))
    (finished : Option (Except Exception α × Environment)) : Config α :=
  if transition.exhausted then .halted else
    .running transition.state (before ++ transition.tasks ++ after)
      (transition.finished.orElse fun _ => finished) (transition.current processId)

/-- Whether the current process, if ready, permits a process's step. -/
@[expose] def permits (state : State) (tasks : List (PID × Task α)) (current : Option PID)
    (processId : PID) (transition : Transition α) : Bool :=
  match current with
  | some running => !isReady state tasks running || (processId == running && !transition.expired)
  | none => true

theorem permits_iff {state : State} {tasks : List (PID × Task α)} {current : Option PID}
    {processId : PID} {transition : Transition α} :
    permits state tasks current processId transition = true ↔
      Allowed state tasks current processId transition := by
  cases current with
  | none => simp [permits, Allowed]
  | some running =>
    simp only [permits, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq,
      Allowed, Option.some.injEq, forall_eq', ← isReady_iff]
    cases isReady state tasks running <;> simp

/-- Every step of a configuration, with its event. -/
@[expose] def Config.successors : Config α → List (Event × Config α)
  | .start env computation =>
      match computation with
      | .get next => [(.internal env.currentPid, .start env (next env))]
      | .set updated next => [(.internal env.currentPid, .start updated next)]
      | computation =>
          if isRequest computation then
            [(.internal env.currentPid,
              .running (State.initial env) [(env.currentPid, Task.root computation)] none
                (some env.currentPid))]
          else []
  | .running state tasks finished current =>
      (splits tasks).flatMap fun (before, (processId, task), after) =>
        (task.transitions state processId).filterMap fun transition =>
          if permits state tasks current processId transition then
            some (transition.event, transition.apply processId before after finished)
          else none
  | .halted => []

theorem Step.mem_successors {first next : Config α} {event : Event}
    (step : Step first event next) : (event, next) ∈ first.successors := by
  cases step with
  | get => simp [Config.successors]
  | set => simp [Config.successors]
  | @enter computation env request =>
    cases computation <;> simp_all [isRequest, Config.successors]
  | run split possible allowed returns
  | exhaust split possible allowed returns =>
    subst split
    simp only [Config.successors, List.mem_flatMap, Prod.exists, List.mem_filterMap]
    refine ⟨_, _, _, _, mem_splits, _, possible, ?_⟩
    simp [permits_iff.mpr allowed, Transition.apply, returns]

/-- The outcome of a configuration without steps. -/
@[expose] def Config.outcome : Config α → Outcome α
  | .start _ (.ok value) => .ok value
  | .start _ (.error exception) => .error exception
  | .start _ _ => .deadlock
  | .running _ [] (some (.ok value, _)) _ => .ok value
  | .running _ [] (some (.error exception, _)) _ => .error exception
  | .running .. => .deadlock
  | .halted => .error .exhausted

theorem Terminal.outcome_eq {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : config.outcome = outcome := by
  cases terminal with
  | deadlock blocked pending =>
    unfold Config.outcome
    split <;> simp_all
  | _ => rfl

theorem Terminal.successors_eq_nil {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : config.successors = [] := by
  cases terminal with
  | deadlock blocked =>
    simp only [Config.successors, List.flatMap_eq_nil_iff, Prod.forall]
    intro before processId task after mem
    simp [blocked processId task (by rw [eq_of_mem_splits mem]; simp)]
  | _ => simp [Config.successors, splits, isRequest]

/-- Whether every run from the configuration ends in an accepted outcome,
following at most `depth` steps along each run. -/
@[expose] def check (accept : Outcome α → Bool) : Nat → Config α → Bool
  | 0, _ => false
  | depth + 1, config =>
      match config.successors with
      | [] => accept config.outcome
      | successors => successors.all fun (_, next) => check accept depth next

theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {first last : Config α}
    {events : List Event} {outcome : Outcome α} (checked : check accept depth first = true)
    (run : Run first events last) (terminal : Terminal last outcome) : accept outcome = true := by
  induction run generalizing depth with
  | refl =>
    cases depth with
    | zero => simp [check] at checked
    | succ depth =>
      simp only [check, terminal.successors_eq_nil, terminal.outcome_eq] at checked
      exact checked
  | step step _ ih =>
    cases depth with
    | zero => simp [check] at checked
    | succ depth =>
      have mem := step.mem_successors
      unfold check at checked
      split at checked
      · rename_i empty; simp [empty] at mem
      · simp only [List.all_eq_true, Prod.forall] at checked
        exact ih (checked _ _ mem) terminal

end Lynx.Concurrent
