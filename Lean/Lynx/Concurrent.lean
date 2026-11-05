module

public import Lynx.Term.DataTypes

/-! Interleaving semantics of local processes, as a labelled transition system.

`Lynx.Result.run` executes one interleaving chosen by its scheduler choices.
This module describes every interleaving instead: a `Step` advances one
process, and a `Run` collects the `Event`s of consecutive steps as a trace.
The runner's soundness theorems show that each run with any scheduler choices
is a `Run` ending in a `Terminal` configuration with the same outcome, so a
property of every terminal configuration holds for every schedule.

Each step mirrors the runner exactly, including how processes save and
restore their state in the shared `Environment`. Environment reads and writes
are not scheduler boundaries: after such a step, the same process continues
while it can run, so its local code executes atomically between process
requests. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- Remove every saved state of a process. -/
@[expose] def removeProcess (processId : PID) : List (PID × ProcessState) → List (PID × ProcessState)
  | [] => []
  | entry :: rest =>
      if entry.1 = processId then removeProcess processId rest else entry :: removeProcess processId rest

/-- The first saved state of a process. -/
@[expose] def findProcess (processId : PID) : List (PID × ProcessState) → Option ProcessState
  | [] => none
  | entry :: rest =>
      if entry.1 = processId then some entry.2 else findProcess processId rest

/-- Restore the environment of a process before running it, including in guards. -/
@[expose] def activate (env : Environment) (processId : PID) : Environment :=
  { env with currentPid := processId
             currentProcess := (findProcess processId env.processes).getD {}
             processes := removeProcess processId env.processes }

/-- Save the current process's state among the others. -/
@[expose] def save (env : Environment) : Environment :=
  { env with processes :=
      (env.currentPid, env.currentProcess) :: removeProcess env.currentPid env.processes }

/-- Append a message to a live mailbox. Messages to unknown PIDs are discarded. -/
@[expose] def deliver (env : Environment) (processId : PID) (message : Term) : Environment :=
  if processId = env.currentPid then
    { env with currentProcess.mailbox := env.currentProcess.mailbox ++ [message] }
  else
    { env with processes := env.processes.map fun (savedPid, process) =>
        (savedPid, if savedPid = processId then
          { process with mailbox := process.mailbox ++ [message] } else process) }

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
  environment : Environment
  /-- Empty when the process ends; otherwise its continuation, followed by
  any process it spawned. -/
  tasks : List (PID × Task α)
  /-- The root's result and final process state, when the root ends. -/
  finished : Option (Except Exception α × ProcessState) := none
  /-- Spawns, sends, and receives are scheduler boundaries. -/
  boundary : Bool := false
  /-- A positive timeout expired, which is the scheduler's choice. -/
  expired : Bool := false
  /-- The process did not return, which ends the whole run. -/
  exhausted : Bool := false

/-- Every step the process can take in this environment: none while blocked,
two for a positive-timeout receive without a match, one otherwise. -/
@[expose] def Task.transitions (env : Environment) (processId : PID) : Task α → List (Transition α)
  | ⟨computation, finish⟩ =>
    let active := activate env processId
    match computation with
    | .error .exhausted =>
        [{ event := .exit processId, environment := active, tasks := [], exhausted := true }]
    | .ok value =>
        [{ event := .exit processId, environment := active, tasks := []
           finished := (finish (.ok value)).map (·, active.currentProcess) }]
    | .error exception =>
        [{ event := .exit processId, environment := active, tasks := []
           finished := (finish (.error exception)).map (·, active.currentProcess) }]
    | .get next =>
        [{ event := .internal processId, environment := save active
           tasks := [(processId, ⟨next active, finish⟩)] }]
    | .set updated next =>
        [{ event := .internal processId, environment := save updated
           tasks := [(processId, ⟨next, finish⟩)] }]
    | Result.schedule child next =>
        let childPid := active.pidCounter + 1
        [{ event := .spawn processId childPid
           environment := save { active with
             pidCounter := childPid
             processes := (childPid, {}) :: active.processes }
           tasks := [(processId, ⟨next childPid, finish⟩), (childPid, Task.child child)]
           boundary := true }]
    | .send destination message next =>
        [{ event := .send processId destination message
           environment := save (deliver active destination message)
           tasks := [(processId, ⟨next, finish⟩)]
           boundary := true }]
    | .receive timeout select next =>
        match selectMessage (select active) active.currentProcess.mailbox with
        | some (message, value, remaining) =>
            [{ event := .receive processId message
               environment := save { active with currentProcess.mailbox := remaining }
               tasks := [(processId, ⟨next (some value), finish⟩)]
               boundary := true }]
        | none =>
            let timedOut : Transition α := {
              event := .timeout processId, environment := save active
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
  /-- Live processes in tree order, the root's result once it ends, and whether
  the last step was an environment access or an exit rather than a boundary. -/
  | running (env : Environment) (tasks : List (PID × Task α))
      (finished : Option (Except Exception α × ProcessState)) (sticky : Bool)
  /-- Some process did not return. -/
  | halted

/-- The process can make progress other than by expiring a timeout. -/
@[expose] def Ready (env : Environment) (tasks : List (PID × Task α)) (processId : PID) : Prop :=
  ∃ task, (processId, task) ∈ tasks ∧
    ∃ transition ∈ task.transitions env processId, transition.expired = false

/-- After an environment access or exit, the current process keeps running while
it is ready. Otherwise any process may take any of its steps. -/
@[expose] def Allowed (env : Environment) (tasks : List (PID × Task α)) (sticky : Bool)
    (processId : PID) (transition : Transition α) : Prop :=
  sticky = true → Ready env tasks env.currentPid →
    processId = env.currentPid ∧ transition.expired = false

inductive Step {α : Type} : Config α → Event → Config α → Prop where
  | get : Step (.start env (.get next)) (.internal env.currentPid) (.start env (next env))
  | set : Step (.start env (.set updated next)) (.internal env.currentPid) (.start updated next)
  /-- The first request starts the scheduler, with the current process as the root. -/
  | enter (request : isRequest computation = true) :
      Step (.start env computation) (.internal env.currentPid)
        (.running (save env) [(env.currentPid, Task.root computation)] none true)
  | run (split : tasks = before ++ (processId, task) :: after)
      (possible : transition ∈ task.transitions env processId)
      (allowed : Allowed env tasks sticky processId transition)
      (returns : transition.exhausted = false) :
      Step (.running env tasks finished sticky) transition.event
        (.running transition.environment (before ++ transition.tasks ++ after)
          (transition.finished.orElse fun _ => finished) (!transition.boundary))
  | exhaust (split : tasks = before ++ (processId, task) :: after)
      (possible : transition ∈ task.transitions env processId)
      (allowed : Allowed env tasks sticky processId transition)
      (exhausted : transition.exhausted = true) :
      Step (.running env tasks finished sticky) transition.event .halted

/-- Consecutive steps and the trace of their events. -/
inductive Run {α : Type} : Config α → List Event → Config α → Prop where
  | refl : Run config [] config
  | step : Step first event next → Run next events last → Run first (event :: events) last

/-- A configuration without steps, and the outcome the runner reports for it. -/
inductive Terminal {α : Type} : Config α → Outcome α → Prop where
  | ok : Terminal (.start env (.ok value)) (.ok value)
  | error : Terminal (.start env (.error exception)) (.error exception)
  | halted : Terminal .halted (.error .exhausted)
  | returned : Terminal (.running env [] (some (.ok value, state)) sticky) (.ok value)
  | raised : Terminal (.running env [] (some (.error exception, state)) sticky) (.error exception)
  /-- Every process is blocked, or the root never produced a result. -/
  | deadlock (blocked : ∀ processId task, (processId, task) ∈ tasks →
        task.transitions env processId = [])
      (pending : tasks = [] → finished = none) :
      Terminal (.running env tasks finished sticky) .deadlock

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
@[expose] def isReady (env : Environment) (tasks : List (PID × Task α)) (processId : PID) : Bool :=
  tasks.any fun (candidate, task) => candidate == processId &&
    (task.transitions env candidate).any fun transition => !transition.expired

theorem isReady_iff {env : Environment} {tasks : List (PID × Task α)} {processId : PID} :
    isReady env tasks processId = true ↔ Ready env tasks processId := by
  simp only [isReady, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    Prod.exists, Ready]
  constructor
  · rintro ⟨_, task, mem, rfl, transition, possible, unexpired⟩
    exact ⟨task, mem, transition, possible, unexpired⟩
  · rintro ⟨task, mem, transition, possible, unexpired⟩
    exact ⟨_, task, mem, rfl, transition, possible, unexpired⟩

/-- The configuration a process step leads to. -/
@[expose] def Transition.apply (transition : Transition α) (before after : List (PID × Task α))
    (finished : Option (Except Exception α × ProcessState)) : Config α :=
  if transition.exhausted then .halted else
    .running transition.environment (before ++ transition.tasks ++ after)
      (transition.finished.orElse fun _ => finished) (!transition.boundary)

/-- Every step of a configuration, with its event. -/
@[expose] def Config.successors : Config α → List (Event × Config α)
  | .start env computation =>
      match computation with
      | .get next => [(.internal env.currentPid, .start env (next env))]
      | .set updated next => [(.internal env.currentPid, .start updated next)]
      | computation =>
          if isRequest computation then
            [(.internal env.currentPid,
              .running (save env) [(env.currentPid, Task.root computation)] none true)]
          else []
  | .running env tasks finished sticky =>
      let restricted := sticky && isReady env tasks env.currentPid
      (splits tasks).flatMap fun (before, (processId, task), after) =>
        (task.transitions env processId).filterMap fun transition =>
          if restricted && !(processId == env.currentPid && !transition.expired) then none
          else some (transition.event, transition.apply before after finished)
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
    split
    · rename_i blocked
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at blocked
      obtain ⟨⟨sticky, ready⟩, notCurrent⟩ := blocked
      obtain ⟨equal, unexpired⟩ := allowed sticky (isReady_iff.mp ready)
      simp_all
    · simp [Transition.apply, returns]

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
