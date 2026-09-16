module

public import Lynx.Term.DataTypes

namespace Lynx.Term.Runner

open Lynx

private def removeProcess (pid : PID) : List (PID × ProcessState) → List (PID × ProcessState)
  | [] => []
  | entry :: rest =>
      if entry.1 = pid then removeProcess pid rest else entry :: removeProcess pid rest

private def findProcess (pid : PID) : List (PID × ProcessState) → Option ProcessState
  | [] => none
  | entry :: rest =>
      if entry.1 = pid then some entry.2 else findProcess pid rest

private def switchTo (env : Environment) (pid : PID) : Environment :=
  { currentPid := pid
    pidCounter := env.pidCounter
    currentProcess := (findProcess pid env.processes).getD {}
    processes := (env.currentPid, env.currentProcess) :: removeProcess pid env.processes
    schedule := env.schedule }

/-- Switch to a saved process without retaining the process that just finished. -/
private def finishAndSwitchTo (env : Environment) (pid : PID) : Environment :=
  { currentPid := pid
    pidCounter := env.pidCounter
    currentProcess := (findProcess pid env.processes).getD {}
    processes := removeProcess pid env.processes
    schedule := env.schedule }

/-- Restore a process whose terminal state was kept outside the process table. -/
private def finishAndRestore (env : Environment) (pid : PID)
    (process : ProcessState) : Environment :=
  { currentPid := pid
    pidCounter := env.pidCounter
    currentProcess := process
    processes := removeProcess pid env.processes
    schedule := env.schedule }

private def addProcess (env : Environment) (pid : PID) (process : ProcessState) : Environment :=
  { currentPid := env.currentPid
    pidCounter := env.pidCounter
    currentProcess := env.currentProcess
    processes := (pid, process) :: removeProcess pid env.processes
    schedule := env.schedule }

private def allocate (env : Environment) : PID × Environment :=
  let pid := env.pidCounter + 1
  (pid, { currentPid := env.currentPid
          pidCounter := pid
          currentProcess := env.currentProcess
          processes := env.processes
          schedule := env.schedule })

private def takeChoice (env : Environment) : ScheduleChoice × Environment :=
  match env.schedule with
  | [] => (.current, env)
  | choice :: rest =>
      (choice, { currentPid := env.currentPid
                 pidCounter := env.pidCounter
                 currentProcess := env.currentProcess
                 processes := env.processes
                 schedule := rest })

/-- Run the current process inside an existing runtime environment. -/
def run (computation : Result α) (env : Environment) : Outcome α :=
  match computation with
  | .ok value => .ok value env
  | .error exception => .error exception env
  | .get next => run (next env) env
  | .set next continuation => run continuation next
  | .spawn child next =>
      let (childPid, allocated) := allocate env
      let allocated := addProcess allocated childPid {}
      let (choice, scheduled) := takeChoice allocated
      match choice with
      | .spawned =>
          let childOutcome := run child (switchTo scheduled childPid)
          let childFinal := match childOutcome with
            | .ok _ final | .error _ final => final
          run (next childPid) (finishAndSwitchTo childFinal env.currentPid)
      | .current =>
          let parentOutcome := run (next childPid) scheduled
          let parentFinal := match parentOutcome with
            | .ok _ final | .error _ final => final
          let parentState := parentFinal.currentProcess
          let childOutcome := run child (finishAndSwitchTo parentFinal childPid)
          let childFinal := match childOutcome with
            | .ok _ final | .error _ final => final
          let restored := finishAndRestore childFinal env.currentPid parentState
          match parentOutcome with
          | .ok value _ => .ok value restored
          | .error exception _ => .error exception restored

end Lynx.Term.Runner

public section

namespace Lynx

/-- Execute a computation in an existing environment. Use `Lynx.run` to start
from a fresh runtime. The implementation is hidden; the application lemmas
below describe its behavior. -/
def Result.run (computation : Result α) (env : Environment) : Outcome α :=
  Term.Runner.run computation env

instance : CoeFun (Result α) fun _ => Environment → Outcome α :=
  ⟨Result.run⟩

namespace Result

@[simp] theorem ok_apply (value : α) (env : Environment) :
    (Result.ok value : Result α) env = .ok value env := by
  change Term.Runner.run (.ok value) env = _
  rw [Term.Runner.run]

@[simp] theorem error_apply (exception : Exception) (env : Environment) :
    (Result.error exception : Result α) env = .error exception env := by
  change Term.Runner.run (.error exception) env = _
  rw [Term.Runner.run]

@[simp] theorem pure_apply (value : α) (env : Environment) :
    (pure value : Result α) env = .ok value env := by
  change Term.Runner.run (.ok value) env = _
  rw [Term.Runner.run]

@[simp] theorem throw_apply (exception : Exception) (env : Environment) :
    (throw exception : Result α) env = .error exception env := by
  change Term.Runner.run (.error exception) env = _
  rw [Term.Runner.run]

@[simp] theorem get_apply (env : Environment) :
    (getThe Environment : Result Environment) env = .ok env env := by
  change Term.Runner.run (.get .ok) env = _
  rw [Term.Runner.run, Term.Runner.run]

@[simp] theorem set_apply (next env : Environment) :
    (MonadStateOf.set next : Result PUnit) env = .ok .unit next := by
  change Term.Runner.run (.set next (.ok PUnit.unit)) env = _
  rw [Term.Runner.run, Term.Runner.run]

@[simp] theorem modify_apply (update : Environment → Environment) (env : Environment) :
    (modify update : Result PUnit) env = .ok .unit (update env) := by
  change Term.Runner.run (.get fun current => .set (update current) (.ok PUnit.unit)) env = _
  rw [Term.Runner.run, Term.Runner.run, Term.Runner.run]

@[simp] theorem get_continuation_apply (continuation : Environment → Result α)
    (env : Environment) :
    (Result.get continuation) env = continuation env env := by
  change Term.Runner.run (.get continuation) env = _
  rw [Term.Runner.run]
  rfl

@[simp] theorem set_continuation_apply (next : Environment) (continuation : Result α)
    (env : Environment) :
    (Result.set next continuation) env = continuation next := by
  change Term.Runner.run (.set next continuation) env = _
  rw [Term.Runner.run]
  rfl

/-- The former state-monad `bind_apply` rule remains valid when the left
computation is pure. It is deliberately conditional: across `spawn`, running
the left side to completion could schedule a child before the continuation. -/
@[simp] theorem IsPure.bind_apply (computation : Result α) (next : α → Result β)
    (env : Environment) (pure : IsPure computation) :
    (computation >>= next) env =
      match computation env with
      | .ok value updated => next value updated
      | .error exception updated => .error exception updated := by
  change Term.Runner.run (Result.bind computation next) env = _
  cases computation <;> simp_all [Result.bind, Term.Runner.run]
  rfl

@[simp] theorem state_get_bind_apply (next : Environment → Result α) (env : Environment) :
    ((MonadState.get : Result Environment) >>= next : Result α) env = next env env := by
  rfl

@[simp] theorem state_set_bind_apply (nextEnv : Environment) (next : PUnit → Result α)
    (env : Environment) :
    (MonadStateOf.set nextEnv >>= next : Result α) env = next .unit nextEnv := by
  rfl

@[simp] theorem state_modify_bind_apply (update : Environment → Environment)
    (next : PUnit → Result α) (env : Environment) :
    (modify update >>= next : Result α) env = next .unit (update env) := by
  rfl

@[simp] theorem state_get_bind_bind_apply (first : Environment → Result α)
    (next : α → Result β) (env : Environment) :
    (((MonadState.get : Result Environment) >>= first) >>= next : Result β) env =
      (first env >>= next) env := by
  rfl

@[simp] theorem state_set_bind_bind_apply (nextEnv : Environment)
    (first : PUnit → Result α) (next : α → Result β) (env : Environment) :
    ((MonadStateOf.set nextEnv >>= first) >>= next : Result β) env =
      (first .unit >>= next) nextEnv := by
  rfl

@[simp] theorem state_modify_bind_bind_apply (update : Environment → Environment)
    (first : PUnit → Result α) (next : α → Result β) (env : Environment) :
    ((modify update >>= first) >>= next : Result β) env =
      (first .unit >>= next) (update env) := by
  rfl

@[simp] theorem IsPure.ok_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (value : α) :
    computation env = .ok value final ↔ computation = .ok value ∧ env = final := by
  cases computation <;> simp_all

@[simp] theorem IsPure.error_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (exception : Exception) :
    computation env = .error exception final ↔
      computation = .error exception ∧ env = final := by
  cases computation <;> simp_all

@[simp] theorem IsPure.bind_ok_iff (computation : Result α) (next : α → Result β)
    (computationPure : IsPure computation) (nextPure : ∀ value, IsPure (next value))
    (env final : Environment) (value : β) :
    (computation >>= next) env = .ok value final ↔
      (computation >>= next) = .ok value ∧ env = final :=
  IsPure.ok_iff _ (IsPure.bind computation next computationPure nextPure) env final value

@[simp] theorem IsPure.bind_error_iff (computation : Result α) (next : α → Result β)
    (computationPure : IsPure computation) (nextPure : ∀ value, IsPure (next value))
    (env final : Environment) (exception : Exception) :
    (computation >>= next) env = .error exception final ↔
      (computation >>= next) = .error exception ∧ env = final :=
  IsPure.error_iff _ (IsPure.bind computation next computationPure nextPure) env final exception

end Result

end Lynx
