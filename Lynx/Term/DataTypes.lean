module

public import Std

public section

namespace Lynx

/-- Process identifiers are monotonically allocated natural numbers. -/
abbrev PID := Nat

inductive Term where
  | integer : Int → Term
  | atom : String → Term
  | pid : PID → Term
  | tuple : Array Term → Term
  | map : List (Term × Term) → Term
  | nil : Term
  | cons : Term → Term → Term
deriving Repr

inductive Exception where
  | error : Term → Exception
  | throw : Term → Exception
  | exit : Term → Exception
deriving Repr

structure ProcessState where
  pdict : List (Term × Term) := []
deriving Repr, Inhabited

inductive ScheduleChoice where
  | spawned
  | current
deriving Repr

instance : Inhabited ScheduleChoice := ⟨.current⟩

structure Environment where
  /-- PID of the process running the current computation. -/
  currentPid : PID := 1
  /-- Greatest PID allocated so far. A spawn increments this before allocation. -/
  pidCounter : PID := 1
  /-- State of the process running the current computation. -/
  currentProcess : ProcessState := {}
  /-- Saved states of non-current processes, indexed by PID. -/
  processes : List (PID × ProcessState) := []
  /-- Scheduler decisions consumed at spawn points. Empty defaults to the caller. -/
  schedule : List ScheduleChoice := []
deriving Repr, Inhabited

namespace Environment

/-- Process dictionary belonging to the process running the current computation. -/
def pdict (env : Environment) : List (Term × Term) := env.currentProcess.pdict

/-- Replace the process dictionary belonging to the current process. -/
def setPdict (env : Environment) (pdict : List (Term × Term)) : Environment :=
  { currentPid := env.currentPid
    pidCounter := env.pidCounter
    currentProcess := { pdict }
    processes := env.processes
    schedule := env.schedule }

@[simp] theorem pdict_setPdict (env : Environment) (pdict : List (Term × Term)) :
    (env.setPdict pdict).pdict = pdict := by
  rfl

end Environment

inductive Outcome (α : Type) where
  | ok : α → Environment → Outcome α
  | error : Exception → Environment → Outcome α
deriving Repr

/-- A resumable process computation. Bind stores continuations so scheduling
does not require translated functions to use continuation-passing style. -/
inductive Result : (α : Type := Term) → Type 1 where
  | ok {α : Type} : α → Result α
  | error {α : Type} : Exception → Result α
  | get {α : Type} : (Environment → Result α) → Result α
  | set {α : Type} : Environment → Result α → Result α
  | spawn {α : Type} : Result Term → (PID → Result α) → Result α

namespace Result

@[expose] protected def bind (computation : Result α) (next : α → Result β) : Result β :=
  match computation with
  | .ok value => next value
  | .error exception => .error exception
  | .get continuation => .get fun env => Result.bind (continuation env) next
  | .set env continuation => .set env (Result.bind continuation next)
  | .spawn child continuation => .spawn child fun pid => Result.bind (continuation pid) next

instance : Monad @Result where
  pure := .ok
  bind := Result.bind

instance : MonadStateOf Environment @Result where
  get := .get .ok
  set env := .set env (.ok .unit)
  modifyGet update := .get fun env =>
    let (value, next) := update env
    .set next (.ok value)

protected def handle (computation : Result α) (handler : Exception → Result α) : Result α :=
  match computation with
  | .ok value => .ok value
  | .error exception => handler exception
  | .get continuation => .get fun env => Result.handle (continuation env) handler
  | .set env continuation => .set env (Result.handle continuation handler)
  | .spawn child continuation => .spawn child fun pid => Result.handle (continuation pid) handler

instance : MonadExceptOf Exception @Result where
  throw := .error
  tryCatch := Result.handle

private theorem bind_ok (computation : Result α) :
    Result.bind computation .ok = computation := by
  induction computation with
  | ok | error => rfl
  | get continuation ih =>
      simp only [Result.bind]
      congr
      funext env
      exact ih env
  | set env continuation ih => simp [Result.bind, ih]
  | spawn child continuation childIh continuationIh =>
      simp only [Result.bind]
      congr
      funext pid
      exact continuationIh pid

private theorem bind_assoc_proof (computation : Result α)
    (next : α → Result β) (final : β → Result γ) :
    Result.bind (Result.bind computation next) final =
      Result.bind computation fun value => Result.bind (next value) final := by
  induction computation with
  | ok | error => rfl
  | get continuation ih =>
      simp only [Result.bind]
      congr
      funext env
      exact ih env next
  | set env continuation ih => simp [Result.bind, ih next]
  | spawn child continuation childIh continuationIh =>
      simp only [Result.bind]
      congr
      funext pid
      exact continuationIh pid next

instance : LawfulMonad @Result := LawfulMonad.mk' _
  (id_map := fun computation => bind_ok computation)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc_proof)

/-- A pure computation is already terminal and therefore independent of runtime state. -/
def IsPure : Result α → Prop
  | .ok _ | .error _ => True
  | _ => False

@[simp] theorem isPure_ok (value : α) : IsPure (.ok value) := trivial
@[simp] theorem isPure_error (exception : Exception) : IsPure (.error exception : Result α) := trivial
@[simp] theorem not_isPure_get (next : Environment → Result α) :
    ¬ IsPure (.get next) := by simp [IsPure]
@[simp] theorem not_isPure_set (env : Environment) (next : Result α) :
    ¬ IsPure (.set env next) := by simp [IsPure]
@[simp] theorem not_isPure_spawn (child : Result Term) (next : PID → Result α) :
    ¬ IsPure (.spawn child next) := by simp [IsPure]

theorem IsPure.terminal (computation : Result α) (pure : IsPure computation) :
    (∃ value, computation = .ok value) ∨
      ∃ exception, computation = .error exception := by
  cases computation <;> simp_all [IsPure]

@[simp↓] theorem IsPure.bind (computation : Result α) (next : α → Result β)
    (computationPure : IsPure computation) (nextPure : ∀ value, IsPure (next value)) :
    IsPure (computation >>= next) := by
  change IsPure (Result.bind computation next)
  cases computation <;> simp_all [IsPure, Result.bind]

@[simp] theorem ok_inj (a b : α) : (Result.ok a : Result α) = .ok b ↔ a = b := by
  constructor
  · intro h; exact Result.ok.inj h
  · rintro rfl; rfl

@[simp] theorem ok_ne_error (value : α) (exception : Exception) :
    (Result.ok value : Result α) ≠ .error exception := by simp

@[simp] theorem error_ne_ok (exception : Exception) (value : α) :
    (Result.error exception : Result α) ≠ .ok value := by simp

@[simp] theorem error_inj (a b : Exception) :
    (Result.error a : Result α) = .error b ↔ a = b := by
  constructor
  · intro h; exact Result.error.inj h
  · rintro rfl; rfl

end Result

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

/-- Run a process computation to a terminal outcome. -/
def run (computation : Result α) (env : Environment := {}) : Outcome α :=
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
          run (next childPid) (switchTo childFinal env.currentPid)
      | .current =>
          let parentOutcome := run (next childPid) scheduled
          let parentFinal := match parentOutcome with
            | .ok _ final | .error _ final => final
          let childOutcome := run child (switchTo parentFinal childPid)
          let childFinal := match childOutcome with
            | .ok _ final | .error _ final => final
          let restored := switchTo childFinal env.currentPid
          match parentOutcome with
          | .ok value _ => .ok value restored
          | .error exception _ => .error exception restored

instance : CoeFun (Result α) fun _ => Environment → Outcome α :=
  ⟨fun computation env => run computation env⟩

namespace Result

@[simp] theorem ok_apply (value : α) (env : Environment) :
    (Result.ok value : Result α) env = .ok value env := by
  change run (.ok value) env = _
  rw [run]
@[simp] theorem error_apply (exception : Exception) (env : Environment) :
    (Result.error exception : Result α) env = .error exception env := by
  change run (.error exception) env = _
  rw [run]
@[simp] theorem pure_apply (value : α) (env : Environment) :
    (pure value : Result α) env = .ok value env := by
  change run (.ok value) env = _
  rw [run]
@[simp] theorem throw_apply (exception : Exception) (env : Environment) :
    (throw exception : Result α) env = .error exception env := by
  change run (.error exception) env = _
  rw [run]
@[simp] theorem get_apply (env : Environment) :
    (getThe Environment : Result Environment) env = .ok env env := by
  change run (.get .ok) env = _
  rw [run, run]
@[simp] theorem set_apply (next env : Environment) :
    (MonadStateOf.set next : Result PUnit) env = .ok .unit next := by
  change run (.set next (.ok PUnit.unit)) env = _
  rw [run, run]
@[simp] theorem modify_apply (update : Environment → Environment) (env : Environment) :
    (modify update : Result PUnit) env = .ok .unit (update env) := by
  change run (.get fun current => .set (update current) (.ok PUnit.unit)) env = _
  rw [run, run, run]

@[simp] theorem get_continuation_apply (continuation : Environment → Result α)
    (env : Environment) :
    (Result.get continuation) env = continuation env env := by
  change run (.get continuation) env = _
  rw [run]

@[simp] theorem set_continuation_apply (next : Environment) (continuation : Result α)
    (env : Environment) :
    (Result.set next continuation) env = continuation next := by
  change run (.set next continuation) env = _
  rw [run]

/-- The former state-monad `bind_apply` rule remains valid when the left
computation is pure. It is deliberately conditional: across `spawn`, running
the left side to completion could schedule a child before the continuation. -/
@[simp] theorem IsPure.bind_apply (computation : Result α) (next : α → Result β)
    (env : Environment) (pure : IsPure computation) :
    (computation >>= next) env =
      match computation env with
      | .ok value updated => next value updated
      | .error exception updated => .error exception updated := by
  change run (Result.bind computation next) env = _
  cases computation <;> simp_all [IsPure, Result.bind, run]

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
  cases computation <;> simp_all [IsPure, run]

@[simp] theorem IsPure.error_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (exception : Exception) :
    computation env = .error exception final ↔
      computation = .error exception ∧ env = final := by
  cases computation <;> simp_all [IsPure, run]

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

@[simp] theorem ok_bind (value : α) (next : α → Result β) :
    (Result.ok value >>= next) = next value := by rfl
@[simp] theorem error_bind (exception : Exception) (next : α → Result β) :
    (Result.error exception >>= next) = .error exception := by rfl

@[simp] theorem get_bind (continuation : Environment → Result α) (next : α → Result β) :
    (Result.get continuation >>= next) =
      .get (fun env => continuation env >>= next) := by rfl
@[simp] theorem set_bind (env : Environment) (continuation : Result α)
    (next : α → Result β) :
    (Result.set env continuation >>= next) = .set env (continuation >>= next) := by rfl
@[simp] theorem spawn_bind (child : Result Term) (continuation : PID → Result α)
    (next : α → Result β) :
    (Result.spawn child continuation >>= next) =
      .spawn child (fun pid => continuation pid >>= next) := by rfl

@[simp] theorem throw_eq (exception : Exception) :
    (throw exception : Result α) = .error exception := rfl

end Result

end Lynx
