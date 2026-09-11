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
