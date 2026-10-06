module

public import Std
public import Lynx.Term.FiniteFloat
import all Lynx.Term.Bitstring

public section

namespace Lynx

/-- Process identifiers are monotonically allocated natural numbers. -/
abbrev PID := Nat

inductive Term where
  | integer : Int → Term
  | float : _root_.Lynx.Term.FiniteFloat → Term
  | atom : String → Term
  /-- Program function index, source arity, and captured values.
  Comparison uses the index followed by the captured values. -/
  | function (id arity : Nat) (captures : Array Term) : Term
  | pid : PID → Term
  | tuple : Array Term → Term
  | map : List (Term × Term) → Term
  | nil : Term
  | cons : Term → Term → Term
  /-- Packed bits, with `0` denoting whole bytes and `1`–`7` denoting
  the used high bits of the last byte. Empty storage ignores the count. -/
  | bitstring : ByteArray → Fin 8 → Term
deriving Repr

inductive Exception where
  | error : Term → Exception
  | throw : Term → Exception
  | exit : Term → Exception
deriving Repr

namespace Exception

@[expose] def classTerm : Exception → Term
  | .error _ => .atom "error"
  | .throw _ => .atom "throw"
  | .exit _ => .atom "exit"

@[expose] def reason : Exception → Term
  | .error value | .throw value | .exit value => value

/-- Raw Core exception tokens retain their class when re-raised. -/
@[expose] def withReason : Exception → Term → Exception
  | .error _, value => .error value
  | .throw _, value => .throw value
  | .exit _, value => .exit value

/-- Stack frames are not recorded by the runtime model. -/
@[expose] def stacktrace (_ : Exception) : Term := .nil

end Exception

structure ProcessState where
  pdict : List (Term × Term) := []
  mailbox : List Term := []
deriving Repr, Inhabited

inductive ScheduleChoice where
  | current
  /-- Prefer this runnable process; unavailable choices fall back to the current/first runnable process. -/
  | swap : PID → ScheduleChoice
  /-- Expire a positive-timeout receive belonging to this PID, if it has no
  matching message. Unavailable choices fall back to ordinary scheduling. -/
  | timeout : PID → ScheduleChoice
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
  /-- Scheduler decisions consumed after spawn, send, and successful receive.
  Empty defaults to the current process when runnable. `swap pid` prefers
  the named process; blocked or finished processes yield automatically.
  Positive receive durations are abstract: timeout choices express expiry
  order, without measuring or waiting for elapsed time. Blocking also consumes
  choices; when no process can run, a finite receive expires automatically. -/
  schedule : List ScheduleChoice := []
deriving Repr, Inhabited

namespace Environment

/-- Process dictionary belonging to the process running the current computation. -/
def pdict (env : Environment) : List (Term × Term) := env.currentProcess.pdict

/-- Replace the process dictionary belonging to the current process. -/
def setPdict (env : Environment) (pdict : List (Term × Term)) : Environment :=
  { currentPid := env.currentPid
    pidCounter := env.pidCounter
    currentProcess := { env.currentProcess with pdict }
    processes := env.processes
    schedule := env.schedule }

@[simp] theorem pdict_setPdict (env : Environment) (pdict : List (Term × Term)) :
    (env.setPdict pdict).pdict = pdict := by
  rfl

end Environment

inductive Outcome (α : Type) where
  | ok : α → Environment → Outcome α
  | error : Exception → Environment → Outcome α
  /-- No modeled process can proceed. This is not an Erlang exception. -/
  | deadlock : Environment → Outcome α
  /-- The dynamic-call depth budget was exhausted. -/
  | exhausted : Environment → Outcome α
deriving Repr

/-- Receive durations are validated before entering the process operation.
Positive durations share one mode: expiry order is chosen by the scheduler. -/
inductive ReceiveTimeout where
  | infinity
  | immediate
  | finite
deriving Repr, Inhabited

/-- A resumable process computation. Bind stores continuations so scheduling
does not require translated functions to use continuation-passing style. -/
inductive Result : (α : Type := Term) → Type 1 where
  | exhausted {α : Type} : Result α
  | ok {α : Type} : α → Result α
  | error {α : Type} : Exception → Result α
  /-- Request a call through the program table. Both returns and exceptions resume
  the caller so surrounding exception handlers also cover dispatched code. -/
  | apply {α : Type} : Term → Array Term → (Except Exception Term → Result α) → Result α
  | get {α : Type} : (Environment → Result α) → Result α
  | set {α : Type} : Environment → Result α → Result α
  /-- Request a zero-arity function spawn through the program table. Validation
  errors resume the caller; execution of the function belongs to the child. -/
  | spawn {α : Type} : Term → (Except Exception Term → Result α) → Result α
  /-- Internal scheduled child, produced after resolving a function value. -/
  | schedule {α : Type} : Result Term → (PID → Result α) → Result α
  /-- Local asynchronous send. The continuation receives control after delivery. -/
  | send {α : Type} : PID → Term → Result α → Result α
  /-- A receive with an already validated timeout. Select the oldest matching
  message and schedule before executing its body. `some` carries clause bindings;
  `none` resumes the timeout body. No match without expiry suspends the process. -/
  | receive {α β : Type} : ReceiveTimeout → (Environment → Term → Option β) → (Option β → Result α) → Result α

/-- Validate before scanning, including when a matching message is queued.
Positive durations are abstract scheduler events, not elapsed milliseconds. -/
@[expose] def ReceiveTimeout.ofTerm : Term → Result ReceiveTimeout
  | .atom "infinity" => .ok .infinity
  | .integer n =>
      if n < 0 || n > 4294967295 then .error (.error (.atom "timeout_value"))
      else if n == 0 then .ok .immediate else .ok .finite
  | _ => .error (.error (.atom "timeout_value"))

namespace Result

@[expose] protected def bind (computation : Result α) (next : α → Result β) : Result β :=
  match computation with
  | .exhausted => .exhausted
  | .ok value => next value
  | .error exception => .error exception
  | .apply function arguments continuation =>
      .apply function arguments fun result => Result.bind (continuation result) next
  | .get continuation => .get fun env => Result.bind (continuation env) next
  | .set env continuation => .set env (Result.bind continuation next)
  | .spawn child continuation =>
      .spawn child fun result => Result.bind (continuation result) next
  | Result.schedule child continuation => Result.schedule child fun pid => Result.bind (continuation pid) next
  | .send pid message continuation => .send pid message (Result.bind continuation next)
  | .receive timeout select continuation =>
      .receive timeout select fun reply => Result.bind (continuation reply) next

instance : Monad @Result where
  pure := .ok
  bind := Result.bind

/-- Validate once before receiving. Every consumed message and timeout is a
scheduler boundary before its continuation, including queued matches. -/
@[expose] def receiveWith (timeout : Term) (select : Environment → Term → Option β)
    (next : Option β → Result α) : Result α := do
  let duration ← ReceiveTimeout.ofTerm timeout
  .receive duration select next

/-- Normalize a successful monadic return without unfolding the `Monad` instance. -/
@[simp] theorem pure_eq_ok (value : α) : (pure value : Result α) = .ok value := rfl

instance : MonadStateOf Environment @Result where
  get := .get .ok
  set env := .set env (.ok .unit)
  modifyGet update := .get fun env =>
    let (value, next) := update env
    .set next (.ok value)

@[expose] protected def handle (computation : Result α) (handler : Exception → Result α) : Result α :=
  match computation with
  | .exhausted => .exhausted
  | .ok value => .ok value
  | .error exception => handler exception
  | .apply function arguments continuation =>
      .apply function arguments fun result => Result.handle (continuation result) handler
  | .get continuation => .get fun env => Result.handle (continuation env) handler
  | .set env continuation => .set env (Result.handle continuation handler)
  | .spawn child continuation =>
      .spawn child fun result => Result.handle (continuation result) handler
  | Result.schedule child continuation => Result.schedule child fun pid => Result.handle (continuation pid) handler
  | .send pid message continuation => .send pid message (Result.handle continuation handler)
  | .receive timeout select continuation =>
      .receive timeout select fun reply => Result.handle (continuation reply) handler

/-- Catch only the protected computation. Exceptions raised by either
continuation propagate to an enclosing handler. -/
@[expose] def tryWith (computation : Result α) (next : α → Result β)
    (handler : Exception → Result β) : Result β :=
  Result.bind
    (Result.handle (Result.bind computation (fun value => .ok (Except.ok value)))
      (fun exception => .ok (Except.error exception)))
    (fun reply => match reply with
      | .ok value => next value
      | .error exception => handler exception)

@[simp] theorem tryWith_ok (value : α) (next : α → Result β)
    (handler : Exception → Result β) :
    Result.tryWith (.ok value) next handler = next value := rfl

@[simp] theorem tryWith_error (exception : Exception) (next : α → Result β)
    (handler : Exception → Result β) :
    Result.tryWith (.error exception) next handler = handler exception := rfl

@[simp] theorem tryWith_exhausted (next : α → Result β) (handler : Exception → Result β) :
    Result.tryWith .exhausted next handler = .exhausted := rfl

instance : MonadExceptOf Exception @Result where
  throw := .error
  tryCatch := Result.handle

@[simp] theorem bind_ok (computation : Result α) :
    (computation >>= Result.ok) = computation := by
  change Result.bind computation .ok = computation
  induction computation with
  | exhausted | ok | error => rfl
  | apply function arguments continuation ih | spawn function continuation ih =>
      simp only [Result.bind]
      congr
      funext result
      exact ih result
  | get continuation ih =>
      simp only [Result.bind]
      congr
      funext env
      exact ih env
  | set env continuation ih => simp [Result.bind, ih]
  | schedule child continuation childIh continuationIh =>
      simp only [Result.bind]
      congr
      funext pid
      exact continuationIh pid
  | send pid message continuation ih => simp [Result.bind, ih]
  | receive timeout select continuation ih =>
      simp only [Result.bind]
      congr
      funext value
      exact ih value

private theorem bind_assoc_proof (computation : Result α)
    (next : α → Result β) (final : β → Result γ) :
    Result.bind (Result.bind computation next) final =
      Result.bind computation fun value => Result.bind (next value) final := by
  induction computation with
  | exhausted | ok | error => rfl
  | apply function arguments continuation ih | spawn function continuation ih =>
      simp only [Result.bind]
      congr
      funext result
      exact ih result next
  | get continuation ih =>
      simp only [Result.bind]
      congr
      funext env
      exact ih env next
  | set env continuation ih => simp [Result.bind, ih next]
  | schedule child continuation childIh continuationIh =>
      simp only [Result.bind]
      congr
      funext pid
      exact continuationIh pid next
  | send pid message continuation ih => simp [Result.bind, ih next]
  | receive timeout select continuation ih =>
      simp only [Result.bind]
      congr
      funext value
      exact ih value next

instance : LawfulMonad @Result := LawfulMonad.mk' _
  (id_map := fun computation => bind_ok computation)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc_proof)

/-- A pure computation is already terminal and therefore independent of runtime state. -/
@[expose] def IsPure : Result α → Prop
  | .ok _ | .error _ => True
  | _ => False

@[simp] theorem isPure_ok (value : α) : IsPure (.ok value) := trivial
@[simp] theorem isPure_error (exception : Exception) : IsPure (.error exception : Result α) := trivial
@[simp] theorem not_isPure_apply (function : Term) (arguments : Array Term)
    (next : Except Exception Term → Result α) :
    ¬ IsPure (.apply function arguments next) := by simp [IsPure]

@[simp] theorem not_isPure_get (next : Environment → Result α) :
    ¬ IsPure (.get next) := by simp [IsPure]
@[simp] theorem not_isPure_set (env : Environment) (next : Result α) :
    ¬ IsPure (.set env next) := by simp [IsPure]
@[simp] theorem not_isPure_spawn (child : Term) (next : Except Exception Term → Result α) :
    ¬ IsPure (.spawn child next) := by simp [IsPure]

@[simp] theorem not_isPure_schedule (child : Result Term) (next : PID → Result α) :
    ¬ IsPure (Result.schedule child next) := by simp [IsPure]

@[simp] theorem not_isPure_send (pid : PID) (message : Term) (next : Result α) :
    ¬ IsPure (.send pid message next) := by simp [IsPure]
@[simp] theorem not_isPure_receive (timeout : ReceiveTimeout) (select : Environment → Term → Option β)
    (next : Option β → Result α) :
    ¬ IsPure (.receive timeout select next) := by simp [IsPure]

end Result

-- Foundational definitions cannot import the purity generator, which depends
-- on this module; provide the same kernel-checked simp lemma directly.
@[simp↓] theorem ReceiveTimeout.ofTerm_pure (timeout : Term) :
    Result.IsPure (ReceiveTimeout.ofTerm timeout) := by
  cases timeout <;> simp [ReceiveTimeout.ofTerm] <;>
    split <;> simp_all <;> split <;> simp_all

namespace Result

@[simp↓] theorem IsPure.handle (computation : Result α) (handler : Exception → Result α)
    (computationPure : IsPure computation) (handlerPure : ∀ exception, IsPure (handler exception)) :
    IsPure (Result.handle computation handler) := by
  cases computation <;> simp_all [IsPure, Result.handle]

@[simp↓] theorem IsPure.bind (computation : Result α) (next : α → Result β)
    (computationPure : IsPure computation) (nextPure : ∀ value, IsPure (next value)) :
    IsPure (computation >>= next) := by
  change IsPure (Result.bind computation next)
  cases computation <;> simp_all [IsPure, Result.bind]

/-- The explicit bind spelling emitted by the translator has a separate simp index. -/
@[simp↓] theorem IsPure.bind_explicit (computation : Result α) (next : α → Result β)
    (computationPure : IsPure computation) (nextPure : ∀ value, IsPure (next value)) :
    IsPure (Result.bind computation next) :=
  IsPure.bind computation next computationPure nextPure

@[simp↓] theorem IsPure.tryWith (computation : Result α) (next : α → Result β)
    (handler : Exception → Result β) (protectedPure : IsPure computation)
    (nextPure : ∀ value, IsPure (next value))
    (handlerPure : ∀ exception, IsPure (handler exception)) :
    IsPure (Result.tryWith computation next handler) := by
  cases computation <;> simp_all [IsPure, Result.tryWith, Result.bind, Result.handle]

/-- A guard may read its process environment, but cannot modify it, schedule,
or make unresolved calls. Every environment read must eventually terminate. -/
@[expose] def IsReadOnly : Result α → Prop
  | .ok _ | .error _ => True
  | .get next => ∀ env, IsReadOnly (next env)
  | _ => False

@[simp↓] theorem IsPure.readOnly (computation : Result α) (pure : IsPure computation) :
    IsReadOnly computation := by
  cases computation <;> simp_all [IsPure, IsReadOnly]

@[simp] theorem isReadOnly_get (next : Environment → Result α) :
    IsReadOnly (.get next) ↔ ∀ env, IsReadOnly (next env) := Iff.rfl

@[simp↓] theorem IsReadOnly.bind (computation : Result α) (next : α → Result β)
    (readOnly : IsReadOnly computation) (nextReadOnly : ∀ value, IsReadOnly (next value)) :
    IsReadOnly (Result.bind computation next) := by
  induction computation with
  | get continuation ih =>
      exact fun env => ih env next (readOnly env) nextReadOnly
  | ok value => exact nextReadOnly value
  | error exception => trivial
  | _ =>
      exact False.elim readOnly

@[simp↓] theorem IsReadOnly.bind_monadic (computation : Result α) (next : α → Result β)
    (readOnly : IsReadOnly computation) (nextReadOnly : ∀ value, IsReadOnly (next value)) :
    IsReadOnly (computation >>= next) := IsReadOnly.bind computation next readOnly nextReadOnly

@[simp↓] theorem IsReadOnly.handle (computation : Result α) (handler : Exception → Result α)
    (readOnly : IsReadOnly computation) (handlerReadOnly : ∀ exception, IsReadOnly (handler exception)) :
    IsReadOnly (Result.handle computation handler) := by
  induction computation with
  | get continuation ih => exact fun env => ih env handler (readOnly env) handlerReadOnly
  | ok value => trivial
  | error exception => exact handlerReadOnly exception
  | _ =>
      exact False.elim readOnly

@[simp↓] theorem IsReadOnly.tryWith (computation : Result α) (next : α → Result β)
    (handler : Exception → Result β) (readOnly : IsReadOnly computation)
    (nextReadOnly : ∀ value, IsReadOnly (next value))
    (handlerReadOnly : ∀ exception, IsReadOnly (handler exception)) :
    IsReadOnly (Result.tryWith computation next handler) := by
  unfold Result.tryWith
  apply IsReadOnly.bind
  · apply IsReadOnly.handle
    · apply IsReadOnly.bind computation _ readOnly
      intro value
      trivial
    · intro exception
      trivial
  · intro reply
    cases reply with
    | ok value => exact nextReadOnly value
    | error exception => exact handlerReadOnly exception

/-- Evaluate a proven read-only computation without invoking the scheduler. -/
@[expose] def toExceptRead (computation : Result α) (env : Environment)
    (readOnly : IsReadOnly computation) : Except Exception α :=
  match computation with
  | .ok value => .ok value
  | .error exception => .error exception
  | .get next => toExceptRead (next env) env (readOnly env)
  | .exhausted | .apply .. | .set .. | .spawn .. | .schedule .. | .send .. | .receive .. =>
      False.elim readOnly

@[simp] theorem not_isPure_exhausted : ¬ IsPure (.exhausted : Result α) := by simp [IsPure]

@[simp] theorem ok_bind (value : α) (next : α → Result β) :
    (Result.ok value >>= next) = next value := by rfl
@[simp] theorem error_bind (exception : Exception) (next : α → Result β) :
    (Result.error exception >>= next) = .error exception := by rfl

@[simp] theorem exhausted_bind (next : α → Result β) :
    (Result.exhausted >>= next) = .exhausted := rfl

@[simp] theorem apply_bind (function : Term) (arguments : Array Term)
    (continuation : Except Exception Term → Result α) (next : α → Result β) :
    (Result.apply function arguments continuation >>= next) =
      .apply function arguments (fun result => continuation result >>= next) := rfl

@[simp] theorem get_bind (continuation : Environment → Result α) (next : α → Result β) :
    (Result.get continuation >>= next) =
      .get (fun env => continuation env >>= next) := by rfl
@[simp] theorem set_bind (env : Environment) (continuation : Result α)
    (next : α → Result β) :
    (Result.set env continuation >>= next) = .set env (continuation >>= next) := by rfl
@[simp] theorem spawn_bind (child : Term) (continuation : Except Exception Term → Result α)
    (next : α → Result β) :
    (Result.spawn child continuation >>= next) =
      .spawn child (fun result => continuation result >>= next) := rfl

@[simp] theorem schedule_bind (child : Result Term) (continuation : PID → Result α)
    (next : α → Result β) :
    (Result.schedule child continuation >>= next) =
      Result.schedule child (fun pid => continuation pid >>= next) := by rfl

@[simp] theorem send_bind (pid : PID) (message : Term) (continuation : Result α)
    (next : α → Result β) :
    (Result.send pid message continuation >>= next) =
      .send pid message (continuation >>= next) := rfl

@[simp] theorem receive_bind (timeout : ReceiveTimeout) (select : Environment → Term → Option γ)
    (continuation : Option γ → Result α) (next : α → Result β) :
    (Result.receive timeout select continuation >>= next) =
      .receive timeout select (fun reply => continuation reply >>= next) := rfl

@[simp] theorem throw_eq (exception : Exception) :
    (throw exception : Result α) = .error exception := rfl

end Result

end Lynx

namespace Lynx.Term

/-- Executable implementation of a function term. Arguments use a Lean array,
avoiding Erlang-list encoding at internal call sites. -/
public abbrev Fun := Array Term → Result

/-- Completed pure calls cannot contain runtime requests. -/
public abbrev PureFun := Array Term → Except Exception Term

/-- Purity is enforced by the callable's return type, rather than a boolean. -/
public inductive FunEntry where
  | pure : (Array Term → PureFun) → FunEntry
  | effectful : (Array Term → Fun) → FunEntry

/-- Program-local function implementations indexed by `Term.function` IDs.
Each entry receives the captured values before the invocation arguments. -/
public abbrev FunTable := Array FunEntry

end Lynx.Term

namespace Lynx.Result

/-- Embed a completed call in a resumable computation. -/
@[expose] public def ofExcept (reply : Except Exception α) : Result α :=
  match reply with
  | .ok value => .ok value
  | .error exception => .error exception

/-- Extract a completed call using a kernel-checked purity proof. -/
@[expose] public def toExcept (computation : Result α) (pure : IsPure computation) : Except Exception α :=
  match computation with
  | .ok value => .ok value
  | .error exception => .error exception
  | .exhausted | .apply .. | .get .. | .set .. | .spawn .. | .schedule ..
    | .send .. | .receive .. => False.elim pure

/-- Read-only evaluation agrees with pure extraction when there are no reads. -/
@[simp] public theorem toExceptRead_pure (computation : Result α) (env : Environment)
    (readOnly : IsReadOnly computation) (pure : IsPure computation) :
    toExceptRead computation env readOnly = toExcept computation pure := by
  cases computation <;> first | rfl | exact False.elim pure

/-- Embedding a completed pure call preserves its result, including exceptions. -/
@[simp] public theorem ofExcept_toExcept (computation : Result α) (pure : IsPure computation) :
    ofExcept (toExcept computation pure) = computation := by
  cases computation <;> first | rfl | exact False.elim pure

end Lynx.Result
