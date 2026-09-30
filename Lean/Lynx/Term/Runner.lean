module

public import Lynx.Term.Apply

/-! Finite local-process execution. Sends insert directly into the destination
mailbox; message transit, remote processes, timers, links, and monitors are not
modeled. Scheduling occurs after spawn/send/successful receive, and another
runnable process takes over when the current one blocks or terminates.
Only continuations created by this run can execute: saved Environment entries
are state snapshots, not independent external actors. Deadlock is relative to
that closed execution.
-/

namespace Lynx.Term.Runner

open Lynx

private def removeProcess (processId : PID) : List (PID × ProcessState) → List (PID × ProcessState)
  | [] => []
  | entry :: rest =>
      if entry.1 = processId then removeProcess processId rest else entry :: removeProcess processId rest

private def findProcess (processId : PID) : List (PID × ProcessState) → Option ProcessState
  | [] => none
  | entry :: rest =>
      if entry.1 = processId then some entry.2 else findProcess processId rest

/-- Select the oldest matching message, preserving all unmatched messages. -/
private def selectMessage (select : Term → Option β) : List Term → Option (β × List Term)
  | [] => none
  | message :: rest =>
      match select message with
      | some value => some (value, rest)
      | none => (selectMessage select rest).map fun (value, remaining) =>
          (value, message :: remaining)

private def save (env : Environment) : Environment :=
  { env with processes :=
      (env.currentPid, env.currentProcess) :: removeProcess env.currentPid env.processes }

private def deliver (env : Environment) (processId : PID) (message : Term) : Environment :=
  if processId = env.currentPid then
    { env with currentProcess.mailbox := env.currentProcess.mailbox ++ [message] }
  else
    { env with processes := env.processes.map fun (savedPid, process) =>
        (savedPid, if savedPid = processId then
          { process with mailbox := process.mailbox ++ [message] } else process) }

/-- Preserve the process tree so advancing either branch has a structural
termination argument. Completion callbacks distinguish the root from children. -/
private inductive Pool (α : Type) where
  | empty
  | process {β : Type} : PID → Result β → (Except Exception β → Option (Except Exception α)) → Pool α
  | parallel : Pool α → Pool α → Pool α

/-- Each step replaces a computation by its continuations, possibly in either
parallel branch. This relation ignores scheduler and mailbox contents. -/
private inductive Progress : Pool α → Pool α → Prop where
  | exhausted : Progress .empty (.process processId .exhausted finish)
  | apply : Progress (.process processId (next (.error (.error (.tuple #[.atom "badfun", callee])))) finish)
      (.process processId (.apply callee arguments next) finish)
  | spawn : Progress (.process processId (next (.error (.error (.atom "badarg")))) finish)
      (.process processId (.spawn child next) finish)
  | ok : Progress .empty (.process processId (.ok value) finish)
  | error : Progress .empty (.process processId (.error exception) finish)
  | get : Progress (.process processId (next env) finish) (.process processId (.get next) finish)
  | set : Progress (.process processId next finish) (.process processId (.set env next) finish)
  | send : Progress (.process processId next finish) (.process processId (.send dest message next) finish)
  | receive : Progress (.process processId (next value) finish) (.process processId (.receive select next) finish)
  | schedule : Progress (.parallel (.process processId (next childPid) finish)
      (.process childPid child (fun _ => none))) (.process processId (Result.schedule child next) finish)
  | left : Progress a' a → Progress (.parallel a' b) (.parallel a b)
  | right : Progress b' b → Progress (.parallel a b') (.parallel a b)

private theorem accEmpty : Acc (@Progress α) .empty := by
  constructor
  intro p h
  cases h

private theorem accParallel (a b : Pool α) (ha : Acc Progress a) (hb : Acc Progress b) :
    Acc Progress (.parallel a b) := by
  induction ha generalizing b with
  | intro a ha iha =>
    induction hb with
    | intro b hb ihb =>
      constructor
      intro p h
      cases h with
      | left h => exact iha _ h _ (Acc.intro b hb)
      | right h => exact ihb _ h

private theorem accProcess {β : Type} (computation : Result β) :
    ∀ (processId : PID) (finish : Except Exception β → Option (Except Exception α)),
      Acc Progress (.process processId computation finish) := by
  induction computation with
  | exhausted =>
    intro processId finish
    constructor
    intro p h
    cases h
    exact accEmpty
  | apply callee arguments next ih | spawn child next ih =>
    intro processId finish
    constructor
    intro p h
    cases h
    apply ih
  | ok value =>
    intro processId finish
    constructor
    intro p h
    cases h
    exact accEmpty
  | error exception =>
    intro processId finish
    constructor
    intro p h
    cases h
    exact accEmpty
  | get next ih =>
    intro processId finish
    constructor
    intro p h
    cases h with
    | get => apply ih
  | set env next ih =>
    intro processId finish
    constructor
    intro p h
    cases h
    apply ih
  | send dest message next ih =>
    intro processId finish
    constructor
    intro p h
    cases h
    apply ih
  | receive select next ih =>
    intro processId finish
    constructor
    intro p h
    cases h with
    | receive => apply ih
  | schedule child next childIH nextIH =>
    intro processId finish
    constructor
    intro p h
    cases h with
    | schedule => exact accParallel _ _ (nextIH _ _ _) (childIH _ _)

private theorem wf : WellFounded (@Progress α) := by
  constructor
  intro p
  induction p with
  | empty => exact accEmpty
  | process processId c finish => exact accProcess c processId finish
  | parallel a b ha hb => exact accParallel a b ha hb

private abbrev Finished (α : Type) := Option (Except Exception α × ProcessState)

private def restore (root : PID) (finished : Finished α) (env : Environment) : Environment :=
  { env with currentPid := root
             currentProcess := match finished with
               | some (_, process) => process
               | none => (findProcess root env.processes).getD {}
             processes := removeProcess root env.processes }

private def findReady (env : Environment) (accept : PID → Bool) : Pool α → Option PID
  | .empty => none
  | .parallel left right => (findReady env accept left).orElse fun _ => findReady env accept right
  | .process processId computation _ =>
      if !accept processId then none else
        match computation with
        | .receive select _ =>
            if (selectMessage select ((findProcess processId env.processes).getD {}).mailbox).isSome
            then some processId else none
        | _ => some processId

/-- Consume one choice at spawn/send/successful receive. A missing or waiting
PID falls back to a runnable process when execution next selects a branch. -/
private def schedule (env : Environment) : Environment × PID :=
  let (choice, rest) := match env.schedule with
    | [] => (ScheduleChoice.current, [])
    | choice :: rest => (choice, rest)
  let preferred := match choice with
    | .current => env.currentPid
    | .swap processId => processId
  ({ env with schedule := rest }, preferred)

private structure Transition (before : Pool α) where
  next : Pool α
  decreases : Progress next before
  environment : Environment
  finished : Finished α := none
  boundary : Bool := false
  exhausted : Bool := false

/-- Execute one structural step of the selected process. A blocked receive
returns no step; unmatched messages and the continuation remain intact. -/
private def step (pool : Pool α) (env : Environment) (chosen : PID) : Option (Transition pool) :=
  match pool with
  | .empty => none
  | .parallel left right =>
      match step left env chosen with
      | some transition => some {
          transition with next := .parallel transition.next right
                          decreases := .left transition.decreases }
      | none => (step right env chosen).map fun transition => {
          transition with next := .parallel left transition.next
                          decreases := .right transition.decreases }
  | .process processId computation finish =>
      if processId != chosen then none else
      let active := { env with
        currentPid := processId
        currentProcess := (findProcess processId env.processes).getD {}
        processes := removeProcess processId env.processes }
      match computation with
      | .exhausted => some {
          next := .empty, decreases := .exhausted, environment := active, exhausted := true }
      | .apply callee _ next => some {
          next := .process processId
            (next (.error (.error (.tuple #[.atom "badfun", callee])))) finish
          decreases := .apply, environment := save active }
      | .spawn _ next => some {
          next := .process processId (next (.error (.error (.atom "badarg")))) finish
          decreases := .spawn, environment := save active }
      | .ok value => some {
          next := .empty, decreases := .ok, environment := active
          finished := (finish (.ok value)).map (·, active.currentProcess) }
      | .error exception => some {
          next := .empty, decreases := .error, environment := active
          finished := (finish (.error exception)).map (·, active.currentProcess) }
      | .get next => some {
          next := .process processId (next active) finish
          decreases := .get, environment := save active }
      | .set updated next => some {
          next := .process processId next finish
          decreases := .set, environment := save updated }
      | Result.schedule child next =>
          let childPid := active.pidCounter + 1
          let active := { active with
            pidCounter := childPid
            processes := (childPid, {}) :: active.processes }
          some {
            next := .parallel (.process processId (next childPid) finish)
              (.process childPid child (fun _ => none))
            decreases := .schedule, environment := save active
            boundary := true }
      | .send destination message next => some {
          next := .process processId next finish
          decreases := .send, environment := save (deliver active destination message)
          boundary := true }
      | .receive select next =>
          (selectMessage select active.currentProcess.mailbox).map fun (value, remaining) => {
            next := .process processId (next value) finish
            decreases := .receive
            environment := save { active with currentProcess.mailbox := remaining }
            boundary := true }

private def isEmpty : Pool α → Bool
  | .empty => true
  | .parallel left right => isEmpty left && isEmpty right
  | .process .. => false

private instance : WellFoundedRelation (Pool α) := ⟨Progress, wf⟩

private def execute (root : PID) (env : Environment) (pool : Pool α)
    (finished : Finished α) (preferred : PID) : Outcome α :=
  let chosen := ((findReady env (· == preferred) pool).orElse fun _ =>
    findReady env (· == env.currentPid) pool).orElse fun _ => findReady env (fun _ => true) pool
  match chosen.bind (step pool env) with
  | none =>
      let final := restore root finished env
      match isEmpty pool, finished with
      | true, some (.ok value, _) => .ok value final
      | true, some (.error exception, _) => .error exception final
      | _, _ => .deadlock final
  | some transition =>
      if transition.exhausted then .exhausted (restore root finished (save transition.environment)) else
      let finished := transition.finished.orElse fun _ => finished
      let (scheduled, preferred) := if transition.boundary then
          schedule transition.environment
        else (transition.environment, transition.environment.currentPid)
      execute root scheduled transition.next finished preferred
termination_by pool
decreasing_by exact transition.decreases

/-- Local computations execute structurally; concurrent execution decreases
through the process tree, without an execution budget. -/
def run (computation : Result α) (env : Environment) : Outcome α :=
  match computation with
  | .exhausted => .exhausted env
  | .apply callee _ next =>
      run (next (.error (.error (.tuple #[.atom "badfun", callee])))) env
  | .spawn _ next => run (next (.error (.error (.atom "badarg")))) env
  | .ok value => .ok value env
  | .error exception => .error exception env
  | .get next => run (next env) env
  | .set next continuation => run continuation next
  | Result.schedule _ _ | .send _ _ _ | .receive _ _ =>
      execute env.currentPid (save env) (.process env.currentPid computation some) none env.currentPid

end Lynx.Term.Runner

public section

namespace Lynx

/-- Execute a computation in an existing environment. Use `Lynx.run` to start
from a fresh runtime. The implementation is hidden; the application lemmas
below describe its behavior. Without a program table, dynamic calls report
`badfun`; use `runWith` for programs containing function values. -/
def Result.run (computation : Result α) (env : Environment) : Outcome α :=
  Term.Runner.run computation env

/-- Execute with the immutable program table and an explicit dynamic-call depth. -/
def Result.runWith (computation : Result α) (table : Term.FunTable)
    (callDepth : Nat) (env : Environment) : Outcome α :=
  Term.Runner.run (Result.resolve table callDepth computation) env

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

@[simp] theorem IsPure.ok_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (value : α) :
    computation env = .ok value final ↔ computation = .ok value ∧ env = final := by
  cases computation <;> simp_all

@[simp] theorem IsPure.error_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (exception : Exception) :
    computation env = .error exception final ↔
      computation = .error exception ∧ env = final := by
  cases computation <;> simp_all

end Result

end Lynx
