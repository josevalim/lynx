module

public import Lynx.Concurrent
public import Lynx.Concurrent.Kernel
public import Lynx.Concurrent.Commute
public import Lynx.Concurrent.Diamond
public import Lynx.Concurrent.Frames
import Lynx.Concurrent.Forced

/-! Checking every run of a closed program. `checkFrom` follows every step of
every configuration, up to a depth. `check` follows one run of those that
differ only in the order of steps that commute (`checkSleep`), and
`check_sound` shows that every run of a program it accepts ends in an accepted
outcome. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- Whether every run ends in an accepted outcome, following at most `depth`
steps along each run. -/
@[expose] def checkFrom (accept : Outcome α → Bool) : Nat → Config α → Bool
  | 0, _ => false
  | depth + 1, config =>
      match config.successors with
      | [] => accept config.outcome
      | successors => Kernel.all successors fun (_, next) => checkFrom accept depth next

/-- Whether every run of a program ends in an accepted outcome. Of the runs
that differ only in the order of steps that commute it follows one, taking at
most `depth` steps along it (`check_sound`). -/
@[expose] def check (accept : Outcome α → Bool) (depth : Nat) (config : Config α) : Bool :=
  checkSleep accept depth [] config

/-- How a run that `check` rejects fails. -/
inductive Failure (α : Type) where
  /-- The run ends in an outcome that is not accepted. -/
  | rejected : Outcome α → Failure α
  /-- The run takes more steps than the depth allows. -/
  | unfinished : Failure α

/-- The first run that `checkFrom` rejects. It mirrors `checkFrom` step by
step, following every run; keep them in sync. -/
@[expose] def counterexampleFrom (accept : Outcome α → Bool) :
    Nat → Config α → Option (List Event × Failure α)
  | 0, _ => some ([], .unfinished)
  | depth + 1, config =>
      match config.successors with
      | [] => if accept config.outcome then none else some ([], .rejected config.outcome)
      | successors => successors.findSome? fun (event, next) =>
          (counterexampleFrom accept depth next).map fun (events, failure) => (event :: events, failure)

/-- The first failure that a visit of the steps not asleep finds, as `explore`
follows them, with the event of the step that leads to it. -/
@[expose] def exploreFailure (visit : List Key → Config α → Option (List Event × Failure α))
    (stays : Key → Config α → Key → Bool) (sleep : List Key) :
    List Key → List (Key × Event × Config α) → Option (List Event × Failure α)
  | _, [] => none
  | done, (key, event, next) :: rest =>
      if Kernel.contains sleep key then exploreFailure visit stays sleep done rest
      else match visit (Kernel.filter (stays key next) (Kernel.append sleep done)) next with
        | some (events, failure) => some (event :: events, failure)
        | none => exploreFailure visit stays sleep (Kernel.append done [key]) rest

/-- The first run that `checkSleep` rejects. It mirrors `checkSleep` step by
step; keep them in sync. -/
@[expose] def counterexampleSleep (accept : Outcome α → Bool) :
    Nat → List Key → Config α → Option (List Event × Failure α)
  | 0, _, _ => some ([], .unfinished)
  | depth + 1, sleep, config =>
      -- A configuration a run reaches always names each process's steps by one key.
      if !config.distinctTasks then some ([], .unfinished) else
      match config.taggedSteps with
      | [] =>
          match config.successors with
          | [] => if accept config.outcome then none else some ([], .rejected config.outcome)
          | successors => successors.findSome? fun (event, next) =>
              (counterexampleSleep accept depth [] next).map fun (events, failure) => (event :: events, failure)
      | tagged =>
          match Kernel.find? (·.2.2.2) tagged with
          | some (_, event, next, _) =>
              (counterexampleSleep accept depth sleep next).map fun (events, failure) => (event :: events, failure)
          | none =>
              let steps := Kernel.map (fun (key, event, next, _) => (key, event, next)) tagged
              exploreFailure (counterexampleSleep accept depth) (config.staysAfter steps) sleep [] steps

/-- The first run that `check` rejects, as the events of its steps and how it
fails. Evaluating it is a fast way to find why a check fails. -/
@[expose] def counterexample (accept : Outcome α → Bool) (depth : Nat) (config : Config α) :
    Option (List Event × Failure α) :=
  counterexampleSleep accept depth [] config

theorem checkFrom_sound {accept : Outcome α → Bool} {depth : Nat} {config last : Config α}
    {events : List Event} {outcome : Outcome α} (checked : checkFrom accept depth config = true)
    (run : Run config events last) (terminal : Terminal last outcome) : accept outcome = true := by
  induction run generalizing depth with
  | refl =>
    cases depth with
    | zero => simp [checkFrom] at checked
    | succ depth =>
      simp only [checkFrom, terminal.successors_eq_nil] at checked
      rw [← terminal.outcome_eq]; exact checked
  | step step _ ih =>
    cases depth with
    | zero => simp [checkFrom] at checked
    | succ depth =>
      simp only [checkFrom] at checked
      split at checked
      · rename_i none; simp [Step, none] at step
      · simp only [Kernel.all_eq, List.all_eq_true] at checked
        exact ih (checked _ step) terminal

/-- The configuration a schedule reaches, taking for each index the successor
at that position. -/
@[expose] def Config.follow : List Nat → Config α → Option (Config α)
  | [], config => some config
  | index :: rest, config =>
      match config.successors[index]? with
      | some (_, next) => next.follow rest
      | none => none

/-- A schedule of a run that ends in an accepted outcome, searching every run
up to a depth. `Config.follow` checks what it finds (`reachable_of_witness`). -/
@[expose] def witness (accept : Outcome α → Bool) : Nat → Config α → Option (List Nat)
  | 0, _ => none
  | depth + 1, config =>
      match config.successors with
      | [] => if accept config.outcome then some [] else none
      | successors => witnessFrom (witness accept depth) 0 successors
where
  /-- The first successor, by position, from which `search` finds a schedule. -/
  witnessFrom (search : Config α → Option (List Nat)) :
      Nat → List (Event × Config α) → Option (List Nat)
    | _, [] => none
    | index, (_, next) :: rest =>
        match search next with
        | some schedule => some (index :: schedule)
        | none => witnessFrom search (index + 1) rest

/-- Following a schedule is a run. -/
theorem Config.run_of_follow {config last : Config α} :
    ∀ {schedule : List Nat}, config.follow schedule = some last → ∃ events, Run config events last
  | [], followed => by
    simp only [Config.follow, Option.some.injEq] at followed
    subst followed; exact ⟨[], .refl⟩
  | index :: rest, followed => by
    simp only [Config.follow] at followed
    split at followed
    · rename_i event next found
      obtain ⟨events, run⟩ := Config.run_of_follow followed
      exact ⟨event :: events, .step (List.mem_of_getElem? found) run⟩
    · cases followed

/-- Every run of a program that `check` accepts ends in an accepted outcome. -/
theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {env : Environment} {computation : Result α}
    {elapsed : PID → Nat → Nat} {last : Config α} {events : List Event} {outcome : Outcome α}
    (checked : check accept depth (.start env computation elapsed) = true)
    (run : Run (.start env computation elapsed) events last) (terminal : Terminal last outcome) :
    accept outcome = true :=
  checkSleep_sound checked run terminal

end Lynx.Concurrent
