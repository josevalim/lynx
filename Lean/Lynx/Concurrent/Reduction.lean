module

public import Lynx.Concurrent
public import Lynx.Concurrent.Kernel

/-! Checking every run of a closed program. `check` follows every step of
every configuration, up to a depth, and `check_sound` shows that every run it
covers ends in an accepted outcome. -/

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

/-- Whether every run from a configuration ends in an accepted outcome,
following at most `depth` steps along each run (`check_sound`). -/
@[expose] def check (accept : Outcome α → Bool) (depth : Nat) (config : Config α) : Bool :=
  checkFrom accept depth config

/-- How a run that `check` rejects fails. -/
inductive Failure (α : Type) where
  /-- The run ends in an outcome that is not accepted. -/
  | rejected : Outcome α → Failure α
  /-- The run takes more steps than the depth allows. -/
  | unfinished : Failure α

/-- The first run that `checkFrom` rejects. It mirrors `checkFrom` step by
step; keep them in sync. -/
@[expose] def counterexampleFrom (accept : Outcome α → Bool) :
    Nat → Config α → Option (List Event × Failure α)
  | 0, _ => some ([], .unfinished)
  | depth + 1, config =>
      match config.successors with
      | [] => if accept config.outcome then none else some ([], .rejected config.outcome)
      | successors => successors.findSome? fun (event, next) =>
          (counterexampleFrom accept depth next).map fun (events, failure) => (event :: events, failure)

/-- The first run that `check` rejects, as the events of its steps and how it
fails. Evaluating it is a fast way to find why a check fails. -/
@[expose] def counterexample (accept : Outcome α → Bool) (depth : Nat) (config : Config α) :
    Option (List Event × Failure α) :=
  counterexampleFrom accept depth config

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

/-- Every run from a configuration that `check` accepts ends in an accepted outcome. -/
theorem check_sound {accept : Outcome α → Bool} {depth : Nat} {config last : Config α}
    {events : List Event} {outcome : Outcome α} (checked : check accept depth config = true)
    (run : Run config events last) (terminal : Terminal last outcome) : accept outcome = true :=
  checkFrom_sound checked run terminal

end Lynx.Concurrent
