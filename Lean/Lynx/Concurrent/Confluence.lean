module

public import Lynx.Concurrent.Reduction
public import Lynx.Concurrent.Termination

/-! Programs without races reach the same terminal configuration under every
interleaving, so one run determines the outcome of every run.

`RaceFree` asks that any two steps of a reachable configuration meet again,
each after at most one more step. Since every run ends (`Config.terminates`),
any two runs that reach a terminal configuration reach the same one
(`RaceFree.outcome_eq`). -/

namespace Lynx.Concurrent

open Lynx

/-! ### Configurations without races -/

/-- Two configurations meet again, each after at most one step. -/
@[expose] public def Meet (first second : Config α) : Prop :=
  ∃ last, (first = last ∨ ∃ event, Step first event last) ∧ (second = last ∨ ∃ event, Step second event last)

/-- Any two steps of a configuration reachable from this one lead to the same
configuration, or to configurations that meet again. -/
@[expose] public def RaceFree (config : Config α) : Prop :=
  ∀ events reached, Run config events reached →
    ∀ event event' next next', Step reached event next → Step reached event' next' →
      next = next' ∨ Meet next next'

public theorem RaceFree.step {config next : Config α} {event : Event}
    (raceFree : RaceFree config) (step : Step config event next) : RaceFree next :=
  fun _ _ run => raceFree _ _ (.step step run)

/-- A configuration with a single next configuration has no races when that one has none. -/
public theorem RaceFree.of_unique {config next : Config α}
    (unique : ∀ event next', Step config event next' → next' = next) (raceFree : RaceFree next) :
    RaceFree config := by
  intro events reached run event event' first second step step'
  cases run with
  | refl => exact .inl ((unique _ _ step).trans (unique _ _ step').symm)
  | step first' rest =>
    obtain rfl := unique _ _ first'
    exact raceFree _ _ rest event event' first second step step'

/-- A configuration without steps. -/
private def Stuck (config : Config α) : Prop := ∀ event next, ¬ Step config event next

private theorem Terminal.stuck_of {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : Stuck config := by
  intro event next step
  simp [Step, terminal.successors_eq_nil] at step

/-- Every configuration reaches one without steps, as every run ends. -/
private theorem exists_stuck (config : Config α) : ∃ events last, Run config events last ∧ Stuck last := by
  induction config using Config.terminates.induction with
  | h config ih =>
    by_cases stuck : Stuck config
    · exact ⟨[], config, .refl, stuck⟩
    · simp only [Stuck, Classical.not_forall, Classical.not_not] at stuck
      obtain ⟨event, next, step⟩ := stuck
      obtain ⟨events, last, run, stuck⟩ := ih next ⟨event, step⟩
      exact ⟨_, last, .step step run, stuck⟩

private theorem run_of_meet {first last stuck : Config α} {events : List Event}
    (reaches : first = last ∨ ∃ event, Step first event last) (run : Run last events stuck) :
    ∃ events, Run first events stuck := by
  rcases reaches with rfl | ⟨event, step⟩
  · exact ⟨_, run⟩
  · exact ⟨_, .step step run⟩

/-- Without races, every run that gets stuck gets stuck in the same configuration. -/
private theorem unique_stuck (config : Config α) : RaceFree config → ∀ {events events' : List Event}
    {last last' : Config α}, Run config events last → Stuck last → Run config events' last' → Stuck last' →
      last' = last := by
  induction config using Config.terminates.induction with
  | h config ih =>
  intro raceFree events events' last last' run stuck run' stuck'
  cases run with
  | refl =>
    cases run' with
    | refl => rfl
    | step step _ => exact absurd step (stuck _ _)
  | step step rest =>
    cases run' with
    | refl => exact absurd step (stuck' _ _)
    | step step' rest' =>
      rcases raceFree [] _ .refl _ _ _ _ step step' with same | ⟨joined, reaches, reaches'⟩
      · subst same
        exact ih _ ⟨_, step⟩ (raceFree.step step) rest stuck rest' stuck'
      · obtain ⟨_, final, toFinal, stuckFinal⟩ := exists_stuck joined
        obtain ⟨_, fromFirst⟩ := run_of_meet reaches toFinal
        obtain ⟨_, fromSecond⟩ := run_of_meet reaches' toFinal
        have one := ih _ ⟨_, step⟩ (raceFree.step step) rest stuck fromFirst stuckFinal
        have two := ih _ ⟨_, step'⟩ (raceFree.step step') rest' stuck' fromSecond stuckFinal
        rw [← two, one]

/-- Without races, every run of a computation that reaches a terminal
configuration reaches the same one, so all have the same outcome. -/
public theorem RaceFree.outcome_eq {config : Config α} (raceFree : RaceFree config)
    {events events' : List Event} {last last' : Config α} {outcome outcome' : Outcome α}
    (run : Run config events last) (terminal : Terminal last outcome)
    (run' : Run config events' last') (terminal' : Terminal last' outcome') :
    outcome' = outcome := by
  obtain rfl := unique_stuck config raceFree run (Terminal.stuck_of terminal) run' (Terminal.stuck_of terminal')
  rw [← terminal.outcome_eq, ← terminal'.outcome_eq]

/-! ### Evaluating one run

`Config.advance` repeatedly takes the first step of a configuration. Its runs
are ordinary runs, so without races it evaluates the outcome of every run. -/

/-- Take the first step, at most `steps` times. -/
@[expose] public def Config.advance : Nat → Config α → Config α
  | 0, config => config
  | steps + 1, config =>
      match config.successors with
      | [] => config
      | (_, next) :: _ => advance steps next

@[simp] public theorem Config.advance_zero (config : Config α) : config.advance 0 = config := rfl

/-- Configurations without successors stay put, so advancing composes. -/
public theorem Config.advance_add (first second : Nat) (config : Config α) :
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

public theorem Config.advance_succ {config next : Config α} {event : Event}
    {rest : List (Event × Config α)} (steps : Nat)
    (first : config.successors = (event, next) :: rest) :
    config.advance (steps + 1) = next.advance steps := by
  simp [Config.advance, first]

public theorem Config.run_advance (steps : Nat) (config : Config α) :
    ∃ events, Run config events (config.advance steps) := by
  induction steps generalizing config with
  | zero => exact ⟨[], .refl⟩
  | succ steps ih =>
    simp only [Config.advance]
    split
    · exact ⟨[], .refl⟩
    · rename_i event next rest found
      obtain ⟨events, run⟩ := ih next
      exact ⟨event :: events, .step (by simp [Step, found]) run⟩

end Lynx.Concurrent
