module

public import Lynx.Concurrent.Frames
import all Lynx.Concurrent.Diamond
import all Lynx.Concurrent.Frames
import all Lynx.Concurrent.Sleep

/-! Forced steps: every run can take a forced step first, as every other step
commutes with it or absorbs it. With the sleep sets of `Lynx.Concurrent.Sleep`,
this proves that `checkSleep` covers every run (`checkSleep_sound`). -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-- Every other step absorbs a forced step, or commutes with it into a
configuration where a forced step closes the square. -/
private theorem Config.forced_square {elapsed : PID → Nat → Nat} {config : Config α} {key key' : Key}
    {event event' : Event} {next middle : Config α} (reachable : config.Reachable elapsed)
    (forced : (key, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf key' = some (event', middle)) (differ : key' ≠ key) :
    (∃ absorbed, next.stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf key' = some (other, last) := by
  sorry

/-- Every run reaching a terminal configuration can take a forced step first. -/
private theorem forced_first {elapsed : PID → Nat → Nat} {outcome : Outcome α} :
    ∀ {first last : Config α} {events : List Event}, Run first events last →
    ∀ {key : Key} {event : Event} {next : Config α}, first.Reachable elapsed →
      (key, event, next, true) ∈ first.taggedSteps → Terminal last outcome → Reaches next last := by
  intro first last events run
  induction run with
  | refl =>
    intro key event next reachable forced terminal
    have step := Config.step_of_stepOf (reachable.stepOf forced)
    simp [Step, terminal.successors_eq_nil] at step
  | step step rest ih =>
    rename_i first event' middle events last
    intro key event next reachable forced terminal
    obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running (elapsed := elapsed) forced
    obtain ⟨key', forced', mem'⟩ := Config.tagged_of_step step
    have step' := reachable.stepOf mem'
    by_cases same : key' = key
    · subst same
      rw [reachable.stepOf forced] at step'
      simp only [Option.some.injEq, Prod.mk.injEq] at step'
      obtain ⟨-, rfl⟩ := step'
      exact ⟨_, rest⟩
    · rcases Config.forced_square reachable forced step' same with ⟨absorbed, after⟩ |
        ⟨key'', event'', last', other, forcedNext, after⟩
      · exact ⟨_, .step (Config.step_of_stepOf after) rest⟩
      · exact Reaches.step (Config.step_of_stepOf after)
          (ih (reachable.step step) forcedNext terminal)

/-! ### Soundness -/

private theorem Config.mem_steps {config : Config α} {key : Key} {event : Event} {next : Config α} :
    (key, event, next) ∈ Kernel.map (fun step => (step.1, step.2.1, step.2.2.1)) config.taggedSteps ↔
      ∃ forced, (key, event, next, forced) ∈ config.taggedSteps := by
  simp only [Kernel.map_eq, List.mem_map, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨key', event', next', forced, mem, rfl, rfl, rfl⟩; exact ⟨forced, mem⟩
  · rintro ⟨forced, mem⟩; exact ⟨key, event, next, forced, mem, rfl, rfl, rfl⟩

/-- `checkSleep` covers every run from a configuration a run reaches whose
first step is not asleep. -/
private theorem checkSleep_reaches {elapsed : PID → Nat → Nat} {accept : Outcome α → Bool} :
    ∀ {depth : Nat} {sleep : List Key} {first last : Config α} {events : List Event} {outcome : Outcome α},
      first.Reachable elapsed → checkSleep accept depth sleep first = true → Run first events last →
      Terminal last outcome →
      (∀ key ∈ sleep, ∃ event next, first.stepOf key = some (event, next)) →
      (∀ key ∈ sleep, ∀ event next, first.stepOf key = some (event, next) → ¬Reaches next last) →
      accept outcome = true := by
  intro depth
  induction depth with
  | zero => intro _ _ _ _ _ _ checked; simp [checkSleep] at checked
  | succ depth ih =>
    intro sleep first last events outcome reachable checked run terminal awake asleep
    unfold checkSleep at checked
    simp only [Bool.and_eq_true] at checked
    obtain ⟨distinct, checked⟩ := checked
    split at checked
    · -- No tagged steps: follow every step.
      rename_i none
      cases run with
      | refl =>
        simp only [terminal.successors_eq_nil, terminal.outcome_eq] at checked
        exact checked
      | step step rest =>
        split at checked
        · rename_i empty; simp [Step, empty] at step
        · simp only [Kernel.all_eq, List.all_eq_true] at checked
          exact ih (reachable.step step) (checked _ step) rest terminal (by simp) (by simp)
    · rename_i tagged nonempty
      cases run with
      | refl =>
        exfalso
        obtain ⟨⟨key, event, next, forced⟩, mem⟩ := List.exists_mem_of_ne_nil _ nonempty
        have := Config.step_of_stepOf (reachable.stepOf mem)
        simp [Step, terminal.successors_eq_nil] at this
      | step step rest =>
      obtain ⟨state, tasks, finished, rfl⟩ : ∃ state tasks finished, first = .running state tasks finished false := by
        obtain ⟨⟨key, event, next, forced⟩, mem⟩ := List.exists_mem_of_ne_nil _ nonempty
        exact Config.Reachable.running (elapsed := elapsed) mem
      split at checked
      · -- A step every run can take first, keeping the same steps asleep.
        rename_i key event next forced found
        have mem := List.mem_of_find?_eq_some (by simpa [Kernel.find?_eq] using found)
        have isForced : forced = true := by simpa using List.find?_some (by simpa [Kernel.find?_eq] using found)
        subst isForced
        have reaches := forced_first (.step step rest) reachable mem terminal
        have found' := reachable.stepOf mem
        have notAsleep : key ∉ sleep := fun slept => asleep key slept event next found' reaches
        obtain ⟨events', run'⟩ := reaches
        -- A step asleep before the forced step reaches after it only what it reached before.
        have after : ∀ key' ∈ sleep, ∀ event₀ next₀,
            (Config.running state tasks finished false).stepOf key' = some (event₀, next₀) →
            ∃ event'' next'', next.stepOf key' = some (event'', next'') ∧
              (Reaches next'' last → Reaches next₀ last) := by
          intro key' slept event₀ next₀ step₀
          have differ : key' ≠ key := fun same => notAsleep (same ▸ slept)
          rcases Config.forced_square reachable mem step₀ differ with ⟨absorbed, after⟩ |
              ⟨key'', event'', last', other, forced', after⟩
          · exact ⟨_, _, after, id⟩
          · exact ⟨_, _, after, Reaches.step (Config.step_of_stepOf
              ((reachable.step (Config.step_of_stepOf step₀)).stepOf forced'))⟩
        refine ih (reachable.step (Config.step_of_stepOf found')) checked run' terminal
          (fun key' slept => ?_) (fun key' slept event'' next'' step'' reaches => ?_)
        · obtain ⟨event₀, next₀, step₀⟩ := awake key' slept
          obtain ⟨event'', next'', step'', -⟩ := after key' slept event₀ next₀ step₀
          exact ⟨event'', next'', step''⟩
        · obtain ⟨event₀, next₀, step₀⟩ := awake key' slept
          obtain ⟨event₁, next₁, step₁, back⟩ := after key' slept event₀ next₀ step₀
          rw [step₁] at step''
          simp only [Option.some.injEq, Prod.mk.injEq] at step''
          obtain ⟨-, rfl⟩ := step''
          exact asleep key' slept event₀ next₀ step₀ (back reaches)
      · -- Follow every step not asleep.
        have tagged' : ∀ key event next, (key, event, next) ∈
            Kernel.map (fun step => (step.1, step.2.1, step.2.2.1))
              (Config.running state tasks finished false).taggedSteps →
            (Config.running state tasks finished false).stepOf key = some (event, next) := by
          intro key event next mem
          obtain ⟨forced, mem⟩ := Config.mem_steps.mp mem
          exact reachable.stepOf mem
        obtain ⟨key, forced, mem⟩ := Config.tagged_of_step step
        refine explore_sound (goal := accept outcome = true)
          (fun key event next mem sleep' visited stays reaches asleep' => ?_)
          (fun key event next mem key' stays event' next' after reaches => ?_)
          (fun key event event' next next' mem mem' => ?_)
          (fun key slept event next mem => asleep key slept event next (tagged' _ _ _ mem))
          ⟨key, _, _, Config.mem_steps.mpr ⟨forced, mem⟩, _, rest⟩ checked
        · obtain ⟨events', run'⟩ := reaches
          have step := tagged' _ _ _ mem
          refine ih (reachable.step (Config.step_of_stepOf step)) visited run' terminal (fun key' slept => ?_) asleep'
          obtain ⟨-, -, -, event₃, last', after, -⟩ :=
            Config.stays reachable.1 distinct tagged' step (stays key' slept)
          exact ⟨event₃, last', after⟩
        · have step := tagged' _ _ _ mem
          obtain ⟨event₀, next₀, step₀, event₃, last', after', back⟩ :=
            Config.stays reachable.1 distinct tagged' step stays
          rw [after'] at after
          simp only [Option.some.injEq, Prod.mk.injEq] at after
          obtain ⟨-, rfl⟩ := after
          obtain ⟨forced₀, mem₀⟩ := Config.tagged_of_stepOf step₀
          refine ⟨event₀, next₀, Config.mem_steps.mpr ⟨forced₀, mem₀⟩, ?_⟩
          rcases back with same | ⟨event₄, back⟩
          · rw [← same]; exact reaches
          · exact Reaches.step (Config.step_of_stepOf back) reaches
        · have one := tagged' _ _ _ mem
          rw [tagged' _ _ _ mem'] at one
          simp only [Option.some.injEq, Prod.mk.injEq] at one
          exact one.2.symm

/-- Every run of a computation that `checkSleep` accepts ends in an accepted outcome. -/
theorem checkSleep_sound {accept : Outcome α → Bool} {depth : Nat} {env : Environment}
    {computation : Result α} {elapsed : PID → Nat → Nat} {last : Config α} {events : List Event}
    {outcome : Outcome α} (checked : checkSleep accept depth [] (.start env computation elapsed) = true)
    (run : Run (.start env computation elapsed) events last) (terminal : Terminal last outcome) :
    accept outcome = true :=
  checkSleep_reaches (elapsed := elapsed) (first := .start env computation elapsed)
    ⟨⟨rfl, trivial, trivial⟩, trivial⟩ checked run terminal (by simp) (by simp)

end Lynx.Concurrent
