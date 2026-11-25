module

public import Lynx.Concurrent.Reduction
public import Lynx.Concurrent.Termination
import all Lynx.Concurrent.Diamond
import all Lynx.Concurrent.Frames
import all Lynx.Concurrent.Sleep
import all Lynx.Concurrent.Forced

/-! Programs without races reach the same terminal configuration under every
interleaving, so one run determines the outcome of every run.

`RaceFree` asks that any two steps of a reachable configuration meet again,
each after at most one more step. Since every run ends (`Config.terminates`),
any two runs that reach a terminal configuration reach the same one
(`RaceFree.outcome_eq`). `RaceFree.of_talks` establishes it for processes
that only message each other, each receiver hearing from a single sender. -/

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

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

/-! ### Processes that only message each other -/

/-- Every message the process sends goes to a destination `talk` allows from
its PID, no receive has a timeout, and it neither replaces its environment,
spawns, nor makes requests to the scheduler. -/
public inductive _root_.Lynx.Result.Talks (talk : PID → PID → Prop) (self : PID) : {β : Type} → Result β → Prop where
  | ok : Result.Talks talk self (.ok value)
  | error : Result.Talks talk self (.error exception)
  | get (next : ∀ env : Environment, env.currentPid = self → Result.Talks talk self (continuation env)) :
      Result.Talks talk self (.get continuation)
  | send (allowed : talk self receiver) (next : Result.Talks talk self continuation) :
      Result.Talks talk self (.send receiver message continuation)
  | receive (next : ∀ reply, Result.Talks talk self (continuation reply)) :
      Result.Talks talk self (.receive .infinity select continuation)

/-- Each receiver hears from a single sender, which is not the clock. -/
@[expose] public def Single (talk : PID → PID → Prop) : Prop :=
  (∀ sender sender' receiver, talk sender receiver → talk sender' receiver → sender = sender') ∧
  ∀ sender receiver, talk sender receiver → sender ≠ clock

/-- A record of a live process without links, monitors or a parked monitor,
whose queue holds messages from processes. -/
@[expose] public def ProcessState.Quiet (process : ProcessState) : Prop :=
  process.exiting = none ∧ process.links = [] ∧ process.monitors = [] ∧ process.monitoring = [] ∧
    process.parked = none ∧ process.eagerExits = [] ∧
    ∀ entry ∈ process.queue, (∃ message, entry.signal = .message message) ∧ entry.source ≠ clock

/-- No timers nor persistent term update in progress, and every record is quiet. -/
@[expose] public def State.Quiet (state : State) : Prop :=
  (state.timers = [] ∧ state.persistent.staged = none) ∧
    ∀ processId process, state.record processId = some process → process.Quiet

/-- Normalizing keeps a quiet record. -/
public theorem ProcessState.Quiet.normalizeRecord {process : ProcessState} (quiet : process.Quiet) (state : State)
    (processId : PID) : state.normalizeRecord processId process = process := by
  obtain ⟨live, links, monitors, -, -, -, queue⟩ := quiet
  unfold State.normalizeRecord
  rw [live]
  dsimp only
  have kept : Kernel.filter (state.keepEntry processId process) process.queue = process.queue := by
    rw [Kernel.filter_eq]
    refine List.filter_eq_self.mpr fun entry mem => ?_
    obtain ⟨⟨message, signal⟩, -⟩ := queue entry mem
    obtain ⟨source, signal'⟩ := entry
    simp only at signal; subst signal
    simp [State.keepEntry, State.inertEntry, live]
  rw [kept, links, monitors]
  simp only [Kernel.filter_eq, List.filter_nil]
  cases process
  simp only at links live monitors ⊢
  subst links live monitors
  rfl

/-- Normalizing keeps a state whose records are quiet. -/
public theorem State.normalize_of_quiet {state : State} (quiet : ∀ entry ∈ state.processes, entry.2.Quiet) :
    state.normalize = state := by
  refine State.ext ?_ rfl rfl rfl
  simp only [State.normalize_eq, Kernel.map_eq, Kernel.filter_eq]
  have mapped : state.processes.map (fun record => (record.1,
      state.normalizeRecord record.1 record.2)) = state.processes := by
    conv => rhs; rw [← List.map_id state.processes]
    refine List.map_congr_left fun record mem => ?_
    rw [(quiet record mem).normalizeRecord]
    rfl
  rw [mapped]
  refine List.filter_eq_self.mpr fun record mem => ?_
  simp [ProcessState.finished, (quiet record mem).1]

/-- Every process only messages others as `talk` allows, in a quiet state. -/
private def Config.Talking (talk : PID → PID → Prop) : Config α → Prop
  | .start .. => False
  | .running _ _ _ true => True
  | .running state tasks _ false => state.Quiet ∧
      ∀ entry ∈ tasks, entry.2.wait = none ∧ entry.2.computation.Talks talk entry.1

/-- A record of a process that ended with nothing left to signal or answer. -/
private def ProcessState.Ended (process : ProcessState) : Prop :=
  ∃ reason, process.exiting = some ⟨reason, [], []⟩ ∧ process.queue = []

/-- No timers nor persistent term update in progress, and every record is
quiet or ended with nothing left, as after a step of quiet processes, before
normalizing. -/
private def State.Calm (state : State) : Prop :=
  (state.timers = [] ∧ state.persistent.staged = none) ∧
    ∀ processId process, state.record processId = some process → process.Quiet ∨ process.Ended

private theorem ProcessState.Quiet.normRecord {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (quiet : process.Quiet) : Lynx.Concurrent.normRecord gone processId process = process := by
  obtain ⟨live, links, monitors, -, -, -, queue⟩ := quiet
  rw [normRecord_live live, links, monitors]
  have kept : Kernel.filter (fun entry => !inert gone processId process entry) process.queue = process.queue := by
    rw [Kernel.filter_eq]
    refine List.filter_eq_self.mpr fun entry mem => ?_
    obtain ⟨⟨message, signal⟩, -⟩ := queue entry mem
    obtain ⟨source, signal'⟩ := entry
    simp only at signal; subst signal
    simp [inert]
  rw [kept]
  cases process
  simp only at links monitors ⊢
  subst links monitors
  rfl

private theorem State.Quiet.calm {state : State} (quiet : state.Quiet) : state.Calm :=
  ⟨quiet.1, fun processId process found => .inl (quiet.2 processId process found)⟩

/-- Normalizing removes the records of processes that ended, and keeps quiet ones. -/
private theorem State.Calm.normalize {state : State} (sorted : state.Sorted) (calm : state.Calm) :
    state.normalize.Quiet := by
  refine ⟨calm.1, fun processId process found => ?_⟩
  rw [State.record_normalize' sorted] at found
  cases record : state.record processId with
  | none => simp [record] at found
  | some original =>
    simp only [record, Option.map_some, Option.filter] at found
    split at found
    · rename_i kept
      cases found
      rcases calm.2 processId original record with quiet | ⟨reason, ended, empty⟩
      · rw [quiet.normRecord]; exact quiet
      · simp [normRecord, ended, empty, ProcessState.finished, Kernel.filter_eq] at kept
    · cases found

private theorem State.Quiet.set {state : State} (quiet : state.Quiet) {processId : PID} {process : ProcessState}
    (quiet' : process.Quiet) : (state.set processId process).Quiet := by
  refine ⟨quiet.1, fun other record found => ?_⟩
  rw [State.record_set] at found
  split at found
  · cases found; exact quiet'
  · exact quiet.2 other record found

private theorem State.Quiet.modify {state : State} (quiet : state.Quiet) {processId : PID}
    {change : ProcessState → ProcessState} (keeps : ∀ process, process.Quiet → (change process).Quiet) :
    (state.modify processId change).Quiet := by
  unfold State.modify
  split
  · rename_i process found
    exact quiet.set (keeps _ (quiet.2 _ _ found))
  · exact quiet

private theorem State.Quiet.process {state : State} (quiet : state.Quiet) (processId : PID) :
    (state.process processId).parked = none := by
  cases found : state.record processId with
  | none => simp [State.process, found]
  | some process => simpa [State.process, found] using (quiet.2 _ _ found).2.2.2.2.1

/-- Sending a message from a process keeps the state quiet. -/
private theorem State.Quiet.send {state : State} (quiet : state.Quiet) {source target : PID} {message : Term}
    (notClock : source ≠ clock) : (state.send source target (.message message)).Quiet := by
  unfold State.send
  rw [quiet.process source]
  dsimp only
  unfold State.enqueue
  split
  · rename_i process found
    split
    · refine quiet.set ?_
      obtain ⟨live, links, monitors, monitoring, parked, eager, queue⟩ := quiet.2 _ _ found
      refine ⟨live, links, monitors, monitoring, parked, eager, fun entry mem => ?_⟩
      simp only [Kernel.append_eq, List.mem_append, List.mem_singleton] at mem
      rcases mem with mem | rfl
      · exact queue entry mem
      · exact ⟨⟨message, rfl⟩, notClock⟩
    · exact quiet
  · exact quiet

/-- A quiet process ends with nothing left to signal or answer. -/
private theorem State.Quiet.terminate_eq {state : State} (quiet : state.Quiet) {processId : PID}
    {process : ProcessState} (found : state.record processId = some process) (reason : Term) :
    ∃ ended : ProcessState, ended.Ended ∧
      state.terminate processId reason = ({ state with timers := [] } : State).set processId ended := by
  obtain ⟨live, links, monitors, monitoring, parked, eager, queue⟩ := quiet.2 _ _ found
  have processOf : state.process processId = process := by simp [State.process, found]
  unfold State.terminate
  simp only [processOf, links, monitors, Kernel.foldl_eq, List.foldl_nil, quiet.1]
  simp only [Kernel.filter_eq, List.filter_nil]
  refine ⟨_, ⟨reason, rfl, ?_⟩, rfl⟩
  simp only [List.filter_eq_nil_iff]
  intro entry mem
  obtain ⟨⟨message, signal⟩, -⟩ := queue entry mem
  simp [signal]

private theorem State.Quiet.terminate {state : State} (quiet : state.Quiet) {processId : PID}
    {process : ProcessState} (found : state.record processId = some process) (reason : Term) :
    (state.terminate processId reason).Calm := by
  obtain ⟨ended, isEnded, equal⟩ := quiet.terminate_eq found reason
  rw [equal]
  refine ⟨⟨rfl, quiet.1.2⟩, fun other record found' => ?_⟩
  rw [State.record_set] at found'
  split at found'
  · cases found'; exact .inr isEnded
  · exact .inl (quiet.2 other record found')

/-- A talking process's own step leaves a calm state, unless it does not
return, and its continuation, which talks too. -/
private theorem Task.own_talks {talk : PID → PID → Prop} (single : Single talk) {state : State}
    {processId : PID} {task : Task α} {transition : Transition α} (quiet : state.Quiet)
    (alive : state.alive processId = true) (waits : task.wait = none)
    (talks : task.computation.Talks talk processId) (mem : transition ∈ task.own state processId) :
    (transition.exhausted = false → transition.state.Calm) ∧
      ∀ entry ∈ transition.tasks, entry.1 = processId ∧ entry.2.wait = none ∧
        entry.2.computation.Talks talk entry.1 := by
  obtain ⟨process, found, -⟩ := State.alive_iff.mp alive
  obtain ⟨computation, finish, wait⟩ := task
  simp only at waits talks
  subst waits
  cases talks with
  | ok =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem
    exact ⟨fun _ => quiet.terminate found _, by simp [Task.ended]⟩
  | error =>
    rename_i exception
    cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;>
      first
        | exact ⟨fun exhausted => by simp at exhausted, by simp⟩
        | exact ⟨fun _ => quiet.terminate found _, by simp [Task.ended]⟩
  | get next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem
    refine ⟨fun _ => quiet.calm, ?_⟩
    simp only [List.mem_singleton]
    rintro _ rfl
    exact ⟨rfl, rfl, next _ rfl⟩
  | send allowed next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem
    refine ⟨fun _ => (quiet.send (single.2 _ _ allowed)).calm, ?_⟩
    simp only [List.mem_singleton]
    rintro _ rfl
    exact ⟨rfl, rfl, next⟩
  | receive next =>
    simp only [Task.own] at mem
    split at mem
    · simp only [List.mem_singleton] at mem; subst mem
      refine ⟨fun _ => State.Quiet.calm (by exact quiet.modify fun _ quiet' => quiet'), ?_⟩
      simp only [List.mem_singleton]
      rintro _ rfl
      exact ⟨rfl, rfl, next _⟩
    · simp at mem

/-- Handling the oldest signal of a quiet process appends a message to its
mailbox, leaving its task as it is. -/
private theorem Task.handle_talks {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (quiet : state.Quiet) (waits : task.wait = none) (mem : transition ∈ task.handle state processId) :
    transition.exhausted = false ∧ transition.state.Calm ∧ transition.tasks = [(processId, task)] := by
  simp only [Task.handle] at mem
  split at mem
  · simp at mem
  · rename_i entry rest queue
    cases found : state.record processId with
    | none => simp [State.process, found] at queue
    | some process =>
    have processOf : state.process processId = process := by simp [State.process, found]
    obtain ⟨live, links, monitors, monitoring, parked, eager, queued⟩ := quiet.2 _ _ found
    rw [processOf] at queue mem
    obtain ⟨⟨message, signal⟩, -⟩ := queued entry (by rw [queue]; exact List.mem_cons_self)
    obtain ⟨source, signal'⟩ := entry
    simp only at signal; subst signal
    have set : (state.set processId { process with queue := rest }).Quiet := quiet.set
      ⟨live, links, monitors, monitoring, parked, eager, fun entry mem =>
        queued entry (by rw [queue]; exact List.mem_cons_of_mem _ mem)⟩
    simp only [State.handle] at mem
    obtain ⟨computation, finish, wait⟩ := task
    simp only at waits; subst waits
    simp only [List.mem_singleton] at mem; subst mem
    refine ⟨rfl, State.Quiet.calm ?_, rfl⟩
    show ((state.set processId { process with queue := rest }).append processId message).Quiet
    unfold State.append
    exact set.modify fun _ quiet' => quiet'

private theorem Config.Talking.step {talk : PID → PID → Prop} (single : Single talk) {elapsed : PID → Nat → Nat}
    {config next : Config α} {event : Event} (reachable : config.Reachable elapsed)
    (talking : config.Talking talk) (step : Step config event next) : next.Talking talk := by
  cases config with
  | start => exact talking.elim
  | running state tasks finished exhausted =>
    cases exhausted
    case true => simp [Step, Config.successors] at step
    obtain ⟨quiet, talks⟩ := talking
    have within : state.Within elapsed := reachable.1.1
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with (((⟨before, processId, task, after, split, transition, possible, same⟩ |
      ⟨processId, process, found, phased⟩) | ⟨processId, process, -, unparked⟩) | ⟨timer, firing, fired⟩) |
      ⟨update, staged, -⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      have tasks' := eq_of_mem_splits split
      have mem : (processId, task) ∈ tasks := by rw [tasks']; simp
      obtain ⟨waits, talksTask⟩ := talks _ mem
      have alive : state.alive processId = true := reachable.2.2.1 _ mem
      simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
      unfold Transition.apply
      split
      · trivial
      · rename_i notExhausted
        have facts : transition.state.Calm ∧ transition.state.Within elapsed ∧
            ∀ entry ∈ transition.tasks, entry.2.wait = none ∧ entry.2.computation.Talks talk entry.1 := by
          rcases possible with possible | possible
          · obtain ⟨calm, newTasks⟩ := Task.own_talks single quiet alive waits talksTask possible
            exact ⟨calm (by simpa using notExhausted), within.own possible, fun entry mem => (newTasks entry mem).2⟩
          · obtain ⟨-, calm, newTasks⟩ := Task.handle_talks quiet waits possible
            refine ⟨calm, within.handleStep possible, ?_⟩
            rw [newTasks]
            simpa using ⟨waits, talksTask⟩
        obtain ⟨calm, within', newTasks⟩ := facts
        refine ⟨calm.normalize within'.1, fun entry mem' => ?_⟩
        simp only [Kernel.append_eq, List.mem_append] at mem'
        rcases mem' with (inBefore | inTransition) | inAfter
        · exact talks entry (by rw [tasks']; simp [inBefore])
        · exact newTasks entry inTransition
        · exact talks entry (by rw [tasks']; simp [inAfter])
    · -- Only a process that ended has phases, and no record of a quiet state has.
      obtain ⟨_, phase, -⟩ := phased
      cases record : state.record processId with
      | none => simp [State.phases, State.exitLinks, State.process, State.phase, record] at phase
      | some process' =>
        have live := (quiet.2 _ _ record).1
        simp [State.phases, State.exitLinks, State.process, State.phase, record, live] at phase
    · simp [quiet.process processId] at unparked
    · simp [State.firing, quiet.1, firstOfEach] at firing
    · simp [quiet.1.2] at staged

private theorem distinctTasks_of_pairwise {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1) :
    (Config.running state tasks finished exhausted).distinctTasks = true := by
  simp only [Config.distinctTasks, Kernel.all_eq, List.all_eq_true, Kernel.any_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.any_eq_false, beq_iff_eq, Prod.forall]
  intro before processId task after mem other task' inside same
  rw [eq_of_mem_splits mem, List.pairwise_append] at pairwise
  exact pairwise.2.2 _ inside _ List.mem_cons_self same

/-- A computation whose own step is not forced among those of talking processes. -/
private def _root_.Lynx.Result.Unforced : Result β → Prop
  | .send .. | .ok _ | .error _ => True
  | _ => False

/-- A step of talking processes that is not forced is a process's own step
that sends, returns or raises. -/
private theorem Config.unforced {talk : PID → PID → Prop} {elapsed : PID → Nat → Nat} {state : State}
    {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {key : Key} {event : Event}
    {next : Config α} (reachable : (Config.running state tasks finished false).Reachable elapsed)
    (talking : (Config.running state tasks finished false).Talking talk)
    (mem : (key, event, next, false) ∈ (Config.running state tasks finished false).taggedSteps) :
    ∃ processId task, key = .own processId ∧ Kernel.lookup processId tasks = some task ∧ task.wait = none ∧
      task.computation.Unforced := by
  obtain ⟨quiet, talks⟩ := talking
  have step := reachable.stepOf mem
  have pairwise := reachable.2.1
  cases key with
  | own processId =>
    obtain ⟨task, transition, lookup, head, -⟩ := Config.stepOf_own step
    have flag := Config.forced_own pairwise lookup head mem
    obtain ⟨waits, talksTask⟩ := talks _ (mem_of_lookup lookup)
    refine ⟨processId, task, rfl, lookup, waits, ?_⟩
    obtain ⟨computation, finish, wait⟩ := task
    simp only at waits talksTask ⊢
    subst waits
    cases talksTask with
    | ok | error | send => trivial
    | get =>
      simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
      simp [Event.local] at flag
    | receive =>
      simp only [Task.own] at head
      split at head
      · simp only [List.head?_cons, Option.some.injEq] at head; subst head
        have kept : ∀ remaining : List Term, ((state.modify processId fun process =>
            { process with mailbox := remaining }).process processId).refCounter =
            (state.process processId).refCounter := by
          intro remaining
          unfold State.modify
          split
          · rename_i process found
            simp only [State.process, State.record_set, ↓reduceIte, found, Option.getD_some]
          · rfl
        simp [Event.local, kept] at flag
      · simp at head
  | handle processId =>
    obtain ⟨task, transition, lookup, head, -⟩ := Config.stepOf_handle step
    have flag := Config.forced_handle pairwise lookup mem
    simp only [Task.handle] at head
    split at head
    · simp at head
    · rename_i entry rest queue
      rw [queue] at flag
      cases found : state.record processId with
      | none => simp [State.process, found] at queue
      | some process =>
        have processOf : state.process processId = process := by simp [State.process, found]
        rw [processOf] at queue
        obtain ⟨⟨message, signal⟩, notClock⟩ := (quiet.2 _ _ found).2.2.2.2.2.2 entry (by rw [queue]; simp)
        simp [Task.forcedHead, signal, notClock] at flag
  | phase processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff] at step
    obtain ⟨_, phase, -⟩ := step
    cases record : state.record processId with
    | none => simp [State.phase, record] at phase
    | some process => simp [State.phase, record, (quiet.2 _ _ record).1] at phase
  | link processId target =>
    simp only [Config.stepOf, Option.map_eq_some_iff] at step
    obtain ⟨_, phase, -⟩ := step
    cases record : state.record processId with
    | none => simp [State.linkPhase, record] at phase
    | some process => simp [State.linkPhase, record, (quiet.2 _ _ record).1] at phase
  | unpark processId =>
    simp [Config.stepOf, quiet.process processId] at step
  | fire reference =>
    simp [Config.stepOf, State.firing, quiet.1, firstOfEach, Kernel.find?_eq] at step
  | commit => simp [Config.stepOf, quiet.1.2] at step

/-! ### Steps of talking processes that are not forced -/

/-- What a send reads and writes in a quiet state: the sender's parked monitor
signal, and the receiver's liveness and, while it lives, its queue's tail. -/
private theorem State.Quiet.sendFrames {state : State} (quiet : state.Quiet) (source target : PID) (message : Term) :
    state.sendFrames source target (.message message) =
      [(source, Field.parked, 0), (target, Field.live, if state.alive target then Field.queueTail else 0)] := by
  simp only [State.sendFrames, quiet.process source, State.enqueueFrames, State.appendFrames]
  split <;> simp_all

/-- What a quiet process ending reads and writes: only its record. -/
private theorem State.Quiet.endFrames {state : State} (quiet : state.Quiet) (processId : PID) :
    state.endFrames processId = ([(processId, Field.all, Field.all)], false) := by
  have links : (state.process processId).links = [] := by
    cases found : state.record processId with
    | none => simp [State.process, found]
    | some process => simpa [State.process, found] using (quiet.2 _ _ found).2.1
  simp [State.endFrames, links, quiet.1, Kernel.filterMap_eq, Kernel.any_eq]

/-- No process of a quiet state holds anything about another that normalizing
drops once it is gone. -/
private theorem State.Quiet.leavesOthers {state : State} (sorted : state.Sorted) (quiet : state.Quiet)
    (processId : PID) : state.leavesOthers processId = true := by
  simp only [State.leavesOthers, Kernel.all_eq, List.all_eq_true, Prod.forall]
  intro other process mem
  have found : state.record other = some process := by
    simpa [State.record, Kernel.lookup_eq] using Sorted.lookup_of_mem sorted mem
  obtain ⟨live, links, monitors, -, -, -, queue⟩ := quiet.2 _ _ found
  simp only [live, links, monitors, Kernel.any_eq, List.any_nil, Bool.not_false, Bool.and_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true', List.any_eq_false]
  refine .inr fun entry mem' => ?_
  obtain ⟨⟨message, signal⟩, -⟩ := queue entry mem'
  simp [signal]

/-- The frames of a send are apart from frames that write neither the sender's
parked monitor signal nor the receiver's liveness, and that touch nothing of
the receiver the send writes. -/
private theorem framesApart_send {sender receiver : PID} {write : Nat} {frames : List Frame}
    (apart : ∀ entry ∈ frames, (entry.1 ≠ sender ∨ entry.2.2 &&& Field.parked = 0) ∧
      (entry.1 ≠ receiver ∨ entry.2.2 &&& Field.live = 0 ∧ write &&& (entry.2.1 ||| entry.2.2) = 0)) :
    framesApart [(sender, Field.parked, 0), (receiver, Field.live, write)] frames = true := by
  simp only [framesApart, Kernel.all_eq, List.all_eq_true, List.mem_cons, List.mem_nil_iff, or_false,
    Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq, forall_eq_or_imp, forall_eq, Prod.forall]
  refine ⟨fun processId reads writes mem => ?_, fun processId reads writes mem => ?_⟩
  · rcases (apart _ mem).1 with differ | unwritten
    · exact .inl (Ne.symm differ)
    · exact .inr ⟨by simp, unwritten⟩
  · rcases (apart _ mem).2 with differ | ⟨unlive, untouched⟩
    · exact .inl (Ne.symm differ)
    · exact .inr ⟨untouched, unlive⟩

/-- Normalizing leaves a quiet state as it is. -/
private theorem State.Quiet.normalize_eq {state : State} (sorted : state.Sorted) (quiet : state.Quiet) :
    state.normalize = state :=
  State.normalize_of_quiet fun _ mem =>
    quiet.2 _ _ (by simpa [State.record, Kernel.lookup_eq] using Sorted.lookup_of_mem sorted mem)

/-- A quiet process ending, normalized, only removes its record. -/
private theorem State.Quiet.terminate_normalize {state : State} (sorted : state.Sorted) (quiet : state.Quiet)
    {processId : PID} {process : ProcessState} (found : state.record processId = some process) (reason : Term) :
    (state.terminate processId reason).normalize = state.remove processId := by
  obtain ⟨ended, ⟨reason', exiting, empty⟩, equal⟩ := quiet.terminate_eq found reason
  have sorted' : (state.terminate processId reason).Sorted := (State.Within.terminate ⟨sorted, rfl⟩ _ _).1
  have removedSorted : (state.remove processId).Sorted := (State.Within.remove ⟨sorted, rfl⟩ _).1
  refine State.ext_records removedSorted (Sorted.normalize sorted') (fun other => ?_) ?_ ?_ ?_
  · rw [State.record_normalize' sorted', equal, State.record_set, State.record_remove]
    split
    · simp [normRecord, exiting, empty, Option.filter, ProcessState.finished, Kernel.filter_eq]
    · rename_i differ
      rw [show ({ state with timers := [] } : State).record other = state.record other from rfl]
      cases record : state.record other with
      | none => rfl
      | some process' =>
        have quiet' := quiet.2 _ _ record
        simp [quiet'.normRecord, Option.filter, ProcessState.finished, quiet'.1]
  · simp [State.normalize_eq, equal, State.set, State.remove, quiet.1]
  · simp [State.normalize_eq, equal, State.set, State.remove]
  · simp [State.normalize_eq, equal, State.set, State.remove]

section
variable {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}

/-- A quiet process's send is confined, within the frames of a send. -/
private theorem Config.sends_confined (quiet : state.Quiet) {processId target : PID} {message : Term} {β : Type}
    {next : Result β} {finish : Except Exception β → Option (Except Exception α)}
    (alive : state.alive processId = true)
    (lookup : Kernel.lookup processId tasks = some ⟨.send target message next, finish, none⟩) :
    (Config.running state tasks finished false).confined (.own processId) = true ∧
      (Config.running state tasks finished false).frames (.own processId) =
        some ([(processId, Field.parked, 0),
          (target, Field.live, if state.alive target then Field.queueTail else 0)], false) := by
  simp only [Config.confined, Config.frames, lookup]
  simp [alive, State.parkedMonitored, quiet.process, Task.ownFrames, quiet.sendFrames]

/-- A quiet process ending is confined, within the frames of its own record. -/
private theorem Config.ends_confined (sorted : state.Sorted) (quiet : state.Quiet) {processId : PID} {β : Type}
    {computation : Result β} {finish : Except Exception β → Option (Except Exception α)}
    (alive : state.alive processId = true)
    (lookup : Kernel.lookup processId tasks = some ⟨computation, finish, none⟩)
    (ends : (∃ value, computation = .ok value) ∨ ∃ exception, computation = .error exception ∧ exception ≠ .exhausted) :
    (Config.running state tasks finished false).confined (.own processId) = true ∧
      (Config.running state tasks finished false).frames (.own processId) =
        some ([(processId, Field.all, Field.all)], false) := by
  rcases ends with ⟨value, rfl⟩ | ⟨exception, rfl, notExhausted⟩
  · simp only [Config.confined, Config.frames, lookup]
    simp [alive, State.parkedMonitored, quiet.process, Task.ownFrames, quiet.endFrames, quiet.leavesOthers sorted]
  · cases exception
    case exhausted => exact absurd rfl notExhausted
    all_goals
      simp only [Config.confined, Config.frames, lookup]
      simp [alive, State.parkedMonitored, quiet.process, Task.ownFrames, quiet.endFrames, quiet.leavesOthers sorted]

private theorem Config.apart_of_frames {key other : Key} {frames frames' : List Frame}
    (confined : (Config.running state tasks finished false).confined key = true)
    (confined' : (Config.running state tasks finished false).confined other = true)
    (found : (Config.running state tasks finished false).frames key = some (frames, false))
    (found' : (Config.running state tasks finished false).frames other = some (frames', false))
    (apart : framesApart frames frames' = true) :
    (Config.running state tasks finished false).apart key other = true := by
  simp [Config.apart, confined, confined', found, found', apart]

end

private theorem Meet.symm {first second : Config α} (meet : Meet first second) : Meet second first := by
  obtain ⟨last, one, two⟩ := meet
  exact ⟨last, two, one⟩

/-- A process that does not return ends the run, which another process's step
before it leaves the same. -/
private theorem Config.exhausted_meet {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId other : PID} {task' : Task α} {β : Type}
    {finish : Except Exception β → Option (Except Exception α)} {event event' : Event} {next next' : Config α}
    (ready : (Config.running state tasks finished false).Ready elapsed) (differ : processId ≠ other)
    (lookup : Kernel.lookup processId tasks = some ⟨(.error .exhausted : Result β), finish, none⟩)
    (lookup' : Kernel.lookup other tasks = some task')
    (step : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next))
    (step' : (Config.running state tasks finished false).stepOf (.own other) = some (event', next')) :
    next = next' ∨ Meet next next' := by
  obtain ⟨⟨within, -, -⟩, fresh⟩ := ready.1
  have canonical : ∀ {first second : State}, first.elapsed = second.elapsed →
      ({ elapsed := first.elapsed } : State) = { elapsed := second.elapsed } := by
    intro first second same; rw [same]
  have exhausts : ∀ state' : State,
      ((⟨(.error .exhausted : Result β), finish, none⟩ : Task α).own state' processId).head? =
        some (Transition.mk (.exit processId (.atom "exhausted")) (state'.remove processId) [] none true) :=
    fun _ => rfl
  rw [Config.stepOf_own_of lookup (exhausts state)] at step
  simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at step
  obtain ⟨-, rfl⟩ := step
  obtain ⟨task'', transition, found, head, rfl⟩ := Config.stepOf_own step'
  rw [lookup'] at found; cases found
  have within' := within.own (List.mem_of_head? head)
  split
  · left
    rw [canonical (show (state.remove processId).elapsed = transition.state.elapsed from
      within.2.trans within'.2.symm)]
  · right
    have kept : Kernel.lookup processId (rewriteTask other (fun _ => transition.tasks) tasks) =
        some ⟨(.error .exhausted : Result β), finish, none⟩ := by
      rw [lookup_rewriteTask differ (fun _ entry mem => by
        rcases Task.own_pids (List.mem_of_head? head) entry mem with same | child
        · rw [same]; exact Ne.symm differ
        · rw [child.1]; exact fresh.child lookup' lookup)]
      exact lookup
    have after := Config.stepOf_own_of (state := transition.state.normalize)
      (finished := transition.finished.orElse fun _ => finished) kept (exhausts _)
    simp only [↓reduceIte] at after
    rw [canonical (show (transition.state.normalize.remove processId).elapsed = (state.remove processId).elapsed from
      within'.2.trans within.2.symm)] at after
    exact ⟨_, .inl rfl, .inr ⟨_, Config.step_of_stepOf after⟩⟩

private theorem State.Quiet.send_live {state : State} (quiet : state.Quiet) {source target : PID}
    {message : Term} {process : ProcessState} (found : state.record target = some process) :
    state.send source target (.message message) =
      state.set target { process with queue := Kernel.append process.queue [⟨source, .message message⟩] } := by
  unfold State.send
  rw [quiet.process source]
  dsimp only
  unfold State.enqueue
  rw [found]
  dsimp only
  rw [ite_eq_left (by simp [(quiet.2 _ _ found).1])]

private theorem State.Quiet.send_missing {state : State} (quiet : state.Quiet) {source target : PID}
    {message : Term} (missing : state.record target = none) : state.send source target (.message message) = state := by
  unfold State.send
  rw [quiet.process source]
  dsimp only
  unfold State.enqueue
  rw [missing]
  rfl

private theorem State.remove_set {state : State} (sorted : state.Sorted) (processId : PID) (process : ProcessState) :
    (state.set processId process).remove processId = state.remove processId := by
  have sorted' : (state.set processId process).Sorted := Lynx.Concurrent.Sorted.insertRecord sorted processId _
  refine State.ext_records (State.Within.remove ⟨sorted, rfl⟩ _).1 (State.Within.remove ⟨sorted', rfl⟩ _).1
    (fun other => ?_) rfl rfl rfl
  rw [State.record_remove, State.record_remove, State.record_set]
  split <;> rfl

private theorem State.Quiet.remove {state : State} (quiet : state.Quiet) (processId : PID) :
    (state.remove processId).Quiet := by
  refine ⟨quiet.1, fun other process found => ?_⟩
  rw [State.record_remove] at found
  split at found
  · cases found
  · exact quiet.2 _ _ found

/-- A process that ends, with how it ends and the event of its end. -/
private theorem Task.ends {β : Type} {computation : Result β} {finish : Except Exception β → Option (Except Exception α)}
    {processId : PID}
    (ends : (∃ value, computation = .ok value) ∨ ∃ exception, computation = .error exception ∧ exception ≠ .exhausted) :
    ∃ event reason result, ∀ state : State,
      ((⟨computation, finish, none⟩ : Task α).own state processId).head? =
        some (Task.ended finish event state processId reason result) := by
  rcases ends with ⟨value, rfl⟩ | ⟨exception, rfl, notExhausted⟩
  · exact ⟨_, _, _, fun _ => rfl⟩
  · cases exception
    case exhausted => exact absurd rfl notExhausted
    all_goals exact ⟨_, _, _, fun _ => rfl⟩

/-- A message to a process that ends is dropped either way. -/
private theorem Config.send_end_meet {talk : PID → PID → Prop} (single : Single talk) {elapsed : PID → Nat → Nat}
    {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {sender receiver : PID}
    {β γ : Type} {message : Term} {continuation : Result β} {finish : Except Exception β → Option (Except Exception α)}
    {computation : Result γ} {finish' : Except Exception γ → Option (Except Exception α)}
    {event event' : Event} {next next' : Config α}
    (ready : (Config.running state tasks finished false).Ready elapsed) (quiet : state.Quiet)
    (allowed : talk sender receiver) (differ : sender ≠ receiver)
    (lookup : Kernel.lookup sender tasks = some ⟨.send receiver message continuation, finish, none⟩)
    (lookup' : Kernel.lookup receiver tasks = some ⟨computation, finish', none⟩)
    (ends : (∃ value, computation = .ok value) ∨ ∃ exception, computation = .error exception ∧ exception ≠ .exhausted)
    (step : (Config.running state tasks finished false).stepOf (.own sender) = some (event, next))
    (step' : (Config.running state tasks finished false).stepOf (.own receiver) = some (event', next')) :
    Meet next next' := by
  obtain ⟨⟨within, -, -⟩, fresh⟩ := ready.1
  have sorted := within.1
  obtain ⟨receiverProcess, foundReceiver, -⟩ := State.alive_iff.mp (fresh.2.1 _ (mem_of_lookup lookup'))
  obtain ⟨endEvent, reason, result, ending⟩ := Task.ends (finish := finish') (processId := receiver) ends
  have sends : ∀ state' : State,
      ((⟨.send receiver message continuation, finish, none⟩ : Task α).own state' sender).head? =
        some (Transition.mk (.send sender receiver message) (state'.send sender receiver (.message message))
          [(sender, ⟨continuation, finish, none⟩)] none false) := fun _ => rfl
  rw [Config.stepOf_own_of lookup (sends state)] at step
  rw [Config.stepOf_own_of lookup' (ending state)] at step'
  simp only [Option.some.injEq, Prod.mk.injEq, Task.ended, Bool.false_eq_true, ↓reduceIte] at step step'
  obtain ⟨-, rfl⟩ := step
  obtain ⟨-, rfl⟩ := step'
  -- After the send, the receiver ends; after it ends, the message is dropped.
  have sent := quiet.send_live (source := sender) (message := message) foundReceiver
  have quietSent : (state.send sender receiver (.message message)).Quiet := quiet.send (single.2 _ _ allowed)
  have sortedSent : (state.send sender receiver (.message message)).Sorted := by
    rw [sent]; exact Lynx.Concurrent.Sorted.insertRecord sorted receiver _
  have normalizedSent := quietSent.normalize_eq sortedSent
  have foundQueued : (state.send sender receiver (.message message)).record receiver =
      some { receiverProcess with queue := Kernel.append receiverProcess.queue [⟨sender, .message message⟩] } := by
    rw [sent, State.record_set, ite_eq_left rfl]
  have ended := quiet.terminate_normalize sorted foundReceiver reason
  have endedSent := quietSent.terminate_normalize sortedSent foundQueued reason
  rw [sent, State.remove_set sorted] at endedSent
  rw [sent] at normalizedSent
  have missing : (state.remove receiver).record receiver = none := by simp [State.record_remove]
  have quietRemoved := quiet.remove receiver
  have sortedRemoved : (state.remove receiver).Sorted := (State.Within.remove ⟨sorted, rfl⟩ _).1
  have tasksSent : Kernel.lookup receiver (rewriteTask sender (fun _ => [(sender, ⟨continuation, finish, none⟩)]) tasks) =
      some ⟨computation, finish', none⟩ := by
    rw [lookup_rewriteTask (Ne.symm differ) (fun _ entry mem => by
      simp only [List.mem_singleton] at mem; subst mem; exact differ)]
    exact lookup'
  have tasksEnded : Kernel.lookup sender (rewriteTask receiver (fun _ => []) tasks) =
      some ⟨.send receiver message continuation, finish, none⟩ := by
    rw [lookup_rewriteTask differ (fun _ entry mem => by simp at mem)]
    exact lookup
  have afterSend := Config.stepOf_own_of (finished := none.orElse fun _ => finished) tasksSent
    (ending (state.set receiver { receiverProcess with queue := Kernel.append receiverProcess.queue [⟨sender, .message message⟩] }).normalize)
  have afterEnd := Config.stepOf_own_of (finished := (finish' result).orElse fun _ => finished) tasksEnded
    (sends (state.terminate receiver reason).normalize)
  simp only [Task.ended, Bool.false_eq_true, ↓reduceIte] at afterSend afterEnd
  rw [normalizedSent, endedSent] at afterSend
  rw [ended, quietRemoved.send_missing missing, quietRemoved.normalize_eq sortedRemoved] at afterEnd
  rw [sent, normalizedSent]
  refine ⟨_, .inr ⟨_, Config.step_of_stepOf afterSend⟩, .inr ⟨.send sender receiver message,
    Config.step_of_stepOf (key := .own sender) ?_⟩⟩
  rw [ended, afterEnd, rewriteTask_comm differ (fun _ entry mem => by
      simp only [List.mem_singleton] at mem; subst mem; exact differ) (fun _ entry mem => by simp at mem)]
  simp

/-- Two own steps of different talking processes that are not forced meet again. -/
private theorem Config.unforced_meet {talk : PID → PID → Prop} (single : Single talk) {elapsed : PID → Nat → Nat}
    {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {processId other : PID}
    {task task' : Task α} {event event' : Event} {next next' : Config α}
    (ready : (Config.running state tasks finished false).Ready elapsed)
    (talking : (Config.running state tasks finished false).Talking talk) (differ : processId ≠ other)
    (lookup : Kernel.lookup processId tasks = some task) (lookup' : Kernel.lookup other tasks = some task')
    (waits : task.wait = none) (waits' : task'.wait = none)
    (unforced : task.computation.Unforced) (unforced' : task'.computation.Unforced)
    (step : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next))
    (step' : (Config.running state tasks finished false).stepOf (.own other) = some (event', next')) :
    next = next' ∨ Meet next next' := by
  obtain ⟨⟨within, normalized, once⟩, fresh⟩ := ready.1
  obtain ⟨quiet, talks⟩ := talking
  have sorted := within.1
  have alive := fresh.2.1 _ (mem_of_lookup lookup)
  have alive' := fresh.2.1 _ (mem_of_lookup lookup')
  have talksTask := (talks _ (mem_of_lookup lookup)).2
  have talksTask' := (talks _ (mem_of_lookup lookup')).2
  have distinct := distinctTasks_of_pairwise (state := state) (finished := finished) (exhausted := false) fresh.1
  have owners : ∀ {first second : PID}, first ≠ second →
      (!((Key.own first).owner.isSome && (Key.own first).owner == (Key.own second).owner &&
        (Key.own first).isOwn == (Key.own second).isOwn)) = true := by
    intro first second differ
    simp [Key.owner, differ]
  have spawns : ∀ {processId : PID} {task : Task α}, Kernel.lookup processId tasks = some task →
      task.computation.Unforced → (Config.running state tasks finished false).spawnsFresh (.own processId) = true := by
    intro processId task lookup unforced
    obtain ⟨computation, finish, wait⟩ := task
    simp only [Config.spawnsFresh, lookup]
    cases computation <;> simp_all [Result.Unforced]
  -- Steps whose frames are apart meet after one step each.
  have apart : (Config.running state tasks finished false).apart (.own processId) (.own other) = true →
      Meet next next' := by
    intro apart
    obtain ⟨_, _, last, after, after'⟩ := Config.commutes_of_apart within normalized once (owners differ)
      (spawns lookup unforced) (spawns lookup' unforced') distinct apart step step'
    exact ⟨last, .inr ⟨_, Config.step_of_stepOf after⟩, .inr ⟨_, Config.step_of_stepOf after'⟩⟩
  have apart' : (Config.running state tasks finished false).apart (.own other) (.own processId) = true →
      Meet next next' := by
    intro apart
    obtain ⟨_, _, last, after, after'⟩ := Config.commutes_of_apart within normalized once (owners (Ne.symm differ))
      (spawns lookup' unforced') (spawns lookup unforced) distinct apart step' step
    exact ⟨last, .inr ⟨_, Config.step_of_stepOf after'⟩, .inr ⟨_, Config.step_of_stepOf after⟩⟩
  obtain ⟨computation, finish, wait⟩ := task
  obtain ⟨computation', finish', wait'⟩ := task'
  simp only at waits waits' unforced unforced' talksTask talksTask'
  subst waits waits'
  -- A process that does not return ends the run either way.
  by_cases exhausted : computation = .error .exhausted
  · subst exhausted; exact Config.exhausted_meet ready differ lookup lookup' step step'
  by_cases exhausted' : computation' = .error .exhausted
  · subst exhausted'
    rcases Config.exhausted_meet ready (Ne.symm differ) lookup' lookup step' step with same | meet
    · exact .inl same.symm
    · exact .inr (Meet.symm meet)
  have shape : ∀ {β : Type} {computation : Result β}, computation.Unforced → computation ≠ .error .exhausted →
      (∃ target message next, computation = .send target message next) ∨
        (∃ value, computation = .ok value) ∨ ∃ exception, computation = .error exception ∧ exception ≠ .exhausted := by
    intro β computation unforced notExhausted
    cases computation <;> simp_all [Result.Unforced]
  -- Bits of the fields a send reads and writes.
  have tail : ∀ alive : Bool, (if alive then Field.queueTail else 0) &&& Field.parked = 0 := by
    intro alive; cases alive <;> decide
  have tail' : ∀ alive : Bool, (if alive then Field.queueTail else 0) &&& (Field.parked ||| 0) = 0 := by
    intro alive; cases alive <;> decide
  rcases shape unforced exhausted with ⟨target, message, continuation, rfl⟩ | ends
  · cases talksTask with
    | send allowed _ =>
    rcases shape unforced' exhausted' with ⟨target', message', continuation', rfl⟩ | ends'
    · cases talksTask' with
      | send allowed' _ =>
      have targets : target ≠ target' := fun same => differ (single.1 _ _ _ allowed (same ▸ allowed'))
      obtain ⟨confined, frames⟩ := Config.sends_confined (finished := finished) quiet alive lookup
      obtain ⟨confined', frames'⟩ := Config.sends_confined (finished := finished) quiet alive' lookup'
      refine .inr (apart (Config.apart_of_frames confined confined' frames frames' (framesApart_send ?_)))
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨.inl (Ne.symm differ), .inr ⟨by decide, tail' _⟩⟩, ⟨.inr (tail _), .inl (Ne.symm targets)⟩⟩
    · by_cases same : target = other
      · subst same
        exact .inr (Config.send_end_meet single ready quiet allowed differ lookup lookup' ends' step step')
      · obtain ⟨confined, frames⟩ := Config.sends_confined (finished := finished) quiet alive lookup
        obtain ⟨confined', frames'⟩ := Config.ends_confined (finished := finished) sorted quiet alive' lookup' ends'
        refine .inr (apart (Config.apart_of_frames confined confined' frames frames' (framesApart_send ?_)))
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
        exact ⟨.inl (Ne.symm differ), .inl (Ne.symm same)⟩
  · rcases shape unforced' exhausted' with ⟨target', message', continuation', rfl⟩ | ends'
    · cases talksTask' with
      | send allowed' _ =>
      by_cases same : target' = processId
      · subst same
        exact .inr (Meet.symm (Config.send_end_meet single ready quiet allowed' (Ne.symm differ) lookup' lookup ends
          step' step))
      · obtain ⟨confined, frames⟩ := Config.ends_confined (finished := finished) sorted quiet alive lookup ends
        obtain ⟨confined', frames'⟩ := Config.sends_confined (finished := finished) quiet alive' lookup'
        refine .inr (apart' (Config.apart_of_frames confined' confined frames' frames (framesApart_send ?_)))
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
        exact ⟨.inl differ, .inl (Ne.symm same)⟩
    · obtain ⟨confined, frames⟩ := Config.ends_confined (finished := finished) sorted quiet alive lookup ends
      obtain ⟨confined', frames'⟩ := Config.ends_confined (finished := finished) sorted quiet alive' lookup' ends'
      refine .inr (apart (Config.apart_of_frames confined confined' frames frames' ?_))
      simp [framesApart, Kernel.all_eq, differ]

/-- A forced step and another step meet again. -/
private theorem Config.forced_meet {elapsed : PID → Nat → Nat} {config : Config α} {key key' : Key}
    {event event' : Event} {next next' : Config α} (ready : config.Ready elapsed)
    (forced : (key, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf key' = some (event', next')) (differ : key' ≠ key) : Meet next next' := by
  have readyNext' := ready.step (Config.step_of_stepOf step')
  rcases Config.forced_square ready.1 ready.2.1 ready.2.2 forced step' differ with ⟨absorbed, after⟩ |
      ⟨key'', event'', last, other, forcedLast, after⟩
  · exact ⟨next', .inr ⟨_, Config.step_of_stepOf after⟩, .inl rfl⟩
  · exact ⟨last, .inr ⟨_, Config.step_of_stepOf after⟩,
      .inr ⟨_, Config.step_of_stepOf (readyNext'.1.stepOf forcedLast)⟩⟩

/-- Processes that only message each other, each receiver hearing from a
single sender, have no races once they run in a quiet state. -/
public theorem RaceFree.of_talks {talk : PID → PID → Prop} (single : Single talk) {env : Environment}
    {computation : Result α} {elapsed : PID → Nat → Nat} {events : List Event} {state : State}
    {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    (run : Run (.start env computation elapsed) events (.running state tasks finished false))
    (quiet : state.Quiet) (talks : ∀ entry ∈ tasks, entry.2.wait = none ∧ entry.2.computation.Talks talk entry.1) :
    RaceFree (.running state tasks finished false) := by
  have readies : ∀ {first last : Config α} {events : List Event}, Run first events last →
      first.Ready elapsed → last.Ready elapsed := by
    intro first last events run
    induction run with
    | refl => exact id
    | step step _ ih => exact fun ready => ih (ready.step step)
  have ready := readies run ⟨⟨⟨rfl, trivial, trivial⟩, trivial⟩, trivial, trivial⟩
  intro events' reached run' event event' next next' step step'
  have both : ∀ {first last : Config α} {events : List Event}, Run first events last →
      first.Ready elapsed ∧ first.Talking talk → last.Ready elapsed ∧ last.Talking talk := by
    intro first last events run
    induction run with
    | refl => exact id
    | step step _ ih =>
      exact fun facts => ih ⟨facts.1.step step, Config.Talking.step single facts.1.1 facts.2 step⟩
  obtain ⟨readyReached, talkingReached⟩ := both run' ⟨ready, quiet, talks⟩
  match reached, readyReached, talkingReached, step, step' with
  | .start .., _, talking, _, _ => exact talking.elim
  | .running _ _ _ true, _, _, step, _ => simp [Step, Config.successors] at step
  | .running state' tasks' finished' false, readyReached, talkingReached, step, step' =>
    obtain ⟨key, forced, mem⟩ := Config.tagged_of_step step
    obtain ⟨key', forced', mem'⟩ := Config.tagged_of_step step'
    have found := readyReached.1.stepOf mem
    have found' := readyReached.1.stepOf mem'
    by_cases same : key = key'
    · subst same
      rw [found] at found'
      simp only [Option.some.injEq, Prod.mk.injEq] at found'
      exact .inl found'.2
    cases forced
    case true => exact .inr (Config.forced_meet readyReached mem found' (Ne.symm same))
    cases forced'
    case true => exact .inr (Meet.symm (Config.forced_meet readyReached mem' found same))
    obtain ⟨processId, task, rfl, lookup, waits, unforced⟩ := Config.unforced readyReached.1 talkingReached mem
    obtain ⟨other, task', rfl, lookup', waits', unforced'⟩ := Config.unforced readyReached.1 talkingReached mem'
    exact Config.unforced_meet single readyReached talkingReached (fun equal => same (by rw [equal]))
      lookup lookup' waits waits' unforced unforced' found found'

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

/-- A configuration whose first steps are each the only one available has no
races when the configuration after them has none. -/
public theorem RaceFree.of_advance (steps : Nat) {config : Config α}
    (unique : ∀ step < steps, ((config.advance step).successors).length ≤ 1)
    (raceFree : RaceFree (config.advance steps)) : RaceFree config := by
  induction steps generalizing config with
  | zero => exact raceFree
  | succ steps ih =>
    have first := unique 0 (Nat.succ_pos _)
    simp only [Config.advance_zero] at first
    cases found : config.successors with
    | nil =>
      have stuck : ∀ steps, config.advance steps = config := by
        intro steps
        cases steps with
        | zero => rfl
        | succ steps =>
          clear ih unique raceFree first
          induction steps with
          | zero => simp [Config.advance, found]
          | succ steps ih => simp [Config.advance, found]
      rw [stuck] at raceFree
      exact raceFree
    | cons head rest =>
      obtain ⟨event, next⟩ := head
      rw [found] at first
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using first)
      subst empty
      refine RaceFree.of_unique (next := next) (fun event' next' step => ?_) (ih (fun step below => ?_) ?_)
      · simp only [Step, found, List.mem_singleton, Prod.mk.injEq] at step
        exact step.2
      · have := unique (step + 1) (by omega)
        rwa [Config.advance_succ step found] at this
      · rwa [Config.advance_succ steps found] at raceFree

end Lynx.Concurrent
