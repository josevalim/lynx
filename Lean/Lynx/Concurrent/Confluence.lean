module

public import Lynx.Concurrent.Reduction
import all Lynx.Concurrent.Reduction
import all Lynx.Concurrent.Footprint

/-! Programs without races reach the same terminal configuration under every
interleaving, so one run determines the outcome of every run.

`RaceFree` asks that any two different steps of a reachable
configuration meet again after one step each. Then any two runs that reach a
terminal configuration reach the same one (`RaceFree.outcome_eq`), and
every run reaches one, since runs end (`Config.terminates`). `RaceFree.of_talks` establishes it for
processes that only talk along their process tree, each receiver hearing from
a single sender. -/

namespace Lynx.Concurrent

open Lynx

/-! ### Configurations without races -/

/-- Any two different steps of a configuration reachable from this one meet
again after one step each. -/
@[expose] public def RaceFree (config : Config α) : Prop :=
  ∀ events reached, Run config events reached →
    ∀ key key' event event' next next', key ≠ key' →
      (key, event, next) ∈ reached.steps → (key', event', next') ∈ reached.steps →
      ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last

/-- A configuration without steps. -/
private def Stuck (config : Config α) : Prop := ∀ event next, ¬ Step config event next

private theorem Terminal.stuck_of {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : Stuck config := by
  intro event next step
  simp [Step, terminal.successors_eq_nil] at step

/-- A configuration that has not started yet has at most one step. -/
private theorem start_unique {env : Environment} {computation : Result α} {elapsed : PID → Nat → Nat}
    {event event' : Event} {next next' : Config α}
    (step : Step (.start env computation elapsed) event next)
    (step' : Step (.start env computation elapsed) event' next') : next = next' := by
  simp only [Step, Config.successors] at step step'
  split at step <;> (try split at step) <;> simp_all

/-- Different steps of a well-formed configuration without races meet again
after one step each. -/
private theorem local_confluence {config first second : Config α} {event event' : Event}
    (wellformed : Wellformed config) (raceFree : RaceFree config)
    (step : Step config event first) (step' : Step config event' second) :
    first = second ∨ ∃ joined, (∃ step, Step first step joined) ∧ ∃ step, Step second step joined := by
  cases config with
  | start => exact .inl (start_unique step step')
  | running state tasks finished exhausted =>
    obtain ⟨key, mem⟩ := Step.keyed step
    obtain ⟨key', mem'⟩ := Step.keyed step'
    by_cases same : key = key'
    · subst same
      exact .inl (steps_unique wellformed mem mem').2
    · exact .inr (raceFree [] _ .refl key key' event event' first second same mem mem')

private theorem RaceFree.step {config next : Config α} {event : Event}
    (raceFree : RaceFree config) (step : Step config event next) : RaceFree next :=
  fun _ _ run => raceFree _ _ (.step step run)

/-- When every run is bounded, some run gets stuck. -/
private theorem exists_stuck : ∀ (bound : Nat) (config : Config α),
    (∀ events last, Run config events last → events.length ≤ bound) →
      ∃ events last, Run config events last ∧ Stuck last
  | bound, config, bounded => by
    by_cases stuck : Stuck config
    · exact ⟨[], config, .refl, stuck⟩
    · simp only [Stuck, Classical.not_forall, Classical.not_not] at stuck
      obtain ⟨event, next, step⟩ := stuck
      cases bound with
      | zero =>
        have := bounded _ _ (.step step .refl)
        simp at this
      | succ bound =>
        obtain ⟨events, last, run, stuck⟩ := exists_stuck bound next fun events last run => by
          have := bounded _ _ (.step step run)
          simp only [List.length_cons] at this
          omega
        exact ⟨_, last, .step step run, stuck⟩

private theorem Run.nil_inv {first last : Config α} (run : Run first [] last) : last = first := by
  cases run; rfl

private theorem Run.cons_inv {first last : Config α} {event : Event} {events : List Event}
    (run : Run first (event :: events) last) : ∃ next, Step first event next ∧ Run next events last := by
  cases run with
  | step step rest => exact ⟨_, step, rest⟩

/-- Every run is at most as long as a stuck run, and every stuck run ends in the
same configuration after the same number of steps. -/
private theorem unique_stuck (last : Config α) : ∀ (length : Nat) (config : Config α)
    (events : List Event), Wellformed config → RaceFree config → Run config events last →
      events.length = length → Stuck last →
      (∀ events' reached, Run config events' reached → events'.length ≤ length) ∧
        ∀ events' last', Run config events' last' → Stuck last' →
          last' = last ∧ events'.length = length
  | 0, config, events, _, _, run, size, stuck => by
    obtain rfl := List.eq_nil_of_length_eq_zero size
    obtain rfl := run.nil_inv
    refine ⟨fun events' reached run' => ?_, fun events' last' run' _ => ?_⟩
    · cases events' with
      | nil => simp
      | cons event events' =>
        obtain ⟨_, step, _⟩ := run'.cons_inv
        exact absurd step (stuck _ _)
    · cases events' with
      | nil => exact ⟨run'.nil_inv, rfl⟩
      | cons event events' =>
        obtain ⟨_, step, _⟩ := run'.cons_inv
        exact absurd step (stuck _ _)
  | length + 1, config, events, wellformed, raceFree, run, size, stuck => by
    cases events with
    | nil => simp at size
    | cons event events =>
    obtain ⟨next, first, rest⟩ := run.cons_inv
    have ih := unique_stuck last length next events (first.wellformed wellformed)
      (raceFree.step first) rest (by simpa using size) stuck
    -- Every other first step leads to the same stuck configuration.
    have others : ∀ event' second, Step config event' second →
        (∀ events' reached, Run second events' reached → events'.length ≤ length) ∧
          ∀ events' last', Run second events' last' → Stuck last' →
            last' = last ∧ events'.length = length := by
      intro event' second step
      rcases local_confluence wellformed raceFree first step with
        same | ⟨joined, ⟨event₁, toJoined⟩, ⟨event₂, toJoined'⟩⟩
      · subst same; exact ih
      · obtain ⟨events₃, last₃, run₃, stuck₃⟩ := exists_stuck length joined
          fun events reached run => by
            have := ih.1 _ _ (.step toJoined run)
            simp only [List.length_cons] at this
            omega
        obtain ⟨rfl, size₃⟩ := ih.2 _ _ (.step toJoined run₃) stuck₃
        simp only [List.length_cons] at size₃
        exact unique_stuck _ length second _ (step.wellformed wellformed)
          (raceFree.step step) (.step toJoined' run₃) (by simpa using size₃) stuck₃
    refine ⟨fun events' reached run' => ?_, fun events' last' run' stuck' => ?_⟩
    · cases events' with
      | nil => simp
      | cons event' events' =>
        obtain ⟨second, step, run'⟩ := run'.cons_inv
        have := (others _ _ step).1 _ _ run'
        simp only [List.length_cons]
        omega
    · cases events' with
      | nil =>
        obtain rfl := run'.nil_inv
        exact absurd first (stuck' _ _)
      | cons event' events' =>
        obtain ⟨second, step, run'⟩ := run'.cons_inv
        obtain ⟨rfl, size'⟩ := (others _ _ step).2 _ _ run' stuck'
        simp [size']

/-- Without races, every run of a computation that reaches a terminal
configuration reaches the same one, so all have the same outcome. -/
public theorem RaceFree.outcome_eq {env : Environment} {computation : Result α}
    {elapsed : PID → Nat → Nat}
    (raceFree : RaceFree (Config.start env computation elapsed)) {events events' : List Event}
    {last last' : Config α} {outcome outcome' : Outcome α}
    (run : Run (.start env computation elapsed) events last) (terminal : Terminal last outcome)
    (run' : Run (.start env computation elapsed) events' last')
    (terminal' : Terminal last' outcome') :
    outcome' = outcome := by
  obtain ⟨-, unique⟩ := unique_stuck last events.length _ events
    (show Wellformed (Config.start env computation elapsed) from trivial) raceFree run rfl
    (Terminal.stuck_of terminal)
  obtain ⟨rfl, -⟩ := unique _ _ run' (Terminal.stuck_of terminal')
  rw [← terminal.outcome_eq, ← terminal'.outcome_eq]

/-! ### Processes that talk along their process tree -/

/-- Every message the process sends goes to a destination `talk` allows from
its PID, which is not a child it has yet to spawn; no receive has a timeout; it
makes no requests to the scheduler; and it spawns without linking or
monitoring, each spawned process satisfying the same. Children are numbered
after the `children` the process already spawned. -/
public inductive _root_.Lynx.Result.Talks (talk : PID → PID → Prop) :
    {β : Type} → PID → Nat → Result β → Prop where
  | ok : Result.Talks talk self children (.ok value)
  | error : Result.Talks talk self children (.error exception)
  | get (next : ∀ env : Environment, env.currentPid = self →
        Result.Talks talk self children (continuation env)) :
      Result.Talks talk self children (.get continuation)
  | set (same : env.currentPid = self) (next : Result.Talks talk self children continuation) :
      Result.Talks talk self children (.set env continuation)
  | send (allowed : talk self receiver)
      (spawned : ∀ index, receiver = self ++ [index] → index ≤ children)
      (next : Result.Talks talk self children continuation) :
      Result.Talks talk self children (.send receiver message continuation)
  | receive (next : ∀ reply, Result.Talks talk self children (continuation reply)) :
      Result.Talks talk self children (.receive .infinity select continuation)
  | schedule (spawned : Result.Talks talk (self ++ [children + 1]) 0 child)
      (next : Result.Talks talk self (children + 1) (continuation (self ++ [children + 1]))) :
      Result.Talks talk self children (Result.schedule {} child continuation)

/-- Each receiver has a single sender, and processes only send to themselves,
their ancestors, or their own children. -/
@[expose] public def Single (talk : PID → PID → Prop) : Prop :=
  (∀ sender sender' receiver, talk sender receiver → talk sender' receiver → sender = sender') ∧
  ∀ sender receiver, talk sender receiver →
    (∃ rest, sender = receiver ++ rest) ∨ ∃ index, receiver = sender ++ [index]

/-- Every live process counts the ancestor of a PID below it among the
children it spawned, so no process spawns the PID later. -/
private def Spawned (state : State) (target : PID) : Prop :=
  ∀ parent index rest, (state.processes parent).isSome → target = parent ++ index :: rest →
    index ≤ (state.process parent).children

/-- No process is linked or monitored, no timer is pending, and the signals in
transit are sorted messages that `talk` allows, to processes already spawned. -/
private structure Calm (talk : PID → PID → Prop) (state : State) : Prop where
  alone : ∀ processId, (state.process processId).links = [] ∧ (state.process processId).monitors = []
  idle : state.timers = []
  sorted : Sorted state.inTransit
  messages : ∀ envelope ∈ state.inTransit, (∃ message, envelope.signal = .message message) ∧
    talk envelope.source envelope.target ∧ envelope.source ≠ envelope.target ∧
    Spawned state envelope.target

/-- Every process talks along the process tree, in a calm state. -/
private def Talking (talk : PID → PID → Prop) : Config α → Prop
  | .start env computation _ => computation.Talks talk env.currentPid 0
  | .running state tasks _ _ => Calm talk state ∧ ∀ entry ∈ tasks,
      entry.2.computation.Talks talk entry.1 (state.process entry.1).children

private theorem State.process_update' {state : State} {processId other : PID}
    {process : Option ProcessState} :
    (state.update processId process).process other =
      if other = processId then process.getD {} else state.process other := by
  simp only [State.process, State.update]; split <;> rfl

private theorem State.process_modify' {state : State} {processId other : PID}
    {change : ProcessState → ProcessState} :
    (state.modify processId change).process other =
      if other = processId then ((state.processes processId).map change).getD {}
      else state.process other := by
  simp only [State.process, State.processes_modify]; split <;> rfl

/-- A state with fewer processes, the same children, and fewer signals in transit stays calm. -/
private theorem Calm.of_shrinks {talk : PID → PID → Prop} {state state' : State}
    (calm : Calm talk state)
    (shrinks : ∀ processId, (state'.processes processId).isSome →
      (state.processes processId).isSome ∧
        (state'.process processId).children = (state.process processId).children)
    (alone : ∀ processId, (state'.process processId).links = [] ∧
      (state'.process processId).monitors = [])
    (idle : state'.timers = []) (sorted : Sorted state'.inTransit)
    (inTransit : ∀ envelope ∈ state'.inTransit, envelope ∈ state.inTransit) : Calm talk state' := by
  refine ⟨alone, idle, sorted, fun envelope mem => ?_⟩
  obtain ⟨message, allowed, distinct, spawned⟩ := calm.messages envelope (inTransit envelope mem)
  refine ⟨message, allowed, distinct, fun parent index rest live below => ?_⟩
  obtain ⟨live', children⟩ := shrinks parent live
  rw [children]
  exact spawned parent index rest live' below

/-- Changing records without linking keeps a state calm. -/
private theorem Calm.modify {talk : PID → PID → Prop} {state : State} {processId : PID}
    {change : ProcessState → ProcessState} (calm : Calm talk state)
    (keeps : ∀ process, (change process).links = process.links ∧
      (change process).monitors = process.monitors ∧ (change process).children = process.children) :
    Calm talk (state.modify processId change) := by
  refine calm.of_shrinks (fun other live => ?_) (fun other => ?_) (by simp [calm.idle])
    (by unfold State.modify; split <;> exact calm.sorted) (fun envelope mem => ?_)
  · rw [State.process_modify', State.processes_modify] at *
    split
    · rename_i same
      subst same
      simp only [↓reduceIte] at live
      obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp
        (by simpa using live : (state.processes other).isSome)
      simp [found, State.process, (keeps process).2.2]
    · simp_all
  · rw [State.process_modify']
    split
    · rename_i same
      subst same
      cases found : state.processes other with
      | none => simp
      | some process =>
        have := calm.alone other
        simp only [State.process, found, Option.getD_some] at this
        simp [(keeps process).1, (keeps process).2.1, this]
    · exact calm.alone other
  · unfold State.modify at mem; split at mem <;> exact mem

/-- Taking a signal out of transit keeps a state calm. -/
private theorem Calm.arrive {talk : PID → PID → Prop} {state : State} {source target : PID}
    (calm : Calm talk state) :
    Calm talk { state with inTransit := arrive source target state.inTransit } :=
  calm.of_shrinks (fun _ live => ⟨live, rfl⟩) calm.alone calm.idle (arrive_sorted calm.sorted)
    fun _ mem => mem_of_mem_arrive mem

/-- A process ending without a reason keeps a state calm. -/
private theorem Calm.remove {talk : PID → PID → Prop} {state : State} {processId : PID}
    (calm : Calm talk state) : Calm talk (state.update processId none) := by
  refine calm.of_shrinks (fun other live => ?_) (fun other => ?_) calm.idle calm.sorted
    fun _ mem => mem
  · simp only [State.processes_update] at live
    split at live
    · simp at live
    · rename_i different
      exact ⟨live, by simp [State.process_update', different]⟩
  · simp only [State.process_update']
    split
    · simp
    · exact calm.alone other

/-- A process without links or monitors ending keeps a state calm. -/
private theorem Calm.terminate {talk : PID → PID → Prop} {state : State} {processId : PID}
    {reason : Term} (calm : Calm talk state) : Calm talk (state.terminate processId reason) := by
  have empty := calm.alone processId
  have equal : state.terminate processId reason =
      { state.update processId none with timers := state.timers.filter (·.destination != processId) } := by
    simp [State.terminate, empty.1, empty.2]
  rw [equal]
  have removed := Calm.remove (talk := talk) (processId := processId) calm
  exact ⟨removed.alone, by simp [calm.idle], removed.sorted, removed.messages⟩

/-- Sending an allowed message to a spawned process keeps a state calm. -/
private theorem Calm.emit {talk : PID → PID → Prop} {state : State} {source target : PID}
    {message : Term} (calm : Calm talk state) (allowed : talk source target)
    (distinct : source ≠ target) (spawned : Spawned state target) :
    Calm talk (state.emit source target (.message message)) := by
  refine ⟨calm.alone, calm.idle, enqueue_sorted calm.sorted, fun envelope mem => ?_⟩
  rcases mem_enqueue.mp mem with rfl | mem
  · exact ⟨⟨message, rfl⟩, allowed, distinct, spawned⟩
  · exact calm.messages envelope mem

/-- Spawning a process without linking or monitoring keeps a state calm. -/
private theorem Calm.spawn {talk : PID → PID → Prop} {state : State} {processId : PID}
    (calm : Calm talk state) (live : (state.processes processId).isSome) :
    Calm talk (state.spawnWith processId {}).2 := by
  obtain ⟨childPid, -, -, children, others⟩ :=
    State.spawnWith_facts (state := state) (processId := processId) (options := {})
  have equal : (state.spawnWith processId {}).2 = (state.spawn processId).2 := by
    simp [State.spawnWith]
  have distinct : processId ≠ (state.spawnWith processId {}).1 := by
    rw [childPid]; exact ne_append_cons _ _ _
  refine ⟨fun other => ?_, by simp [equal, State.spawn, State.update, calm.idle],
    by simpa [equal, State.spawn, State.update] using calm.sorted, fun envelope mem => ?_⟩
  · rw [equal]
    simp only [State.spawn, State.process_update', Kernel.append_eq]
    split
    · simp
    · split
      · rename_i same
        subst same
        simp [calm.alone]
      · exact calm.alone other
  · have mem' : envelope ∈ state.inTransit := by simpa [equal, State.spawn, State.update] using mem
    obtain ⟨message, allowed, ne, spawned⟩ := calm.messages envelope mem'
    refine ⟨message, allowed, ne, fun parent index rest live' below => ?_⟩
    by_cases self : parent = processId
    · subst self
      rw [children]
      have := spawned parent index rest live below
      omega
    · by_cases child : parent = (state.spawnWith processId {}).1
      · exfalso
        rw [child, childPid] at below
        have := spawned processId _ (index :: rest) live (by simpa using below)
        omega
      · obtain ⟨live'', children'⟩ := others parent self child
        rw [children']
        exact spawned parent index rest (live'' ▸ live') below

/-- Processes of a well-formed configuration count the live processes below them. -/
private theorem tree_of_wellformed {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted)) {parent descendant : PID}
    {index : Nat} {rest : List Nat} (live : (state.processes parent).isSome)
    (live' : (state.processes descendant).isSome) (below : descendant = parent ++ index :: rest) :
    index ≤ (state.process parent).children := by
  have mem := wellformed.2.2.2.2 parent live
  have mem' := wellformed.2.2.2.2 descendant live'
  simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right] at mem mem'
  obtain ⟨task, mem⟩ := mem
  obtain ⟨task', mem'⟩ := mem'
  exact wellformed.2.1 (parent, task) mem (descendant, task') mem' index rest below

/-- A talking process sends to processes already spawned. -/
private theorem spawned_of_send {talk : PID → PID → Prop} (single : Single talk) {state : State}
    {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted)) {sender receiver : PID}
    (live : (state.processes sender).isSome) (allowed : talk sender receiver)
    (child : ∀ index, receiver = sender ++ [index] → index ≤ (state.process sender).children) :
    Spawned state receiver := by
  intro parent index rest live' below
  rcases single.2 _ _ allowed with ⟨more, above⟩ | ⟨last, above⟩
  · exact tree_of_wellformed wellformed live' live (rest := rest ++ more) (by rw [above, below]; simp)
  · rcases List.eq_nil_or_concat rest with rfl | ⟨rest', final, rfl⟩
    · rw [above] at below
      obtain ⟨rfl, same⟩ := List.append_inj' below rfl
      simp only [List.cons.injEq, and_true] at same
      subst same
      exact child _ above
    · rw [above, List.concat_eq_append,
        show parent ++ index :: (rest' ++ [final]) = (parent ++ index :: rest') ++ [final] by simp]
        at below
      obtain ⟨rfl, -⟩ := List.append_inj' below rfl
      exact tree_of_wellformed wellformed live' live rfl

/-- What a talking process's own step leaves keeps talking, in a calm state. -/
private theorem talks_own {talk : PID → PID → Prop} (single : Single talk) {state : State}
    {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (calm : Calm talk state)
    {processId : PID} {task : Task α} (mem : (processId, task) ∈ tasks)
    (talks : task.computation.Talks talk processId (state.process processId).children)
    {transition : Transition α} (possible : transition ∈ task.own state processId) :
    Calm talk transition.state ∧ ∀ entry ∈ transition.tasks,
      entry.2.computation.Talks talk entry.1 (transition.state.process entry.1).children := by
  have live := wellformed.2.2.1 _ mem
  obtain ⟨computation, finish⟩ := task
  dsimp only at talks
  generalize counted : (state.process processId).children = children at talks
  cases talks with
  | ok =>
    simp only [Task.own, List.mem_singleton] at possible
    subst possible
    exact ⟨calm.terminate, by simp [Task.ended]⟩
  | error =>
    rename_i exception
    cases exception <;> simp only [Task.own, List.mem_singleton] at possible <;> subst possible
    all_goals first
      | exact ⟨calm.remove, by simp⟩
      | exact ⟨calm.terminate, by simp [Task.ended]⟩
  | get next =>
    simp only [Task.own, List.mem_singleton] at possible
    subst possible
    refine ⟨calm, ?_⟩
    simp only [List.mem_singleton, forall_eq]
    rw [counted]
    exact next _ rfl
  | set same next =>
    simp only [Task.own, List.mem_singleton] at possible
    subst possible
    refine ⟨calm.modify fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
    simp only [List.mem_singleton, forall_eq]
    rename_i env _
    have : ((state.store processId env).process processId).children = children := by
      rw [← counted, State.store, State.process_modify']
      obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp live
      simp [found, State.process]
    rw [this]
    exact next
  | send allowed spawned next =>
    rename_i receiver message continuation
    simp only [Task.own, List.mem_singleton] at possible
    subst possible
    refine ⟨?_, ?_⟩
    · dsimp only
      split
      · exact calm.modify fun _ => ⟨rfl, rfl, rfl⟩
      · rename_i distinct
        exact calm.emit allowed (Ne.symm distinct)
          (spawned_of_send single wellformed live allowed (counted ▸ spawned))
    · simp only [List.mem_singleton, forall_eq]
      have : ((if receiver = processId then state.append processId message
          else state.emit processId receiver (.message message)).process processId).children =
          children := by
        rw [← counted]
        split
        · rw [State.append, State.process_modify']
          obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp live
          simp [found, State.process]
        · rfl
      rw [this]
      exact next
  | receive next =>
    simp only [Task.own] at possible
    split at possible
    · simp only [List.mem_singleton] at possible
      subst possible
      refine ⟨calm.modify fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
      simp only [List.mem_singleton, forall_eq]
      rename_i remaining _
      have : ((state.modify processId fun process => { process with mailbox := remaining }).process
          processId).children = children := by
        rw [← counted, State.process_modify']
        obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp live
        simp [found, State.process]
      rw [this]
      exact next _
    · simp at possible
  | schedule spawned next =>
    simp only [Task.own, List.mem_singleton] at possible
    subst possible
    obtain ⟨childPid, -, -, parentChildren, -⟩ :=
      State.spawnWith_facts (state := state) (processId := processId) (options := {})
    refine ⟨calm.spawn live, ?_⟩
    have childRecord : ((state.spawnWith processId {}).2.process (state.spawnWith processId {}).1).children =
        0 := by
      simp [State.spawnWith, State.spawn, State.process_update']
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [parentChildren, childRecord, childPid, counted]
    exact ⟨next, spawned⟩

/-- A message arriving keeps processes talking, in a calm state. -/
private theorem talks_delivery {talk : PID → PID → Prop} {state : State} (calm : Calm talk state)
    {processId : PID} {task : Task α} {envelope : Envelope} {rest : List Envelope}
    (delivered : (envelope, rest) ∈ deliverable state.inTransit) (target : envelope.target = processId) :
    Calm talk (task.delivery state processId envelope rest).state ∧
      (task.delivery state processId envelope rest).tasks = [(processId, task)] ∧
      state.Keeps (task.delivery state processId envelope rest).state := by
  obtain ⟨found, rfl⟩ := mem_deliverable_iff.mp delivered
  have mem : envelope ∈ state.inTransit :=
    List.mem_of_find?_eq_some (oldest_iff.mp found)
  obtain ⟨⟨message, signal⟩, -⟩ := calm.messages envelope mem
  obtain ⟨source, target', signal'⟩ := envelope
  dsimp only at signal target
  subst signal target
  simp only [Task.delivery, State.receive]
  exact ⟨(calm.arrive (source := source) (target := target')).modify fun _ => ⟨rfl, rfl, rfl⟩, trivial,
    State.keeps_inTransit.trans State.keeps_append⟩

private theorem talking_apply {talk : PID → PID → Prop} {state : State}
    {before after : List (PID × Task α)} {processId : PID} {task : Task α} {transition : Transition α}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (talks : ∀ entry ∈ before ++ (processId, task) :: after,
      entry.2.computation.Talks talk entry.1 (state.process entry.1).children)
    (calm : Calm talk transition.state)
    (own : ∀ entry ∈ transition.tasks,
      entry.2.computation.Talks talk entry.1 (transition.state.process entry.1).children)
    (others : ∀ entry ∈ before ++ after,
      (transition.state.process entry.1).children = (state.process entry.1).children) :
    Talking talk (transition.apply before after finished exhausted) := by
  refine ⟨calm, fun entry mem => ?_⟩
  simp only [Kernel.append_eq, List.mem_append] at mem
  rcases mem with (mem | mem) | mem
  · rw [others entry (by simp [mem])]
    exact talks entry (by simp [mem])
  · exact own entry mem
  · rw [others entry (by simp [mem])]
    exact talks entry (by simp [mem])

/-- Steps keep processes talking. -/
private theorem Step.talking {talk : PID → PID → Prop} (single : Single talk) {first next : Config α}
    {event : Event} (step : Step first event next) (wellformed : Wellformed first)
    (talking : Talking talk first) : Talking talk next := by
  cases first with
  | start env computation elapsed =>
    simp only [Talking] at talking
    simp only [Step, Config.successors] at step
    cases talking with
    | ok => simp [isRequest] at step
    | error => simp [isRequest] at step
    | get next =>
      simp only [List.mem_singleton, Prod.mk.injEq] at step
      obtain ⟨rfl, rfl⟩ := step
      exact next env rfl
    | set same next =>
      simp only [List.mem_singleton, Prod.mk.injEq] at step
      obtain ⟨rfl, rfl⟩ := step
      simp only [Talking, same]
      exact next
    | send | receive | schedule =>
      simp only [isRequest, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at step
      obtain ⟨rfl, rfl⟩ := step
      refine ⟨⟨fun processId => ?_, rfl, List.Pairwise.nil, by simp [State.initial]⟩, ?_⟩
      · simp only [State.initial, State.process]
        split <;> simp
      · simp only [List.mem_singleton, forall_eq]
        simp only [State.initial, State.process, ↓reduceIte, Option.getD_some, Task.root]
        constructor <;> assumption
  | running state tasks finished exhausted =>
    obtain ⟨calm, talks⟩ := talking
    obtain ⟨key, mem⟩ := Step.keyed step
    rw [mem_steps] at mem
    rcases mem with ⟨before, processId, task, after, transition, split, keyed, rfl, rfl⟩ |
      ⟨envelope, rest, delivered, dead, rfl, rfl, rfl⟩ | ⟨timer, firing, rfl, rfl, rfl⟩
    · have equal := eq_of_mem_splits split
      subst equal
      have member : (processId, task) ∈ before ++ (processId, task) :: after := by simp
      have distinct : ∀ entry ∈ before ++ after, entry.1 ≠ processId := by
        have pairs := wellformed.1
        rw [List.pairwise_append, List.pairwise_cons] at pairs
        intro entry mem
        simp only [List.mem_append] at mem
        rcases mem with mem | mem
        · exact pairs.2.2 entry mem (processId, task) (by simp)
        · exact fun same => pairs.2.1.1 entry mem same.symm
      rw [mem_keyed] at keyed
      rcases keyed with ⟨index, -, own⟩ | ⟨envelope, rest, delivered, target, -, rfl⟩
      · have possible := List.mem_of_getElem? own
        obtain ⟨calm', own'⟩ := talks_own single wellformed calm member (talks _ member) possible
        refine talking_apply talks calm' own' fun entry mem => ?_
        have possible' : transition ∈ task.transitions state processId :=
          List.mem_append_left _ possible
        refine ((transition_facts possible' (wellformed.2.2.1 _ member)).1 entry.1
          (distinct entry mem) fun child spawn same => ?_).2
        refine child_fresh wellformed member possible' spawn ?_
        rw [← same]
        simp only [List.mem_map, List.mem_append, List.mem_cons]
        simp only [List.mem_append] at mem
        exact ⟨entry, by rcases mem with mem | mem <;> simp [mem], rfl⟩
      · obtain ⟨calm', tasksEq, kept⟩ := talks_delivery (task := task) calm delivered target
        refine talking_apply talks calm' ?_ fun entry _ => (kept entry.1).2
        rw [tasksEq]
        simp only [List.mem_singleton, forall_eq]
        rw [(kept processId).2]
        exact talks _ member
    · obtain ⟨found, rfl⟩ := mem_deliverable_iff.mp delivered
      obtain ⟨⟨message, signal⟩, -⟩ := calm.messages envelope
        (List.mem_of_find?_eq_some (oldest_iff.mp found))
      simp only [State.bounce, signal]
      exact ⟨calm.arrive, talks⟩
    · simp [State.firing, calm.idle, firstOfEach] at firing

/-! ### Steps of talking processes commute -/

private theorem agree_of {observes : Observes} {effect : Effect} {state : State}
    (records : ∀ entry ∈ observes.records,
      (effect.record entry.1 (state.processes entry.1)).map entry.2 = (state.processes entry.1).map entry.2)
    (timers : observes.timers = [])
    (inTransit : ∀ view ∈ observes.inTransit,
      view ((effect.inTransit.getD id) state.inTransit) = view state.inTransit) :
    observes.Agree state (effect.apply state) :=
  ⟨records, by simp [timers], inTransit, rfl⟩

private theorem apply_comm_of {first second : Effect} {state : State}
    (records : ∀ processId, first.record processId (second.record processId (state.processes processId)) =
      second.record processId (first.record processId (state.processes processId)))
    (timers : (first.timers.getD id) ((second.timers.getD id) state.timers) =
      (second.timers.getD id) ((first.timers.getD id) state.timers))
    (inTransit : (first.inTransit.getD id) ((second.inTransit.getD id) state.inTransit) =
      (second.inTransit.getD id) ((first.inTransit.getD id) state.inTransit)) :
    first.apply (second.apply state) = second.apply (first.apply state) :=
  State.ext' (funext records) timers inTransit rfl

/-- Two steps whose effects keep what the other observes and commute meet again. -/
private theorem square_of {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {event event' : Event} {next next' : Config α} {footprint footprint' : Footprint}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key', event', next') ∈ (Config.running state tasks finished exhausted).steps)
    (distinct : key ≠ key')
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint)
    (found' : (Config.running state tasks finished exhausted).footprint key' = some footprint')
    (agree : footprint'.observes.Agree state (footprint.effect.apply state))
    (agree' : footprint.observes.Agree state (footprint'.effect.apply state))
    (commutes : footprint.effect.apply (footprint'.effect.apply state) =
      footprint'.effect.apply (footprint.effect.apply state)) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  obtain ⟨move, moved⟩ := moves wellformed mem found
  obtain ⟨move', moved'⟩ := moves wellformed mem' found'
  have pair : Pair state tasks finished exhausted key key' footprint footprint' move move' :=
    ⟨wellformed, found, found', ⟨_, _, moved⟩, ⟨_, _, moved'⟩, distinct, agree, agree'⟩
  obtain ⟨last, forth, back⟩ := pair.square moved moved' commutes mem mem'
  exact ⟨last, ⟨_, Step.of_mem_steps forth⟩, ⟨_, Step.of_mem_steps back⟩⟩

/-- Whether a process returns or raises next. -/
private def Task.ends (task : Task α) : Bool :=
  match task.computation with
  | .ok _ | .error _ => true
  | _ => false

/-- What a talking process's own step observes and does: it observes its own
record; changes its own record and the record of the child it spawns; sends at
most one message, to another process; and, unless it ends or may send to
itself, commutes with a message arriving. -/
private structure OwnShape (talk : PID → PID → Prop) (state : State) (processId : PID)
    (task : Task α) : Prop where
  view : ∃ view, (task.footprint state processId).observes = Observes.record processId view
  timers : ((task.footprint state processId).effect.timers.getD id) [] = []
  others : ∀ other, other ≠ processId → other ≠ processId ++ [(state.process processId).children + 1] →
    (task.footprint state processId).effect.record other = id
  sends : (∀ inTransit, ((task.footprint state processId).effect.inTransit.getD id) inTransit = inTransit) ∨
    ∃ receiver message, receiver ≠ processId ∧ ∀ inTransit,
      ((task.footprint state processId).effect.inTransit.getD id) inTransit =
        enqueue ⟨processId, receiver, .message message⟩ inTransit
  survives : talk processId processId ∨ task.ends ∨ ∀ process message,
    state.processes processId = some process →
    (task.footprint state processId).effect.record processId (some (process.append message)) =
      ((task.footprint state processId).effect.record processId (some process)).map
        (ProcessState.append message) ∧
    ((task.footprint state processId).effect.record processId (some process)).isSome ∧
    ∀ view, (task.footprint state processId).observes = Observes.record processId view →
      view (process.append message) = view process

private theorem record_cons_ne {processId other : PID} {change : Option ProcessState → Option ProcessState}
    {rest : List (PID × (Option ProcessState → Option ProcessState))} {timers inTransit}
    (different : other ≠ processId) :
    ({ records := (processId, change) :: rest, timers, inTransit } : Effect).record other =
      ({ records := rest } : Effect).record other := by
  have : (processId == other) = false := by simpa using Ne.symm different
  simp [Effect.record, this]

private theorem record_cons_self {processId : PID} {change : Option ProcessState → Option ProcessState}
    {rest : List (PID × (Option ProcessState → Option ProcessState))} {timers inTransit} :
    ({ records := (processId, change) :: rest, timers, inTransit } : Effect).record processId = change := by
  simp [Effect.record]

private theorem record_nil {other : PID} {timers inTransit} :
    ({ records := [], timers, inTransit } : Effect).record other = id := rfl

private theorem own_shape {talk : PID → PID → Prop} {state : State} {processId : PID}
    {task : Task α} {children : Nat}
    (alone : (state.process processId).links = [] ∧ (state.process processId).monitors = [])
    (talks : task.computation.Talks talk processId children)
    (enabled : 0 < (task.own state processId).length) : OwnShape talk state processId task := by
  obtain ⟨computation, finish⟩ := task
  dsimp only at talks
  cases talks with
  | ok =>
    refine ⟨⟨_, rfl⟩, rfl, fun other different _ => ?_, .inl fun inTransit => ?_, .inr (.inl rfl)⟩
    · simp only [Task.footprint, Footprint.ending, Effect.ending, Kernel.filter_eq,
        Kernel.foldl_eq]
      exact record_cons_ne different
    · simp [Task.footprint, Footprint.ending, Effect.ending, alone.1, alone.2]
  | error =>
    rename_i exception
    cases exception
    all_goals first
      | refine ⟨⟨_, rfl⟩, rfl, fun other different _ => ?_, .inl fun inTransit => ?_, .inr (.inl rfl)⟩
        · simp only [Task.footprint, Footprint.ending, Effect.ending, Kernel.filter_eq,
            Kernel.foldl_eq]
          exact record_cons_ne different
        · simp [Task.footprint, Footprint.ending, Effect.ending, alone.1, alone.2]
      | refine ⟨⟨_, rfl⟩, rfl, fun other different _ => ?_, .inl fun inTransit => rfl, .inr (.inl rfl)⟩
        simp only [Task.footprint]
        exact record_cons_ne different
  | get =>
    refine ⟨⟨_, rfl⟩, rfl, fun _ _ _ => rfl, .inl fun _ => rfl, .inr (.inr ?_)⟩
    intro process message _
    exact ⟨rfl, rfl, fun view same => by
      simp only [Task.footprint, Observes.record, Observes.mk.injEq, List.cons.injEq, Prod.mk.injEq,
        true_and, and_true] at same
      subst same; rfl⟩
  | set =>
    refine ⟨⟨_, rfl⟩, rfl, fun other different _ => ?_, .inl fun _ => rfl, .inr (.inr ?_)⟩
    · simp only [Task.footprint, Effect.change]
      exact record_cons_ne different
    · intro process message _
      simp only [Task.footprint, Effect.change, record_cons_self]
      exact ⟨rfl, rfl, fun view same => by
        simp only [Observes.record, Observes.mk.injEq, List.cons.injEq, Prod.mk.injEq,
          true_and, and_true] at same
        subst same; rfl⟩
  | send allowed spawned next =>
    rename_i receiver message continuation
    by_cases self : receiver = processId
    · subst self
      refine ⟨⟨_, rfl⟩, by simp [Task.footprint, Effect.change], fun other different _ => ?_,
        .inl fun _ => by simp [Task.footprint, Effect.change], .inl allowed⟩
      simp only [Task.footprint, ↓reduceIte, Effect.change]
      exact record_cons_ne different
    · refine ⟨⟨_, rfl⟩, by simp [Task.footprint, self, Effect.send], fun other _ _ => ?_,
        .inr ⟨receiver, message, self, fun _ => by simp [Task.footprint, self, Effect.send]⟩,
        .inr (.inr ?_)⟩
      · simp [Task.footprint, self, Effect.send, record_nil]
      · intro process message' _
        simp only [Task.footprint, self, ↓reduceIte, Effect.send, record_nil, id]
        exact ⟨rfl, rfl, fun view same => by
          simp only [Observes.record, Observes.mk.injEq, List.cons.injEq, Prod.mk.injEq,
            true_and, and_true] at same
          subst same; rfl⟩
  | receive =>
    rename_i select continuation next
    have matched : (selectMessage (select (state.view processId)) (state.process processId).mailbox).isSome := by
      simp only [Task.own] at enabled
      split at enabled
      · rename_i found; simp [found]
      · simp at enabled
    obtain ⟨⟨message, value, rest⟩, found⟩ := Option.isSome_iff_exists.mp matched
    refine ⟨⟨_, rfl⟩, by simp [Task.footprint, found, Effect.change], fun other different _ => ?_,
      .inl fun _ => by simp [Task.footprint, found, Effect.change], .inr (.inr ?_)⟩
    · simp only [Task.footprint, found, Effect.change]
      exact record_cons_ne different
    · intro process message' record
      have mailbox : (state.process processId).mailbox = process.mailbox := by
        simp [State.process, record]
      rw [mailbox] at matched
      obtain ⟨selectedEq, remainingEq, -⟩ := selectMessage_append (extra := [message']) matched
      simp only [Task.footprint, found, Effect.change, record_cons_self, Option.map_some,
        Option.isSome_some, Option.some.injEq, true_and]
      refine ⟨by simp [ProcessState.append, remainingEq], fun view same => ?_⟩
      simp only [Observes.record, Observes.mk.injEq, List.cons.injEq, Prod.mk.injEq,
        true_and, and_true] at same
      subst same
      simp [ProcessState.append, selectedEq]
  | schedule =>
    refine ⟨⟨_, rfl⟩, rfl, fun other different notChild => ?_, .inl fun _ => rfl, .inr (.inr ?_)⟩
    · simp only [Task.footprint, Footprint.spawn, Kernel.append_eq]
      rw [record_cons_ne different, record_cons_ne notChild]
      rfl
    · intro process message _
      simp only [Task.footprint, Footprint.spawn, record_cons_self, Kernel.append_eq]
      exact ⟨rfl, rfl, fun view same => by
        simp only [Observes.record, Observes.mk.injEq, List.cons.injEq, Prod.mk.injEq,
          true_and, and_true] at same
        subst same; rfl⟩

/-- The footprint of a message arriving. -/
private theorem delivery_message {state : State} {envelope : Envelope} {message : Term}
    (signal : envelope.signal = .message message) :
    Footprint.delivery state envelope =
      { observes := { records := [(envelope.target, ProcessState.live)],
                      inTransit := [oldest envelope.source envelope.target] }
        effect := { records := [(envelope.target, Option.map (ProcessState.append message))],
                    inTransit := some (arrive envelope.source envelope.target) }
        frames := some [(envelope.target, [.mailbox], [.mailbox])] } := by
  obtain ⟨source, target, signal'⟩ := envelope
  dsimp only at signal
  subst signal
  rfl

/-- The footprint of a message reaching a process that is not live. -/
private theorem bounce_message {envelope : Envelope} {message : Term}
    (signal : envelope.signal = .message message) :
    Footprint.bounce envelope =
      { observes := { records := [(envelope.target, ProcessState.live)],
                      inTransit := [oldest envelope.source envelope.target] }
        effect := { inTransit := some (arrive envelope.source envelope.target) }
        frames := some [(envelope.target, [], [])] } := by
  obtain ⟨source, target, signal'⟩ := envelope
  dsimp only at signal
  subst signal
  rfl

/-- The oldest signal of a pair stays when any signal is sent. -/
private theorem oldest_enqueue {source target : PID} {inTransit : List Envelope} {oldestFound : Envelope}
    (sorted : Sorted inTransit) (found : inTransit.find? (Envelope.between source target) = some oldestFound)
    (envelope : Envelope) : oldest source target (enqueue envelope inTransit) = oldest source target inTransit := by
  simp only [oldest, Kernel.find?_eq]
  by_cases same : envelope.pair = (source, target)
  · rw [find?_enqueue_same same sorted found, found]
  · rw [find?_enqueue_other same]

private theorem oldest_arrive {source target source' target' : PID}
    (distinct : (source, target) ≠ (source', target')) (inTransit : List Envelope) :
    oldest source target (arrive source' target' inTransit) = oldest source target inTransit := by
  simp only [oldest, Kernel.find?_eq]; rw [find?_arrive_other distinct]

/-- The child a live process spawns next is not live yet. -/
private theorem child_dead {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted)) {processId : PID}
    (live : (state.processes processId).isSome) :
    state.processes (processId ++ [(state.process processId).children + 1]) = none := by
  cases found : state.processes (processId ++ [(state.process processId).children + 1]) with
  | none => rfl
  | some _ =>
    have := tree_of_wellformed wellformed live (descendant := processId ++ [(state.process processId).children + 1])
      (by simp [found]) (rest := []) rfl
    omega

/-- A process's own step leaves the record of other live processes. -/
private theorem OwnShape.live {talk : PID → PID → Prop} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId other : PID} {task : Task α}
    (shape : OwnShape talk state processId task)
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (live : (state.processes processId).isSome) (different : other ≠ processId)
    (live' : (state.processes other).isSome) : (task.footprint state processId).effect.record other = id :=
  shape.others other different fun same => by
    rw [same, child_dead wellformed live] at live'
    contradiction

/-- A process's own step leaves the record of a process that it does not
spawn and that is not live. -/
private theorem OwnShape.spawned {talk : PID → PID → Prop} {state : State} {processId other : PID}
    {task : Task α} (shape : OwnShape talk state processId task)
    (live : (state.processes processId).isSome) (dead : state.processes other = none)
    (spawned : Spawned state other) : (task.footprint state processId).effect.record other = id := by
  refine shape.others other (fun same => by rw [← same, dead] at live; contradiction) fun same => ?_
  have := spawned processId _ [] live same
  omega

/-- What a process's own step observes stays when an effect leaves its record. -/
private theorem OwnShape.agree {talk : PID → PID → Prop} {state : State} {processId : PID}
    {task : Task α} {effect : Effect} (shape : OwnShape talk state processId task)
    (unchanged : ∀ view, (task.footprint state processId).observes = Observes.record processId view →
      (effect.record processId (state.processes processId)).map view = (state.processes processId).map view) :
    (task.footprint state processId).observes.Agree state (effect.apply state) := by
  obtain ⟨view, observes⟩ := shape.view
  rw [observes]
  exact agree_of (fun entry mem => by
    simp only [Observes.record, List.mem_singleton] at mem
    subst mem; exact unchanged _ observes) rfl (by simp [Observes.record])

private theorem comm_of_id {first second : γ → γ} (identity : first = id ∨ second = id) (item : γ) :
    first (second item) = second (first item) := by
  rcases identity with rfl | rfl <;> rfl

/-- How a talking process's own step changes the signals in transit, with a
change of another pair. -/
private theorem OwnShape.transit_comm {talk : PID → PID → Prop} {state : State} {processId : PID}
    {task : Task α} (shape : OwnShape talk state processId task) {change : List Envelope → List Envelope}
    (commutes : ∀ receiver message, receiver ≠ processId →
      change (enqueue ⟨processId, receiver, .message message⟩ state.inTransit) =
        enqueue ⟨processId, receiver, .message message⟩ (change state.inTransit)) :
    ((task.footprint state processId).effect.inTransit.getD id) (change state.inTransit) =
      change (((task.footprint state processId).effect.inTransit.getD id) state.inTransit) := by
  rcases shape.sends with same | ⟨receiver, message, different, sent⟩
  · rw [same, same]
  · rw [sent, sent, commutes receiver message different]

private theorem OwnShape.oldest {talk : PID → PID → Prop} {state : State} {processId : PID}
    {task : Task α} (shape : OwnShape talk state processId task) {source target : PID}
    {oldestFound : Envelope} (sorted : Sorted state.inTransit)
    (found : state.inTransit.find? (Envelope.between source target) = some oldestFound) :
    oldest source target (((task.footprint state processId).effect.inTransit.getD id) state.inTransit) =
      oldest source target state.inTransit := by
  rcases shape.sends with same | ⟨receiver, message, different, sent⟩
  · rw [same]
  · rw [sent, oldest_enqueue sorted found]

private theorem OwnShape.timers_comm {talk : PID → PID → Prop} {state : State} {processId : PID}
    {task : Task α} (shape : OwnShape talk state processId task) (idle : state.timers = [])
    {change : Option (List Timer → List Timer)} (empty : (change.getD id) [] = []) :
    ((task.footprint state processId).effect.timers.getD id) ((change.getD id) state.timers) =
      (change.getD id) (((task.footprint state processId).effect.timers.getD id) state.timers) := by
  rw [idle, empty, shape.timers, empty]

/-- Own steps of different talking processes commute. -/
private theorem own_own {talk : PID → PID → Prop} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId other : PID}
    {task task' : Task α} {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (calm : Calm talk state)
    (distinct : processId ≠ other)
    (shape : OwnShape talk state processId task) (shape' : OwnShape talk state other task')
    (found : tasks.lookup processId = some task) (found' : tasks.lookup other = some task')
    (enabled : 0 < (task.own state processId).length) (enabled' : 0 < (task'.own state other).length)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (.own other 0, event', next') ∈ (Config.running state tasks finished exhausted).steps) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  have live := live_of_lookup wellformed (processId := processId) (by simp [found])
  have live' := live_of_lookup wellformed (processId := other) (by simp [found'])
  have recordId := shape.live wellformed live (Ne.symm distinct) live'
  have recordId' := shape'.live wellformed live' distinct live
  refine square_of wellformed mem mem' (by simp [distinct]) (by simp [Config.footprint, found, enabled])
    (by simp [Config.footprint, found', enabled']) (shape'.agree fun _ _ => by rw [recordId]; rfl)
    (shape.agree fun _ _ => by rw [recordId']; rfl) (apply_comm_of (fun candidate => ?_)
      (shape.timers_comm calm.idle shape'.timers) (shape.transit_comm fun receiver message _ => ?_))
  · by_cases mine : candidate = processId ∨ candidate = processId ++ [(state.process processId).children + 1]
    · refine comm_of_id (.inr ?_) _
      rcases mine with rfl | rfl
      · exact recordId'
      · refine shape'.others _ (fun same => ?_) fun same => ?_
        · rw [← same, child_dead wellformed live] at live'; contradiction
        · have := congrArg List.dropLast same
          simp only [List.dropLast_concat] at this
          exact distinct this
    · simp only [not_or] at mine
      exact comm_of_id (.inl (shape.others _ mine.1 mine.2)) _
  · rcases shape'.sends with same | ⟨receiver', message', _, sent⟩
    · rw [same, same]
    · rw [sent, sent]
      exact enqueue_comm (fun same => distinct (by simpa [Envelope.pair] using (congrArg Prod.fst same).symm)) _

/-- What a signal arriving or bouncing observes and does: it observes whether
its receiver is live and the oldest signal of its pair, changes at most the
receiver's record, keeping whether it is live, and takes the signal out of
transit. -/
private structure SignalShape (state : State) (source target : PID) (footprint : Footprint) : Prop where
  observes : footprint.observes =
    { records := [(target, ProcessState.live)], inTransit := [oldest source target] }
  others : ∀ other, other ≠ target → footprint.effect.record other = id
  live : ∀ record, (footprint.effect.record target record).map ProcessState.live =
    record.map ProcessState.live
  timers : footprint.effect.timers = none
  inTransit : footprint.effect.inTransit = some (arrive source target)
  found : (state.inTransit.find? (Envelope.between source target)).isSome

private theorem delivery_shape {state : State} {envelope : Envelope} {message : Term}
    (signal : envelope.signal = .message message)
    (found : state.inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope) :
    SignalShape state envelope.source envelope.target (Footprint.delivery state envelope) := by
  rw [delivery_message signal]
  refine ⟨rfl, fun other different => ?_, fun record => ?_, rfl, rfl, by simp [found]⟩
  · dsimp only; rw [record_cons_ne different]; rfl
  · dsimp only; rw [record_cons_self]; cases record <;> rfl

private theorem bounce_shape {state : State} {envelope : Envelope} {message : Term}
    (signal : envelope.signal = .message message)
    (found : state.inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope) :
    SignalShape state envelope.source envelope.target (Footprint.bounce envelope) := by
  rw [bounce_message signal]
  exact ⟨rfl, fun _ _ => rfl, fun _ => rfl, rfl, rfl, by simp [found]⟩

private theorem SignalShape.agree {state : State} {source target : PID} {footprint : Footprint}
    {effect : Effect} (shape : SignalShape state source target footprint)
    (live : (effect.record target (state.processes target)).map ProcessState.live =
      (state.processes target).map ProcessState.live)
    (oldestKept : oldest source target ((effect.inTransit.getD id) state.inTransit) =
      oldest source target state.inTransit) :
    footprint.observes.Agree state (effect.apply state) := by
  rw [shape.observes]
  exact agree_of (fun entry mem => by simp only [List.mem_singleton] at mem; subst mem; exact live) rfl
    (fun view mem => by simp only [List.mem_singleton] at mem; subst mem; exact oldestKept)

/-- Signals of different pairs commute. -/
private theorem signal_signal {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key key' : Key}
    {event event' : Event} {next next' : Config α} {footprint footprint' : Footprint}
    {source target source' target' : PID}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key', event', next') ∈ (Config.running state tasks finished exhausted).steps)
    (distinct : key ≠ key')
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint)
    (found' : (Config.running state tasks finished exhausted).footprint key' = some footprint')
    (shape : SignalShape state source target footprint)
    (shape' : SignalShape state source' target' footprint')
    (pairs : (source, target) ≠ (source', target'))
    (apart : ∀ other, footprint.effect.record other = id ∨ footprint'.effect.record other = id) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  have keeps : ∀ {source target source' target' : PID} {footprint footprint' : Footprint},
      SignalShape state source target footprint → SignalShape state source' target' footprint' →
      (source, target) ≠ (source', target') →
      footprint'.observes.Agree state (footprint.effect.apply state) := by
    intro source target source' target' footprint footprint' shape shape' pairs
    refine shape'.agree ?_ ?_
    · by_cases same : target' = target
      · subst same; exact shape.live _
      · rw [shape.others _ same]; rfl
    · simp only [shape.inTransit, Option.getD_some]
      exact oldest_arrive (Ne.symm pairs) _
  refine square_of wellformed mem mem' distinct found found' (keeps shape shape' pairs)
    (keeps shape' shape (Ne.symm pairs)) (apply_comm_of (fun other => comm_of_id (apart other) _)
      (by simp [shape.timers, shape'.timers]) ?_)
  simp only [shape.inTransit, shape'.inTransit, Option.getD_some]
  exact arrive_comm pairs _

/-- A process's own step commutes with a signal it keeps and whose receiver's
record it commutes with. -/
private theorem own_signal {talk : PID → PID → Prop} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID} {task : Task α}
    {key : Key} {event event' : Event} {next next' : Config α} {footprint : Footprint}
    {source target : PID}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (calm : Calm talk state)
    (shape : OwnShape talk state processId task) (found : tasks.lookup processId = some task)
    (enabled : 0 < (task.own state processId).length)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key, event', next') ∈ (Config.running state tasks finished exhausted).steps)
    (distinct : Key.own processId 0 ≠ key)
    (found' : (Config.running state tasks finished exhausted).footprint key = some footprint)
    (shape' : SignalShape state source target footprint)
    (live : ((task.footprint state processId).effect.record target (state.processes target)).map
      ProcessState.live = (state.processes target).map ProcessState.live)
    (unchanged : ∀ view, (task.footprint state processId).observes = Observes.record processId view →
      (footprint.effect.record processId (state.processes processId)).map view =
        (state.processes processId).map view)
    (records : ∀ other, (task.footprint state processId).effect.record other
        (footprint.effect.record other (state.processes other)) =
      footprint.effect.record other ((task.footprint state processId).effect.record other
        (state.processes other))) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  obtain ⟨oldestFound, oldestFoundEq⟩ := Option.isSome_iff_exists.mp shape'.found
  refine square_of wellformed mem mem' distinct (by simp [Config.footprint, found, enabled]) found'
    (shape'.agree live (shape.oldest calm.sorted oldestFoundEq)) (shape.agree unchanged)
    (apply_comm_of records (shape.timers_comm calm.idle (by simp [shape'.timers])) ?_)
  simp only [shape'.inTransit, Option.getD_some]
  exact shape.transit_comm fun receiver message _ =>
    arrive_enqueue calm.sorted (.inr (by simp [oldestFoundEq]))

/-- A process without links, monitors, or timers ends by removing its record. -/
private theorem terminate_alone {state : State} {processId : PID} {reason : Term}
    (links : (state.process processId).links = []) (monitors : (state.process processId).monitors = [])
    (idle : state.timers = []) : state.terminate processId reason = state.update processId none := by
  simp only [State.terminate, links, monitors, List.foldl_nil, Kernel.filter_eq, Kernel.foldl_eq]
  exact State.ext' rfl (by simp [State.update, idle]) rfl rfl

/-- A process that returns or raises next ends the same way from any state
where it has no links, monitors, or timers. -/
private theorem ends_own {task : Task α} {processId : PID} (ends : task.ends = true) :
    ∃ event finished exhausted, ∀ state : State, (state.process processId).links = [] →
      (state.process processId).monitors = [] → state.timers = [] →
      task.own state processId =
        [{ event, state := state.update processId none, tasks := [], finished, exhausted }] := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | ok value =>
    refine ⟨.exit processId (.atom "normal"), finish (.ok value), false,
      fun state links monitors idle => ?_⟩
    simp [Task.own, Task.ended, terminate_alone links monitors idle]
  | error exception =>
    by_cases exhaustedCase : exception = .exhausted
    · subst exhaustedCase
      exact ⟨_, none, true, fun _ _ _ _ => rfl⟩
    · refine ⟨.exit processId (exitReason exception), finish (.error exception), false,
        fun state links monitors idle => ?_⟩
      cases exception with
      | exhausted => contradiction
      | _ => simp [Task.own, Task.ended, terminate_alone links monitors idle]
  | _ => simp [Task.ends] at ends

private theorem lookup_split {before after : List (PID × Task α)} {processId : PID} {task : Task α}
    (distinct : (before ++ (processId, task) :: after).Pairwise fun first second => first.1 ≠ second.1) :
    (before ++ after).lookup processId = none := by
  rw [List.pairwise_append, List.pairwise_cons] at distinct
  refine lookup_none fun found => ?_
  simp only [List.map_append, List.mem_append, List.mem_map, Prod.exists, exists_and_right,
    exists_eq_right] at found
  rcases found with ⟨task', mem⟩ | ⟨task', mem⟩
  · exact distinct.2.2 _ mem (processId, task) (by simp) rfl
  · exact distinct.2.1.1 _ mem rfl

/-- A message reaching a process that ends next: taking it, then ending, meets
ending, then the message bouncing. -/
private theorem deliver_ends {talk : PID → PID → Prop} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {processId : PID} {task : Task α}
    {envelope : Envelope} {message : Term} {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (calm : Calm talk state)
    (found : tasks.lookup processId = some task) (ends : task.ends = true)
    (signal : envelope.signal = .message message) (target : envelope.target = processId)
    (oldestFound : state.inTransit.find? (Envelope.between envelope.source processId) = some envelope)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (.deliver envelope.source processId, event', next') ∈
      (Config.running state tasks finished exhausted).steps) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  obtain ⟨endEvent, endFinished, endExhausted, own⟩ := ends_own (processId := processId) ends
  obtain ⟨before, after, transition, rfl, possible, -, rfl⟩ := local_step wellformed found mem
  obtain ⟨links, monitors⟩ := calm.alone processId
  rw [own state links monitors calm.idle, List.mem_singleton] at possible
  subst possible
  have delivered : (envelope, arrive envelope.source processId state.inTransit) ∈
      deliverable state.inTransit := by
    rw [mem_deliverable_iff, target]
    exact ⟨oldest_iff.mpr oldestFound, rfl⟩
  have expected : (Key.deliver envelope.source processId,
      (task.delivery state processId envelope (arrive envelope.source processId state.inTransit)).event,
      (task.delivery state processId envelope (arrive envelope.source processId state.inTransit)).apply
        before after finished exhausted) ∈
      (Config.running state (before ++ (processId, task) :: after) finished exhausted).steps :=
    mem_steps.mpr (.inl ⟨before, processId, task, after, _, mem_splits,
      mem_keyed.mpr (.inr ⟨envelope, _, delivered, target, rfl, rfl⟩), rfl, rfl⟩)
  obtain ⟨-, rfl⟩ := steps_unique wellformed mem' expected
  -- Taking the message keeps the process without links, monitors, or timers.
  let rest := arrive envelope.source processId state.inTransit
  let received := ({ state with inTransit := rest }.append processId message)
  have delivery : task.delivery state processId envelope rest =
      { event := .deliver envelope, state := received, tasks := [(processId, task)] } := by
    simp [Task.delivery, State.receive, signal, target, received]
  have receivedLinks : (received.process processId).links = [] := by
    simp only [received, State.append, State.process_modify', ↓reduceIte, Kernel.append_eq]
    cases found : state.processes processId <;> simp_all [State.process]
  have receivedMonitors : (received.process processId).monitors = [] := by
    simp only [received, State.append, State.process_modify', ↓reduceIte, Kernel.append_eq]
    cases found : state.processes processId <;> simp_all [State.process]
  have receivedIdle : received.timers = [] := by simp [received, State.append, calm.idle]
  have same : received.update processId none = { state.update processId none with inTransit := rest } := by
    refine State.ext' (funext fun other => ?_) ?_ ?_ ?_
    rotate_left
    all_goals try (simp only [received, State.append, State.modify, State.update,
        Kernel.append_eq]; split <;> rfl)
    simp only [State.processes_update, received, State.append, State.processes_modify,
        Kernel.append_eq]
    split <;> simp_all
  have dead := lookup_split (wellformed.1)
  refine ⟨.running { state.update processId none with inTransit := rest } (before ++ after)
    (endFinished.orElse fun _ => finished) (exhausted || endExhausted), ⟨.bounce envelope, ?_⟩,
    ⟨endEvent, ?_⟩⟩
  · refine Step.of_mem_steps (key := .bounce envelope.source envelope.target) ?_
    refine mem_steps.mpr (.inr (.inl ⟨envelope, rest, delivered, by simp [target, dead], rfl, rfl, ?_⟩))
    simp [State.bounce, signal]
  · rw [delivery]
    refine Step.of_mem_steps (key := .own processId 0) ?_
    have split : (before, (processId, task), after) ∈
        splits (Kernel.append (Kernel.append before [(processId, task)]) after) := by
      simpa using (mem_splits (before := before) (item := (processId, task)) (after := after))
    refine mem_steps.mpr (.inl ⟨before, processId, task, after, _, split,
      mem_keyed.mpr (.inl ⟨0, rfl, by rw [own received receivedLinks receivedMonitors receivedIdle]; rfl⟩),
      rfl, ?_⟩)
    simp [Transition.apply, same]

/-- What the step with a key of a talking configuration is. -/
private theorem footprint_cases {talk : PID → PID → Prop} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {key : Key} {footprint : Footprint}
    (calm : Calm talk state)
    (found : (Config.running state tasks finished exhausted).footprint key = some footprint) :
    (∃ processId task, key = .own processId 0 ∧ tasks.lookup processId = some task ∧
      0 < (task.own state processId).length ∧ footprint = task.footprint state processId) ∨
    (∃ envelope message task, key = .deliver envelope.source envelope.target ∧
      envelope.signal = .message message ∧ tasks.lookup envelope.target = some task ∧
      state.inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope ∧
      footprint = Footprint.delivery state envelope) ∨
    (∃ envelope message, key = .bounce envelope.source envelope.target ∧
      envelope.signal = .message message ∧ tasks.lookup envelope.target = none ∧
      state.inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope ∧
      footprint = Footprint.bounce envelope) := by
  cases key with
  | own processId index =>
    simp only [Config.footprint, Kernel.lookup_eq, Kernel.length_eq] at found
    split at found
    · rename_i task lookup
      split at found
      · rename_i bound
        simp only [Option.some.injEq] at found
        have : index = 0 := by have := Task.own_length (state := state) (processId := processId) (task := task); omega
        subst this
        exact .inl ⟨processId, task, rfl, lookup, bound, found.symm⟩
      · simp at found
    · simp at found
  | deliver source target =>
    simp only [Config.footprint, Kernel.lookup_eq, Kernel.find?_eq] at found
    split at found
    · rename_i task envelope lookup oldestFound
      simp only [Option.some.injEq] at found
      obtain ⟨rfl, rfl⟩ := between_of_find oldestFound
      obtain ⟨⟨message, signal⟩, -⟩ := calm.messages envelope (List.mem_of_find?_eq_some oldestFound)
      exact .inr (.inl ⟨envelope, message, task, rfl, signal, lookup, oldestFound, found.symm⟩)
    · simp at found
  | bounce source target =>
    simp only [Config.footprint, Kernel.lookup_eq, Kernel.find?_eq] at found
    split at found
    · rename_i envelope lookup oldestFound
      simp only [Option.some.injEq] at found
      obtain ⟨rfl, rfl⟩ := between_of_find oldestFound
      obtain ⟨⟨message, signal⟩, -⟩ := calm.messages envelope (List.mem_of_find?_eq_some oldestFound)
      exact .inr (.inr ⟨envelope, message, rfl, signal, lookup, oldestFound, found.symm⟩)
    · simp at found
  | fire reference =>
    simp [Config.footprint, calm.idle] at found

private theorem delivery_record {state : State} {envelope : Envelope} {message : Term}
    (signal : envelope.signal = .message message) (other : PID) :
    (Footprint.delivery state envelope).effect.record other =
      if other = envelope.target then Option.map (ProcessState.append message) else id := by
  rw [delivery_message signal]
  dsimp only
  split
  · rename_i same; subst same; exact record_cons_self
  · rename_i different; rw [record_cons_ne different]; rfl

/-- A talking process's own step and a message arriving meet again. -/
private theorem own_deliver {talk : PID → PID → Prop} (single : Single talk) {state : State}
    {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    {processId : PID} {task task' : Task α} {envelope : Envelope} {message : Term}
    {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (calm : Calm talk state)
    (talks : ∀ entry ∈ tasks, entry.2.computation.Talks talk entry.1 (state.process entry.1).children)
    (found : tasks.lookup processId = some task) (enabled : 0 < (task.own state processId).length)
    (signal : envelope.signal = .message message) (found' : tasks.lookup envelope.target = some task')
    (oldestFound : state.inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (.deliver envelope.source envelope.target, event', next') ∈
      (Config.running state tasks finished exhausted).steps) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  have shape := own_shape (calm.alone processId) (talks _ (mem_of_lookup found)) enabled
  have shape' := delivery_shape (state := state) signal oldestFound
  have live := live_of_lookup wellformed (processId := processId) (by simp [found])
  have live' := live_of_lookup wellformed (processId := envelope.target) (by simp [found'])
  have footprint' : (Config.running state tasks finished exhausted).footprint
      (.deliver envelope.source envelope.target) = some (Footprint.delivery state envelope) := by
    simp [Config.footprint, found', oldestFound]
  obtain ⟨-, allowed, ne, -⟩ := calm.messages envelope (List.mem_of_find?_eq_some oldestFound)
  by_cases same : envelope.target = processId
  · rcases shape.survives with self | ends | facts
    · exact absurd (single.1 _ _ _ allowed (same ▸ self)) (same ▸ ne)
    · rw [same] at mem' oldestFound
      exact deliver_ends wellformed calm found ends signal same oldestFound mem mem'
    · obtain ⟨process, record⟩ := Option.isSome_iff_exists.mp live
      obtain ⟨appended, kept, views⟩ := facts process message record
      refine own_signal wellformed calm shape found enabled mem mem' (by simp) footprint' shape'
        ?_ (fun view observes => ?_) (fun other => ?_)
      · rw [same, record]
        obtain ⟨changed, found⟩ := Option.isSome_iff_exists.mp kept
        simp [found, ProcessState.live]
      · rw [delivery_record signal, record]
        simp [same, views view observes]
      · rw [delivery_record signal]
        split
        · rename_i other
          subst other
          rw [same, record]
          exact appended
        · rfl
  · refine own_signal wellformed calm shape found enabled mem mem' (by simp) footprint' shape'
      (by rw [shape.live wellformed live same live']; rfl) (fun view _ => ?_) (fun other => ?_)
    · simp [delivery_record signal, Ne.symm same]
    · rw [delivery_record signal]
      split
      · rename_i other
        subst other
        rw [shape.live wellformed live same live']
        rfl
      · rfl

/-- A talking process's own step and a message bouncing meet again. -/
private theorem own_bounce {talk : PID → PID → Prop} {state : State}
    {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    {processId : PID} {task : Task α} {envelope : Envelope} {message : Term}
    {event event' : Event} {next next' : Config α}
    (wellformed : Wellformed (.running state tasks finished exhausted)) (calm : Calm talk state)
    (talks : ∀ entry ∈ tasks, entry.2.computation.Talks talk entry.1 (state.process entry.1).children)
    (found : tasks.lookup processId = some task) (enabled : 0 < (task.own state processId).length)
    (signal : envelope.signal = .message message) (missing : tasks.lookup envelope.target = none)
    (oldestFound : state.inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope)
    (mem : (.own processId 0, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (.bounce envelope.source envelope.target, event', next') ∈
      (Config.running state tasks finished exhausted).steps) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  have shape := own_shape (calm.alone processId) (talks _ (mem_of_lookup found)) enabled
  have shape' := bounce_shape (state := state) signal oldestFound
  have live := live_of_lookup wellformed (processId := processId) (by simp [found])
  have dead := dead_of_missing wellformed missing
  obtain ⟨-, -, -, spawned⟩ := calm.messages envelope (List.mem_of_find?_eq_some oldestFound)
  refine own_signal wellformed calm shape found enabled mem mem' (by simp)
    (by simp [Config.footprint, missing, oldestFound]) shape'
    (by rw [shape.spawned live dead spawned]; rfl) (fun _ _ => ?_) (fun _ => ?_)
  · rw [bounce_message signal]; rfl
  · rw [bounce_message signal]; rfl

/-- Different steps of a talking configuration meet again. -/
private theorem talking_joins {talk : PID → PID → Prop} (single : Single talk) {state : State}
    {tasks : List (PID × Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (talking : Talking talk (.running state tasks finished exhausted)) {key key' : Key}
    {event event' : Event} {next next' : Config α} (distinct : key ≠ key')
    (mem : (key, event, next) ∈ (Config.running state tasks finished exhausted).steps)
    (mem' : (key', event', next') ∈ (Config.running state tasks finished exhausted).steps) :
    ∃ last, (∃ step, Step next step last) ∧ ∃ step, Step next' step last := by
  obtain ⟨calm, talks⟩ := talking
  obtain ⟨footprint, found⟩ := footprint_of_mem wellformed mem
  obtain ⟨footprint', found'⟩ := footprint_of_mem wellformed mem'
  have swap : ∀ {first second : Config α},
      (∃ last, (∃ step, Step second step last) ∧ ∃ step, Step first step last) →
      ∃ last, (∃ step, Step first step last) ∧ ∃ step, Step second step last :=
    fun ⟨last, forth, back⟩ => ⟨last, back, forth⟩
  have apart : ∀ {envelope envelope' : Envelope} {message message' : Term} {task task' : Task α},
      envelope.signal = .message message → envelope'.signal = .message message' →
      tasks.lookup envelope.target = some task → tasks.lookup envelope'.target = some task' →
      state.inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope →
      state.inTransit.find? (Envelope.between envelope'.source envelope'.target) = some envelope' →
      Key.deliver envelope.source envelope.target ≠ Key.deliver envelope'.source envelope'.target →
      ∀ other, (Footprint.delivery state envelope).effect.record other = id ∨
        (Footprint.delivery state envelope').effect.record other = id := by
    intro envelope envelope' message message' task task' signal signal' _ _ oldestFound oldestFound'
      different other
    obtain ⟨-, allowed, -, -⟩ := calm.messages envelope (List.mem_of_find?_eq_some oldestFound)
    obtain ⟨-, allowed', -, -⟩ := calm.messages envelope' (List.mem_of_find?_eq_some oldestFound')
    rw [delivery_record signal, delivery_record signal']
    by_cases same : other = envelope.target
    · refine .inr ?_
      have : other ≠ envelope'.target := fun same' => different (by
        rw [← same, ← same', single.1 _ _ _ allowed (same ▸ same' ▸ allowed')])
      simp [this]
    · exact .inl (by simp [same])
  rcases footprint_cases calm found with
    ⟨processId, task, rfl, lookup, enabled, rfl⟩ |
    ⟨envelope, message, task, rfl, signal, lookup, oldestFound, rfl⟩ |
    ⟨envelope, message, rfl, signal, missing, oldestFound, rfl⟩ <;>
  rcases footprint_cases calm found' with
    ⟨processId', task', rfl, lookup', enabled', rfl⟩ |
    ⟨envelope', message', task', rfl, signal', lookup', oldestFound', rfl⟩ |
    ⟨envelope', message', rfl, signal', missing', oldestFound', rfl⟩
  · exact own_own wellformed calm (fun same => distinct (congrArg (Key.own · 0) same))
      (own_shape (calm.alone _) (talks _ (mem_of_lookup lookup)) enabled)
      (own_shape (calm.alone _) (talks _ (mem_of_lookup lookup')) enabled') lookup lookup' enabled enabled'
      mem mem'
  · exact own_deliver single wellformed calm talks lookup enabled signal' lookup' oldestFound' mem mem'
  · exact own_bounce wellformed calm talks lookup enabled signal' missing' oldestFound' mem mem'
  · exact swap (own_deliver single wellformed calm talks lookup' enabled' signal lookup oldestFound mem' mem)
  · exact signal_signal wellformed mem mem' distinct found found' (delivery_shape signal oldestFound)
      (delivery_shape signal' oldestFound')
      (fun same => distinct (by simp only [Prod.mk.injEq] at same; rw [same.1, same.2]))
      (apart signal signal' lookup lookup' oldestFound oldestFound' distinct)
  · exact signal_signal wellformed mem mem' distinct found found' (delivery_shape signal oldestFound)
      (bounce_shape signal' oldestFound')
      (fun same => by simp only [Prod.mk.injEq] at same; rw [same.2, missing'] at lookup; cases lookup)
      fun _ => .inr (by rw [bounce_message signal']; rfl)
  · exact swap (own_bounce wellformed calm talks lookup' enabled' signal missing oldestFound mem' mem)
  · exact signal_signal wellformed mem mem' distinct found found' (bounce_shape signal oldestFound)
      (delivery_shape signal' oldestFound')
      (fun same => by simp only [Prod.mk.injEq] at same; rw [same.2, lookup'] at missing; cases missing)
      fun _ => .inl (by rw [bounce_message signal]; rfl)
  · exact signal_signal wellformed mem mem' distinct found found' (bounce_shape signal oldestFound)
      (bounce_shape signal' oldestFound')
      (fun same => distinct (by simp only [Prod.mk.injEq] at same; rw [same.1, same.2]))
      fun _ => .inl (by rw [bounce_message signal]; rfl)

/-- A computation whose processes only talk along the process tree, with a
single sender for each receiver, has no races. -/
public theorem RaceFree.of_talks {talk : PID → PID → Prop} (single : Single talk)
    {env : Environment} {computation : Result α} {elapsed : PID → Nat → Nat}
    (talks : computation.Talks talk env.currentPid 0) :
    RaceFree (Config.start env computation elapsed) := by
  intro events reached run key key' event event' next next' distinct mem mem'
  have preserved : ∀ {first last : Config α} {events : List Event}, Run first events last →
      Wellformed first ∧ Talking talk first → Wellformed last ∧ Talking talk last := by
    intro first last events run
    induction run with
    | refl => exact id
    | step step _ ih => exact fun facts => ih ⟨step.wellformed facts.1, step.talking single facts.1 facts.2⟩
  obtain ⟨wellformed, talking⟩ := preserved run ⟨trivial, talks⟩
  cases reached with
  | start => simp [Config.steps] at mem
  | running state tasks finished exhausted =>
    exact talking_joins single wellformed talking distinct mem mem'

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
