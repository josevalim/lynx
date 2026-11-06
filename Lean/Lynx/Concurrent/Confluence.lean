module

public import Lynx.Concurrent.Reduction
import all Lynx.Concurrent.Reduction

/-! Steps of different processes commute unless they race on a mailbox, so
programs without such races reach the same terminal configuration under
every interleaving.

Two steps race when both deliver to the same process, when one delivers to a
process whose receive the other times out, or when one delivers to the
process the other spawns. A receive that consumes a message is unaffected by
later deliveries, since it selects the oldest match. Steps that act on other
processes through the scheduler, such as links, monitors, and exit signals,
are not plain, and plain steps are required whenever another process can
step. When no reachable configuration has racing steps, every run ends in the
same configuration, so one run determines the outcome of every schedule. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- The process a step delivers a message to. -/
@[expose] def Event.destination : Event → Option PID
  | .send _ receiver _ => some receiver
  | _ => none

/-- Whether two steps of different processes may not commute. -/
@[expose] def Event.Races (first second : Event) : Prop :=
  ∃ receiver, first.destination = some receiver ∧
    (second.destination = some receiver ∨ second = .timeout receiver ∨
      ∃ parent, second = .spawn parent receiver)

/-- Whether the next step of a process only changes its own record, sends to a
PID, or spawns without linking or monitoring. Requests to the scheduler, a
pending exit signal, and the exit of a linked or monitored process act on
other processes, so they are not plain. -/
@[expose] def Task.plain (state : State) (processId : PID) (task : Task α) : Bool :=
  (state.process processId).signal.isNone &&
    match task.computation with
    | .request .. => false
    | .schedule options .. => !options.link && !options.monitor
    | .ok _ | .error _ =>
        (state.process processId).links.isEmpty && (state.process processId).monitors.isEmpty
    | _ => true

/-- No two processes can take steps that may not commute. -/
@[expose] def Config.Unraced : Config α → Prop
  | .start .. => True
  | .running state tasks _ _ => ∀ before first task after second other rest,
      tasks = before ++ (first, task) :: after ++ (second, other) :: rest →
      ∀ transition ∈ task.transitions state first, ∀ next ∈ other.transitions state second,
        task.plain state first ∧ other.plain state second ∧
        ¬ transition.event.Races next.event ∧ ¬ next.event.Races transition.event

/-- No configuration reachable from this one has racing steps. -/
@[expose] def Config.RaceFree (config : Config α) : Prop :=
  ∀ events reached, Run config events reached → reached.Unraced

/-- Every message the process sends goes to a destination `talk` allows from its
PID, no receive has a timeout, it makes no requests to the scheduler, and it
spawns without linking or monitoring, each spawned process satisfying the same.
Children are numbered after the `children` the process already spawned. -/
inductive _root_.Lynx.Result.Talks (talk : PID → PID → Prop) :
    {β : Type} → PID → Nat → Result β → Prop where
  | ok : Result.Talks talk self children (.ok value)
  | error : Result.Talks talk self children (.error exception)
  | get (next : ∀ env : Environment, env.currentPid = self →
        Result.Talks talk self children (continuation env)) :
      Result.Talks talk self children (.get continuation)
  | set (same : env.currentPid = self) (next : Result.Talks talk self children continuation) :
      Result.Talks talk self children (.set env continuation)
  | send (allowed : talk self receiver) (next : Result.Talks talk self children continuation) :
      Result.Talks talk self children (.send receiver message continuation)
  | receive (next : ∀ reply, Result.Talks talk self children (continuation reply)) :
      Result.Talks talk self children (.receive .infinity select continuation)
  | schedule (spawned : Result.Talks talk (self ++ [children + 1]) 0 child)
      (next : Result.Talks talk self (children + 1) (continuation (self ++ [children + 1]))) :
      Result.Talks talk self children (Result.schedule {} child continuation)

/-- Each receiver has a single sender, and processes only send to themselves,
their ancestors, or their own children. Such messages never race with each
other or with a spawn. -/
@[expose] def Single (talk : PID → PID → Prop) : Prop :=
  (∀ sender sender' receiver, talk sender receiver → talk sender' receiver → sender = sender') ∧
  ∀ sender receiver, talk sender receiver →
    (∃ rest, sender = receiver ++ rest) ∨ ∃ index, receiver = sender ++ [index]

/-! ### Effects on the shared state -/

private theorem State.ext {first second : State} (equal : first.processes = second.processes) :
    first = second := by
  cases first; cases second; simp_all

/-- Change the record of a process, when it is live. -/
private def State.alter (state : State) (processId : PID)
    (change : ProcessState → ProcessState) : State :=
  { processes := fun candidate =>
      if candidate = processId then (state.processes processId).map change
      else state.processes candidate }

/-- How a plain step changes the shared state, relative to its process. -/
private inductive Effect where
  | stay
  | store (pdict : List (Term × Term)) (refCounter : Nat)
  | exit
  | spawn (child : PID)
  | send (receiver : PID) (message : Term)
  | take (index : Nat)

private def Effect.apply (processId : PID) (state : State) : Effect → State
  | .stay => state
  | .store pdict refCounter => state.alter processId fun process =>
      { process with pdict, refCounter }
  | .exit => state.update processId none
  | .spawn child => (state.alter processId fun process =>
      { process with children := process.children + 1 }).update child (some {})
  | .send receiver message => state.alter receiver fun process =>
      { process with mailbox := process.mailbox ++ [message] }
  | .take index => state.alter processId fun process =>
      { process with mailbox := process.mailbox.eraseIdx index }

private theorem selectMessage_index {select : Term → Option β} {mailbox : List Term}
    {message : Term} {value : β} {remaining : List Term}
    (selected : selectMessage select mailbox = some (message, value, remaining)) :
    ∃ index < mailbox.length, remaining = mailbox.eraseIdx index ∧
      ∀ extra, selectMessage select (mailbox ++ extra) = some (message, value, remaining ++ extra) := by
  induction mailbox generalizing remaining with
  | nil => simp [selectMessage] at selected
  | cons head rest ih =>
    simp only [selectMessage] at selected
    split at selected
    · rename_i matched
      simp only [Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl, rfl⟩ := selected
      exact ⟨0, by simp, by simp, fun extra => by simp [selectMessage, matched]⟩
    · rename_i unmatched
      simp only [Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at selected
      obtain ⟨_, _, remaining', found, rfl, rfl, rfl⟩ := selected
      obtain ⟨index, bound, rfl, extend⟩ := ih found
      exact ⟨index + 1, by simp [bound], by simp, fun extra => by
        simp [selectMessage, unmatched, extend]⟩

/-- Prove states equal by comparing every process record. -/
local macro "state_ext" : tactic =>
  `(tactic| (apply State.ext; funext candidate; simp only [State.update, State.alter, State.modify, State.deliver, State.store, State.spawn, State.process, Effect.apply]; (repeat' split) <;> simp_all))

/-- Which effects a step's event announces. -/
private def Effect.Matches (processId : PID) (process : ProcessState) : Effect → Event → Prop
  | .send receiver message, event => event = .send processId receiver message
  | .spawn child, event => event = .spawn processId child ∧
      child = processId ++ [process.children + 1]
  | .take index, event => index < process.mailbox.length ∧ event.destination = none ∧
      ∀ parent child, event ≠ .spawn parent child
  | _, event => event.destination = none ∧ ∀ parent child, event ≠ .spawn parent child

@[simp] private theorem State.process_of_processes {state : State} {processId : PID}
    {process : ProcessState} (live : state.processes processId = some process) :
    state.process processId = process := by
  simp [State.process, live]

/-- A process without links or monitors exits without notifying others. -/
private theorem terminate_quiet {state : State} {processId : PID} {process : ProcessState}
    {reason : Term} (live : state.processes processId = some process)
    (links : process.links = []) (monitors : process.monitors = []) :
    state.terminate processId reason = state.update processId none := by
  simp [State.terminate, live, links, monitors]

/-- Each plain step of a live process has an effect on the shared state, and the
same step remains available, with the same effect, after other processes append
to its mailbox, unless it times out. -/
private theorem transition_effect {state : State} {processId : PID} {process : ProcessState}
    {task : Task α} {transition : Transition α}
    (live : state.processes processId = some process)
    (plain : task.plain state processId = true)
    (possible : transition ∈ task.transitions state processId) :
    ∃ effect : Effect, effect.Matches processId process transition.event ∧
      transition.state = effect.apply processId state ∧
      ∀ other extra,
        other.processes processId = some { process with mailbox := process.mailbox ++ extra } →
        (transition.event = .timeout processId → extra = []) →
        ∃ moved ∈ task.transitions other processId,
          moved.state = effect.apply processId other ∧ moved.event = transition.event ∧
          moved.tasks = transition.tasks ∧ moved.finished = transition.finished ∧
          moved.exhausted = transition.exhausted := by
  obtain ⟨computation, finish⟩ := task
  simp only [Task.plain, State.process_of_processes live, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at plain
  obtain ⟨signal, plain⟩ := plain
  have signal' : (state.process processId).signal = none := by simp [live, signal]
  have moved_signal : ∀ (other : State) extra,
      other.processes processId = some { process with mailbox := process.mailbox ++ extra } →
      (other.process processId).signal = none := by
    intro other extra moved
    simp [moved, signal]
  have moved_view : ∀ (other : State) extra,
      other.processes processId = some { process with mailbox := process.mailbox ++ extra } →
      other.view processId = state.view processId := by
    intro other extra moved
    simp [State.view, moved, live]
  cases computation with
  | ok value =>
    simp only [List.isEmpty_iff, Bool.and_eq_true] at plain
    obtain ⟨links, monitors⟩ := plain
    simp only [Task.transitions, signal', List.mem_singleton] at possible
    subst possible
    refine ⟨.exit, by simp [Effect.Matches, Event.destination], terminate_quiet live links monitors,
      ?_⟩
    intro other extra moved _
    simp only [Task.transitions, moved_signal other extra moved, List.mem_singleton,
      exists_eq_left, moved_view other extra moved]
    and_intros <;> first | exact terminate_quiet moved links monitors | rfl | trivial
  | error exception =>
    simp only [List.isEmpty_iff, Bool.and_eq_true] at plain
    obtain ⟨links, monitors⟩ := plain
    cases exception <;> simp only [Task.transitions, signal', List.mem_singleton] at possible <;>
      subst possible
    case exhausted =>
      refine ⟨.exit, by simp [Effect.Matches, Event.destination], rfl, ?_⟩
      intro other extra moved _
      simp only [Task.transitions, moved_signal other extra moved, List.mem_singleton,
        exists_eq_left]
      and_intros <;> first | rfl | trivial
    all_goals
      refine ⟨.exit, by simp [Effect.Matches, Event.destination],
        terminate_quiet live links monitors, ?_⟩
      intro other extra moved _
      simp only [Task.transitions, moved_signal other extra moved, List.mem_singleton,
        exists_eq_left, moved_view other extra moved]
      and_intros <;> first | exact terminate_quiet moved links monitors | rfl | trivial
  | get next =>
    simp only [Task.transitions, signal', List.mem_singleton] at possible
    subst possible
    refine ⟨.stay, by simp [Effect.Matches, Event.destination], rfl, ?_⟩
    intro other extra moved _
    simp only [Task.transitions, moved_signal other extra moved, List.mem_singleton,
      exists_eq_left, moved_view other extra moved]
    and_intros <;> first | rfl | trivial
  | set updated next =>
    simp only [Task.transitions, signal', List.mem_singleton] at possible
    subst possible
    refine ⟨.store updated.pdict updated.refCounter, by simp [Effect.Matches, Event.destination],
      by state_ext, ?_⟩
    intro other extra moved _
    simp only [Task.transitions, moved_signal other extra moved, List.mem_singleton,
      exists_eq_left]
    and_intros <;> first | rfl | trivial | state_ext
  | schedule options child next =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at plain
    obtain ⟨noLink, noMonitor⟩ := plain
    simp only [Task.transitions, signal', List.mem_singleton] at possible
    subst possible
    have spawnWith : ∀ (current : State), current.spawnWith processId options =
        current.spawn processId := by
      intro current
      simp [State.spawnWith, noLink, noMonitor]
    refine ⟨.spawn (processId ++ [process.children + 1]),
      by simp [Effect.Matches, spawnWith, State.spawn, live], ?_, ?_⟩
    · rw [spawnWith]; state_ext
    intro other extra moved _
    simp only [Task.transitions, moved_signal other extra moved, List.mem_singleton,
      exists_eq_left]
    and_intros <;> first
      | rfl | trivial
      | (rw [spawnWith]; state_ext)
      | simp [spawnWith, State.spawn, moved, live]
  | send receiver message next =>
    simp only [Task.transitions, signal', List.mem_singleton] at possible
    subst possible
    have deliver (current : State) : current.deliver receiver message =
        (Effect.send receiver message).apply processId current := by
      simp only [State.deliver]
      split <;> state_ext
    refine ⟨.send receiver message, by simp [Effect.Matches], deliver state, ?_⟩
    intro other extra moved _
    simp only [Task.transitions, moved_signal other extra moved, List.mem_singleton,
      exists_eq_left]
    and_intros <;> first | exact deliver other | rfl | trivial
  | receive timeout select next =>
    simp only [Task.transitions, signal'] at possible
    split at possible
    · rename_i message value remaining selected
      simp only [List.mem_singleton] at possible
      subst possible
      simp only [State.view, State.process_of_processes live] at selected
      obtain ⟨index, bound, rfl, extend⟩ := selectMessage_index selected
      refine ⟨.take index, by simp [Effect.Matches, Event.destination, bound], by state_ext, ?_⟩
      intro other extra moved _
      simp only [Task.transitions, State.view,
        State.process_of_processes moved, signal, extend, List.mem_singleton, exists_eq_left,
        and_true]
      simp only [← List.eraseIdx_append_of_lt_length bound]
      state_ext
    · rename_i unmatched
      cases timeout with
      | infinity => simp at possible
      | immediate | finite =>
        simp only [List.mem_singleton] at possible
        subst possible
        refine ⟨.stay, by simp [Effect.Matches, Event.destination], rfl, ?_⟩
        intro other extra moved timedOut
        obtain rfl := timedOut rfl
        have same : other.process processId = state.process processId := by simp [moved, live]
        simp only [Task.transitions, State.view, same, signal'] at unmatched ⊢
        simp [unmatched, Effect.apply]
  | request => simp at plain

/-- Effects of different processes commute when they do not race. -/
private theorem Effect.apply_comm {state : State} {first second : PID} {effect other : Effect}
    (distinct : first ≠ second)
    (sends : ∀ receiver message receiver' message', effect = .send receiver message →
      other = .send receiver' message' → receiver ≠ receiver')
    (sendSpawn : ∀ receiver message child, effect = .send receiver message →
      other = .spawn child → receiver ≠ child)
    (spawnSend : ∀ receiver message child, other = .send receiver message →
      effect = .spawn child → receiver ≠ child)
    (spawned : ∀ child, effect = .spawn child → child ≠ first ∧ child ≠ second ∧
      ∀ child', other = .spawn child' → child ≠ child')
    (spawned' : ∀ child, other = .spawn child → child ≠ first ∧ child ≠ second)
    (taken : ∀ index message process, effect = .take index → other = .send first message →
      state.processes first = some process → index < process.mailbox.length)
    (taken' : ∀ index message process, other = .take index → effect = .send second message →
      state.processes second = some process → index < process.mailbox.length) :
    effect.apply first (other.apply second state) = other.apply second (effect.apply first state) := by
  cases effect <;> cases other <;>
    simp only [reduceCtorEq, Effect.send.injEq, Effect.spawn.injEq, Effect.take.injEq,
      false_imp_iff, implies_true, forall_eq', and_imp, forall_apply_eq_imp_iff₂]
      at sends sendSpawn spawnSend spawned spawned' taken taken' <;>
    apply State.ext <;> funext candidate <;>
    simp only [Effect.apply, State.alter, State.update] <;>
    (repeat' split) <;> (try subst_vars) <;>
    first
      | (cases found : state.processes candidate with
          | none => simp
          | some process =>
            have bound := taken _ _ _ rfl rfl rfl found
            simp [List.eraseIdx_append_of_lt_length bound])
      | (cases found : state.processes candidate with
          | none => simp
          | some process =>
            have bound := taken' _ _ _ rfl rfl rfl found
            simp [List.eraseIdx_append_of_lt_length bound])
      | (simp_all; done)
      | (simp_all; exact absurd rfl (sends _ _ _ _ rfl rfl rfl))
      | (simp_all; refine congrArg (Option.map · _) ?_; funext process; simp)

private def Effect.delivered (effect : Effect) (processId : PID) : List Term :=
  match effect with
  | .send receiver message => if processId = receiver then [message] else []
  | _ => []

/-- Another process's step only appends to a live process's mailbox. -/
private theorem Effect.apply_other {effect : Effect} {processId other : PID} {state : State}
    {process : ProcessState} (found : state.processes other = some process)
    (distinct : other ≠ processId) (notChild : ∀ child, effect = .spawn child → other ≠ child) :
    (effect.apply processId state).processes other =
      some { process with mailbox := process.mailbox ++ effect.delivered other } := by
  cases effect with
  | send receiver message =>
    simp only [Effect.apply, State.alter, Effect.delivered]
    by_cases same : other = receiver
    · subst same; simp [found]
    · simp [same, found]
  | spawn child =>
    have fresh := notChild child rfl
    simp [Effect.apply, State.alter, State.update, distinct, fresh, found, Effect.delivered]
  | _ => simp [Effect.apply, State.alter, State.update, distinct, found, Effect.delivered]

/-- Two steps of different processes that do not race can be taken in either
order, ending in the same configuration. -/
private theorem diamond {state : State} {before middle after : List (PID × Task α)}
    {first second : PID} {task other : Task α} {transition next : Transition α}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state
      (before ++ (first, task) :: middle ++ (second, other) :: after) finished exhausted))
    (possible : transition ∈ task.transitions state first)
    (possible' : next ∈ other.transitions state second)
    (plain : task.plain state first = true) (plain' : other.plain state second = true)
    (unraced : ¬ transition.event.Races next.event ∧ ¬ next.event.Races transition.event) :
    ∃ next' ∈ other.transitions transition.state second,
      ∃ transition' ∈ task.transitions next.state first,
        next'.apply (before ++ transition.tasks ++ middle) after
            (transition.finished.orElse fun _ => finished) (exhausted || transition.exhausted) =
          transition'.apply before (middle ++ next.tasks ++ after)
            (next.finished.orElse fun _ => finished) (exhausted || next.exhausted) := by
  obtain ⟨pairwise, fresh, live, quietPairs⟩ := wellformed
  have distinct : first ≠ second :=
    pairwise_between (relation := fun first second : PID × Task α => first.1 ≠ second.1)
      (first := (first, task)) (second := (second, other)) pairwise
  have quiet : task.Quiet ∨ other.Quiet :=
    pairwise_between (relation := fun first second : PID × Task α => first.2.Quiet ∨ second.2.Quiet)
      (first := (first, task)) (second := (second, other)) quietPairs
  obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp (live (first, task) (by simp))
  obtain ⟨process', found'⟩ := Option.isSome_iff_exists.mp (live (second, other) (by simp))
  obtain ⟨effect, matched, stateEq, stable⟩ := transition_effect found plain possible
  obtain ⟨effect', matched', stateEq', stable'⟩ := transition_effect found' plain' possible'
  have quietFinished := (transition_frame possible).2.2
  have quietFinished' := (transition_frame possible').2.2
  -- A spawned child is fresh: no live process has its PID.
  have childFresh : ∀ child, effect = .spawn child → child ≠ second ∧ child ≠ first := by
    intro child spawned
    subst spawned
    simp only [Effect.Matches] at matched
    refine ⟨fun equal => ?_, fun equal => ne_append_cons first _ [] (by rw [← matched.2, equal])⟩
    have := fresh (first, task) (by simp) (second, other) (by simp) _ []
      (by rw [← equal, matched.2])
    simp only [State.process_of_processes found] at this
    omega
  have childFresh' : ∀ child, effect' = .spawn child → child ≠ first ∧ child ≠ second := by
    intro child spawned
    subst spawned
    simp only [Effect.Matches] at matched'
    refine ⟨fun equal => ?_, fun equal => ne_append_cons second _ [] (by rw [← matched'.2, equal])⟩
    have := fresh (second, other) (by simp) (first, task) (by simp) _ []
      (by rw [← equal, matched'.2])
    simp only [State.process_of_processes found'] at this
    omega
  -- Each step remains available after the other, which at most appends to its mailbox.
  have races {sender receiver : PID} {message : Term} {step : Event} {effect : Effect}
      {process : ProcessState} (matched : effect.Matches sender process step)
      (sends : effect = .send receiver message) : step.destination = some receiver := by
    subst sends; simp only [Effect.Matches] at matched; simp [matched, Event.destination]
  have delivered : ∀ (effect : Effect) (process : ProcessState) (sender receiver : PID)
      (step other : Event), effect.Matches sender process step →
      ¬ step.Races other → other = .timeout receiver → effect.delivered receiver = [] := by
    intro effect process sender receiver step other matched unraced timedOut
    cases effect with
    | send target message =>
      simp only [Effect.delivered]
      split
      · rename_i same
        subst same timedOut
        exact absurd ⟨receiver, races matched rfl, .inr (.inl rfl)⟩ unraced
      · rfl
    | _ => rfl
  have firstAfter : next.state.processes first =
      some { process with mailbox := process.mailbox ++ effect'.delivered first } := by
    rw [stateEq']
    exact Effect.apply_other found distinct fun child spawned => (childFresh' child spawned).1.symm
  have secondAfter : transition.state.processes second =
      some { process' with mailbox := process'.mailbox ++ effect.delivered second } := by
    rw [stateEq]
    exact Effect.apply_other found' (Ne.symm distinct)
      fun child spawned => (childFresh child spawned).1.symm
  obtain ⟨transition', possibleAfter, stateAfter, eventAfter, tasksAfter, finishedAfter,
    exhaustedAfter⟩ := stable next.state (effect'.delivered first) firstAfter
      (fun timedOut => delivered effect' process' second first next.event transition.event
        matched' unraced.2 timedOut)
  obtain ⟨next', possibleAfter', stateAfter', eventAfter', tasksAfter', finishedAfter',
    exhaustedAfter'⟩ := stable' transition.state (effect.delivered second) secondAfter
      (fun timedOut => delivered effect process first second transition.event next.event
        matched unraced.1 timedOut)
  refine ⟨next', possibleAfter', transition', possibleAfter, ?_⟩
  have commuted : transition'.state = next'.state := by
    rw [stateAfter, stateAfter', stateEq, stateEq']
    refine Effect.apply_comm distinct ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro receiver message receiver' message' sends sends' same
      subst same
      exact unraced.1 ⟨receiver, races matched sends, .inl (races matched' sends')⟩
    · intro receiver message child sends spawned same
      subst same spawned
      simp only [Effect.Matches] at matched'
      exact unraced.1 ⟨receiver, races matched sends, .inr (.inr ⟨second, matched'.1⟩)⟩
    · intro receiver message child sends spawned same
      subst same spawned
      simp only [Effect.Matches] at matched
      exact unraced.2 ⟨receiver, races matched' sends, .inr (.inr ⟨first, matched.1⟩)⟩
    · intro child spawned
      refine ⟨(childFresh child spawned).2, (childFresh child spawned).1, ?_⟩
      intro child' spawned' same
      subst spawned spawned' same
      simp only [Effect.Matches] at matched matched'
      have := List.append_inj' (matched.2.symm.trans matched'.2) rfl
      exact distinct this.1
    · intro child spawned
      exact childFresh' child spawned
    · intro index message process'' taken sends found''
      subst taken
      simp only [Effect.Matches] at matched
      rw [found] at found''
      cases found''
      exact matched.1
    · intro index message process'' taken sends found''
      subst taken
      simp only [Effect.Matches] at matched'
      rw [found'] at found''
      cases found''
      exact matched'.1
  have finishedComm : (next'.finished.orElse fun _ => transition.finished.orElse fun _ => finished) =
      (transition'.finished.orElse fun _ => next.finished.orElse fun _ => finished) := by
    rw [finishedAfter, finishedAfter']
    rcases quiet with quiet | quiet
    · rw [quietFinished quiet]; cases next.finished <;> rfl
    · rw [quietFinished' quiet]; cases transition.finished <;> rfl
  simp only [Transition.apply, tasksAfter, tasksAfter', commuted, finishedComm, exhaustedAfter,
    exhaustedAfter', List.append_assoc, Bool.or_assoc, Bool.or_comm transition.exhausted]

/-! ### Unique terminal configurations -/

/-- A configuration without steps. -/
private def Stuck (config : Config α) : Prop := ∀ event next, ¬ Step config event next

private theorem Terminal.stuck {config : Config α} {outcome : Outcome α}
    (terminal : Terminal config outcome) : Stuck config := by
  intro event next step
  have := step.mem_successors
  rw [terminal.successors_eq_nil] at this
  simp at this

/-- A process has at most one step in a given state. -/
private theorem transitions_subsingleton {state : State} {processId : PID} {task : Task α}
    {first second : Transition α} (possible : first ∈ task.transitions state processId)
    (possible' : second ∈ task.transitions state processId) : first = second := by
  obtain ⟨computation, finish⟩ := task
  rcases signal : (state.process processId).signal with _ | reason
  · cases computation with
    | error exception => cases exception <;> simp_all [Task.transitions]
    | receive timeout select next =>
      simp only [Task.transitions, signal] at possible possible'
      split at possible <;> (try cases timeout) <;> simp_all
    | _ => simp_all [Task.transitions]
  · simp_all [Task.transitions]

/-- Steps of an earlier and a later process close in one step each. -/
private theorem close_ordered {state : State} {before middle after : List (PID × Task α)}
    {first second : PID} {task other : Task α} {transition next : Transition α}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state
      (before ++ (first, task) :: middle ++ (second, other) :: after) finished exhausted))
    (unraced : (Config.running state
      (before ++ (first, task) :: middle ++ (second, other) :: after) finished exhausted).Unraced)
    (possible : transition ∈ task.transitions state first)
    (possible' : next ∈ other.transitions state second) :
    ∃ event event' last,
      Step (transition.apply before (middle ++ (second, other) :: after) finished exhausted)
        event last ∧
      Step (next.apply (before ++ (first, task) :: middle) after finished exhausted) event' last := by
  obtain ⟨plain, plain', races, races'⟩ := unraced _ _ _ _ _ _ _ rfl _ possible _ possible'
  obtain ⟨next', possibleAfter', transition', possibleAfter, equal⟩ :=
    diamond wellformed possible possible' plain plain' ⟨races, races'⟩
  refine ⟨next'.event, transition'.event, next'.apply (before ++ transition.tasks ++ middle) after
    (transition.finished.orElse fun _ => finished) (exhausted || transition.exhausted), ?_, ?_⟩
  · exact Step.run (by simp) possibleAfter'
  · rw [equal]
    exact Step.run (by simp) possibleAfter

private theorem local_confluence_run {state : State} {tasks before after before' after' : List (PID × Task α)}
    {processId processId' : PID} {task task' : Task α} {transition transition' : Transition α}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state tasks finished exhausted))
    (unraced : (Config.running state tasks finished exhausted).Unraced)
    (split : tasks = before ++ (processId, task) :: after)
    (possible : transition ∈ task.transitions state processId)
    (split' : tasks = before' ++ (processId', task') :: after')
    (possible' : transition' ∈ task'.transitions state processId') :
    transition.apply before after finished exhausted =
        transition'.apply before' after' finished exhausted ∨
      ∃ event₁ event₂ last, Step (transition.apply before after finished exhausted) event₁ last ∧
        Step (transition'.apply before' after' finished exhausted) event₂ last := by
  rcases split_order (split.symm.trans split') with ⟨rfl, same, rfl⟩ | ⟨middle, rfl, rfl⟩ |
    ⟨middle, rfl, rfl⟩
  · simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact .inl (by rw [transitions_subsingleton possible possible'])
  · have tasks : tasks = before ++ (processId, task) :: middle ++ (processId', task') :: after' := by
      rw [split]; simp
    rw [tasks] at wellformed unraced
    exact .inr (close_ordered wellformed unraced possible possible')
  · have tasks : tasks = before' ++ (processId', task') :: middle ++ (processId, task) :: after := by
      rw [split']; simp
    rw [tasks] at wellformed unraced
    obtain ⟨event₁, event₂, last, first, second⟩ :=
      close_ordered wellformed unraced possible' possible
    exact .inr ⟨event₂, event₁, last, second, first⟩

/-- Different steps from a well-formed configuration without races can be
completed to a common configuration. -/
private theorem local_confluence {config first second : Config α} {event event' : Event}
    (wellformed : Wellformed config) (unraced : config.Unraced)
    (step : Step config event first) (step' : Step config event' second) :
    first = second ∨ ∃ event₁ event₂ last, Step first event₁ last ∧ Step second event₂ last := by
  cases step with
  | get => cases step' with
    | get => exact .inl rfl
    | enter request => simp [isRequest] at request
  | set => cases step' with
    | set => exact .inl rfl
    | enter request => simp [isRequest] at request
  | enter request => cases step' with
    | get => simp [isRequest] at request
    | set => simp [isRequest] at request
    | enter => exact .inl rfl
  | run split possible =>
    cases step' with
    | run split' possible' => exact local_confluence_run wellformed unraced split possible split' possible'

private theorem Config.RaceFree.step {config next : Config α} {event : Event}
    (raceFree : config.RaceFree) (step : Step config event next) : next.RaceFree :=
  fun _ _ run => raceFree _ _ (.step step run)

/-- When every run is bounded, some run gets stuck. -/
private theorem exists_stuck : ∀ (bound : Nat) (config : Config α),
    (∀ events last, Run config events last → events.length ≤ bound) →
      ∃ events last, Run config events last ∧ Stuck last
  | bound, config, bounded => by
    rcases Classical.em (Stuck config) with stuck | moves
    · exact ⟨[], config, .refl, stuck⟩
    · simp only [Stuck, Classical.not_forall, Classical.not_not] at moves
      obtain ⟨event, next, step⟩ := moves
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
    (events : List Event), Wellformed config → config.RaceFree → Run config events last →
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
      rcases local_confluence wellformed (raceFree [] config .refl) first step with
        same | ⟨event₁, event₂, joined, toJoined, toJoined'⟩
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
theorem Config.RaceFree.outcome_eq {env : Environment} {computation : Result α}
    (raceFree : (Config.start env computation).RaceFree) {events events' : List Event}
    {last last' : Config α} {outcome outcome' : Outcome α}
    (run : Run (.start env computation) events last) (terminal : Terminal last outcome)
    (run' : Run (.start env computation) events' last') (terminal' : Terminal last' outcome') :
    outcome' = outcome := by
  obtain ⟨-, unique⟩ := unique_stuck last events.length _ events
    (show Wellformed (Config.start env computation) from trivial) raceFree run rfl terminal.stuck
  obtain ⟨rfl, -⟩ := unique _ _ run' terminal'.stuck
  rw [← terminal.outcome_eq, ← terminal'.outcome_eq]

/-! ### Programs that only talk along their process tree -/

/-- No process is linked, monitored, or has a pending exit signal. -/
private def Calm (state : State) : Prop :=
  ∀ processId, (state.process processId).links = [] ∧
    (state.process processId).monitors = [] ∧ (state.process processId).signal = none

/-- A talking process in a calm state takes plain steps. -/
private theorem talks_plain {talk : PID → PID → Prop} {state : State} {processId : PID}
    {task : Task α} {children : Nat} (calm : Calm state)
    (talks : task.computation.Talks talk processId children) :
    task.plain state processId = true := by
  obtain ⟨links, monitors, signal⟩ := calm processId
  obtain ⟨computation, finish⟩ := task
  dsimp only at talks
  cases talks <;> simp [Task.plain, links, monitors, signal]

/-- Plain effects keep the state calm. -/
private theorem Effect.calm {effect : Effect} {processId : PID} {state : State}
    (calm : Calm state) : Calm (effect.apply processId state) := by
  intro other
  have record : ∀ (current : State) (target : PID), Calm current →
      ∀ change : ProcessState → ProcessState,
        (∀ process, (change process).links = process.links ∧
          (change process).monitors = process.monitors ∧
          (change process).signal = process.signal) →
        Calm (current.alter target change) := by
    intro current target calm change keeps candidate
    obtain ⟨links, monitors, signal⟩ := calm candidate
    simp only [State.alter, State.process] at links monitors signal ⊢
    split
    · cases found : current.processes target with
      | none => simp
      | some process =>
        rename_i equal
        subst equal
        simp only [found, Option.getD_some] at links monitors signal
        simp [found, (keeps process).1, (keeps process).2.1, (keeps process).2.2, links, monitors,
          signal]
    · exact ⟨links, monitors, signal⟩
  have update : ∀ (current : State) (target : PID) (process : Option ProcessState), Calm current →
      ((process.getD {}).links = [] ∧ (process.getD {}).monitors = [] ∧
        (process.getD {}).signal = none) → Calm (current.update target process) := by
    intro current target process calm empty candidate
    simp only [State.process_update]
    split
    · exact empty
    · exact calm candidate
  cases effect <;> simp only [Effect.apply]
  case stay => exact calm other
  case exit => exact update _ _ none calm (by simp) other
  case spawn child =>
    exact update _ _ (some {}) (record _ _ calm _ (by intro _; exact ⟨rfl, rfl, rfl⟩)) (by simp)
      other
  all_goals exact record _ _ calm _ (by intro _; exact ⟨rfl, rfl, rfl⟩) other

/-- The continuations of a step keep talking, counting children from their records. -/
private theorem talks_transitions {talk : PID → PID → Prop} {state : State} {processId : PID}
    {computation : Result β} {finish : Except Exception β → Option (Except Exception α)}
    {transition : Transition α} (signal : (state.process processId).signal = none)
    (talks : computation.Talks talk processId (state.process processId).children)
    (possible : transition ∈ (⟨computation, finish⟩ : Task α).transitions state processId) :
    ∀ entry ∈ transition.tasks,
      entry.2.computation.Talks talk entry.1 (transition.state.process entry.1).children := by
  generalize counted : (state.process processId).children = children at talks
  cases talks with
  | ok | error =>
    first
      | (simp only [Task.transitions, signal, List.mem_singleton] at possible; subst possible; simp)
      | (rename_i exception; cases exception <;>
          simp only [Task.transitions, signal, List.mem_singleton] at possible <;> subst possible <;>
          simp)
  | get next =>
    simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    simp only [List.mem_singleton, forall_eq]
    rw [counted]
    exact next _ rfl
  | set same next =>
    simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    simp only [List.mem_singleton, forall_eq]
    rw [show ∀ env : Environment, ((state.store processId env).process processId).children =
        children from fun env => by rw [← counted]; simp [State.store, State.update, State.process]]
    exact next
  | send allowed next =>
    simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    simp only [List.mem_singleton, forall_eq]
    have delivered : ∀ receiver message,
        ((state.deliver receiver message).process processId).children = children :=
      fun _ _ => ((KeepsChildren.refl processId state).deliver).1.trans counted
    rw [delivered]
    exact next
  | receive next =>
    simp only [Task.transitions, signal] at possible
    split at possible
    · simp only [List.mem_singleton] at possible
      subst possible
      simp only [List.mem_singleton, forall_eq, State.process_update, ite_true, Option.getD_some]
      rw [counted]
      exact next _
    · simp at possible
  | schedule spawned next =>
    simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    have fresh : processId ≠ processId ++ [children + 1] := ne_append_cons _ _ _
    simp only [State.spawnWith, State.spawn, Bool.false_eq_true, ite_false, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, counted]
    refine ⟨?_, ?_⟩
    · simpa [State.update, State.process, fresh, counted] using next
    · simpa [State.update, State.process, Task.child] using spawned

/-- What a talking process's step can be. -/
private theorem talks_event {talk : PID → PID → Prop} {state : State} {processId : PID}
    {task : Task α} {transition : Transition α} (signal : (state.process processId).signal = none)
    (talks : task.computation.Talks talk processId (state.process processId).children)
    (possible : transition ∈ task.transitions state processId) :
    (∀ receiver, transition.event.destination = some receiver → talk processId receiver) ∧
    (∀ receiver, transition.event ≠ .timeout receiver) ∧
    (∀ parent child, transition.event = .spawn parent child →
      child = processId ++ [(state.process processId).children + 1]) := by
  obtain ⟨computation, finish⟩ := task
  dsimp only at talks
  generalize counted : (state.process processId).children = children at talks ⊢
  cases talks with
  | ok | error =>
    first
      | (simp only [Task.transitions, signal, List.mem_singleton] at possible; subst possible;
          simp [Event.destination])
      | (rename_i exception; cases exception <;>
          simp only [Task.transitions, signal, List.mem_singleton] at possible <;>
          subst possible <;> simp [Event.destination])
  | get | set =>
    simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    simp [Event.destination]
  | send allowed =>
    simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    simp [Event.destination, allowed]
  | receive =>
    simp only [Task.transitions, signal] at possible
    split at possible
    · simp only [List.mem_singleton] at possible
      subst possible
      simp [Event.destination]
    · simp at possible
  | schedule =>
    simp only [Task.transitions, signal, List.mem_singleton] at possible
    subst possible
    simp [Event.destination, State.spawnWith, State.spawn, counted]

/-- A step leaves the child counts of other processes unchanged. -/
private theorem children_unchanged {state : State} {before after : List (PID × Task α)}
    {processId : PID} {task : Task α} {transition : Transition α}
    {finished : Option (Except Exception α × Environment)} {exhausted : Bool}
    (wellformed : Wellformed (.running state (before ++ (processId, task) :: after) finished exhausted))
    (possible : transition ∈ task.transitions state processId) :
    ∀ entry ∈ before ++ after,
      (transition.state.process entry.1).children = (state.process entry.1).children := by
  obtain ⟨distinct, fresh, -, -⟩ := wellformed
  obtain ⟨frame, -, -⟩ := transition_frame possible
  obtain ⟨-, -, -, spawned⟩ := transition_tasks possible
  intro entry mem
  have old : entry ∈ before ++ (processId, task) :: after := by
    simp only [List.mem_append, List.mem_cons] at mem ⊢
    rcases mem with mem | mem <;> simp [mem]
  have ne : entry.1 ≠ processId := by
    have pairs := distinct
    rw [List.pairwise_append, List.pairwise_cons] at pairs
    simp only [List.mem_append] at mem
    rcases mem with mem | mem
    · exact pairs.2.2 entry mem (processId, task) (by simp)
    · exact fun equal => pairs.2.1.1 entry mem equal.symm
  refine (frame entry.1 ne fun child spawn equal => ?_).process.2.2.1
  have := fresh (processId, task) (by simp) entry old _ [] (by
    rw [equal, (spawned child spawn).1])
  dsimp only at this
  omega

/-- Every process of a configuration talks along the process tree, in a calm state. -/
private def Talking (talk : PID → PID → Prop) : Config α → Prop
  | .start env computation => computation.Talks talk env.currentPid 0
  | .running state tasks _ _ => Calm state ∧ ∀ entry ∈ tasks,
      entry.2.computation.Talks talk entry.1 (state.process entry.1).children

private theorem talking_apply {talk : PID → PID → Prop} {state : State}
    {before after : List (PID × Task α)} {processId : PID} {task : Task α}
    {transition : Transition α} {finished : Option (Except Exception α × Environment)}
    {exhausted : Bool}
    (wellformed : Wellformed (.running state (before ++ (processId, task) :: after) finished exhausted))
    (talking : Talking talk (.running state (before ++ (processId, task) :: after) finished exhausted))
    (possible : transition ∈ task.transitions state processId) :
    Talking talk (transition.apply before after finished exhausted) := by
  obtain ⟨calm, talks⟩ := talking
  have selfTalks := talks (processId, task) (by simp)
  obtain ⟨process, found⟩ :=
    Option.isSome_iff_exists.mp (wellformed.2.2.1 (processId, task) (by simp))
  obtain ⟨effect, -, stateEq, -⟩ := transition_effect found (talks_plain calm selfTalks) possible
  refine ⟨by rw [stateEq]; exact Effect.calm calm, ?_⟩
  intro entry mem
  simp only [List.mem_append] at mem
  rcases mem with (mem | mem) | mem
  · rw [children_unchanged wellformed possible entry (by simp [mem])]
    exact talks entry (by simp [mem])
  · obtain ⟨computation, finish⟩ := task
    exact talks_transitions (calm processId).2.2 selfTalks possible entry mem
  · rw [children_unchanged wellformed possible entry (by simp [mem])]
    exact talks entry (by simp [mem])

private theorem Step.talking {talk : PID → PID → Prop} {first next : Config α} {event : Event}
    (step : Step first event next) (wellformed : Wellformed first) (talking : Talking talk first) :
    Talking talk next := by
  cases step with
  | get =>
    cases talking with
    | get next => exact next _ rfl
  | set =>
    cases talking with
    | set same next => simpa [Talking, same] using next
  | enter =>
    simp only [Talking] at talking
    refine ⟨fun processId => ?_, ?_⟩
    · simp only [State.initial, State.process]
      split <;> simp
    · intro entry mem
      simp only [List.mem_singleton] at mem
      subst mem
      simpa [State.initial, State.process, Task.root] using talking
  | run split possible =>
    subst split
    exact talking_apply wellformed talking possible

/-- Talking processes of a well-formed configuration do not race. -/
private theorem talking_unraced {talk : PID → PID → Prop} (single : Single talk)
    {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α × Environment)}
    {exhausted : Bool} (wellformed : Wellformed (.running state tasks finished exhausted))
    (talking : Talking talk (.running state tasks finished exhausted))
    {first second : PID} {task other : Task α} {transition next : Transition α}
    (member : (first, task) ∈ tasks) (member' : (second, other) ∈ tasks) (distinct : first ≠ second)
    (possible : transition ∈ task.transitions state first)
    (possible' : next ∈ other.transitions state second) :
    ¬ transition.event.Races next.event := by
  obtain ⟨-, fresh, -, -⟩ := wellformed
  obtain ⟨calm, talks⟩ := talking
  obtain ⟨destinations, -, -⟩ := talks_event (calm first).2.2 (talks _ member) possible
  obtain ⟨destinations', timeouts', spawns'⟩ :=
    talks_event (calm second).2.2 (talks _ member') possible'
  rintro ⟨receiver, sends, races⟩
  have allowed := destinations receiver sends
  rcases races with sends' | timedOut | ⟨parent, spawned⟩
  · exact distinct (single.1 _ _ _ allowed (destinations' receiver sends'))
  · exact timeouts' receiver timedOut
  · have child := spawns' parent receiver spawned
    rcases single.2 _ _ allowed with ⟨rest, below⟩ | ⟨index, above⟩
    · rw [child] at below
      have := fresh (second, other) member' (first, task) member _ rest (by simpa using below)
      dsimp only at this
      omega
    · rw [child] at above
      exact distinct (List.append_inj' above rfl).1.symm

/-- A computation whose processes only talk along the process tree, with a
single sender for each receiver, has no races. -/
theorem Config.RaceFree.of_talks {talk : PID → PID → Prop} (single : Single talk)
    {env : Environment} {computation : Result α}
    (talks : computation.Talks talk env.currentPid 0) : (Config.start env computation).RaceFree := by
  intro events reached run
  have preserved : ∀ {first last : Config α} {events : List Event}, Run first events last →
      Wellformed first ∧ Talking talk first → Wellformed last ∧ Talking talk last := by
    intro first last events run
    induction run with
    | refl => exact id
    | step step _ ih =>
      exact fun facts => ih ⟨step.wellformed facts.1, step.talking facts.1 facts.2⟩
  obtain ⟨wellformed, talking⟩ := preserved run ⟨trivial, talks⟩
  cases reached with
  | start => trivial
  | running state tasks finished exhausted =>
    intro before first task after second other rest split transition possible next possible'
    have distinct : first ≠ second :=
      pairwise_between (relation := fun first second : PID × Task α => first.1 ≠ second.1)
        (first := (first, task)) (second := (second, other)) (split ▸ wellformed.1)
    have member : (first, task) ∈ tasks := by simp [split]
    have member' : (second, other) ∈ tasks := by simp [split]
    exact ⟨talks_plain talking.1 (talking.2 _ member), talks_plain talking.1 (talking.2 _ member'),
      talking_unraced single wellformed talking member member' distinct possible possible',
      talking_unraced single wellformed talking member' member (Ne.symm distinct) possible'
        possible⟩

end Lynx.Concurrent
