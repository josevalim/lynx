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

/-! ### Changes other processes cannot see

A forced step of a process only changes its own record, in a way the steps of
other processes neither read nor undo. `State.Changed` relates the states
before and after such a change, and every step of another process keeps it. -/

/-- What steps of other processes read of a process's record. -/
private structure Outside (first second : ProcessState) : Prop where
  exiting : second.exiting = first.exiting
  trapExit : second.trapExit = first.trapExit
  parked : second.parked = first.parked
  links : ∀ entry : Entry, entry.signal = .link → (entry ∈ second.queue ↔ entry ∈ first.queue)

/-- Queue a signal at a record. -/
private def ProcessState.push (process : ProcessState) (entry : Entry) : ProcessState :=
  { process with queue := Kernel.append process.queue [entry] }

/-- Apply a `normal` link exit from a process that ended when it is sent. -/
private def ProcessState.eagerExit (process : ProcessState) (source : PID) : ProcessState :=
  { process with links := Kernel.filter (·.1 != source) process.links,
                 eagerExits := insertPid source process.eagerExits }

/-- A relation between records of a process that steps of other processes
cannot tell apart, and that what they change in the record keeps. -/
private structure Unseen (related : ProcessState → ProcessState → Prop) : Prop where
  outside : ∀ {first second}, related first second → Outside first second
  push : ∀ {first second} entry, related first second → related (first.push entry) (second.push entry)
  eagerExit : ∀ {first second} source, related first second →
    related (first.eagerExit source) (second.eagerExit source)
  unpark : ∀ {first second}, related first second →
    related { first with parked := none } { second with parked := none }

/-- Two states that differ only in the record of a process, related by `related`. -/
private def State.Changed (processId : PID) (related : ProcessState → ProcessState → Prop)
    (state state' : State) : Prop :=
  (∀ other, other ≠ processId → state'.record other = state.record other) ∧
  Option.Rel related (state.record processId) (state'.record processId) ∧
  state'.timers = state.timers ∧ state'.elapsed = state.elapsed

private theorem State.record_modify (state : State) (processId other : PID) (change : ProcessState → ProcessState) :
    (state.modify processId change).record other =
      if other = processId then (state.record processId).map change else state.record other := by
  unfold State.modify
  split
  · rename_i process found
    rw [State.record_set]
    by_cases same : other = processId
    · simp [same, found]
    · simp [same]
  · rename_i missing
    by_cases same : other = processId
    · subst same; simp [missing]
    · simp [same]

namespace State.Changed

variable {processId : PID} {related : ProcessState → ProcessState → Prop} {state state' : State}

private theorem record_other (changed : state.Changed processId related state') {other : PID} (differ : other ≠ processId) :
    state'.record other = state.record other := changed.1 other differ

private theorem process_other (changed : state.Changed processId related state') {other : PID} (differ : other ≠ processId) :
    state'.process other = state.process other := by
  simp only [State.process, changed.record_other differ]

/-- The two records of the process. -/
private theorem records (changed : state.Changed processId related state') :
    (state.record processId = none ∧ state'.record processId = none) ∨
      ∃ process process', state.record processId = some process ∧ state'.record processId = some process' ∧
        related process process' := by
  have rel := changed.2.1
  generalize state.record processId = first at rel
  generalize state'.record processId = second at rel
  cases rel with
  | none => exact .inl ⟨rfl, rfl⟩
  | some related => exact .inr ⟨_, _, rfl, rfl, related⟩

private theorem outside (changed : state.Changed processId related state') (unseen : Unseen related) :
    Option.Rel Outside (state.record processId) (state'.record processId) := by
  rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, related⟩
  · rw [first, second]; exact .none
  · rw [first, second]; exact .some (unseen.outside related)

/-- What another process reads of a record is the same in both. -/
private theorem get (changed : state.Changed processId related state') (unseen : Unseen related) {β : Type}
    {get : ProcessState → β} (same : ∀ first second, Outside first second → get second = get first)
    (missing : β) (other : PID) :
    ((state'.record other).map get).getD missing = ((state.record other).map get).getD missing := by
  by_cases differ : other = processId
  · subst differ
    rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, related⟩
    · rw [first, second]
    · simp [first, second, same _ _ (unseen.outside related)]
  · rw [changed.record_other differ]

private theorem alive (changed : state.Changed processId related state') (unseen : Unseen related) (other : PID) :
    state'.alive other = state.alive other := by
  have := changed.get unseen (get := fun process => process.exiting.isNone)
    (fun _ _ outside => by rw [outside.exiting]) false other
  simp only [State.alive]
  cases first : state.record other <;> cases second : state'.record other <;> simp_all

private theorem gone (changed : state.Changed processId related state') (unseen : Unseen related) :
    state'.gone = state.gone := by
  funext other; simp only [State.gone, changed.alive unseen]

private theorem process_get (changed : state.Changed processId related state') (unseen : Unseen related) {β : Type}
    {get : ProcessState → β} (same : ∀ first second, Outside first second → get second = get first)
    (empty : get {} = get {}) (other : PID) : get (state'.process other) = get (state.process other) := by
  by_cases differ : other = processId
  · subst differ
    simp only [State.process]
    rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, related⟩
    · rw [first, second]
    · simp [first, second, same _ _ (unseen.outside related)]
  · rw [changed.process_other differ]

private theorem set (changed : state.Changed processId related state') {other : PID} (differ : other ≠ processId)
    (process : ProcessState) : (state.set other process).Changed processId related (state'.set other process) := by
  refine ⟨fun third differ' => ?_, ?_, changed.2.2.1, changed.2.2.2⟩
  · simp only [State.record_set]
    split
    · rfl
    · exact changed.record_other differ'
  · simp only [State.record_set, Ne.symm differ, ↓reduceIte]
    exact changed.2.1

private theorem setRelated (changed : state.Changed processId related state') {process process' : ProcessState}
    (related' : related process process') :
    (state.set processId process).Changed processId related (state'.set processId process') := by
  refine ⟨fun third differ' => ?_, ?_, changed.2.2.1, changed.2.2.2⟩
  · simp only [State.record_set, differ', ↓reduceIte]
    exact changed.record_other differ'
  · simp only [State.record_set, ↓reduceIte]
    exact .some related'

private theorem remove (changed : state.Changed processId related state') {other : PID} (differ : other ≠ processId) :
    (state.remove other).Changed processId related (state'.remove other) := by
  refine ⟨fun third differ' => ?_, ?_, changed.2.2.1, changed.2.2.2⟩
  · simp only [State.record_remove]
    split
    · rfl
    · exact changed.record_other differ'
  · simp only [State.record_remove, Ne.symm differ, ↓reduceIte]
    exact changed.2.1

private theorem modify (changed : state.Changed processId related state') {other : PID} (differ : other ≠ processId)
    (change : ProcessState → ProcessState) :
    (state.modify other change).Changed processId related (state'.modify other change) := by
  unfold State.modify
  rw [changed.record_other differ]
  split
  · exact changed.set differ _
  · exact changed

/-- Changing the record of the process in a way the relation keeps. -/
private theorem modifyRelated (changed : state.Changed processId related state') {change : ProcessState → ProcessState}
    (keeps : ∀ {first second}, related first second → related (change first) (change second)) :
    (state.modify processId change).Changed processId related (state'.modify processId change) := by
  unfold State.modify
  rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, related'⟩
  · rw [first, second]; exact changed
  · rw [first, second]; exact changed.setRelated (keeps related')

private theorem timers (changed : state.Changed processId related state') (timers : List Timer) :
    { state with timers }.Changed processId related { state' with timers } :=
  ⟨changed.1, changed.2.1, rfl, changed.2.2.2⟩

/-- A signal falls back without changing the process, or only queues at it. -/
private theorem fallback (changed : state.Changed processId related state') (unseen : Unseen related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal ≠ .unlink id) :
    (state.fallback source target signal).Changed processId related (state'.fallback source target signal) := by
  by_cases same : source = processId
  · subst same
    cases signal <;> simp only [State.fallback]
    all_goals first
      | exact changed
      | exact changed.modifyRelated (fun related => unseen.push _ related)
      | exact absurd rfl (allowed rfl _)
  · cases signal <;> simp only [State.fallback] <;> first | exact changed | exact changed.modify same _

private theorem enqueue (changed : state.Changed processId related state') (unseen : Unseen related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal ≠ .unlink id) :
    (state.enqueue source target signal).Changed processId related (state'.enqueue source target signal) := by
  unfold State.enqueue
  by_cases same : target = processId
  · subst same
    rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, related'⟩
    · rw [first, second]; exact changed.fallback unseen allowed
    · rw [first, second]
      dsimp only
      have exiting : process'.exiting.isNone = process.exiting.isNone := by rw [(unseen.outside related').exiting]
      rw [exiting]
      split
      · have pushed := unseen.push { source, signal } related'
        unfold ProcessState.push at pushed
        exact changed.setRelated pushed
      · exact changed.fallback unseen allowed
  · rw [changed.record_other same]
    split
    · split
      · exact changed.set same _
      · exact changed.fallback unseen allowed
    · exact changed.fallback unseen allowed

private theorem parked (changed : state.Changed processId related state') (unseen : Unseen related) (other : PID) :
    (state'.process other).parked = (state.process other).parked :=
  changed.process_get unseen (fun _ _ outside => outside.parked) rfl other

private theorem unpark (changed : state.Changed processId related state') (unseen : Unseen related) (other : PID) :
    (state.unpark other).Changed processId related (state'.unpark other) := by
  unfold State.unpark
  rw [changed.parked unseen]
  split
  · have modified : (state.modify other fun process => { process with parked := none }).Changed processId related
        (state'.modify other fun process => { process with parked := none }) := by
      by_cases same : other = processId
      · subst same; exact changed.modifyRelated unseen.unpark
      · exact changed.modify same _
    exact modified.enqueue unseen fun _ _ => by simp
  · exact changed

private theorem send (changed : state.Changed processId related state') (unseen : Unseen related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal ≠ .unlink id) :
    (state.send source target signal).Changed processId related (state'.send source target signal) := by
  unfold State.send
  rw [changed.parked unseen]
  refine State.Changed.enqueue ?_ unseen allowed
  split
  · split
    · exact changed.unpark unseen source
    · exact changed
  · exact changed

/-- Whether a link is queued at a process is the same in both. -/
private theorem any_queue (changed : state.Changed processId related state') (unseen : Unseen related)
    (target : PID) (find : Entry → Bool) (only : ∀ entry, find entry = true → entry.signal = .link) :
    Kernel.any (state'.process target).queue find = Kernel.any (state.process target).queue find := by
  refine changed.process_get unseen (get := fun process => Kernel.any process.queue find) (fun first second outside => ?_)
    rfl target
  simp only [Kernel.any_eq]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨entry, mem, found⟩ <;> refine ⟨entry, ?_, found⟩
  · exact (outside.links _ (only _ found)).mp mem
  · exact (outside.links _ (only _ found)).mpr mem

private theorem eagerLink (changed : state.Changed processId related state') (unseen : Unseen related)
    (source target : PID) (reason : Term) : state'.eagerLink source target reason = state.eagerLink source target reason := by
  unfold State.eagerLink
  rw [changed.alive unseen, changed.process_get unseen (fun _ _ outside => outside.trapExit) rfl target,
    changed.any_queue unseen target _ fun entry found => by
      obtain ⟨_, signal⟩ := entry; cases signal <;> simp_all]

private theorem linkExit (changed : state.Changed processId related state') (unseen : Unseen related)
    (source target : PID) (reason : Term) :
    (state.linkExit source target reason).Changed processId related (state'.linkExit source target reason) := by
  unfold State.linkExit
  rw [changed.eagerLink unseen]
  split
  · by_cases same : target = processId
    · subst same; exact changed.modifyRelated (unseen.eagerExit source)
    · exact changed.modify same _
  · exact changed.send unseen fun _ _ => by simp

private theorem answer (changed : state.Changed processId related state') (unseen : Unseen related)
    (other : PID) (entry : Entry) :
    (state.answer other entry).Changed processId related (state'.answer other entry) := by
  unfold State.answer
  split <;> first | exact changed | exact changed.send unseen fun _ _ => by simp

private theorem allocate (changed : state.Changed processId related state') {other : PID}
    (differ : other ≠ processId) :
    (state'.allocate other).1 = (state.allocate other).1 ∧
      (state.allocate other).2.Changed processId related (state'.allocate other).2 :=
  ⟨by simp only [State.allocate, changed.process_other differ], changed.modify differ _⟩

private theorem foldl {γ : Type} {step : State → γ → State}
    (keeps : ∀ {state state'} item, state.Changed processId related state' →
      (step state item).Changed processId related (step state' item)) :
    ∀ (items : List γ) {state state'}, state.Changed processId related state' →
      (Kernel.foldl step state items).Changed processId related (Kernel.foldl step state' items)
  | [], _, _, changed => changed
  | item :: rest, _, _, changed => by
      have := foldl keeps rest (keeps item changed)
      simpa only [Kernel.foldl_eq, List.foldl_cons] using this

private theorem terminate (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) (reason : Term) :
    (state.terminate other reason).Changed processId related (state'.terminate other reason) := by
  unfold State.terminate
  simp only [changed.process_other differ, changed.2.2.1]
  refine State.Changed.foldl (fun target changed' => ?_) _ ((changed.timers _).set differ _)
  rw [changed'.eagerLink unseen]
  split
  · exact (changed'.modify differ _).linkExit unseen _ _ _
  · exact changed'

private theorem spawnWith (changed : state.Changed processId related state') {other : PID}
    (differ : other ≠ processId) (options : SpawnOptions)
    (fresh : Kernel.append other [(state.process other).children + 1] ≠ processId) :
    (state'.spawnWith other options).1 = (state.spawnWith other options).1 ∧
      (state.spawnWith other options).2.Changed processId related (state'.spawnWith other options).2 := by
  refine ⟨by simp only [State.spawnWith, changed.process_other differ], ?_⟩
  unfold State.spawnWith
  dsimp only
  rw [changed.process_other differ]
  have started := (changed.set differ ({ state.process other with children := (state.process other).children + 1 })).set
    fresh {}
  let child := Kernel.append other [(state.process other).children + 1]
  have linked := (started.modify differ fun process =>
      { process with links := Kernel.append process.links [(child, none)] }).modify fresh
    fun child => { child with links := [(other, none)] }
  by_cases monitor : options.monitor <;> by_cases link : options.link <;>
    simp only [monitor, link, ↓reduceIte, Bool.false_eq_true, State.allocate]
  · rw [linked.process_other differ]
    exact ((linked.modify differ _).modify differ _).modify fresh _
  · rw [started.process_other differ]
    exact ((started.modify differ _).modify differ _).modify fresh _
  · exact linked
  · exact started

end State.Changed

/-- Two answers to a request that agree but for a process's record. -/
private def Answer.Changed {β : Type} (processId : PID) (related : ProcessState → ProcessState → Prop) :
    Answer β → Answer β → Prop
  | .reply value state, .reply value' state' => value' = value ∧ state.Changed processId related state'
  | .wait waiting state, .wait waiting' state' => waiting' = waiting ∧ state.Changed processId related state'
  | .continue computation state, .continue computation' state' =>
      computation' = computation ∧ state.Changed processId related state'
  | _, _ => False

namespace State.Changed

variable {processId : PID} {related : ProcessState → ProcessState → Prop} {state state' : State}

private theorem request (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) {β : Type} (next : Term → Result β) (query : Request) :
    Answer.Changed processId related (state.request other next query) (state'.request other next query) := by
  cases query with
  | monitor target alias =>
    simp only [State.request]
    obtain ⟨same, allocated⟩ := changed.allocate differ
    rw [same]
    split
    · exact ⟨rfl, allocated⟩
    · exact ⟨rfl, (allocated.unpark unseen other).modify differ _⟩
  | demonitor reference flush =>
    simp only [State.request, changed.process_other differ]
    split <;> exact ⟨rfl, changed.modify differ _⟩
  | link target =>
    simp only [State.request, changed.process_other differ, changed.alive unseen]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed⟩
    · exact ⟨rfl, (changed.modify differ _).send unseen fun same => absurd same differ⟩
  | unlink target =>
    simp only [State.request, changed.process_other differ]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, (changed.modify differ _).send unseen fun same => absurd same differ⟩
    · exact ⟨rfl, changed⟩
  | exit target reason quirk =>
    simp only [State.request, changed.process_other differ]
    split
    · exact ⟨rfl, changed.send unseen fun same => absurd same differ⟩
    split
    · exact ⟨rfl, changed.send unseen fun same => absurd same differ⟩
    · exact ⟨rfl, changed.send unseen fun same => absurd same differ⟩
  | trapExit enabled =>
    simp only [State.request, changed.process_other differ]
    split
    · exact ⟨rfl, changed⟩
    · exact ⟨rfl, changed.modify differ _⟩
  | alive target =>
    simp only [State.request, changed.alive unseen]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed.send unseen fun same => absurd same differ⟩
    · exact ⟨rfl, changed.enqueue unseen fun same => absurd same differ⟩
  | sendAlias alias message =>
    exact ⟨rfl, changed.send unseen fun same => absurd same differ⟩
  | startTimer destination message duration =>
    simp only [State.request]
    obtain ⟨same, allocated⟩ := changed.allocate differ
    rw [same, allocated.alive unseen]
    refine ⟨rfl, ?_⟩
    split
    · rw [allocated.2.2.1]; exact allocated.timers _
    · exact allocated
  | cancelTimer reference =>
    simp only [State.request, changed.2.2.1, changed.process_other differ]
    split
    · exact ⟨by rw [changed.2.2.2], (changed.timers _).modify differ _⟩
    · exact ⟨rfl, changed⟩


private theorem exitSignal (changed : state.Changed processId related state') {target : PID}
    (differ : target ≠ processId) (source : PID) (reason : Term) (linked normalKills : Bool) :
    (state'.exitSignal target source reason linked normalKills).2 = (state.exitSignal target source reason linked normalKills).2 ∧
      (state.exitSignal target source reason linked normalKills).1.Changed processId related
        (state'.exitSignal target source reason linked normalKills).1 := by
  simp only [State.exitSignal, changed.process_other differ]
  split
  · exact ⟨rfl, changed⟩
  have removed : (if linked then state.modify target fun process =>
        { process with links := Kernel.filter (·.1 != source) process.links } else state).Changed processId related
      (if linked then state'.modify target fun process =>
        { process with links := Kernel.filter (·.1 != source) process.links } else state') := by
    split
    · exact changed.modify differ _
    · exact changed
  split
  · exact ⟨rfl, removed⟩
  split
  · exact ⟨rfl, removed.modify differ _⟩
  split
  · exact ⟨rfl, removed⟩
  · exact ⟨rfl, removed⟩

private theorem handle (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) (waiting : Option Wait) (entry : Entry) :
    (state'.handle other waiting entry).2 = (state.handle other waiting entry).2 ∧
      (state.handle other waiting entry).1.Changed processId related (state'.handle other waiting entry).1 := by
  have sends : ∀ {first second : State} (signal : Signal), first.Changed processId related second →
      (first.send other entry.source signal).Changed processId related (second.send other entry.source signal) :=
    fun _ changed' => changed'.send unseen fun same => absurd same differ
  have either : ∀ {condition : Prop} [Decidable condition] {first first' second second' : State},
      first.Changed processId related first' → second.Changed processId related second' →
      (if condition then first else second).Changed processId related (if condition then first' else second') :=
    fun one two => by split; exact one; exact two
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | message message => exact ⟨rfl, changed.modify differ _⟩
  | aliasMessage alias message =>
    simp only [State.handle, changed.process_other differ]
    exact ⟨trivial, either (changed.modify differ _) changed⟩
  | exit reason linked normalKills =>
    simp only [State.handle]
    obtain ⟨same, changed'⟩ := changed.exitSignal differ source reason linked normalKills
    exact ⟨by rw [same], changed'⟩
  | link =>
    simp only [State.handle, changed.process_other differ]
    exact ⟨trivial, either changed (changed.modify differ _)⟩
  | unlink id =>
    simp only [State.handle, changed.process_other differ]
    exact ⟨trivial, sends _ (either (changed.modify differ _) changed)⟩
  | unlinkAck id =>
    simp only [State.handle, changed.process_other differ]
    exact ⟨trivial, either (changed.modify differ _) changed⟩
  | monitor reference => exact ⟨rfl, changed.modify differ _⟩
  | down reference reason =>
    simp only [State.handle, changed.process_other differ]
    have dropped := either (condition := (isNormal reason && Kernel.contains (state.process other).eagerExits source) = true)
      (changed.modify differ fun process =>
        { process with eagerExits := Kernel.filter (· != source) process.eagerExits }) changed
    split
    · exact ⟨rfl, ((dropped.modify differ _).modify differ _)⟩
    · exact ⟨rfl, dropped⟩
  | isAlive => exact ⟨rfl, sends _ changed⟩
  | reply value =>
    simp only [State.handle]
    split <;> exact ⟨rfl, changed⟩
  | flush =>
    simp only [State.handle]
    split <;> exact ⟨rfl, changed⟩

private theorem linkPhase (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) (target : PID) :
    Option.Rel (State.Changed processId related) (state.linkPhase other target) (state'.linkPhase other target) := by
  simp only [State.linkPhase, changed.record_other differ]
  split
  · split
    · split
      · exact .some (((changed.set differ _).linkExit unseen _ _ _))
      · exact .none
    · exact .none
  · exact .none

private theorem phase (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) :
    Option.Rel (State.Changed processId related) (state.phase other) (state'.phase other) := by
  simp only [State.phase, changed.record_other differ]
  split
  · split
    · split
      · exact .none
      · exact .some ((changed.set differ _).send unseen fun same => absurd same differ)
      · split
        · exact .some ((changed.set differ _).answer unseen _ _)
        · exact .none
    · exact .none
  · exact .none

private theorem fire (changed : state.Changed processId related state') (unseen : Unseen related)
    (timer : Timer) :
    (state.fire timer).Changed processId related (state'.fire timer) := by
  simp only [State.fire, changed.2.2.1]
  exact (changed.timers _).enqueue unseen fun _ _ => by simp

end State.Changed

/-- Two transitions that agree but for a process's record. -/
private def Transition.Changed (processId : PID) (related : ProcessState → ProcessState → Prop)
    (transition transition' : Transition α) : Prop :=
  transition'.event = transition.event ∧ transition'.tasks = transition.tasks ∧
    transition'.finished = transition.finished ∧ transition'.exhausted = transition.exhausted ∧
    transition.state.Changed processId related transition'.state

namespace State.Changed

variable {processId : PID} {related : ProcessState → ProcessState → Prop} {state state' : State}

private theorem inertEntry (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) (entry : Entry) :
    state'.inertEntry other entry = state.inertEntry other entry := by
  simp only [State.inertEntry, State.allocated, changed.process_other differ, changed.gone unseen]

private theorem ended (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) {γ : Type}
    (finish : Except Exception γ → Option (Except Exception α)) (event : Event) (reason : Term)
    (result : Except Exception γ) :
    Transition.Changed processId related (Task.ended finish event state other reason result)
      (Task.ended finish event state' other reason result) :=
  ⟨rfl, rfl, rfl, rfl, changed.terminate unseen differ reason⟩

private theorem own (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) (task : Task α)
    (fresh : Kernel.append other [(state.process other).children + 1] ≠ processId) :
    Option.Rel (Transition.Changed processId related) (task.own state other).head? (task.own state' other).head? := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => exact .none
  | none =>
  have view : state'.view other = state.view other := by simp only [State.view, changed.process_other differ]
  cases computation with
  | ok value => exact .some (changed.ended unseen differ _ _ _ _)
  | error exception =>
    cases exception with
    | exhausted => exact .some ⟨rfl, rfl, rfl, rfl, changed.remove differ⟩
    | _ => exact .some (changed.ended unseen differ _ _ _ _)
  | get next =>
    simp only [Task.own, view, List.head?_cons]
    exact .some ⟨rfl, rfl, rfl, rfl, changed⟩
  | set updated next =>
    simp only [Task.own, List.head?_cons]
    exact .some ⟨rfl, rfl, rfl, rfl, changed.modify differ _⟩
  | schedule options child next =>
    obtain ⟨same, spawned⟩ := changed.spawnWith differ options fresh
    simp only [Task.own, same, List.head?_cons]
    exact .some ⟨rfl, rfl, rfl, rfl, spawned⟩
  | send destination message next =>
    simp only [Task.own, List.head?_cons]
    exact .some ⟨rfl, rfl, rfl, rfl, changed.send unseen fun same => absurd same differ⟩
  | receive timeout select next =>
    simp only [Task.own, view, changed.process_other differ]
    split
    · exact .some ⟨rfl, rfl, rfl, rfl, changed.modify differ _⟩
    · have awaited : state'.awaitedEntry other = state.awaitedEntry other := funext fun entry => by
        simp only [State.awaitedEntry, changed.inertEntry unseen differ]
      rw [awaited]
      split
      · exact .none
      · split
        · exact .none
        · exact .some ⟨rfl, rfl, rfl, rfl, changed⟩
  | request query next =>
    simp only [Task.own]
    have answered := changed.request unseen differ next query
    revert answered
    generalize state.request other next query = answer
    generalize state'.request other next query = answer'
    intro answered
    cases answer <;> cases answer' <;> simp only [Answer.Changed] at answered
    all_goals obtain ⟨rfl, answered⟩ := answered
    all_goals exact .some ⟨rfl, rfl, rfl, rfl, answered⟩

private theorem handleTask (changed : state.Changed processId related state') (unseen : Unseen related)
    {other : PID} (differ : other ≠ processId) (task : Task α) :
    Option.Rel (Transition.Changed processId related) (task.handle state other).head?
      (task.handle state' other).head? := by
  simp only [Task.handle, changed.process_other differ]
  split
  · exact .none
  · rename_i entry rest _
    obtain ⟨same, handled⟩ := (changed.set differ { state.process other with queue := rest }).handle unseen differ
      (task.wait.map (·.1)) entry
    revert same handled
    generalize ((state.set other { state.process other with queue := rest }).handle other (task.wait.map (·.1)) entry) = first
    generalize ((state'.set other { state.process other with queue := rest }).handle other (task.wait.map (·.1)) entry) = second
    obtain ⟨handled, resumed, exits⟩ := first
    obtain ⟨handled', resumed', exits'⟩ := second
    intro same changed'
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    dsimp only
    split
    · exact .some (changed'.ended unseen differ _ _ _ _)
    · split
      · exact .some ⟨rfl, rfl, rfl, rfl, changed'⟩
      · exact .some ⟨rfl, rfl, rfl, rfl, changed'⟩

end State.Changed

/-- A process's own step leaves tasks of itself and of the child it spawns. -/
private theorem Task.own_pids {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.own state processId) :
    ∀ entry ∈ transition.tasks, entry.1 = processId ∨
      entry.1 = Kernel.append processId [(state.process processId).children + 1] := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    cases computation with
    | schedule options child next =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      simp [State.spawnWith]
    | receive =>
      simp only [Task.own] at mem
      repeat' split at mem
      all_goals (simp only [List.mem_singleton, List.not_mem_nil] at mem; try (subst mem; simp))
    | request =>
      simp only [Task.own] at mem
      split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> simp
    | error exception =>
      cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;> simp [Task.ended]
    | _ => simp only [Task.own, List.mem_singleton] at mem; subst mem; simp [Task.ended]

/-- A process's own step, by its task. -/
private theorem Config.stepOf_own_of {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.own state processId).head? = some transition) :
    (Config.running state tasks finished false).stepOf (.own processId) = some (transition.event,
      if transition.exhausted then .running { transition.state with processes := [], timers := [] } [] finished true
      else .running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
        (transition.finished.orElse fun _ => finished) false) := by
  obtain ⟨before, after, split⟩ := splitAt_of_lookup lookup
  simp [Config.stepOf, split, head, Transition.apply, rewriteTask_of_splitAt split]

/-- Handling a signal, by the process's task. -/
private theorem Config.stepOf_handle_of {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.handle state processId).head? = some transition) :
    (Config.running state tasks finished false).stepOf (.handle processId) = some (transition.event,
      if transition.exhausted then .running { transition.state with processes := [], timers := [] } [] finished true
      else .running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
        (transition.finished.orElse fun _ => finished) false) := by
  obtain ⟨before, after, split⟩ := splitAt_of_lookup lookup
  simp [Config.stepOf, split, head, Transition.apply, rewriteTask_of_splitAt split]

private theorem rel_of_some {β γ : Type _} {relate : β → γ → Prop} {first : β} {second : Option γ}
    (rel : Option.Rel relate (some first) second) : ∃ second', second = some second' ∧ relate first second' := by
  cases rel with
  | some related => exact ⟨_, rfl, related⟩

/-- The child a process with a task spawns next has no task. -/
private theorem TasksFresh.child {state : State} {tasks : List (PID × Task α)} (fresh : TasksFresh state tasks)
    {processId other : PID} {task task' : Task α} (lookup : Kernel.lookup processId tasks = some task)
    (lookup' : Kernel.lookup other tasks = some task') :
    Kernel.append processId [(state.process processId).children + 1] ≠ other := fun same =>
  fresh.2.2 _ (mem_of_lookup lookup) _ (mem_of_lookup lookup') _ (Nat.lt_succ_self _)
    (by rw [same]; exact List.prefix_refl _)

/-- A step of a process's task after a change of another process's record
and task: the same transition, then the change. -/
private theorem Config.transition_changed {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId other : PID}
    {related : ProcessState → ProcessState → Prop} {task' : Task α} {first : Transition α}
    {firsts seconds : List (Transition α)} (differ : other ≠ processId)
    {elapsed : PID → Nat → Nat} (pids : ∀ entry ∈ first.tasks, entry.1 ≠ processId)
    (related' : Option.Rel (Transition.Changed processId related) firsts.head? seconds.head?)
    (head : firsts.head? = some first) (within : first.state.Within elapsed)
    (within' : ∀ second, seconds.head? = some second → second.state.Within elapsed) :
    ∃ second : Transition α, seconds.head? = some second ∧ second.event = first.event ∧
      ((if second.exhausted then Config.running { second.state with processes := [], timers := [] } [] finished true
        else .running second.state.normalize
          (rewriteTask other (fun _ => second.tasks) (rewriteTask processId (fun _ => [(processId, task')]) tasks))
          (second.finished.orElse fun _ => finished) false) =
        (if first.exhausted then Config.running { first.state with processes := [], timers := [] } [] finished true
        else .running first.state.normalize (rewriteTask other (fun _ => first.tasks) tasks)
          (first.finished.orElse fun _ => finished) false) ∨
      ∃ (raw raw' : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α)),
        raw.Changed processId related raw' ∧ raw.Within elapsed ∧ raw'.Within elapsed ∧
        Kernel.lookup processId tasks₁ = Kernel.lookup processId tasks ∧
        (if first.exhausted then Config.running { first.state with processes := [], timers := [] } [] finished true
          else .running first.state.normalize (rewriteTask other (fun _ => first.tasks) tasks)
            (first.finished.orElse fun _ => finished) false) = .running raw.normalize tasks₁ finished₁ false ∧
        (if second.exhausted then Config.running { second.state with processes := [], timers := [] } [] finished true
          else .running second.state.normalize
            (rewriteTask other (fun _ => second.tasks) (rewriteTask processId (fun _ => [(processId, task')]) tasks))
            (second.finished.orElse fun _ => finished) false) =
          .running raw'.normalize (rewriteTask processId (fun _ => [(processId, task')]) tasks₁) finished₁ false) := by
  obtain ⟨second, head', event', tasks', finished', exhausted', changed'⟩ := rel_of_some (head ▸ related')
  refine ⟨second, head', event', ?_⟩
  rw [exhausted', tasks', finished']
  split
  · left
    have elapsed := changed'.2.2.2
    revert elapsed
    cases first.state; cases second.state
    intro elapsed
    simp only at elapsed
    rw [elapsed]
  · right
    refine ⟨first.state, second.state, _, _, changed', within, within' _ head',
      lookup_rewriteTask (Ne.symm differ) (fun _ => pids) tasks, rfl, ?_⟩
    rw [rewriteTask_comm (Ne.symm differ) (fun _ entry mem => by
        simp only [List.mem_singleton] at mem; subst mem; exact Ne.symm differ) (fun _ => pids)]

/-- The step of another key, after a change of a live process's record that
the step cannot see and of its task: the same step, then the change. -/
private theorem Config.step_changed {state state' : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {related : ProcessState → ProcessState → Prop}
    {task task' : Task α} {key : Key} {event : Event} {next : Config α}
    {elapsed : PID → Nat → Nat} (within : state.Within elapsed) (within' : state'.Within elapsed)
    (changed : state.Changed processId related state') (unseen : Unseen related) (fresh : TasksFresh state tasks)
    (lookup : Kernel.lookup processId tasks = some task) (owner : key.owner ≠ some processId)
    (step : (Config.running state tasks finished false).stepOf key = some (event, next)) :
    ∃ next', (Config.running state' (rewriteTask processId (fun _ => [(processId, task')]) tasks) finished false).stepOf
        key = some (event, next') ∧
      (next' = next ∨ ∃ (raw raw' : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α)),
        raw.Changed processId related raw' ∧ raw.Within elapsed ∧ raw'.Within elapsed ∧
        Kernel.lookup processId tasks₁ = Kernel.lookup processId tasks ∧
        next = .running raw.normalize tasks₁ finished₁ false ∧
        next' = .running raw'.normalize (rewriteTask processId (fun _ => [(processId, task')]) tasks₁) finished₁ false) := by
  have alive : state.alive processId = true := fresh.2.1 _ (mem_of_lookup lookup)
  have exiting : ∀ {process : ProcessState}, state.record processId = some process → process.exiting = none :=
    fun found => by simpa [State.alive, found] using alive
  have tasks' : ∀ {other : PID}, other ≠ processId → ∀ {other' : Task α}, Kernel.lookup other tasks = some other' →
      Kernel.lookup other (rewriteTask processId (fun _ => [(processId, task')]) tasks) = some other' := by
    intro other differ other' found
    rw [lookup_rewriteTask differ (fun _ entry mem => by
      simp only [List.mem_singleton] at mem; subst mem; exact Ne.symm differ)]
    exact found
  -- Steps that keep the tasks.
  have kept : ∀ {first second : Option State} {event' : Event},
      Option.Rel (State.Changed processId related) first second →
      (∀ raw, first = some raw → raw.Within elapsed) → (∀ raw', second = some raw' → raw'.Within elapsed) →
      first.map (fun raw => (event', Config.running raw.normalize tasks finished false)) = some (event, next) →
      ∃ next', second.map (fun raw => (event', Config.running raw.normalize
          (rewriteTask processId (fun _ => [(processId, task')]) tasks) finished false)) = some (event, next') ∧
        (next' = next ∨ ∃ (raw raw' : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α)),
          raw.Changed processId related raw' ∧ raw.Within elapsed ∧ raw'.Within elapsed ∧
          Kernel.lookup processId tasks₁ = Kernel.lookup processId tasks ∧
          next = .running raw.normalize tasks₁ finished₁ false ∧
          next' = .running raw'.normalize (rewriteTask processId (fun _ => [(processId, task')]) tasks₁) finished₁ false) := by
    intro first second event' rel sorted sorted' found
    cases rel with
    | none => simp at found
    | some changed' =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨_, rfl, .inr ⟨_, _, _, _, changed', sorted _ rfl, sorted' _ rfl, rfl, rfl, rfl⟩⟩
  cases key with
  | own other =>
    have differ : other ≠ processId := fun same => owner (by simp [Key.owner, same])
    obtain ⟨other', first, found, head, -⟩ := Config.stepOf_own step
    rw [Config.stepOf_own_of (finished := finished) found head] at step
    simp only [Option.some.injEq, Prod.mk.injEq] at step
    obtain ⟨rfl, rfl⟩ := step
    obtain ⟨second, head', event', result⟩ := Config.transition_changed (finished := finished) (task' := task') differ
      (fun entry inside => by
        rcases Task.own_pids (List.mem_of_head? head) entry inside with same | child
        · rw [same]; exact differ
        · rw [child]; exact fresh.child found lookup)
      (changed.own unseen differ other' (fresh.child found lookup)) head
      (within.own (List.mem_of_head? head)) (fun _ head' => within'.own (List.mem_of_head? head'))
    rw [← event']
    exact ⟨_, Config.stepOf_own_of (tasks' differ found) head', result⟩
  | handle other =>
    have differ : other ≠ processId := fun same => owner (by simp [Key.owner, same])
    obtain ⟨other', first, found, head, -⟩ := Config.stepOf_handle step
    rw [Config.stepOf_handle_of (finished := finished) found head] at step
    simp only [Option.some.injEq, Prod.mk.injEq] at step
    obtain ⟨rfl, rfl⟩ := step
    obtain ⟨second, head', event', result⟩ := Config.transition_changed (finished := finished) (task' := task') differ
      (fun entry inside => by rw [(Task.handle_pids (List.mem_of_head? head)).1 entry inside]; exact differ)
      (changed.handleTask unseen differ other') head
      (within.handleStep (List.mem_of_head? head)) (fun _ head' => within'.handleStep (List.mem_of_head? head'))
    rw [← event']
    exact ⟨_, Config.stepOf_handle_of (tasks' differ found) head', result⟩
  | phase other =>
    by_cases same : other = processId
    · subst same
      simp only [Config.stepOf, State.phase, Option.map_eq_some_iff] at step
      obtain ⟨_, found, -⟩ := step
      split at found
      · rename_i process record
        rw [exiting record] at found
        simp at found
      · simp at found
    · exact kept (changed.phase unseen same) (fun _ found => within.phase found)
        (fun _ found => within'.phase found) step
  | link other target =>
    by_cases same : other = processId
    · subst same
      simp only [Config.stepOf, State.linkPhase, Option.map_eq_some_iff] at step
      obtain ⟨_, found, -⟩ := step
      split at found
      · rename_i process record
        rw [exiting record] at found
        simp at found
      · simp at found
    · exact kept (changed.linkPhase unseen same target) (fun _ found => within.linkPhase found)
        (fun _ found => within'.linkPhase found) step
  | unpark other =>
    simp only [Config.stepOf, changed.parked unseen] at step ⊢
    cases parked : (state.process other).parked with
    | none => simp [parked] at step
    | some pair =>
      simp only [parked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at step ⊢
      obtain ⟨rfl, rfl⟩ := step
      exact ⟨_, ⟨rfl, rfl⟩, .inr ⟨_, _, _, _, changed.unpark unseen other, within.unpark other,
        within'.unpark other, rfl, rfl, rfl⟩⟩
  | fire reference =>
    have firing : state'.firing = state.firing := by simp only [State.firing, changed.2.2.1]
    simp only [Config.stepOf, firing, Kernel.find?_eq] at step ⊢
    cases timer : List.find? (·.reference == reference) state.firing with
    | none => simp [timer] at step
    | some timer' =>
      simp only [timer, Option.map_some, Option.some.injEq, Prod.mk.injEq] at step ⊢
      obtain ⟨rfl, rfl⟩ := step
      exact ⟨_, ⟨rfl, rfl⟩, .inr ⟨_, _, _, _, changed.fire unseen timer', within.fire timer',
        within'.fire timer', rfl, rfl, rfl⟩⟩

/-! ### Normalizing a live record again -/

private theorem normRecord_live {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) :
    normRecord gone processId process = { process with
      queue := Kernel.filter (fun entry => !inert gone processId process entry) process.queue
      links := Kernel.filter (fun link => !(link.2.isSome && gone link.1)) process.links } := by
  unfold normRecord; rw [live]

private theorem lookup_filter_congr {β : Type} {key : PID} {keep keep' : PID × β → Bool} :
    ∀ (entries : List (PID × β)), (∀ entry ∈ entries, entry.1 = key → keep entry = keep' entry) →
      (entries.filter keep).lookup key = (entries.filter keep').lookup key
  | [], _ => rfl
  | (other, value) :: rest, same => by
      have ih := lookup_filter_congr rest fun entry mem => same entry (List.mem_cons_of_mem _ mem)
      by_cases equal : other = key
      · subst equal
        have keeps := same (other, value) List.mem_cons_self rfl
        cases first : keep (other, value) <;> rw [first] at keeps <;>
          simp [List.filter_cons, first, ← keeps, ih]
      · have differ : (key == other) = false := by simp [Ne.symm equal]
        cases first : keep (other, value) <;> cases second : keep' (other, value) <;>
          simp [List.filter_cons, first, second, List.lookup_cons, differ, ih]

private theorem lookup_filter_of_keep {β : Type} {key : PID} {keep : PID × β → Bool} :
    ∀ {entries : List (PID × β)}, (∀ entry ∈ entries, entry.1 = key → keep entry = true) →
      (entries.filter keep).lookup key = entries.lookup key
  | [], _ => rfl
  | (other, value) :: rest, kept => by
      have ih := lookup_filter_of_keep (keep := keep) fun entry mem => kept entry (List.mem_cons_of_mem _ mem)
      by_cases same : other = key
      · subst same
        simp [List.filter_cons, kept (other, value) List.mem_cons_self rfl]
      · have differ : (key == other) = false := by simp [Ne.symm same]
        by_cases keeps : keep (other, value) = true
        · simp [List.filter_cons, keeps, List.lookup_cons, differ, ih]
        · simp [List.filter_cons, keeps, List.lookup_cons, differ, ih]

/-- Whether a queued signal does nothing depends on the record only through
fields normalizing keeps, and on links only of processes not gone. -/
private theorem inert_congr {gone : PID → Bool} {processId : PID} {process process' : ProcessState}
    (refCounter : process'.refCounter = process.refCounter) (monitoring : process'.monitoring = process.monitoring)
    (aliases : process'.aliases = process.aliases)
    (links : ∀ source, gone source = false → Kernel.lookup source process'.links = Kernel.lookup source process.links)
    (entry : Entry) : inert gone processId process' entry = inert gone processId process entry := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp only [inert, refCounter, monitoring, aliases]
  rename_i id
  cases gone' : gone source
  · rw [links source gone']
  · simp

private theorem inert_normRecord {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) (entry : Entry) :
    inert gone processId (normRecord gone processId process) entry = inert gone processId process entry := by
  rw [normRecord_live live]
  apply inert_congr
  · rfl
  · rfl
  · rfl
  · intro source notGone
    simp only [Kernel.lookup_eq, Kernel.filter_eq]
    exact lookup_filter_of_keep fun entry _ same => by simp [same, notGone]

private theorem normRecord_push {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) (entry : Entry) :
    normRecord gone processId ((normRecord gone processId process).push entry) =
      normRecord gone processId (process.push entry) := by
  have live₁ : ((normRecord gone processId process).push entry).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show (process.push entry).exiting = none from live)]
  have inertPushed : ∀ other : ProcessState, inert gone processId (other.push entry) = inert gone processId other :=
    fun _ => rfl
  rw [inertPushed, inertPushed, funext (inert_normRecord (gone := gone) (processId := processId) live),
    normRecord_live live]
  simp [ProcessState.push, Kernel.filter_eq, Kernel.append_eq, List.filter_append, List.filter_filter]

private theorem normRecord_eagerExit {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) (source : PID) :
    normRecord gone processId ((normRecord gone processId process).eagerExit source) =
      normRecord gone processId (process.eagerExit source) := by
  have live₁ : ((normRecord gone processId process).eagerExit source).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show (process.eagerExit source).exiting = none from live)]
  -- Removing a link only makes more signals inert.
  have more : ∀ entry, inert gone processId process entry = true →
      inert gone processId (process.eagerExit source) entry = true := by
    intro entry inert'
    obtain ⟨from', signal⟩ := entry
    cases signal <;> simp only [inert, ProcessState.eagerExit] at inert' ⊢ <;> try exact inert'
    rename_i id
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Kernel.lookup_eq, Kernel.filter_eq] at inert' ⊢
    rcases inert' with gone' | missing
    · exact .inl gone'
    · right
      by_cases same : from' = source
      · subst same
        rw [show List.lookup from' (process.links.filter (·.1 != from')) = none from by
          induction process.links with
          | nil => rfl
          | cons head rest ih =>
            obtain ⟨key, value⟩ := head
            by_cases equal : key = from'
            · subst equal; simpa [List.filter_cons] using ih
            · have differ : (from' == key) = false := by simp [Ne.symm equal]
              simp [equal, List.lookup_cons, differ, ih]]
        simp
      · rw [lookup_filter_of_keep fun entry _ equal => by simp [equal, same]]
        exact missing
  have same : inert gone processId ((normRecord gone processId process).eagerExit source) =
      inert gone processId (process.eagerExit source) := by
    funext entry
    refine inert_congr (process := process.eagerExit source)
      (process' := (normRecord gone processId process).eagerExit source) ?_ ?_ ?_ ?_ entry
    · rw [normRecord_live live]; rfl
    · rw [normRecord_live live]; rfl
    · rw [normRecord_live live]; rfl
    · intro from' notGone
      rw [normRecord_live live]
      simp only [ProcessState.eagerExit, Kernel.lookup_eq, Kernel.filter_eq, List.filter_filter]
      exact lookup_filter_congr _ fun entry _ equal => by simp [equal, notGone]
  rw [same]
  rw [normRecord_live live]
  simp only [ProcessState.eagerExit, Kernel.filter_eq, List.filter_filter]
  congr 1
  · refine List.filter_congr fun entry _ => ?_
    cases inert' : inert gone processId (process.eagerExit source) entry
    · have := mt (more entry) (by simp [inert'])
      simp [ProcessState.eagerExit, this]
    · simp only [ProcessState.eagerExit, Kernel.filter_eq] at inert'
      simp [inert']
  · refine List.filter_congr fun entry _ => ?_
    cases gone entry.fst <;> cases entry.snd.isSome <;> simp

private theorem normRecord_unpark {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) :
    normRecord gone processId { normRecord gone processId process with parked := none } =
      normRecord gone processId { process with parked := none } := by
  have live₁ : ({ normRecord gone processId process with parked := none } : ProcessState).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show ({ process with parked := none } : ProcessState).exiting = none
    from live)]
  have unparked : ∀ other : ProcessState, inert gone processId { other with parked := none } = inert gone processId other :=
    fun _ => rfl
  rw [unparked, unparked, funext (inert_normRecord (gone := gone) (processId := processId) live), normRecord_live live]
  simp [Kernel.filter_eq, List.filter_filter]

/-- A change of a live record that steps of other processes neither read nor
undo, while `ok` holds of the record, which their changes keep. -/
private structure Hidden (ok : ProcessState → Prop) (change : ProcessState → ProcessState) : Prop where
  exiting : ∀ {process}, ok process → (change process).exiting = process.exiting
  trapExit : ∀ {process}, ok process → (change process).trapExit = process.trapExit
  parked : ∀ {process}, ok process → (change process).parked = process.parked
  links : ∀ {process}, ok process → ∀ entry : Entry, entry.signal = .link →
    (entry ∈ (change process).queue ↔ entry ∈ process.queue)
  push : ∀ {process} entry, ok process → ok (process.push entry) ∧ change (process.push entry) = (change process).push entry
  eagerExit : ∀ {process} source, ok process →
    ok (process.eagerExit source) ∧ change (process.eagerExit source) = (change process).eagerExit source
  unpark : ∀ {process}, ok process → ok { process with parked := none } ∧
    change { process with parked := none } = { change process with parked := none }

/-- A live record after a change, up to what normalizing drops. -/
private def Forced (processId : PID) (ok : ProcessState → Prop) (change : ProcessState → ProcessState)
    (process process' : ProcessState) : Prop :=
  ok process ∧ process.exiting = none ∧ process'.exiting = none ∧
    ∀ gone, normRecord gone processId process' = normRecord gone processId (change process)

private theorem mem_normRecord_link {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) {entry : Entry} (link : entry.signal = .link) :
    entry ∈ (normRecord gone processId process).queue ↔ entry ∈ process.queue := by
  rw [normRecord_live live]
  obtain ⟨source, signal⟩ := entry
  simp only at link; subst link
  simp [Kernel.filter_eq, inert]

private theorem Hidden.unseen {processId : PID} {ok : ProcessState → Prop} {change : ProcessState → ProcessState}
    (hidden : Hidden ok change) : Unseen (Forced processId ok change) where
  outside := by
    intro first second ⟨ok', live, live', same⟩
    have live'' : (change first).exiting = none := (hidden.exiting ok').trans live
    have field : ∀ {β : Type} (get : ProcessState → β), (∀ process : ProcessState, process.exiting = none →
        get (normRecord (fun _ => false) processId process) = get process) → get second = get (change first) :=
      fun get keeps => by rw [← keeps _ live', same, keeps _ live'']
    refine ⟨by rw [live, live'], ?_, ?_, fun entry link => ?_⟩
    · rw [field (·.trapExit) fun _ live => by rw [normRecord_live live], hidden.trapExit ok']
    · rw [field (·.parked) fun _ live => by rw [normRecord_live live], hidden.parked ok']
    · rw [← mem_normRecord_link (gone := fun _ => false) (processId := processId) live' link, same,
        mem_normRecord_link live'' link, hidden.links ok' entry link]
  push := by
    intro first second entry ⟨ok', live, live', same⟩
    obtain ⟨ok'', pushed⟩ := hidden.push entry ok'
    refine ⟨ok'', live, live', fun gone => ?_⟩
    rw [← normRecord_push live', same gone, normRecord_push ((hidden.exiting ok').trans live), pushed]
  eagerExit := by
    intro first second source ⟨ok', live, live', same⟩
    obtain ⟨ok'', exited⟩ := hidden.eagerExit source ok'
    refine ⟨ok'', live, live', fun gone => ?_⟩
    rw [← normRecord_eagerExit live', same gone, normRecord_eagerExit ((hidden.exiting ok').trans live), exited]
  unpark := by
    intro first second ⟨ok', live, live', same⟩
    obtain ⟨ok'', unparked⟩ := hidden.unpark ok'
    refine ⟨ok'', live, live', fun gone => ?_⟩
    rw [← normRecord_unpark live', same gone, normRecord_unpark ((hidden.exiting ok').trans live), unparked]

/-! ### Normalizing around a forced change -/

/-- Sorted states with the same records, timers and elapsed times are equal. -/
private theorem State.ext_records {state state' : State} (sorted : state.Sorted) (sorted' : state'.Sorted)
    (records : ∀ processId, state'.record processId = state.record processId)
    (timers : state'.timers = state.timers) (elapsed : state'.elapsed = state.elapsed) : state' = state := by
  have processes : state'.processes = state.processes :=
    Sorted.ext sorted' sorted fun processId => by
      have := records processId; simpa [State.record, Kernel.lookup_eq] using this
  cases state; cases state'
  simp only at processes timers elapsed
  simp only [State.mk.injEq]
  exact ⟨processes, timers, elapsed⟩

private theorem ProcessState.finished_live {process : ProcessState} (live : process.exiting = none) :
    process.finished = false := by
  simp [ProcessState.finished, live]

/-- Normalizing drops from a record, for which processes are gone, only what it
drops for whichever processes are gone. -/
private theorem normRecord_any {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none)
    (inert' : ∀ entry ∈ process.queue, inert gone processId process entry = true →
      ∀ gone', inert gone' processId process entry = true)
    (links : ∀ link ∈ process.links, (link.2.isSome && gone link.1) = false) (gone' : PID → Bool) :
    normRecord gone' processId (normRecord gone processId process) = normRecord gone' processId process := by
  have kept : Kernel.filter (fun link => !(link.2.isSome && gone link.1)) process.links = process.links := by
    rw [Kernel.filter_eq]; exact List.filter_eq_self.mpr fun link mem => by simp [links link mem]
  have live₁ : (normRecord gone processId process).exiting = none := by rw [normRecord_live live]; exact live
  have same : inert gone' processId (normRecord gone processId process) = inert gone' processId process := by
    funext entry
    apply inert_congr
    · rw [normRecord_live live]
    · rw [normRecord_live live]
    · rw [normRecord_live live]
    · intro source _; rw [normRecord_live live]; simp only [kept]
  rw [normRecord_live live₁, same, normRecord_live (gone := gone) live, normRecord_live (gone := gone') live, kept]
  simp only [Kernel.filter_eq, List.filter_filter]
  congr 1
  refine List.filter_congr fun entry mem => ?_
  cases first : inert gone' processId process entry
  · cases second : inert gone processId process entry
    · rfl
    · simp [inert' entry mem second gone'] at first
  · rfl

/-- After a forced change of a live record at a normalized state, the
normalized state differs only in that record, by the change. -/
private theorem State.changed_forced {state : State} {processId : PID} {process : ProcessState}
    {ok : ProcessState → Prop} {change : ProcessState → ProcessState} (sorted : state.Sorted)
    (normalized : state.normalize = state) (found : state.record processId = some process)
    (live : process.exiting = none) (ok' : ok process) (hidden : Hidden ok change)
    (renormalize : ∀ gone, normRecord gone processId (normRecord state.gone processId (change process)) =
      normRecord gone processId (change process)) :
    state.Changed processId (Forced processId ok change) (state.set processId (change process)).normalize := by
  have sorted' : (state.set processId (change process)).Sorted := Sorted.insertRecord sorted _ _
  have live' : (change process).exiting = none := (hidden.exiting ok').trans live
  have gone : (state.set processId (change process)).gone = state.gone := by
    funext other
    simp only [State.gone, State.alive, State.record_set]
    by_cases same : other = processId
    · subst same; simp [found, live, live']
    · simp [same]
  refine ⟨fun other differ => ?_, ?_, rfl, rfl⟩
  · rw [State.record_normalize' sorted', gone, State.record_set, if_neg differ]
    conv => rhs; rw [← normalized]
    rw [State.record_normalize' sorted]
  · rw [State.record_normalize' sorted', gone, State.record_set, if_pos rfl, found]
    simp only [Option.map_some, Option.filter, ProcessState.finished_live
      (show (normRecord state.gone processId (change process)).exiting = none by rw [normRecord_live live']; exact live'),
      Bool.not_false, ↓reduceIte]
    refine .some ⟨ok', live, ?_, renormalize⟩
    rw [normRecord_live live']; exact live'

/-- A forced change taken after another step reaches what the other step
reaches after the change, when normalizing before the change drops nothing
it reads. -/
private theorem State.forced_close {raw raw' : State} {processId : PID} {process : ProcessState}
    {ok : ProcessState → Prop} {change : ProcessState → ProcessState} (sorted : raw.Sorted) (sorted' : raw'.Sorted)
    (changed : raw.Changed processId (Forced processId ok change) raw') (unseen : Unseen (Forced processId ok change))
    (found : raw.record processId = some process)
    (live : (change (normRecord raw.gone processId process)).exiting = none)
    (renormalize : normRecord raw.gone processId (change (normRecord raw.gone processId process)) =
      normRecord raw.gone processId (change process)) :
    (raw.normalize.set processId (change (normRecord raw.gone processId process))).normalize = raw'.normalize := by
  rcases changed.records with ⟨missing, -⟩ | ⟨first, second, found', found'', -, live₀, live', same⟩
  · rw [found] at missing; cases missing
  rw [found] at found'; cases found'
  have sortedNormal : raw.normalize.Sorted := Sorted.normalize sorted
  have sortedSet : (raw.normalize.set processId (change (normRecord raw.gone processId process))).Sorted :=
    Sorted.insertRecord sortedNormal _ _
  have gone : (raw.normalize.set processId (change (normRecord raw.gone processId process))).gone = raw.gone := by
    funext other
    simp only [State.gone, State.alive, State.record_set]
    by_cases equal : other = processId
    · subst equal
      simp [live, found, live₀]
    · simp only [equal, ↓reduceIte]
      have := State.gone_normalize sorted other
      simp only [State.gone, State.alive] at this
      exact this
  refine (State.ext_records (Sorted.normalize sorted') (Sorted.normalize sortedSet) (fun other => ?_)
    changed.2.2.1.symm changed.2.2.2.symm)
  rw [State.record_normalize' sortedSet, gone, State.record_normalize' sorted', changed.gone unseen]
  by_cases equal : other = processId
  · subst equal
    rw [State.record_set, if_pos rfl, found'']
    simp only [Option.map_some, Option.filter, ProcessState.finished_live (show
      (normRecord raw.gone other (change (normRecord raw.gone other process))).exiting = none by
        rw [normRecord_live live]; exact live),
      ProcessState.finished_live (show (normRecord raw.gone other second).exiting = none by
        rw [normRecord_live live']; exact live'),
      Bool.not_false, ↓reduceIte, same, renormalize]
  · rw [State.record_set, if_neg equal, changed.record_other equal]
    have goneNormal : raw.normalize.gone = raw.gone := funext (State.gone_normalize sorted)
    have again : ((raw.normalize.record other).map (normRecord raw.gone other)).filter (!·.finished) =
        raw.normalize.record other := by
      rw [← goneNormal, ← State.record_normalize' sortedNormal, State.normalize_normalize sorted]
    rw [again, State.record_normalize' sorted]

/-! ### Records of normalized states -/

private theorem State.set_self {state : State} {processId : PID} {process : ProcessState} (sorted : state.Sorted)
    (found : state.record processId = some process) : state.set processId process = state :=
  State.ext_records sorted (Sorted.insertRecord sorted _ _) (fun other => by
    rw [State.record_set]; split
    · rename_i same; subst same; exact found.symm
    · rfl) rfl rfl

private theorem State.modify_found {state : State} {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) (change : ProcessState → ProcessState) :
    state.modify processId change = state.set processId (change process) := by
  unfold State.modify; rw [found]

/-- The record of a live process after normalizing. -/
private theorem State.record_normalize_live {state : State} {processId : PID} {process : ProcessState}
    (sorted : state.Sorted) (found : state.record processId = some process) (live : process.exiting = none) :
    state.normalize.record processId = some (normRecord state.gone processId process) := by
  rw [State.record_normalize' sorted, found]
  simp [Option.filter, ProcessState.finished_live (show (normRecord state.gone processId process).exiting = none by
    rw [normRecord_live live]; exact live)]

/-- What a record of a normalized state keeps: no signal that does nothing, and
no link being removed from a process that is gone. -/
private theorem clean_live {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (clean : normRecord gone processId process = process) (live : process.exiting = none) :
    (∀ entry ∈ process.queue, inert gone processId process entry = false) ∧
      ∀ link ∈ process.links, (link.2.isSome && gone link.1) = false := by
  rw [normRecord_live live] at clean
  have queue := congrArg ProcessState.queue clean
  have links := congrArg ProcessState.links clean
  simp only [Kernel.filter_eq, List.filter_eq_self, Bool.not_eq_eq_eq_not, Bool.not_true] at queue links
  exact ⟨queue, links⟩

/-- A change normalizing leaves as it is when it leaves the record as it is. -/
private theorem renormalize_of_clean {gone : PID → Bool} {processId : PID} {change : ProcessState → ProcessState}
    {process : ProcessState} (clean : normRecord gone processId (change process) = change process) (gone' : PID → Bool) :
    normRecord gone' processId (normRecord gone processId (change process)) = normRecord gone' processId (change process) := by
  rw [clean]

/-- Whether a signal does nothing after a change of the reference counter alone
depends on which processes are gone only when it did before. -/
private theorem inert_any {gone : PID → Bool} {processId : PID} {process process' : ProcessState} {entry : Entry}
    (links : process'.links = process.links) (clean : inert gone processId process entry = false)
    (inert' : inert gone processId process' entry = true) (gone' : PID → Bool) :
    inert gone' processId process' entry = true := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp only [inert, links] at clean inert' ⊢ <;> first | exact inert' | simp_all

/-! ### Forced changes of a process's own fields -/

/-- Storing an environment. -/
private def storeChange (env : Environment) (process : ProcessState) : ProcessState :=
  { process with pdict := env.pdict, refCounter := max process.refCounter env.refCounter }

/-- Removing the received message. -/
private def receiveChange (remaining : List Term) (process : ProcessState) : ProcessState :=
  { process with mailbox := remaining }

private theorem hidden_id : Hidden (fun _ => True) id :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ _ => ⟨trivial, rfl⟩, fun _ _ => ⟨trivial, rfl⟩,
    fun _ => ⟨trivial, rfl⟩⟩

private theorem hidden_store (env : Environment) : Hidden (fun _ => True) (storeChange env) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ _ => ⟨trivial, rfl⟩, fun _ _ => ⟨trivial, rfl⟩,
    fun _ => ⟨trivial, rfl⟩⟩

/-- Records that keep a mailbox, a dictionary and a reference counter. -/
private def Keeps (process : ProcessState) (other : ProcessState) : Prop :=
  other.mailbox = process.mailbox ∧ other.pdict = process.pdict ∧ other.refCounter = process.refCounter

private theorem hidden_receive (process : ProcessState) (remaining : List Term) :
    Hidden (Keeps process) (receiveChange remaining) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ keeps => ⟨keeps, rfl⟩,
    fun _ keeps => ⟨keeps, rfl⟩, fun keeps => ⟨keeps, rfl⟩⟩

private theorem hidden_keeps (process : ProcessState) : Hidden (Keeps process) id :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ keeps => ⟨keeps, rfl⟩,
    fun _ keeps => ⟨keeps, rfl⟩, fun keeps => ⟨keeps, rfl⟩⟩

private theorem normRecord_receive {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) (remaining : List Term) :
    normRecord gone processId (receiveChange remaining (normRecord gone processId process)) =
      normRecord gone processId (receiveChange remaining process) := by
  have live₁ : (receiveChange remaining (normRecord gone processId process)).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show (receiveChange remaining process).exiting = none from live)]
  have same : ∀ other : ProcessState, inert gone processId (receiveChange remaining other) = inert gone processId other :=
    fun _ => rfl
  rw [same, same, funext (inert_normRecord (gone := gone) (processId := processId) live), normRecord_live live]
  simp [receiveChange, Kernel.filter_eq, List.filter_filter]

private theorem normRecord_store {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) (env : Environment) :
    normRecord gone processId (storeChange env (normRecord gone processId process)) =
      normRecord gone processId (storeChange env process) := by
  have live₁ : (storeChange env (normRecord gone processId process)).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show (storeChange env process).exiting = none from live)]
  -- A larger reference counter only makes more signals inert.
  have more : ∀ entry, inert gone processId process entry = true →
      inert gone processId (storeChange env process) entry = true := by
    intro entry inert'
    obtain ⟨source, signal⟩ := entry
    cases signal with
    | down reference reason =>
      simp only [inert, storeChange, Bool.and_eq_true] at inert' ⊢
      obtain ⟨⟨named, counted⟩, unmonitored⟩ := inert'
      refine ⟨⟨named, ?_⟩, unmonitored⟩
      generalize reference.getLast? = last at counted ⊢
      cases last <;> simp at counted ⊢
      exact ⟨counted.1, decide_eq_true (Nat.le_trans counted.2 (Nat.le_max_left _ _))⟩
    | aliasMessage alias message =>
      simp only [inert, storeChange, Bool.and_eq_true] at inert' ⊢
      obtain ⟨⟨⟨named, counted⟩, unaliased⟩, unmonitored⟩ := inert'
      refine ⟨⟨⟨named, ?_⟩, unaliased⟩, unmonitored⟩
      generalize alias.getLast? = last at counted ⊢
      cases last <;> simp at counted ⊢
      exact ⟨counted.1, decide_eq_true (Nat.le_trans counted.2 (Nat.le_max_left _ _))⟩
    | _ => exact inert'
  have same : inert gone processId (storeChange env (normRecord gone processId process)) =
      inert gone processId (storeChange env process) := by
    funext entry
    apply inert_congr
    · rw [normRecord_live live]; rfl
    · rw [normRecord_live live]; rfl
    · rw [normRecord_live live]; rfl
    · intro source notGone
      rw [normRecord_live live]
      simp only [storeChange, Kernel.lookup_eq, Kernel.filter_eq]
      exact lookup_filter_of_keep fun entry _ equal => by simp [equal, notGone]
  rw [same, normRecord_live live]
  simp only [storeChange, Kernel.filter_eq, List.filter_filter, Bool.and_self]
  congr 1
  refine List.filter_congr fun entry _ => ?_
  cases inert' : inert gone processId (storeChange env process) entry
  · have := mt (more entry) (by simp [inert'])
    simp [storeChange] at inert'
    simp [inert', this]
  · simp only [storeChange] at inert'
    simp [inert']

/-! ### Which tagged steps are forced -/

/-- Whether an event is reading or replacing the environment, or receiving. -/
private def Event.local : Event → Bool
  | .internal _ | .receive .. => true
  | _ => false

private theorem Config.forced_own {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {event : Event} {next : Config α} {forced : Bool}
    (mem : (Key.own processId, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps) :
    forced = event.local := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at mem
  rcases mem with (((⟨⟨before, ⟨other, task⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -⟩)
  · obtain ⟨transition, -, -, rfl, -, rfl⟩ := own
    cases transition.event <;> rfl
  · obtain ⟨transition, -, key, -⟩ := handle; cases key
  · obtain ⟨target, -, found⟩ := link
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨_, _, key, -⟩ := found; cases key
  · split at phase
    · simp only [List.mem_singleton, Prod.mk.injEq] at phase; obtain ⟨key, -⟩ := phase; cases key
    · simp at phase
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at unpark
    obtain ⟨_, _, key, -⟩ := unpark; cases key
  · cases key

private theorem Config.forced_handle {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {event : Event} {next : Config α} {forced : Bool}
    {task : Task α} (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (lookup : Kernel.lookup processId tasks = some task)
    (mem : (Key.handle processId, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps) :
    forced = match (state.process processId).queue with
      | entry :: _ => task.forcedHead state processId entry
      | [] => false := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at mem
  rcases mem with (((⟨⟨before, ⟨other, task'⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -⟩)
  · obtain ⟨transition, -, key, -⟩ := own; cases key
  · obtain ⟨transition, -, key, -, -, rfl⟩ := handle
    cases key
    have found := lookup_of_splitAt (splitAt_of_mem pairwise split)
    rw [lookup] at found
    cases found
    rfl
  · obtain ⟨target, -, found⟩ := link
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨_, _, key, -⟩ := found; cases key
  · split at phase
    · simp only [List.mem_singleton, Prod.mk.injEq] at phase; obtain ⟨key, -⟩ := phase; cases key
    · simp at phase
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at unpark
    obtain ⟨_, _, key, -⟩ := unpark; cases key
  · cases key

private theorem Config.forced_phase {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {event : Event} {next : Config α} {forced : Bool}
    (mem : (Key.phase processId, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps) :
    forced = state.dropsDown processId := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at mem
  rcases mem with (((⟨⟨before, ⟨other, task'⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -⟩)
  · obtain ⟨transition, -, key, -⟩ := own; cases key
  · obtain ⟨transition, -, key, -⟩ := handle; cases key
  · obtain ⟨target, -, found⟩ := link
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨_, _, key, -⟩ := found; cases key
  · split at phase
    · simp only [List.mem_singleton, Prod.mk.injEq] at phase
      obtain ⟨key, -, -, rfl⟩ := phase; cases key; rfl
    · simp at phase
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at unpark
    obtain ⟨_, _, key, -⟩ := unpark; cases key
  · cases key

/-! ### Forced changes against steps of other keys -/

/-- A forced step of a live process, changing only its record and its task,
against a step of another key: the other step absorbs it, or the forced step
taken after the other step closes the square, as `atMiddle` shows it stays
forced, with the same change. -/
private theorem Config.forced_other {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {process : ProcessState}
    {ok : ProcessState → Prop} {change : ProcessState → ProcessState} {task task' : Task α} {key key' : Key}
    {event' : Event} {middle : Config α}
    (reachable : (Config.running state tasks finished false).Reachable elapsed)
    (lookup : Kernel.lookup processId tasks = some task) (found : state.record processId = some process)
    (live : process.exiting = none) (ok' : ok process) (hidden : Hidden ok change)
    (renormalize : ∀ gone, normRecord gone processId (normRecord state.gone processId (change process)) =
      normRecord gone processId (change process))
    (owner : key'.owner ≠ some processId)
    (step' : (Config.running state tasks finished false).stepOf key' = some (event', middle))
    (atMiddle : ∀ (raw : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α))
      (process₁ : ProcessState), raw.Within elapsed →
      (Config.running raw.normalize tasks₁ finished₁ false).Reachable elapsed →
      Kernel.lookup processId tasks₁ = some task → raw.record processId = some process₁ → ok process₁ →
      process₁.exiting = none →
      ∃ event'', (key, event'', .running (raw.normalize.set processId (change (normRecord raw.gone processId process₁))).normalize
          (rewriteTask processId (fun _ => [(processId, task')]) tasks₁) finished₁ false, true) ∈
          (Config.running raw.normalize tasks₁ finished₁ false).taggedSteps ∧
        (change (normRecord raw.gone processId process₁)).exiting = none ∧
        normRecord raw.gone processId (change (normRecord raw.gone processId process₁)) =
          normRecord raw.gone processId (change process₁)) :
    (∃ absorbed, (Config.running (state.set processId (change process)).normalize
        (rewriteTask processId (fun _ => [(processId, task')]) tasks) finished false).stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        (Config.running (state.set processId (change process)).normalize
          (rewriteTask processId (fun _ => [(processId, task')]) tasks) finished false).stepOf key' = some (other, last) := by
  have reachable₀ := reachable
  obtain ⟨⟨within, normalized, -⟩, fresh⟩ := reachable
  have changed := State.changed_forced within.1 normalized found live ok' hidden renormalize
  have within' : ((state.set processId (change process)).normalize).Within elapsed := (within.set _ _).normalize
  obtain ⟨next', stepped, same | ⟨raw, raw', tasks₁, finished₁, changedRaw, withinRaw, withinRaw', lookupAfter,
      rfl, rfl⟩⟩ := Config.step_changed (task' := task') within within' changed hidden.unseen fresh lookup owner step'
  · subst same
    exact .inl ⟨event', stepped⟩
  · right
    have reachableMiddle := reachable₀.step (Config.step_of_stepOf step')
    rcases changedRaw.records with ⟨missing, -⟩ | ⟨process₁, process₂, found₁, -, ok₁, live₁, -, -⟩
    · exfalso
      have alive := reachableMiddle.2.2.1 _ (mem_of_lookup (lookupAfter ▸ lookup))
      rw [State.alive_normalize withinRaw.1] at alive
      simp [State.alive, missing] at alive
    obtain ⟨event'', mem, liveChanged, renormalized⟩ := atMiddle raw tasks₁ finished₁ process₁ withinRaw
      reachableMiddle (lookupAfter ▸ lookup) found₁ ok₁ live₁
    rw [State.forced_close withinRaw.1 withinRaw'.1 changedRaw hidden.unseen found₁ liveChanged renormalized] at mem
    exact ⟨key, event'', _, event', mem, stepped⟩

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
