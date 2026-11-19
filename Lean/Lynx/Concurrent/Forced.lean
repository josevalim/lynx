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
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second}, related first second →
      related { first with links := Kernel.filter (·.1 != target) first.links }
        { second with links := Kernel.filter (·.1 != target) second.links }) :
    (state.fallback source target signal).Changed processId related (state'.fallback source target signal) := by
  by_cases same : source = processId
  · subst same
    cases signal <;> simp only [State.fallback]
    all_goals first
      | exact changed
      | exact changed.modifyRelated (fun related => unseen.push _ related)
      | exact changed.modifyRelated (allowed rfl _ rfl)
  · cases signal <;> simp only [State.fallback] <;> first | exact changed | exact changed.modify same _

private theorem enqueue (changed : state.Changed processId related state') (unseen : Unseen related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second}, related first second →
      related { first with links := Kernel.filter (·.1 != target) first.links }
        { second with links := Kernel.filter (·.1 != target) second.links }) :
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
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second}, related first second →
      related { first with links := Kernel.filter (·.1 != target) first.links }
        { second with links := Kernel.filter (·.1 != target) second.links }) :
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
      { process with links := Kernel.append (Kernel.filter (·.1 != child) process.links) [(child, none)] }).modify fresh
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
    cases signal <;> simp only [inert, ProcessState.eagerExit] at inert' ⊢ <;> exact inert'
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

/-- A change normalizing undoes leaves the normalized state as it is. -/
private theorem State.Changed.normalize_same {raw raw' : State} {processId : PID} {process : ProcessState}
    {ok : ProcessState → Prop} {change : ProcessState → ProcessState} (sorted : raw.Sorted) (sorted' : raw'.Sorted)
    (changed : raw.Changed processId (Forced processId ok change) raw') (unseen : Unseen (Forced processId ok change))
    (found : raw.record processId = some process)
    (nothing : normRecord raw.gone processId (change process) = normRecord raw.gone processId process) :
    raw'.normalize = raw.normalize := by
  rcases changed.records with ⟨missing, -⟩ | ⟨first, second, found', found'', -, live₀, live', same⟩
  · rw [found] at missing; cases missing
  rw [found] at found'; cases found'
  refine State.ext_records (Sorted.normalize sorted) (Sorted.normalize sorted') (fun other => ?_)
    changed.2.2.1 changed.2.2.2
  rw [State.record_normalize' sorted', State.record_normalize' sorted, changed.gone unseen]
  by_cases equal : other = processId
  · subst equal
    rw [found'', found]
    simp only [Option.map_some, same, nothing]
  · rw [changed.record_other equal]

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

private theorem State.set_set {state : State} {processId : PID} (sorted : state.Sorted)
    (first second : ProcessState) : (state.set processId first).set processId second = state.set processId second :=
  State.ext_records (Sorted.insertRecord sorted _ _) (Sorted.insertRecord (Sorted.insertRecord sorted _ _) _ _)
    (fun other => by simp only [State.record_set]; split <;> rfl) rfl rfl

private theorem State.append_set {state : State} {processId : PID} (sorted : state.Sorted)
    (process : ProcessState) (message : Term) :
    (state.set processId process).append processId message =
      state.set processId { process with mailbox := Kernel.append process.mailbox [message] } := by
  unfold State.append State.modify
  rw [State.record_set, if_pos rfl]
  exact State.set_set sorted _ _

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

private theorem receiveChange_normRecord {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) (remaining : List Term) :
    normRecord gone processId (receiveChange remaining process) =
      receiveChange remaining (normRecord gone processId process) := by
  rw [normRecord_live (show (receiveChange remaining process).exiting = none from live), normRecord_live live]
  rfl

private theorem hidden_id : Hidden (fun _ => True) id :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ _ => ⟨trivial, rfl⟩, fun _ _ => ⟨trivial, rfl⟩,
    fun _ => ⟨trivial, rfl⟩⟩

private theorem hidden_store (env : Environment) : Hidden (fun _ => True) (storeChange env) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ _ => ⟨trivial, rfl⟩, fun _ _ => ⟨trivial, rfl⟩,
    fun _ => ⟨trivial, rfl⟩⟩

/-- Records that keep a mailbox, a dictionary and a reference counter. -/
private def Keeps (process : ProcessState) (other : ProcessState) : Prop :=
  other.mailbox = process.mailbox ∧ other.pdict = process.pdict ∧ other.refCounter = process.refCounter

private theorem hidden_store' (process : ProcessState) (env : Environment) :
    Hidden (Keeps process) (storeChange env) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ keeps => ⟨keeps, rfl⟩,
    fun _ keeps => ⟨keeps, rfl⟩, fun keeps => ⟨keeps, rfl⟩⟩

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

/-! ### Forced changes handling the oldest signal -/

/-- Handling the oldest signal without changing anything else. -/
private def popChange (process : ProcessState) : ProcessState :=
  { process with queue := process.queue.tail }

/-- Handling the oldest signal, a message. -/
private def messageChange (message : Term) (process : ProcessState) : ProcessState :=
  { process with queue := process.queue.tail, mailbox := Kernel.append process.mailbox [message] }

/-- Whether a link is not the one an acknowledgement removes. -/
private def unacked (source : PID) (id : Nat) (link : PID × Option Nat) : Bool :=
  !(link.1 == source && link.2 == some id)

/-- Handling the oldest signal, removing the link being removed. -/
private def ackedChange (source : PID) (id : Nat) (process : ProcessState) : ProcessState :=
  { process with queue := process.queue.tail, links := Kernel.filter (unacked source id) process.links }

/-- Handling the oldest signal, an acknowledgement of an unlink. -/
private def ackChange (source : PID) (id : Nat) (process : ProcessState) : ProcessState :=
  if Kernel.lookup source process.links == some (some id) then ackedChange source id process else popChange process

/-- Records whose oldest queued signal is a signal. -/
private def Heads (entry : Entry) (process : ProcessState) : Prop :=
  ∃ rest, process.queue = entry :: rest

private theorem Heads.push {entry : Entry} {process : ProcessState} (heads : Heads entry process) (other : Entry) :
    Heads entry (process.push other) ∧ (process.push other).queue.tail = Kernel.append process.queue.tail [other] := by
  obtain ⟨rest, queue⟩ := heads
  simp [Heads, ProcessState.push, queue, Kernel.append_eq]

private theorem Heads.links {entry : Entry} {process : ProcessState} (heads : Heads entry process)
    (notLink : entry.signal ≠ .link) (other : Entry) (link : other.signal = .link) :
    other ∈ process.queue.tail ↔ other ∈ process.queue := by
  obtain ⟨rest, queue⟩ := heads
  rw [queue]
  simp only [List.tail_cons, List.mem_cons]
  constructor
  · exact .inr
  · rintro (same | mem)
    · subst same; exact absurd link notLink
    · exact mem

private theorem hidden_pop {entry : Entry} (notLink : entry.signal ≠ .link) : Hidden (Heads entry) popChange where
  exiting _ := rfl
  trapExit _ := rfl
  parked _ := rfl
  links heads other link := heads.links notLink other link
  push other heads := by
    obtain ⟨heads', tail⟩ := heads.push other
    exact ⟨heads', by simp only [popChange, tail]; rfl⟩
  eagerExit _ heads := ⟨heads, rfl⟩
  unpark heads := ⟨heads, rfl⟩

private theorem hidden_message {entry : Entry} (notLink : entry.signal ≠ .link) (message : Term) :
    Hidden (Heads entry) (messageChange message) where
  exiting _ := rfl
  trapExit _ := rfl
  parked _ := rfl
  links heads other link := heads.links notLink other link
  push other heads := by
    obtain ⟨heads', tail⟩ := heads.push other
    exact ⟨heads', by simp only [messageChange, tail]; rfl⟩
  eagerExit _ heads := ⟨heads, rfl⟩
  unpark heads := ⟨heads, rfl⟩

private theorem lookup_filter_self {β : Type} (key : PID) :
    ∀ entries : List (PID × β), Kernel.lookup key (Kernel.filter (·.1 != key) entries) = none
  | [] => rfl
  | (other, value) :: rest => by
      have ih := lookup_filter_self key rest
      simp only [Kernel.lookup_eq, Kernel.filter_eq] at ih ⊢
      by_cases same : other = key
      · subst same; simpa [List.filter_cons] using ih
      · have differ : (key == other) = false := by simp [Ne.symm same]
        simp [List.filter_cons, same, List.lookup_cons, differ, ih]

private theorem hidden_ack {entry : Entry} (notLink : entry.signal ≠ .link) (source : PID) (id : Nat) :
    Hidden (Heads entry) (ackChange source id) where
  exiting _ := by unfold ackChange ackedChange popChange; split <;> rfl
  trapExit _ := by unfold ackChange ackedChange popChange; split <;> rfl
  parked _ := by unfold ackChange ackedChange popChange; split <;> rfl
  links heads other link := by unfold ackChange ackedChange popChange; split <;> exact heads.links notLink other link
  push := fun {process} other heads => by
    obtain ⟨heads', tail⟩ := heads.push other
    refine ⟨heads', ?_⟩
    unfold ackChange ackedChange popChange
    by_cases linked : (Kernel.lookup source process.links == some (some id)) = true <;>
      simp only [ProcessState.push, linked, ↓reduceIte, Bool.false_eq_true] at tail ⊢ <;> rw [tail]
  eagerExit := fun {process} exited heads => by
    refine ⟨heads, ?_⟩
    unfold ackChange ackedChange popChange ProcessState.eagerExit
    by_cases same : exited = source
    · subst same
      simp only [lookup_filter_self, reduceCtorEq, beq_iff_eq, ↓reduceIte]
      split
      · congr 1
        simp only [Kernel.filter_eq, List.filter_filter]
        refine List.filter_congr fun link _ => ?_
        by_cases key : link.1 = exited <;> simp [unacked, key]
      · rfl
    · have kept : Kernel.lookup source (Kernel.filter (·.1 != exited) process.links) =
          Kernel.lookup source process.links := by
        simp only [Kernel.lookup_eq, Kernel.filter_eq]
        exact lookup_filter_of_keep fun entry _ equal => by simp [equal, Ne.symm same]
      rw [kept]
      split
      · simp only [Kernel.filter_eq, List.filter_filter, Bool.and_comm]
      · rfl
  unpark heads := by
    refine ⟨heads, ?_⟩
    unfold ackChange ackedChange popChange; split <;> rfl

/-- Handling the oldest signal of a clean record leaves it clean. -/
private theorem normRecord_popped {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (clean : normRecord gone processId process = process) (live : process.exiting = none)
    {change : ProcessState → ProcessState} (queue : (change process).queue = process.queue.tail)
    (same : ∀ entry, inert gone processId (change process) entry = inert gone processId process entry)
    (links : (change process).links = process.links) (live' : (change process).exiting = none) :
    normRecord gone processId (change process) = change process := by
  have cleaned := clean_live clean live
  rw [normRecord_live live', funext same, queue, links]
  have keepQueue : Kernel.filter (fun entry => !inert gone processId process entry) process.queue.tail =
      process.queue.tail := by
    rw [Kernel.filter_eq]
    exact List.filter_eq_self.mpr fun entry mem => by
      simp [cleaned.1 entry (List.mem_of_mem_tail mem)]
  have keepLinks : Kernel.filter (fun link => !(link.2.isSome && gone link.1)) process.links = process.links := by
    rw [Kernel.filter_eq]; exact List.filter_eq_self.mpr fun link mem => by simp [cleaned.2 link mem]
  rw [keepQueue, keepLinks, ← queue, ← links]

/-- Normalizing before handling a kept oldest signal of a message or marker
reaches what handling it reaches. -/
private theorem normRecord_message {gone : PID → Bool} {processId : PID} {process : ProcessState} {entry : Entry}
    (live : process.exiting = none) (heads : Heads entry process) (kept : inert gone processId process entry = false)
    (message : Term) :
    normRecord gone processId (messageChange message (normRecord gone processId process)) =
      normRecord gone processId (messageChange message process) := by
  obtain ⟨rest, queue⟩ := heads
  have live₁ : (messageChange message (normRecord gone processId process)).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show (messageChange message process).exiting = none from live)]
  have same : ∀ other : ProcessState, inert gone processId (messageChange message other) = inert gone processId other :=
    fun _ => rfl
  rw [same, same, funext (inert_normRecord (gone := gone) (processId := processId) live), normRecord_live live]
  simp [messageChange, queue, kept, Kernel.filter_eq, List.filter_filter]

private theorem normRecord_pop {gone : PID → Bool} {processId : PID} {process : ProcessState} {entry : Entry}
    (live : process.exiting = none) (heads : Heads entry process) (kept : inert gone processId process entry = false) :
    normRecord gone processId (popChange (normRecord gone processId process)) =
      normRecord gone processId (popChange process) := by
  obtain ⟨rest, queue⟩ := heads
  have live₁ : (popChange (normRecord gone processId process)).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show (popChange process).exiting = none from live)]
  have same : ∀ other : ProcessState, inert gone processId (popChange other) = inert gone processId other :=
    fun _ => rfl
  rw [same, same, funext (inert_normRecord (gone := gone) (processId := processId) live), normRecord_live live]
  simp [popChange, queue, kept, Kernel.filter_eq, List.filter_filter]

/-! ### Forced own steps against handling by the same process -/

private theorem selectMessage_append {β : Type} {select : Term → Option β} {message selected : Term} {value : β}
    {remaining : List Term} :
    ∀ {messages : List Term}, selectMessage select messages = some (selected, value, remaining) →
      selectMessage select (Kernel.append messages [message]) = some (selected, value, Kernel.append remaining [message])
  | [], found => by simp [selectMessage] at found
  | head :: rest, found => by
      simp only [selectMessage, Kernel.append_eq, List.cons_append] at found ⊢
      cases matched : select head with
      | some value' =>
        simp only [matched, Option.some.injEq, Prod.mk.injEq] at found ⊢
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact ⟨rfl, rfl, rfl⟩
      | none =>
        simp only [matched] at found ⊢
        cases selected' : selectMessage select rest with
        | none => simp [selected'] at found
        | some result =>
          obtain ⟨selected'', value'', remaining''⟩ := result
          simp only [selected', Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl, rfl⟩ := found
          have := selectMessage_append (message := message) selected'
          simp only [Kernel.append_eq] at this
          simp [this]

/-- A change of a record's dictionary, reference counter and mailbox only. -/
private def ownChange (pdict : List (Term × Term) → List (Term × Term)) (refCounter : Nat → Nat)
    (mailbox : List Term → List Term) (process : ProcessState) : ProcessState :=
  { process with pdict := pdict process.pdict, refCounter := refCounter process.refCounter,
                 mailbox := mailbox process.mailbox }

/-- Records changed by `change`, where `ok` holds of the original. -/
private def Same (ok : ProcessState → Prop) (change : ProcessState → ProcessState) (process process' : ProcessState) :
    Prop :=
  ok process ∧ process' = change process

/-- Records whose mailbox satisfies `ok`, with a dictionary and reference counter. -/
private def OwnOk (ok : List Term → Prop) (pdict : List (Term × Term)) (refCounter : Nat) (process : ProcessState) :
    Prop :=
  ok process.mailbox ∧ process.pdict = pdict ∧ process.refCounter = refCounter

/-- A change of a record's own fields, while its mailbox satisfies `ok`, which
appending a message keeps and which the change commutes with. -/
private structure OwnChange (ok : List Term → Prop) (mailbox : List Term → List Term) : Prop where
  append : ∀ {messages} message, ok messages →
    ok (Kernel.append messages [message]) ∧ mailbox (Kernel.append messages [message]) =
      Kernel.append (mailbox messages) [message]

private theorem OwnChange.unseen {ok : List Term → Prop} {mailbox : List Term → List Term}
    {pdict : List (Term × Term) → List (Term × Term)} {refCounter : Nat → Nat} {dict : List (Term × Term)}
    {counter : Nat} :
    Unseen (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox)) where
  outside := by
    rintro first second ⟨-, rfl⟩
    exact ⟨rfl, rfl, rfl, fun _ _ => .rfl⟩
  push := fun _ ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩
  eagerExit := fun _ ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩
  unpark := fun ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩

namespace State.Changed

variable {processId : PID} {state state' : State} {ok : List Term → Prop} {mailbox : List Term → List Term}
  {pdict : List (Term × Term) → List (Term × Term)} {refCounter : Nat → Nat} {dict : List (Term × Term)}
  {counter : Nat}

/-- The record of the process itself, read through the change. -/
private theorem process_self
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') {β : Type} (get : ProcessState → β) (keeps : ∀ process, get (ownChange pdict refCounter mailbox process) =
        get process) :
    get (state'.process processId) = get (state.process processId) ∨
      (state.record processId = none ∧ state'.record processId = none) := by
  rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, -, rfl⟩
  · exact .inr ⟨first, second⟩
  · left; simp [State.process, first, second, keeps]

private theorem modifySelf
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') (change : ProcessState → ProcessState)
    (commutes : ∀ process, OwnOk ok dict counter process → OwnOk ok dict counter (change process) ∧
      change (ownChange pdict refCounter mailbox process) = ownChange pdict refCounter mailbox (change process)) :
    (state.modify processId change).Changed processId
      (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox)) (state'.modify processId change) :=
  changed.modifyRelated fun ⟨ok', same⟩ => by
    subst same; exact ⟨(commutes _ ok').1, (commutes _ ok').2⟩

private theorem process_self'
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') {β : Type} (get : ProcessState → β) (keeps : ∀ process, get (ownChange pdict refCounter mailbox process) =
        get process) : get (state'.process processId) = get (state.process processId) := by
  rcases changed.process_self get keeps with same | ⟨first, second⟩
  · exact same
  · simp [State.process, first, second]

private theorem appendSelf
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') (own : OwnChange ok mailbox) (message : Term) :
    (state.append processId message).Changed processId
      (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      (state'.append processId message) :=
  changed.modifySelf _ fun process ok' => ⟨⟨(own.append message ok'.1).1, ok'.2⟩, by
    simp only [ownChange, (own.append message ok'.1).2]⟩

/-- Handling a signal by the process itself, after a change of its own fields. -/
private theorem handleSelf
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') (own : OwnChange ok mailbox) (waiting : Option Wait) (entry : Entry) :
    (state'.handle processId waiting entry).2 = (state.handle processId waiting entry).2 ∧
      (state.handle processId waiting entry).1.Changed processId
        (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
        (state'.handle processId waiting entry).1 := by
  have unseen := OwnChange.unseen (ok := ok) (mailbox := mailbox) (pdict := pdict) (refCounter := refCounter)
    (dict := dict) (counter := counter)
  have links := changed.process_self' (·.links) fun _ => rfl
  have aliases := changed.process_self' (·.aliases) fun _ => rfl
  have monitoring := changed.process_self' (·.monitoring) fun _ => rfl
  have eagerExits := changed.process_self' (·.eagerExits) fun _ => rfl
  have trapExit := changed.process_self' (·.trapExit) fun _ => rfl
  have either : ∀ {condition : Prop} [Decidable condition] {first first' second second' : State},
      first.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox)) first' →
      second.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox)) second' →
      (if condition then first else second).Changed processId
        (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
        (if condition then first' else second') :=
    fun one two => by split; exact one; exact two
  have modified : ∀ {first first' : State} (change : ProcessState → ProcessState),
      (∀ process, (change process).mailbox = process.mailbox ∧ (change process).pdict = process.pdict ∧
        (change process).refCounter = process.refCounter ∧
        change (ownChange pdict refCounter mailbox process) = ownChange pdict refCounter mailbox (change process)) →
      first.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox)) first' →
      (first.modify processId change).Changed processId
        (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox)) (first'.modify processId change) :=
    fun change keeps changed' => changed'.modifySelf change fun process ok' => by
      obtain ⟨mailbox', pdict', counter', commutes⟩ := keeps process
      exact ⟨⟨by rw [mailbox']; exact ok'.1, by rw [pdict']; exact ok'.2.1, by rw [counter']; exact ok'.2.2⟩,
        commutes⟩
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | message message => exact ⟨rfl, changed.appendSelf own message⟩
  | aliasMessage alias message =>
    simp only [State.handle, aliases]
    exact ⟨by first | rfl | trivial, either (changed.appendSelf own message) changed⟩
  | exit reason linked normalKills =>
    simp only [State.handle, State.exitSignal, links, trapExit]
    have removed := either (condition := linked = true)
      (modified (fun process => { process with links := Kernel.filter (·.1 != source) process.links })
        (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed) changed
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, removed⟩
    split
    · exact ⟨rfl, removed.appendSelf own _⟩
    split
    · exact ⟨rfl, removed⟩
    · exact ⟨rfl, removed⟩
  | link =>
    simp only [State.handle, links]
    exact ⟨by first | rfl | trivial, either changed (modified (fun process =>
      { process with links := Kernel.append process.links [(source, none)] }) (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed)⟩
  | unlink id =>
    simp only [State.handle, links]
    exact ⟨by first | rfl | trivial, (either (modified (fun process =>
      { process with links := Kernel.filter (·.1 != source) process.links }) (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed)
      changed).send unseen fun _ _ => by simp⟩
  | unlinkAck id =>
    simp only [State.handle, links]
    exact ⟨by first | rfl | trivial, either (modified (fun process =>
      { process with links := Kernel.filter (fun link => !(link.1 == source && link.2 == some id)) process.links })
      (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed) changed⟩
  | monitor reference => exact ⟨rfl, modified (fun process =>
      { process with monitors := Kernel.append process.monitors [(reference, source)] }) (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed⟩
  | down reference reason =>
    simp only [State.handle, eagerExits, monitoring]
    have dropped := either (condition := (isNormal reason && Kernel.contains (state.process processId).eagerExits
        source) = true)
      (modified (fun process => { process with eagerExits := Kernel.filter (· != source) process.eagerExits })
        (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed) changed
    split
    · exact ⟨rfl, (modified (fun process => { process with
        monitoring := Kernel.filter (·.1 != reference) process.monitoring
        aliases := Kernel.erase process.aliases reference }) (fun _ => ⟨rfl, rfl, rfl, rfl⟩) dropped).appendSelf own _⟩
    · exact ⟨rfl, dropped⟩
  | isAlive => exact ⟨rfl, changed.send unseen fun _ _ => by simp⟩
  | reply value =>
    simp only [State.handle]
    split <;> exact ⟨rfl, changed⟩
  | flush =>
    simp only [State.handle]
    split <;> exact ⟨rfl, changed⟩

/-- The process itself ends, after a change of its own fields: normalizing
forgets the fields that differ. -/
private theorem terminateSelf
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') (reason : Term) (before : state.Sorted) (before' : state'.Sorted)
    (sorted : (state.terminate processId reason).Sorted) (sorted' : (state'.terminate processId reason).Sorted) :
    (state'.terminate processId reason).normalize = (state.terminate processId reason).normalize := by
  let ended := Same (fun process : ProcessState => process.exiting.isSome = true) (ownChange pdict refCounter id)
  have unseen : Unseen ended :=
    ⟨by rintro first second ⟨-, rfl⟩; exact ⟨rfl, rfl, rfl, fun _ _ => .rfl⟩,
      fun _ ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩,
      fun _ ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩,
      fun ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩⟩
  rcases changed.records with ⟨missing, missing'⟩ | ⟨process, second, found, found'', -, rfl⟩
  · -- Without a record, the states are the same.
    have same : state' = state := State.ext_records before before' (fun other => by
      by_cases equal : other = processId
      · subst equal; rw [missing, missing']
      · exact changed.record_other equal) changed.2.2.1 changed.2.2.2
    rw [same]
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = ownChange pdict refCounter mailbox process := by
    simp [State.process, found'']
  -- After ending, the records differ only in the dictionary and reference counter.
  have endedChanged : (state.terminate processId reason).Changed processId ended
      (state'.terminate processId reason) := by
    unfold State.terminate
    simp only [processOf, processOf', changed.2.2.1]
    refine State.Changed.foldl (fun target changed' => ?_) _ ⟨fun other differ => ?_, ?_, rfl, changed.2.2.2⟩
    · rw [changed'.eagerLink unseen]
      split
      · refine (changed'.modifyRelated fun {first second} related => ?_).linkExit unseen _ _ _
        obtain ⟨ok', same⟩ := related
        subst same
        refine ⟨?_, rfl⟩
        cases exiting : first.exiting <;> simp_all
      · exact changed'
    · simp only [State.record_set, differ, ↓reduceIte]
      exact changed.record_other differ
    · simp only [State.record_set, ↓reduceIte]
      exact .some ⟨rfl, rfl⟩
  have goneSame := endedChanged.gone unseen
  refine State.ext_records (Sorted.normalize sorted) (Sorted.normalize sorted') (fun other => ?_)
    endedChanged.2.2.1 endedChanged.2.2.2
  rw [State.record_normalize' sorted', State.record_normalize' sorted, goneSame]
  by_cases equal : other = processId
  · subst equal
    rcases endedChanged.records with ⟨none₁, none₂⟩ | ⟨record, record', found₁, found₂, exiting, rfl⟩
    · rw [none₁, none₂]
    · rw [found₁, found₂]
      obtain ⟨reason', exiting'⟩ := Option.isSome_iff_exists.mp exiting
      simp only [Option.map_some]
      unfold normRecord
      simp only [ownChange, exiting']
  · rw [endedChanged.record_other equal]

end State.Changed

/-! ### Forced handling against the process's own step -/

/-- A change of a record's queue, mailbox and links only. -/
private def queueChange (queue : List Entry → List Entry) (mailbox : List Term → List Term)
    (links : List (PID × Option Nat) → List (PID × Option Nat)) (process : ProcessState) : ProcessState :=
  { process with queue := queue process.queue, mailbox := mailbox process.mailbox, links := links process.links }

/-- Records with a signal queued. -/
private def Queued (process : ProcessState) : Prop := process.queue ≠ []

/-- How handling the oldest signal changes the queue, mailbox and links, in a
way that a process's own steps commute with. -/
private structure QueueChange (queue : List Entry → List Entry) (mailbox : List Term → List Term)
    (links : List (PID × Option Nat) → List (PID × Option Nat)) : Prop where
  push : ∀ {entries} entry, entries ≠ [] → queue (Kernel.append entries [entry]) = Kernel.append (queue entries) [entry]
  lookupNone : ∀ (target : PID) (entries : List (PID × Option Nat)),
    (Kernel.lookup target (links entries) == some none) = (Kernel.lookup target entries == some none)
  filtered : ∀ (target : PID) (entries : List (PID × Option Nat)),
    links (Kernel.filter (·.1 != target) entries) = Kernel.filter (·.1 != target) (links entries)
  relink : ∀ (target : PID) (entries : List (PID × Option Nat)),
    links (Kernel.append (Kernel.filter (·.1 != target) entries) [(target, none)]) =
      Kernel.append (Kernel.filter (·.1 != target) (links entries)) [(target, none)]
  select : ∀ {β : Type} (select : Term → Option β) {messages remaining : List Term} {message : Term} {value : β},
    selectMessage select messages = some (message, value, remaining) →
      selectMessage select (mailbox messages) = some (message, value, mailbox remaining)

private theorem QueueChange.unseen {queue : List Entry → List Entry} {mailbox : List Term → List Term}
    {links : List (PID × Option Nat) → List (PID × Option Nat)} (change : QueueChange queue mailbox links)
    (linking : ∀ (entries : List Entry) entry, entries ≠ [] → entry.signal = .link →
      (entry ∈ queue entries ↔ entry ∈ entries)) :
    Unseen (Same Queued (queueChange queue mailbox links)) where
  outside := by
    rintro first second ⟨queued, rfl⟩
    exact ⟨rfl, rfl, rfl, fun entry link => linking _ entry queued link⟩
  push := fun entry ⟨queued, same⟩ => by
    subst same
    refine ⟨by simp [Queued, ProcessState.push, Kernel.append_eq], ?_⟩
    simp only [queueChange, ProcessState.push, change.push entry queued]
  eagerExit := fun source ⟨queued, same⟩ => by
    subst same
    exact ⟨queued, by simp only [queueChange, ProcessState.eagerExit, change.filtered]⟩
  unpark := fun ⟨queued, same⟩ => by subst same; exact ⟨queued, rfl⟩

namespace State.Changed

variable {processId : PID} {state state' : State} {queue : List Entry → List Entry} {mailbox : List Term → List Term}
  {links : List (PID × Option Nat) → List (PID × Option Nat)}

private theorem queue_modify
    (changed : state.Changed processId (Same Queued (queueChange queue mailbox links)) state')
    (change : ProcessState → ProcessState) (queued : ∀ process, (change process).queue = process.queue)
    (commutes : ∀ process, Queued process →
      change (queueChange queue mailbox links process) = queueChange queue mailbox links (change process)) :
    (state.modify processId change).Changed processId (Same Queued (queueChange queue mailbox links))
      (state'.modify processId change) :=
  changed.modifyRelated fun ⟨ok', same⟩ => by
    subst same
    exact ⟨by simp only [Queued, queued]; exact ok', commutes _ ok'⟩

/-- A process's request, after handling its oldest signal changed its queue, mailbox and links. -/
private theorem requestSelf
    (changed : state.Changed processId (Same Queued (queueChange queue mailbox links)) state')
    (unseen : Unseen (Same Queued (queueChange queue mailbox links))) (change : QueueChange queue mailbox links)
    {process : ProcessState} (found : state.record processId = some process)
    (unlinked : ∀ (target : PID) (id : Nat), Kernel.lookup target process.links = some none →
      links (Kernel.map (fun link => if link.1 == target then (link.1, some id) else link) process.links) =
        Kernel.map (fun link => if link.1 == target then (link.1, some id) else link) (links process.links))
    {β : Type} (next : Term → Result β) (query : Request) :
    Answer.Changed processId (Same Queued (queueChange queue mailbox links)) (state.request processId next query)
      (state'.request processId next query) := by
  rcases changed.records with ⟨missing, -⟩ | ⟨first, second, found', found'', queued, rfl⟩
  · rw [found] at missing; cases missing
  rw [found] at found'; cases found'
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = queueChange queue mailbox links process := by
    simp [State.process, found'']
  have allocated : (state'.allocate processId).1 = (state.allocate processId).1 ∧
      (state.allocate processId).2.Changed processId (Same Queued (queueChange queue mailbox links))
        (state'.allocate processId).2 := by
    refine ⟨by simp only [State.allocate, processOf, processOf']; rfl, ?_⟩
    exact changed.queue_modify _ (fun _ => rfl) (fun _ _ => rfl)
  cases query with
  | monitor target alias =>
    simp only [State.request]
    obtain ⟨same, allocated⟩ := allocated
    rw [same]
    split
    · exact ⟨rfl, allocated⟩
    · exact ⟨rfl, (allocated.unpark unseen processId).queue_modify _ (fun _ => rfl) (fun _ _ => rfl)⟩
  | demonitor reference flush =>
    simp only [State.request, processOf, processOf', queueChange]
    split <;> exact ⟨rfl, changed.queue_modify _ (fun _ => rfl) (fun _ _ => rfl)⟩
  | link target =>
    simp only [State.request, processOf, processOf', changed.alive unseen, queueChange]
    by_cases self : target = processId
    · simp only [self, ↓reduceIte]; exact ⟨rfl, changed⟩
    simp only [self, ↓reduceIte]
    by_cases eager : Kernel.contains process.eagerExits target = true
    · simp only [eager, ↓reduceIte]; exact ⟨rfl, changed⟩
    simp only [eager, ↓reduceIte, Bool.false_eq_true]
    by_cases gone : (!state.alive target && !process.trapExit) = true
    · simp only [gone, ↓reduceIte]; exact ⟨rfl, changed⟩
    simp only [gone, ↓reduceIte, Bool.false_eq_true]
    have relinked := changed.queue_modify (fun process => { process with
        links := Kernel.append (Kernel.filter (·.1 != target) process.links) [(target, none)] }) (fun _ => rfl)
      fun _ _ => by simp only [queueChange, change.relink]
    have lookups := change.lookupNone target process.links
    generalize Kernel.lookup target process.links = found₁ at lookups ⊢
    generalize Kernel.lookup target (links process.links) = found₂ at lookups ⊢
    rcases found₁ with _ | _ | id <;> rcases found₂ with _ | _ | id' <;> simp at lookups <;>
      first
        | exact ⟨rfl, changed⟩
        | exact ⟨rfl, relinked.send unseen fun _ _ => by simp⟩
  | unlink target =>
    simp only [State.request, processOf, processOf', queueChange]
    by_cases self : target = processId
    · simp only [self, ↓reduceIte]; exact ⟨rfl, changed⟩
    simp only [self, ↓reduceIte]
    have lookups := change.lookupNone target process.links
    have unlinking := unlinked target (process.unlinks + 1)
    generalize Kernel.lookup target process.links = found₁ at lookups unlinking ⊢
    generalize Kernel.lookup target (links process.links) = found₂ at lookups ⊢
    rcases found₁ with _ | _ | id <;> rcases found₂ with _ | _ | id' <;> simp at lookups <;>
      first
        | exact ⟨rfl, changed⟩
        | (rw [State.modify_found found, State.modify_found found'']
           refine ⟨rfl, State.Changed.send ?_ unseen fun _ _ _ _ _ ⟨queued', same⟩ => ?_⟩
           · exact changed.setRelated ⟨queued, by simp only [queueChange, unlinking rfl]⟩
           · subst same; exact ⟨queued', by simp only [queueChange, change.filtered]⟩)
  | exit target reason quirk =>
    simp only [State.request, processOf, processOf', queueChange]
    split
    · exact ⟨rfl, changed.send unseen fun _ _ => by simp⟩
    split
    · exact ⟨rfl, changed.send unseen fun _ _ => by simp⟩
    · exact ⟨rfl, changed.send unseen fun _ _ => by simp⟩
  | trapExit enabled =>
    simp only [State.request, processOf, processOf', queueChange]
    split
    · exact ⟨rfl, changed⟩
    · exact ⟨rfl, changed.queue_modify _ (fun _ => rfl) (fun _ _ => rfl)⟩
  | alive target =>
    simp only [State.request, changed.alive unseen]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed.send unseen fun _ _ => by simp⟩
    · exact ⟨rfl, changed.enqueue unseen fun _ _ => by simp⟩
  | sendAlias alias message =>
    exact ⟨rfl, changed.send unseen fun _ _ => by simp⟩
  | startTimer destination message duration =>
    simp only [State.request]
    obtain ⟨same, allocated⟩ := allocated
    rw [same, allocated.alive unseen]
    refine ⟨rfl, ?_⟩
    split
    · rw [allocated.2.2.1]; exact allocated.timers _
    · exact allocated
  | cancelTimer reference =>
    simp only [State.request, changed.2.2.1, processOf, processOf', queueChange]
    split
    · exact ⟨by rw [changed.2.2.2], (changed.timers _).queue_modify _ (fun _ => rfl) (fun _ _ => rfl)⟩
    · exact ⟨rfl, changed⟩

/-- A process spawns a child, after handling its oldest signal changed its queue, mailbox and links. -/
private theorem spawnSelf
    (changed : state.Changed processId (Same Queued (queueChange queue mailbox links)) state')
    (change : QueueChange queue mailbox links) {process : ProcessState}
    (found : state.record processId = some process) (options : SpawnOptions)
    (fresh : Kernel.append processId [process.children + 1] ≠ processId) :
    (state'.spawnWith processId options).1 = (state.spawnWith processId options).1 ∧
      (state.spawnWith processId options).2.Changed processId (Same Queued (queueChange queue mailbox links))
        (state'.spawnWith processId options).2 := by
  rcases changed.records with ⟨missing, -⟩ | ⟨first, second, found', found'', queued, rfl⟩
  · rw [found] at missing; cases missing
  rw [found] at found'; cases found'
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = queueChange queue mailbox links process := by
    simp [State.process, found'']
  refine ⟨by simp only [State.spawnWith, processOf, processOf']; rfl, ?_⟩
  unfold State.spawnWith
  dsimp only
  rw [processOf, processOf']
  have started := (changed.setRelated (process := { process with children := process.children + 1 })
    (process' := { queueChange queue mailbox links process with
      children := (queueChange queue mailbox links process).children + 1 }) ⟨queued, rfl⟩).set fresh {}
  let child := Kernel.append processId [process.children + 1]
  have linked := (started.queue_modify (fun process =>
      { process with links := Kernel.append (Kernel.filter (·.1 != child) process.links) [(child, none)] })
      (fun _ => rfl) (fun _ _ => by simp only [queueChange, change.relink])).modify fresh
    fun child => { child with links := [(processId, none)] }
  have counter : ∀ {first second : State}, first.Changed processId (Same Queued (queueChange queue mailbox links))
      second → (second.process processId).refCounter = (first.process processId).refCounter :=
    fun {first second} changed' => by
      rcases changed'.records with ⟨one, two⟩ | ⟨a, b, one, two, -, rfl⟩
      · simp [State.process, one, two]
      · simp [State.process, one, two, queueChange]
  by_cases monitor : options.monitor <;> by_cases link : options.link <;>
    simp only [monitor, link, ↓reduceIte, Bool.false_eq_true, State.allocate]
  · simp only [State.process, State.record_modify, State.record_set, ↓reduceIte, Ne.symm fresh, Option.map_some,
      Option.getD_some, queueChange]
    refine ((linked.queue_modify _ ?_ ?_).queue_modify _ ?_ ?_).modify fresh _ <;> intros <;> rfl
  · simp only [State.process, State.record_modify, State.record_set, ↓reduceIte, Ne.symm fresh, Option.map_some,
      Option.getD_some, queueChange]
    refine ((started.queue_modify _ ?_ ?_).queue_modify _ ?_ ?_).modify fresh _ <;> intros <;> rfl
  · exact linked
  · exact started

/-- The process ends, after handling its oldest signal changed its queue,
mailbox and links in a way ending forgets. -/
private theorem terminateQueue
    (changed : state.Changed processId (Same Queued (queueChange queue mailbox links)) state')
    (change : QueueChange queue mailbox links)
    (requests : ∀ (entries : List Entry) (keep : Entry → Bool), entries ≠ [] →
      (∀ entry, keep entry = true → (entry.signal matches .link | .monitor _ | .isAlive) = true) →
      Kernel.filter keep (queue entries) = Kernel.filter keep entries)
    (exitLinks : ∀ entries : List (PID × Option Nat),
      Kernel.foldl (fun links (peer, unlinking) => if unlinking.isNone then insertPid peer links else links) []
        (links entries) =
      Kernel.foldl (fun links (peer, unlinking) => if unlinking.isNone then insertPid peer links else links) [] entries)
    (reason : Term) (before : state.Sorted) (before' : state'.Sorted)
    (sorted : (state.terminate processId reason).Sorted) (sorted' : (state'.terminate processId reason).Sorted) :
    (state'.terminate processId reason).normalize = (state.terminate processId reason).normalize := by
  let ended := Same (fun process : ProcessState => process.exiting.isSome = true) (queueChange id id links)
  have unseen : Unseen ended :=
    ⟨by rintro first second ⟨-, rfl⟩; exact ⟨rfl, rfl, rfl, fun _ _ => .rfl⟩,
      fun _ ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩,
      fun _ ⟨ok', same⟩ => by
        subst same; exact ⟨ok', by simp only [queueChange, ProcessState.eagerExit, change.filtered]⟩,
      fun ⟨ok', same⟩ => by subst same; exact ⟨ok', rfl⟩⟩
  rcases changed.records with ⟨missing, missing'⟩ | ⟨process, second, found, found'', queued, rfl⟩
  · have same : state' = state := State.ext_records before before' (fun other => by
      by_cases equal : other = processId
      · subst equal; rw [missing, missing']
      · exact changed.record_other equal) changed.2.2.1 changed.2.2.2
    rw [same]
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = queueChange queue mailbox links process := by
    simp [State.process, found'']
  have endedChanged : (state.terminate processId reason).Changed processId ended
      (state'.terminate processId reason) := by
    unfold State.terminate
    simp only [processOf, processOf', changed.2.2.1, queueChange, exitLinks]
    rw [requests _ _ queued fun entry kept => by
      obtain ⟨_, signal⟩ := entry; cases signal <;> simp_all]
    refine State.Changed.foldl (fun target changed' => ?_) _ ⟨fun other differ => ?_, ?_, rfl, changed.2.2.2⟩
    · rw [changed'.eagerLink unseen]
      split
      · refine (changed'.modifyRelated fun {first second} related => ?_).linkExit unseen _ _ _
        obtain ⟨ok', same⟩ := related
        subst same
        refine ⟨?_, rfl⟩
        cases exiting : first.exiting <;> simp_all
      · exact changed'
    · simp only [State.record_set, differ, ↓reduceIte]
      exact changed.record_other differ
    · simp only [State.record_set, ↓reduceIte]
      exact .some ⟨rfl, rfl⟩
  have goneSame := endedChanged.gone unseen
  refine State.ext_records (Sorted.normalize sorted) (Sorted.normalize sorted') (fun other => ?_)
    endedChanged.2.2.1 endedChanged.2.2.2
  rw [State.record_normalize' sorted', State.record_normalize' sorted, goneSame]
  by_cases equal : other = processId
  · subst equal
    rcases endedChanged.records with ⟨none₁, none₂⟩ | ⟨record, record', found₁, found₂, exiting, rfl⟩
    · rw [none₁, none₂]
    · rw [found₁, found₂]
      obtain ⟨reason', exiting'⟩ := Option.isSome_iff_exists.mp exiting
      simp only [Option.map_some]
      unfold normRecord
      simp only [queueChange, exiting']
      rfl
  · rw [endedChanged.record_other equal]

/-- A process's own step, after handling its oldest signal changed its queue,
mailbox and links: the same transition, with related states unless it ends the process. -/
private theorem ownSelf
    (changed : state.Changed processId (Same Queued (queueChange queue mailbox links)) state')
    (unseen : Unseen (Same Queued (queueChange queue mailbox links))) (change : QueueChange queue mailbox links)
    {process : ProcessState} (found : state.record processId = some process)
    (unlinked : ∀ (target : PID) (id : Nat), Kernel.lookup target process.links = some none →
      links (Kernel.map (fun link => if link.1 == target then (link.1, some id) else link) process.links) =
        Kernel.map (fun link => if link.1 == target then (link.1, some id) else link) (links process.links))
    (awaited : Kernel.any (queue process.queue) (state'.awaitedEntry processId) = true →
      Kernel.any process.queue (state.awaitedEntry processId) = true)
    (noMatch : ∀ {β : Type} (select : Term → Option β), selectMessage select process.mailbox = none →
      Kernel.any process.queue (state.awaitedEntry processId) = false →
      selectMessage select (mailbox process.mailbox) = none)
    (fresh : Kernel.append processId [process.children + 1] ≠ processId)
    {task : Task α} {transition : Transition α} (head : (task.own state processId).head? = some transition) :
    ∃ transition' : Transition α, (task.own state' processId).head? = some transition' ∧
      transition'.event = transition.event ∧ transition'.tasks = transition.tasks ∧
      transition'.finished = transition.finished ∧ transition'.exhausted = transition.exhausted ∧
      (transition.state.Changed processId (Same Queued (queueChange queue mailbox links)) transition'.state ∨
        (∃ reason, transition.state = state.terminate processId reason ∧
          transition'.state = state'.terminate processId reason) ∨
        transition.exhausted = true) := by
  rcases changed.records with ⟨missing, -⟩ | ⟨first, second, found', found'', queued, rfl⟩
  · rw [found] at missing; cases missing
  rw [found] at found'; cases found'
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = queueChange queue mailbox links process := by
    simp [State.process, found'']
  have view : state'.view processId = state.view processId := by
    simp only [State.view, processOf, processOf']; rfl
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at head
  | none =>
  cases computation with
  | ok value =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, .inr (.inl ⟨_, rfl, rfl⟩)⟩
  | error exception =>
    cases exception <;> simp only [Task.own, List.head?_cons, Option.some.injEq] at head <;> subst head <;>
      first
        | exact ⟨_, rfl, rfl, rfl, rfl, rfl, .inr (.inr rfl)⟩
        | exact ⟨_, rfl, rfl, rfl, rfl, rfl, .inr (.inl ⟨_, rfl, rfl⟩)⟩
  | get next =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    exact ⟨Transition.mk (.internal processId) state' [(processId, ⟨next (state.view processId), finish, none⟩)]
      none false, by simp [Task.own, view], rfl, rfl, rfl, rfl, .inl changed⟩
  | set updated next =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    exact ⟨Transition.mk (.internal processId) (state'.store processId updated) [(processId, ⟨next, finish, none⟩)]
      none false, rfl, rfl, rfl, rfl, rfl, .inl (changed.queue_modify _ (fun _ => rfl) (fun _ _ => rfl))⟩
  | schedule options child next =>
    have spawned := changed.spawnSelf change found options fresh
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    refine ⟨Transition.mk (.spawn processId (state.spawnWith processId options).1) (state'.spawnWith processId options).2
      [(processId, ⟨next (state.spawnWith processId options).1, finish, none⟩),
        ((state.spawnWith processId options).1, Task.child child)] none false,
      by simp only [Task.own, List.head?_cons, spawned.1], rfl, rfl, rfl, rfl, .inl spawned.2⟩
  | send destination message next =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    exact ⟨Transition.mk (.send processId destination message)
      (state'.send processId destination (.message message)) [(processId, ⟨next, finish, none⟩)] none false,
      rfl, rfl, rfl, rfl, rfl, .inl (changed.send unseen fun _ _ => by simp)⟩
  | receive timeout select next =>
    simp only [Task.own, processOf] at head
    simp only [Task.own, processOf', view]
    cases selected : selectMessage (select (state.view processId)) process.mailbox with
    | some result =>
      obtain ⟨message, value, remaining⟩ := result
      have selected' := change.select (select (state.view processId)) selected
      simp only [selected, List.head?_cons, Option.some.injEq] at head; subst head
      refine ⟨Transition.mk (.receive processId message)
        (state'.modify processId fun process => { process with mailbox := mailbox remaining })
        [(processId, ⟨next (some value), finish, none⟩)] none false, ?_, rfl, rfl, rfl, rfl, .inl ?_⟩
      · simp [queueChange, selected']
      · rw [State.modify_found found, State.modify_found found'']
        exact changed.setRelated ⟨queued, rfl⟩
    | none =>
      simp only [selected] at head
      cases timeout with
      | infinity => simp at head
      | _ =>
        cases quiet : Kernel.any process.queue (state.awaitedEntry processId) with
        | true =>
          simp only [Kernel.any_eq, List.any_eq_true] at quiet
          simp [quiet] at head
        | false =>
          have quietE : ¬∃ entry, entry ∈ process.queue ∧ state.awaitedEntry processId entry = true := by
            simpa [Kernel.any_eq, List.any_eq_true] using quiet
          simp only [quiet, quietE, Bool.false_eq_true, ↓reduceIte, List.head?_cons, Option.some.injEq] at head
          subst head
          have quiet' : Kernel.any (queue process.queue) (state'.awaitedEntry processId) = false := by
            cases more : Kernel.any (queue process.queue) (state'.awaitedEntry processId)
            · rfl
            · rw [awaited more] at quiet; cases quiet
          refine ⟨Transition.mk (.timeout processId) state' [(processId, ⟨next none, finish, none⟩)] none false,
            ?_, rfl, rfl, rfl, rfl, .inl changed⟩
          have quietE' : ¬∃ entry, entry ∈ queue process.queue ∧ state'.awaitedEntry processId entry = true := by
            simpa [Kernel.any_eq, List.any_eq_true] using quiet'
          simp [queueChange, noMatch _ selected quiet, quiet', quietE']
  | request query next =>
    have answered := changed.requestSelf unseen change found unlinked next query
    simp only [Task.own] at head ⊢
    revert answered head
    generalize state.request processId next query = answer
    generalize state'.request processId next query = answer'
    intro head answered
    cases answer <;> cases answer' <;> unfold Answer.Changed at answered
    all_goals first
      | exact answered.elim
      | (obtain ⟨rfl, answered⟩ := answered
         simp only [List.head?_cons, Option.some.injEq] at head
         subst head
         exact ⟨_, rfl, rfl, rfl, rfl, rfl, .inl answered⟩)

end State.Changed

/-! ### Which tagged steps are forced -/

/-- Whether an event is reading or replacing the environment, or receiving. -/
private def Event.local : Event → Bool
  | .internal _ | .receive .. => true
  | _ => false

private theorem Config.forced_own {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {event : Event} {next : Config α} {forced : Bool}
    {task : Task α} {transition : Transition α} (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.own state processId).head? = some transition)
    (mem : (Key.own processId, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps) :
    forced = (transition.event.local &&
      (transition.state.process processId).refCounter == (state.process processId).refCounter) := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at mem
  rcases mem with (((⟨⟨before, ⟨other, task'⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -⟩)
  · obtain ⟨transition', mem, key, -, -, rfl⟩ := own
    cases key
    have found := lookup_of_splitAt (splitAt_of_mem pairwise split)
    rw [lookup] at found
    cases found
    rw [head?_of_length mem (Task.own_length ..)] at head
    cases head
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
      (∃ event'', (key, event'', .running (raw.normalize.set processId (change (normRecord raw.gone processId process₁))).normalize
          (rewriteTask processId (fun _ => [(processId, task')]) tasks₁) finished₁ false, true) ∈
          (Config.running raw.normalize tasks₁ finished₁ false).taggedSteps ∧
        (change (normRecord raw.gone processId process₁)).exiting = none ∧
        normRecord raw.gone processId (change (normRecord raw.gone processId process₁)) =
          normRecord raw.gone processId (change process₁)) ∨
      -- The forced step does nothing after the other step.
      task' = task ∧ normRecord raw.gone processId (change process₁) = normRecord raw.gone processId process₁) :
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
  · have reachableMiddle := reachable₀.step (Config.step_of_stepOf step')
    rcases changedRaw.records with ⟨missing, -⟩ | ⟨process₁, process₂, found₁, -, ok₁, live₁, -, -⟩
    · exfalso
      have alive := reachableMiddle.2.2.1 _ (mem_of_lookup (lookupAfter ▸ lookup))
      rw [State.alive_normalize withinRaw.1] at alive
      simp [State.alive, missing] at alive
    rcases atMiddle raw tasks₁ finished₁ process₁ withinRaw reachableMiddle (lookupAfter ▸ lookup) found₁ ok₁ live₁ with
      ⟨event'', mem, liveChanged, renormalized⟩ | ⟨rfl, nothing⟩
    · rw [State.forced_close withinRaw.1 withinRaw'.1 changedRaw hidden.unseen found₁ liveChanged renormalized] at mem
      exact .inr ⟨key, event'', _, event', mem, stepped⟩
    · left
      refine ⟨event', ?_⟩
      rw [stepped, rewriteTask_same (lookupAfter ▸ lookup), State.Changed.normalize_same withinRaw.1 withinRaw'.1 changedRaw
        hidden.unseen found₁ nothing]

private theorem Config.tagged_own_forced {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.own state processId).head? = some transition)
    (isLocal : transition.event.local = true)
    (counter : (transition.state.process processId).refCounter = (state.process processId).refCounter) :
    (Key.own processId, transition.event, if transition.exhausted then
        Config.running { transition.state with processes := [], timers := [] } [] finished true
      else .running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
        (transition.finished.orElse fun _ => finished) false, true) ∈
      (Config.running state tasks finished false).taggedSteps := by
  obtain ⟨flag, mem⟩ := Config.tagged_of_stepOf (Config.stepOf_own_of (finished := finished) lookup head)
  have flagged := Config.forced_own pairwise lookup head mem
  rw [isLocal, counter] at flagged
  simp only [beq_self_eq_true, Bool.and_self] at flagged
  rw [flagged] at mem
  exact mem

/-- A process's own forced step against a step of another key. -/
private theorem Config.forced_own_other {elapsed : PID → Nat → Nat} {config : Config α} {processId : PID}
    {event event' : Event} {next middle : Config α} {key' : Key} (reachable : config.Reachable elapsed)
    (forced : (Key.own processId, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf key' = some (event', middle)) (owner : key'.owner ≠ some processId) :
    (∃ absorbed, next.stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf key' = some (other, last) := by
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running (elapsed := elapsed) forced
  have step := reachable.stepOf forced
  obtain ⟨task, transition, lookup, head, -⟩ := Config.stepOf_own step
  have flagged := Config.forced_own reachable.2.1 lookup head forced
  simp only [Bool.true_eq, Bool.and_eq_true, beq_iff_eq] at flagged
  obtain ⟨isLocal, counter⟩ := flagged
  rw [Config.stepOf_own_of (finished := finished) lookup head] at step
  simp only [Option.some.injEq, Prod.mk.injEq] at step
  obtain ⟨rfl, rfl⟩ := step
  have sorted := reachable.1.1.1
  have alive := reachable.2.2.1 _ (mem_of_lookup lookup)
  obtain ⟨process, found, live⟩ := State.alive_iff.mp alive
  have clean := (Clean.of_normalized sorted reachable.1.2.1 found).1
  -- At a later configuration where the process keeps its fields, its own step is the same change.
  have later : ∀ {raw : State} {process₁ : ProcessState}, raw.Within elapsed → raw.record processId = some process₁ →
      process₁.exiting = none → Keeps process process₁ →
      raw.normalize.record processId = some (normRecord raw.gone processId process₁) ∧
        raw.normalize.view processId = state.view processId ∧
        (raw.normalize.process processId).mailbox = process.mailbox ∧
        (raw.normalize.process processId).refCounter = process.refCounter := fun within found₁ live₁ keeps => by
    have record := State.record_normalize_live within.1 found₁ live₁
    refine ⟨record, ?_, ?_, ?_⟩
    · simp only [State.view, State.process, record, found, Option.getD_some]
      rw [normRecord_live live₁, keeps.2.1, keeps.2.2]
    · simp only [State.process, record, Option.getD_some]; rw [normRecord_live live₁]; exact keeps.1
    · simp only [State.process, record, Option.getD_some]; rw [normRecord_live live₁]; exact keeps.2.2
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at head
  | none =>
  cases computation with
  | get next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    rw [show state.normalize = (state.set processId (id process)).normalize by rw [id, State.set_self sorted found]]
    refine Config.forced_other (key := .own processId) reachable lookup found live ⟨rfl, rfl, rfl⟩ (hidden_keeps process)
      (renormalize_of_clean (change := id) clean) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ keeps₁ live₁
    obtain ⟨record, view, -, -⟩ := later within found₁ live₁ keeps₁
    have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (transition := Transition.mk (.internal processId) raw.normalize
        [(processId, ⟨next₀ (raw.normalize.view processId), finish, none⟩)] none false) (by simp [Task.own]) rfl rfl
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none, view] at tagged
    rw [show raw.normalize.normalize = (raw.normalize.set processId (id (normRecord raw.gone processId process₁))).normalize
      by rw [id, State.set_self (Sorted.normalize within.1) record]] at tagged
    exact .inl ⟨_, tagged, by rw [id, normRecord_live live₁]; exact live₁,
      normRecord_normRecord (fun _ gone => gone) _ _⟩
  | set updated next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    -- The forced step allocates no reference.
    have kept : max process.refCounter updated.refCounter = process.refCounter := by
      simp only [State.store, State.process, State.modify_found found, State.record_set, ↓reduceIte,
        Option.getD_some, found] at counter
      exact counter
    rw [show state.store processId updated = state.set processId (storeChange updated process) from
      State.modify_found found _]
    have cleaned := clean_live clean live
    refine Config.forced_other (key := .own processId) reachable lookup found live ⟨rfl, rfl, rfl⟩
      (hidden_store' process updated) (normRecord_any live (fun entry mem inert' gone' =>
        inert_any (process := process) (process' := storeChange updated process) rfl (cleaned.1 entry mem)
          inert' gone') cleaned.2) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ keeps₁ live₁
    obtain ⟨record, -, -, counter₁⟩ := later within found₁ live₁ keeps₁
    have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (transition := Transition.mk (.internal processId) (raw.normalize.store processId updated)
        [(processId, ⟨next₀, finish, none⟩)] none false) (by simp [Task.own]) rfl (by
          simp only [State.store, State.process, State.modify_found record, State.record_set, ↓reduceIte,
            Option.getD_some, record]
          rw [normRecord_live live₁, keeps₁.2.2, kept])
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    rw [show raw.normalize.store processId updated =
      raw.normalize.set processId (storeChange updated (normRecord raw.gone processId process₁)) from
      State.modify_found record _] at tagged
    exact .inl ⟨_, tagged, by rw [storeChange, normRecord_live live₁]; exact live₁, normRecord_store live₁ updated⟩
  | receive timeout select next₀ =>
    have mailbox : (state.process processId).mailbox = process.mailbox := by simp [State.process, found]
    cases selected : selectMessage (select (state.view processId)) process.mailbox with
    | none =>
      exfalso
      simp only [Task.own, mailbox, selected] at head
      repeat' split at head
      all_goals simp only [List.head?_nil, List.head?_cons, Option.some.injEq, reduceCtorEq] at head
      all_goals subst head; simp [Event.local] at isLocal
    | some result =>
      obtain ⟨message, value, remaining⟩ := result
      simp only [Task.own, mailbox, selected, List.head?_cons, Option.some.injEq] at head; subst head
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
      rw [show (state.modify processId fun process => { process with mailbox := remaining }) =
        state.set processId (receiveChange remaining process) from State.modify_found found _]
      refine Config.forced_other (key := .own processId) reachable lookup found live ⟨rfl, rfl, rfl⟩
        (hidden_receive process remaining)
        (renormalize_of_clean (by rw [receiveChange_normRecord live, clean])) owner step' ?_
      intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ keeps₁ live₁
      obtain ⟨record, view, mailbox₁, counter₁⟩ := later within found₁ live₁ keeps₁
      have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
        (transition := Transition.mk (.receive processId message)
          (raw.normalize.modify processId fun process => { process with mailbox := remaining })
          [(processId, ⟨next₀ (some value), finish, none⟩)] none false)
        (by simp [Task.own, view, mailbox₁, selected]) rfl (by
          simp only [State.process, State.modify_found record, State.record_set, ↓reduceIte, Option.getD_some,
            record])
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
      rw [show (raw.normalize.modify processId fun process => { process with mailbox := remaining }) =
        raw.normalize.set processId (receiveChange remaining (normRecord raw.gone processId process₁)) from
        State.modify_found record _] at tagged
      exact .inl ⟨_, tagged, by rw [receiveChange, normRecord_live live₁]; exact live₁,
        normRecord_receive live₁ remaining⟩
  | ok value =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp [Event.local, Task.ended] at isLocal
  | error exception =>
    cases exception <;> simp only [Task.own, List.head?_cons, Option.some.injEq] at head <;> subst head <;>
      simp [Event.local, Task.ended] at isLocal
  | schedule options child next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp [Event.local] at isLocal
  | send destination message next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp [Event.local] at isLocal
  | request query next₀ =>
    simp only [Task.own] at head
    split at head <;> simp only [List.head?_cons, Option.some.injEq] at head <;> subst head <;>
      simp [Event.local] at isLocal

private theorem Config.tagged_handle_forced {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    {entry : Entry} {rest : List Entry} (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (lookup : Kernel.lookup processId tasks = some task) (queue : (state.process processId).queue = entry :: rest)
    (head : (task.handle state processId).head? = some transition) (flag : task.forcedHead state processId entry = true) :
    (Key.handle processId, transition.event, if transition.exhausted then
        Config.running { transition.state with processes := [], timers := [] } [] finished true
      else .running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
        (transition.finished.orElse fun _ => finished) false, true) ∈
      (Config.running state tasks finished false).taggedSteps := by
  obtain ⟨forced, mem⟩ := Config.tagged_of_stepOf (Config.stepOf_handle_of (finished := finished) lookup head)
  have flagged := Config.forced_handle pairwise lookup mem
  rw [queue] at flagged
  simp only [flag] at flagged
  rw [flagged] at mem
  exact mem

/-- The record of a live process after normalizing, which keeps its oldest signal. -/
private theorem State.normalize_heads {raw : State} {processId : PID} {process : ProcessState} {entry : Entry}
    (sorted : raw.Sorted) (found : raw.record processId = some process) (live : process.exiting = none)
    (heads : Heads entry process) (kept : inert raw.gone processId process entry = false) :
    raw.normalize.record processId = some (normRecord raw.gone processId process) ∧
      ∃ rest, (normRecord raw.gone processId process).queue = entry :: rest := by
  refine ⟨State.record_normalize_live sorted found live, ?_⟩
  obtain ⟨rest, queue⟩ := heads
  rw [normRecord_live live]
  exact ⟨List.filter (fun other => !inert raw.gone processId process other) rest,
    by simp [queue, kept, Kernel.filter_eq]⟩

/-- Handling a message at the head of a live process's queue. -/
private theorem Task.handle_message {state : State} {processId : PID} {task : Task α} {process : ProcessState}
    {source : PID} {message : Term} {rest : List Entry} (sorted : state.Sorted)
    (found : state.record processId = some process)
    (queue : process.queue = ⟨source, .message message⟩ :: rest) :
    task.handle state processId = [Transition.mk (.handle processId ⟨source, .message message⟩)
      (state.set processId (messageChange message process)) [(processId, task)] none false] := by
  have processOf : state.process processId = process := by simp [State.process, found]
  simp only [Task.handle, processOf, queue, State.handle, State.append_set sorted]
  simp [messageChange, queue]

/-- The value a reply or marker resumes a waiting process with. -/
private def resumedBy (task : Task α) (entry : Entry) : Option Term :=
  match task.wait, entry.signal with
  | some (.reply expected, _), .reply value => if expected == entry.source then some value else none
  | some (.flush value, _), .flush => some value
  | _, _ => none

/-- A task, resumed with a value if it waits. -/
private def resumeTask : Option Term → Task α → Task α
  | some value, ⟨_, finish, some (_, next)⟩ => ⟨next value, finish, none⟩
  | _, task => task

/-- Handling a reply or marker at the head of a live process's queue. -/
private theorem Task.handle_quiet {state : State} {processId : PID} {task : Task α} {process : ProcessState}
    {entry : Entry} {rest : List Entry} (sorted : state.Sorted) (found : state.record processId = some process)
    (queue : process.queue = entry :: rest) (quiet : (entry.signal matches .reply _ | .flush) = true) :
    task.handle state processId = [Transition.mk (.handle processId entry) (state.set processId (popChange process))
      [(processId, resumeTask (resumedBy task entry) task)] none false] := by
  have processOf : state.process processId = process := by simp [State.process, found]
  have popped : ({ process with queue := rest } : ProcessState) = popChange process := by simp [popChange, queue]
  obtain ⟨source, signal⟩ := entry
  obtain ⟨computation, finish, wait⟩ := task
  cases signal <;> simp only [reduceCtorEq] at quiet
  all_goals
    cases wait with
    | none => simp [Task.handle, processOf, queue, State.handle, popped, resumedBy, resumeTask]
    | some waiting =>
      obtain ⟨wait, next⟩ := waiting
      cases wait with
      | reply expected =>
        by_cases same : expected = source <;>
          simp [Task.handle, processOf, queue, State.handle, popped, resumedBy, resumeTask, same]
      | _ => simp [Task.handle, processOf, queue, State.handle, popped, resumedBy, resumeTask]

/-- Handling an acknowledgement of an unlink at the head of a live process's queue. -/
private theorem Task.handle_ack {state : State} {processId : PID} {task : Task α} {process : ProcessState}
    {source : PID} {id : Nat} {rest : List Entry} (sorted : state.Sorted)
    (found : state.record processId = some process)
    (queue : process.queue = ⟨source, .unlinkAck id⟩ :: rest) :
    task.handle state processId = [Transition.mk (.handle processId ⟨source, .unlinkAck id⟩)
      (state.set processId (ackChange source id process)) [(processId, task)] none false] := by
  have processOf : state.process processId = process := by simp [State.process, found]
  have modified : ∀ change : ProcessState → ProcessState,
      (state.set processId { process with queue := rest }).modify processId change =
        state.set processId (change { process with queue := rest }) := fun change => by
    rw [State.modify_found (by rw [State.record_set, if_pos rfl]), State.set_set sorted]
  have processSet : (state.set processId { process with queue := rest }).process processId =
      { process with queue := rest } := by simp [State.process, State.record_set]
  by_cases linked : (Kernel.lookup source process.links == some (some id)) = true
  · have linked' : List.lookup source process.links = some (some id) := by
      simpa [Kernel.lookup_eq] using linked
    simp only [Task.handle, processOf, queue, State.handle, processSet, linked, ↓reduceIte, modified]
    have unacked' : unacked source id = fun link => !link.1 == source || !link.2 == some id := by
      funext link; simp [unacked, Bool.not_and]
    simp [ackChange, ackedChange, unacked', linked', queue, Bool.not_and]
  · have linked' : ¬List.lookup source process.links = some (some id) := by
      simpa [Kernel.lookup_eq] using linked
    simp only [Task.handle, processOf, queue, State.handle, processSet, linked, ↓reduceIte, Bool.false_eq_true]
    simp [ackChange, ackedChange, popChange, linked', queue]

private theorem ackChange_fields (source : PID) (id : Nat) (process : ProcessState) :
    (ackChange source id process).exiting = process.exiting ∧
      inert = inert := ⟨by unfold ackChange ackedChange popChange; split <;> rfl, rfl⟩

/-- Whether a queued signal does nothing depends on neither the queue nor the links. -/
private theorem inert_ack {gone : PID → Bool} {processId source : PID} {id : Nat} {process : ProcessState} :
    inert gone processId (ackChange source id process) = inert gone processId process := by
  unfold ackChange ackedChange popChange; split <;> rfl

/-- Handling an acknowledgement at a clean record leaves it clean. -/
private theorem normRecord_ack_clean {gone : PID → Bool} {processId source : PID} {id : Nat} {process : ProcessState}
    (clean : normRecord gone processId process = process) (live : process.exiting = none) (gone' : PID → Bool) :
    normRecord gone' processId (normRecord gone processId (ackChange source id process)) =
      normRecord gone' processId (ackChange source id process) := by
  have cleaned := clean_live clean live
  have live' : (ackChange source id process).exiting = none := (ackChange_fields source id process).1.trans live
  congr 1
  rw [normRecord_live live', inert_ack]
  have keepLinks : ∀ links : List (PID × Option Nat), (∀ link ∈ links, link ∈ process.links) →
      Kernel.filter (fun link => !(link.2.isSome && gone link.1)) links = links := fun links sub => by
    rw [Kernel.filter_eq]; exact List.filter_eq_self.mpr fun link mem => by simp [cleaned.2 link (sub link mem)]
  have keepQueue : Kernel.filter (fun entry => !inert gone processId process entry) process.queue.tail =
      process.queue.tail := by
    rw [Kernel.filter_eq]
    exact List.filter_eq_self.mpr fun entry mem => by simp [cleaned.1 entry (List.mem_of_mem_tail mem)]
  unfold ackChange ackedChange popChange
  split
  · rw [keepLinks _ fun link mem => by
        simp only [Kernel.filter_eq, List.mem_filter] at mem; exact mem.1]
    simp only [keepQueue]
  · simp only [keepQueue, keepLinks _ fun _ mem => mem]

/-- Normalizing before handling a queued acknowledgement reaches what handling it reaches. -/
private theorem normRecord_ack_kept {gone : PID → Bool} {processId source : PID} {id : Nat} {process : ProcessState}
    (live : process.exiting = none) (heads : Heads ⟨source, .unlinkAck id⟩ process) :
    normRecord gone processId (ackChange source id (normRecord gone processId process)) =
      normRecord gone processId (ackChange source id process) := by
  obtain ⟨rest, queue⟩ := heads
  have liveNormal : (normRecord gone processId process).exiting = none := by rw [normRecord_live live]; exact live
  rw [normRecord_live ((ackChange_fields source id _).1.trans liveNormal),
    normRecord_live ((ackChange_fields source id _).1.trans live), inert_ack, inert_ack,
    funext (inert_normRecord (gone := gone) (processId := processId) live)]
  let keep := fun link : PID × Option Nat => !(link.2.isSome && gone link.1)
  -- Normalizing, then handling, keeps the same links as handling, then normalizing.
  have links : Kernel.filter keep (ackChange source id (normRecord gone processId process)).links =
      Kernel.filter keep (ackChange source id process).links := by
    have normal : (normRecord gone processId process).links = Kernel.filter keep process.links := by
      rw [normRecord_live live]
    have dropped : ∀ entries : List (PID × Option Nat), gone source = true →
        Kernel.filter keep (Kernel.filter (unacked source id) entries) = Kernel.filter keep entries := by
      intro entries goneSource
      simp only [Kernel.filter_eq, List.filter_filter]
      refine List.filter_congr fun link _ => ?_
      by_cases key : link.1 = source <;> by_cases value : link.2 = some id <;>
        simp_all [keep, unacked]
    unfold ackChange ackedChange popChange
    simp only [normal]
    cases goneSource : gone source
    · have lookups : Kernel.lookup source (Kernel.filter keep process.links) = Kernel.lookup source process.links := by
        simp only [Kernel.lookup_eq, Kernel.filter_eq]
        exact lookup_filter_of_keep fun link _ same => by simp [keep, same, goneSource]
      rw [lookups]
      split
      · simp only [Kernel.filter_eq, List.filter_filter]
        refine List.filter_congr fun link _ => ?_
        cases keep link <;> cases unacked source id link <;> rfl
      · simp only [Kernel.filter_eq, List.filter_filter, Bool.and_self]
    · split <;> split <;> simp only [Kernel.filter_eq, List.filter_filter] <;>
        refine List.filter_congr fun link _ => ?_ <;>
        by_cases key : link.1 = source <;> rcases link with ⟨peer, _ | value⟩ <;> simp_all [keep, unacked] <;>
        cases gone peer <;> simp
  have queues : Kernel.filter (fun entry => !inert gone processId process entry)
        (ackChange source id (normRecord gone processId process)).queue =
      Kernel.filter (fun entry => !inert gone processId process entry) (ackChange source id process).queue := by
    unfold ackChange ackedChange popChange
    rw [normRecord_live live]
    have kept : inert gone processId process ⟨source, .unlinkAck id⟩ = false := by simp [inert]
    split <;> split <;> simp [queue, kept, Kernel.filter_eq, List.filter_filter]
  rw [links, queues]
  unfold ackChange ackedChange popChange
  rw [normRecord_live live]
  split <;> split <;> rfl

/-- Whether a signal other than an acknowledgement that does nothing yet is forced does not
depend on the state. -/
private theorem Task.forcedHead_transfer {state state' : State} {processId : PID} {task : Task α} {entry : Entry}
    (notAck : ∀ id, entry.signal ≠ .unlinkAck id)
    (notInert : state.inertEntry processId entry = false) (flagged : task.forcedHead state processId entry = true) :
    task.forcedHead state' processId entry = true := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp_all [Task.forcedHead]

/-- A forced handling of the oldest signal against a step of another key. -/
private theorem Config.forced_handle_other {elapsed : PID → Nat → Nat} {config : Config α} {processId : PID}
    {event event' : Event} {next middle : Config α} {key' : Key} (reachable : config.Reachable elapsed)
    (forced : (Key.handle processId, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf key' = some (event', middle)) (owner : key'.owner ≠ some processId) :
    (∃ absorbed, next.stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf key' = some (other, last) := by
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running (elapsed := elapsed) forced
  have step := reachable.stepOf forced
  obtain ⟨task, transition, lookup, head, -⟩ := Config.stepOf_handle step
  have flagged := Config.forced_handle reachable.2.1 lookup forced
  rw [Config.stepOf_handle_of (finished := finished) lookup head] at step
  simp only [Option.some.injEq, Prod.mk.injEq] at step
  obtain ⟨rfl, rfl⟩ := step
  have sorted := reachable.1.1.1
  have alive := reachable.2.2.1 _ (mem_of_lookup lookup)
  obtain ⟨process, found, live⟩ := State.alive_iff.mp alive
  have clean := (Clean.of_normalized sorted reachable.1.2.1 found).1
  have cleaned := clean_live clean live
  have processOf : state.process processId = process := by simp [State.process, found]
  rw [processOf] at flagged
  cases queue : process.queue with
  | nil => simp [queue] at flagged
  | cons entry rest =>
  simp only [queue] at flagged
  have notInert : state.inertEntry processId entry = false := by
    rw [State.inertEntry_eq, processOf]
    exact cleaned.1 entry (by simp [queue])
  have heads : Heads entry process := ⟨rest, queue⟩
  -- A reply or marker only leaves the queue, resuming the process if it waits for it.
  have quietCase : (entry.signal matches .reply _ | .flush) = true → ((∃ absorbed,
      (if transition.exhausted then
          Config.running { transition.state with processes := [], timers := [] } [] finished true
        else Config.running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
          (transition.finished.orElse fun _ => finished) false).stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        (if transition.exhausted then
            Config.running { transition.state with processes := [], timers := [] } [] finished true
          else Config.running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
            (transition.finished.orElse fun _ => finished) false).stepOf key' = some (other, last)) := by
    intro quiet
    have notLink : entry.signal ≠ .link := fun link => by rw [link] at quiet; cases quiet
    have kept : ∀ gone process', inert gone processId process' entry = false := fun _ _ => by
      obtain ⟨source, signal⟩ := entry; cases signal <;> simp_all [inert]
    have handled := Task.handle_quiet (task := task) sorted found queue quiet
    rw [handled] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    refine Config.forced_other (key := .handle processId) (task' := resumeTask (resumedBy task entry) task) reachable
      lookup found live heads (hidden_pop notLink) (renormalize_of_clean (normRecord_popped clean live
        (by simp [popChange]) (fun _ => rfl) rfl live)) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ heads₁ live₁
    obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ (kept _ _)
    have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
      simp [State.process, record]
    have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (by rw [processOf₁, queue₁])
      (by rw [Task.handle_quiet (Sorted.normalize within.1) record queue₁ quiet]; rfl)
      (Task.forcedHead_transfer (fun _ ack => by rw [ack] at quiet; cases quiet) notInert flagged.symm)
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    exact .inl ⟨_, tagged, by rw [popChange, normRecord_live live₁]; exact live₁, normRecord_pop live₁ heads₁ (kept _ _)⟩
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | message message =>
    have fromProcess : (source != clock) = true := by simpa [Task.forcedHead, notInert] using flagged
    rw [Task.handle_message sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    refine Config.forced_other (key := .handle processId) (task' := task) reachable lookup found live heads
      (hidden_message (by simp) message) (renormalize_of_clean (normRecord_popped clean live
        (by simp [messageChange]) (fun _ => rfl) rfl live)) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ heads₁ live₁
    obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ (by simp [inert])
    have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
      simp [State.process, record]
    have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (by rw [processOf₁, queue₁])
      (transition := Transition.mk (.handle processId ⟨source, .message message⟩)
        (raw.normalize.set processId (messageChange message (normRecord raw.gone processId process₁)))
        [(processId, task)] none false)
      (by rw [Task.handle_message (Sorted.normalize within.1) record queue₁]; rfl)
      (by simp only [Task.forcedHead, fromProcess, Bool.or_true])
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    exact .inl ⟨_, tagged, by rw [messageChange, normRecord_live live₁]; exact live₁,
      normRecord_message live₁ heads₁ (by simp [inert]) message⟩
  | reply value => exact quietCase rfl
  | flush => exact quietCase rfl
  | unlinkAck id =>
    rw [Task.handle_ack sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    refine Config.forced_other (key := .handle processId) (task' := task) reachable lookup found live heads
      (hidden_ack (by simp) source id) (normRecord_ack_clean clean live) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ heads₁ live₁
    have kept : inert raw.gone processId process₁ ⟨source, .unlinkAck id⟩ = false := by simp [inert]
    obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ kept
    have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
      simp [State.process, record]
    have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1
      lookup₁ (by rw [processOf₁, queue₁])
      (by rw [Task.handle_ack (Sorted.normalize within.1) record queue₁]; rfl)
      (by simp [Task.forcedHead])
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    exact .inl ⟨_, tagged, by rw [(ackChange_fields source id _).1, normRecord_live live₁]; exact live₁,
      normRecord_ack_kept live₁ heads₁⟩
  | _ => simp [Task.forcedHead, notInert] at flagged

private theorem normRecord_ownChange {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) (pdict : List (Term × Term) → List (Term × Term)) (mailbox : List Term → List Term) :
    normRecord gone processId (ownChange pdict id mailbox process) =
      ownChange pdict id mailbox (normRecord gone processId process) := by
  rw [normRecord_live (show (ownChange pdict id mailbox process).exiting = none from live), normRecord_live live]
  rfl

private theorem hidden_own (ok : List Term → Prop) (dict : List (Term × Term)) (counter : Nat)
    (pdict : List (Term × Term) → List (Term × Term)) (mailbox : List Term → List Term) :
    Hidden (OwnOk ok dict counter) (ownChange pdict id mailbox) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => .rfl, fun _ ok' => ⟨ok', rfl⟩,
    fun _ ok' => ⟨ok', rfl⟩, fun ok' => ⟨ok', rfl⟩⟩

/-- Records changed exactly are changed up to normalization, while live. -/
private theorem State.Changed.forced_of_same {state state' : State} {processId : PID} {ok : ProcessState → Prop}
    {change : ProcessState → ProcessState} (changed : state.Changed processId (Same ok change) state')
    (live : ∀ process, state.record processId = some process → process.exiting = none)
    (exiting : ∀ process, (change process).exiting = process.exiting) :
    state.Changed processId (Forced processId ok change) state' := by
  refine ⟨changed.1, ?_, changed.2.2⟩
  rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, ok', rfl⟩
  · rw [first, second]; exact .none
  · rw [first, second]
    exact .some ⟨ok', live _ first, by rw [exiting]; exact live _ first, fun _ => rfl⟩

private theorem rewriteTask_twice {processId : PID} (first second : Task α) :
    ∀ tasks : List (PID × Task α), rewriteTask processId (fun _ => [(processId, second)])
      (rewriteTask processId (fun _ => [(processId, first)]) tasks) =
        rewriteTask processId (fun _ => [(processId, second)]) tasks
  | [] => rfl
  | (other, task) :: rest => by
      by_cases same : other = processId
      · subst same; simp [rewriteTask]
      · simp [rewriteTask, same, rewriteTask_twice first second rest]

private theorem rewriteTask_ended {processId : PID} (first : Task α) :
    ∀ tasks : List (PID × Task α), rewriteTask processId (fun _ => [])
      (rewriteTask processId (fun _ => [(processId, first)]) tasks) = rewriteTask processId (fun _ => []) tasks
  | [] => rfl
  | (other, task) :: rest => by
      by_cases same : other = processId
      · subst same; simp [rewriteTask]
      · simp [rewriteTask, same, rewriteTask_ended first rest]

/-- A process's forced own step, a change of its own fields, against handling
its oldest signal: handling absorbs it when it ends the process, and the forced
step closes the square otherwise. -/
private theorem Config.own_handle_square {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {process : ProcessState} {task : Task α}
    {computation : Result task.β} {pdict : List (Term × Term) → List (Term × Term)} {mailbox : List Term → List Term}
    {ok : List Term → Prop} {event' : Event} {middle : Config α}
    (reachable : (Config.running state tasks finished false).Reachable elapsed)
    (lookup : Kernel.lookup processId tasks = some task) (waiting : task.wait = none)
    (found : state.record processId = some process) (live : process.exiting = none)
    (own : OwnChange ok mailbox) (ok' : ok process.mailbox)
    (step' : (Config.running state tasks finished false).stepOf (.handle processId) = some (event', middle))
    (atMiddle : ∀ (raw : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α))
      (process₁ : ProcessState), raw.Within elapsed →
      (Config.running raw.normalize tasks₁ finished₁ false).Reachable elapsed →
      Kernel.lookup processId tasks₁ = some task → raw.record processId = some process₁ →
      OwnOk ok process.pdict process.refCounter process₁ → process₁.exiting = none →
      ∃ event'', (Key.own processId, event'', .running (raw.normalize.set processId
          (ownChange pdict id mailbox (normRecord raw.gone processId process₁))).normalize
          (rewriteTask processId (fun _ => [(processId, ⟨computation, task.finish, none⟩)]) tasks₁) finished₁ false, true) ∈
          (Config.running raw.normalize tasks₁ finished₁ false).taggedSteps) :
    (∃ absorbed, (Config.running (state.set processId (ownChange pdict id mailbox process))
        (rewriteTask processId (fun _ => [(processId, ⟨computation, task.finish, none⟩)]) tasks) finished false).stepOf
        (.handle processId) = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        (Config.running (state.set processId (ownChange pdict id mailbox process))
          (rewriteTask processId (fun _ => [(processId, ⟨computation, task.finish, none⟩)]) tasks) finished false).stepOf
          (.handle processId) = some (other, last) := by
  have sorted := reachable.1.1.1
  have within := reachable.1.1
  let change := ownChange pdict id mailbox
  let task' : Task α := ⟨computation, task.finish, none⟩
  have changed : state.Changed processId (Same (OwnOk ok process.pdict process.refCounter) change)
      (state.set processId (change process)) :=
    ⟨fun other differ => by rw [State.record_set, if_neg differ],
      by rw [State.record_set, if_pos rfl, found]; exact .some ⟨⟨ok', rfl, rfl⟩, rfl⟩, rfl, rfl⟩
  obtain ⟨task₀, transition, lookup₀, head, rfl⟩ := Config.stepOf_handle step'
  rw [lookup] at lookup₀; cases lookup₀
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : (state.set processId (change process)).process processId = change process := by
    simp [State.process, State.record_set]
  have lookup' : Kernel.lookup processId (rewriteTask processId (fun _ => [(processId, task')]) tasks) = some task' :=
    lookup_rewriteTask_self lookup
  cases queue : process.queue with
  | nil => simp [Task.handle, processOf, queue] at head
  | cons entry rest =>
  have queue' : (change process).queue = entry :: rest := queue
  have changedSet := changed.setRelated (process := { process with queue := rest })
    (process' := { change process with queue := rest }) ⟨⟨ok', rfl, rfl⟩, rfl⟩
  obtain ⟨same, changedHandled⟩ := changedSet.handleSelf own (task.wait.map (·.1)) entry
  have resumedNone := State.handle_not_waiting (state.set processId { process with queue := rest }) processId entry
  rw [waiting] at same changedHandled
  simp only [Option.map_none] at same changedHandled
  -- The handling step after the forced step.
  have handleN : ∀ transition', (task'.handle (state.set processId (change process)) processId).head? =
      some transition' → (Config.running (state.set processId (change process))
        (rewriteTask processId (fun _ => [(processId, task')]) tasks) finished false).stepOf (.handle processId) =
        some (transition'.event, if transition'.exhausted then
            Config.running { transition'.state with processes := [], timers := [] } [] finished true
          else .running transition'.state.normalize
            (rewriteTask processId (fun _ => transition'.tasks) (rewriteTask processId (fun _ => [(processId, task')]) tasks))
            (transition'.finished.orElse fun _ => finished) false) :=
    fun transition' head' => Config.stepOf_handle_of lookup' head'
  revert head
  simp only [Task.handle, processOf, queue, waiting, Option.map_none]
  generalize hT : (state.set processId { process with queue := rest }).handle processId none entry = triple
  generalize hT' : ((state.set processId (change process)).set processId { change process with queue := rest }).handle
    processId none entry = triple'
  rw [hT] at same changedHandled resumedNone
  rw [hT'] at same changedHandled
  obtain ⟨handled, resumed, exits⟩ := triple
  obtain ⟨handled', resumed', exits'⟩ := triple'
  intro head
  simp only [Prod.mk.injEq] at same resumedNone
  obtain ⟨resumedSame, exitsSame⟩ := same
  subst resumedSame exitsSame
  subst resumedNone
  have sortedHandled : handled.Within elapsed := by
    have := (within.set processId { process with queue := rest }).handle processId none entry
    rw [hT] at this; exact this
  have sortedHandled' : handled'.Within elapsed := by
    have := ((within.set processId (change process)).set processId { change process with queue := rest }).handle
      processId none entry
    rw [hT'] at this; exact this
  cases exits' with
  | some reason =>
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    have headN : (task'.handle (state.set processId (change process)) processId).head? =
        some (Task.ended task'.finish (.handle processId entry) handled' processId reason (.error (.exit reason))) := by
      simp [Task.handle, processOf', queue', hT', task']
    left
    refine ⟨Event.handle processId entry, ?_⟩
    rw [handleN _ headN]
    simp only [Task.ended, Bool.false_eq_true, ↓reduceIte, rewriteTask_ended]
    rw [State.Changed.terminateSelf changedHandled reason sortedHandled.1 sortedHandled'.1
      (sortedHandled.terminate processId reason).1 (sortedHandled'.terminate processId reason).1]
  | none =>
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    have headN : (task'.handle (state.set processId (change process)) processId).head? =
        some { event := .handle processId entry, state := handled', tasks := [(processId, task')] } := by
      simp [Task.handle, processOf', queue', hT', task']
    right
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none, rewriteTask_same lookup] at step' ⊢
    have reachableMiddle := reachable.step (Config.step_of_stepOf step')
    have alive := reachableMiddle.2.2.1 _ (mem_of_lookup lookup)
    rw [State.alive_normalize sortedHandled.1] at alive
    obtain ⟨process₁, found₁, live₁⟩ := State.alive_iff.mp alive
    have related₁ : OwnOk ok process.pdict process.refCounter process₁ := by
      rcases changedHandled.records with ⟨missing, -⟩ | ⟨first, second, found₂, -, ok₁, -⟩
      · rw [found₁] at missing; cases missing
      · rw [found₁] at found₂; cases found₂; exact ok₁
    obtain ⟨event'', mem⟩ := atMiddle handled tasks finished process₁ sortedHandled reachableMiddle lookup found₁
      related₁ live₁
    have forcedChanged := changedHandled.forced_of_same (fun _ found₂ => by
      rw [found₁] at found₂; cases found₂; exact live₁) (fun _ => rfl)
    have liveNormal : (normRecord handled.gone processId process₁).exiting = none := by
      rw [normRecord_live live₁]; exact live₁
    rw [State.forced_close sortedHandled.1 sortedHandled'.1 forcedChanged
      (hidden_own ok process.pdict process.refCounter pdict mailbox).unseen found₁
      liveNormal
      (by rw [normRecord_ownChange liveNormal, normRecord_ownChange live₁,
        normRecord_normRecord (fun _ gone => gone)])] at mem
    refine ⟨.own processId, event'', _, Event.handle processId entry, mem, ?_⟩
    rw [handleN _ headN]
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none, rewriteTask_twice]
    rfl

/-- Replacing a live record of a normalized state by one normalizing keeps as it
is leaves the state normalized. -/
private theorem State.normalize_set_clean {state : State} {processId : PID} {process process' : ProcessState}
    (sorted : state.Sorted) (normalized : state.normalize = state) (found : state.record processId = some process)
    (live : process.exiting = none) (live' : process'.exiting = none)
    (clean : normRecord state.gone processId process' = process') :
    (state.set processId process').normalize = state.set processId process' := by
  have sorted' : (state.set processId process').Sorted := Sorted.insertRecord sorted _ _
  have gone : (state.set processId process').gone = state.gone := by
    funext other
    simp only [State.gone, State.alive, State.record_set]
    by_cases same : other = processId
    · subst same; simp [found, live, live']
    · simp [same]
  refine State.ext_records sorted' (Sorted.normalize sorted') (fun other => ?_) rfl rfl
  rw [State.record_normalize' sorted', gone, State.record_set]
  by_cases same : other = processId
  · subst same
    simp [clean, Option.filter, ProcessState.finished_live live']
  · simp only [same, ↓reduceIte]
    conv => rhs; rw [← normalized]
    rw [State.record_normalize' sorted]

/-- Selecting a message from a mailbox, or leaving it as it is without one. -/
private def selectFrom {β : Type} (select : Term → Option β) (messages : List Term) : List Term :=
  match selectMessage select messages with
  | some (_, _, remaining) => remaining
  | none => messages

private theorem ownChange_select {β : Type} (select : Term → Option β) (message : Term) (value : β) :
    OwnChange (fun messages => ∃ remaining, selectMessage select messages = some (message, value, remaining))
      (selectFrom select) where
  append other := by
    rintro ⟨remaining, selected⟩
    have appended := selectMessage_append (message := other) selected
    refine ⟨⟨_, appended⟩, ?_⟩
    simp only [Kernel.append_eq] at appended ⊢
    simp [selectFrom, selected, appended]

private theorem ownChange_true : OwnChange (fun _ => True) id where
  append _ _ := ⟨trivial, rfl⟩

/-- A process's own forced step against handling its oldest signal. -/
private theorem Config.forced_own_handle {elapsed : PID → Nat → Nat} {config : Config α} {processId : PID}
    {event event' : Event} {next middle : Config α} (reachable : config.Reachable elapsed)
    (forced : (Key.own processId, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf (.handle processId) = some (event', middle)) :
    (∃ absorbed, next.stepOf (.handle processId) = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf (.handle processId) = some (other, last) := by
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running (elapsed := elapsed) forced
  have step := reachable.stepOf forced
  obtain ⟨task, transition, lookup, head, -⟩ := Config.stepOf_own step
  have flagged := Config.forced_own reachable.2.1 lookup head forced
  simp only [Bool.true_eq, Bool.and_eq_true, beq_iff_eq] at flagged
  obtain ⟨isLocal, counter⟩ := flagged
  rw [Config.stepOf_own_of (finished := finished) lookup head] at step
  simp only [Option.some.injEq, Prod.mk.injEq] at step
  obtain ⟨rfl, rfl⟩ := step
  have sorted := reachable.1.1.1
  have normalized := reachable.1.2.1
  have alive := reachable.2.2.1 _ (mem_of_lookup lookup)
  obtain ⟨process, found, live⟩ := State.alive_iff.mp alive
  have clean := (Clean.of_normalized sorted normalized found).1
  have processOf : state.process processId = process := by simp [State.process, found]
  -- At a later configuration where the process keeps its fields, it reads the same view.
  have later : ∀ {raw : State} {process₁ : ProcessState} {ok : List Term → Prop}, raw.Within elapsed →
      raw.record processId = some process₁ → process₁.exiting = none →
      OwnOk ok process.pdict process.refCounter process₁ →
      raw.normalize.record processId = some (normRecord raw.gone processId process₁) ∧
        raw.normalize.view processId = state.view processId ∧
        (raw.normalize.process processId).mailbox = process₁.mailbox ∧
        (raw.normalize.process processId).refCounter = process.refCounter := fun within found₁ live₁ ok₁ => by
    have record := State.record_normalize_live within.1 found₁ live₁
    refine ⟨record, ?_, ?_, ?_⟩
    · simp only [State.view, State.process, record, found, Option.getD_some]
      rw [normRecord_live live₁, ok₁.2.1, ok₁.2.2]
    · simp only [State.process, record, Option.getD_some]; rw [normRecord_live live₁]
    · simp only [State.process, record, Option.getD_some]; rw [normRecord_live live₁]; exact ok₁.2.2
  have cleanOwn : ∀ (pdict : List (Term × Term) → List (Term × Term)) (mailbox : List Term → List Term),
      normRecord state.gone processId (ownChange pdict id mailbox process) = ownChange pdict id mailbox process :=
    fun pdict mailbox => by rw [normRecord_ownChange live, clean]
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at head
  | none =>
  cases computation with
  | get next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    rw [show state.normalize = state.set processId (ownChange id id id process) by
      rw [normalized]; exact (State.set_self sorted found).symm]
    refine Config.own_handle_square (computation := next₀ (state.view processId)) (pdict := id) (mailbox := id)
      reachable lookup rfl found live ownChange_true trivial step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ok₁ live₁
    obtain ⟨record, view, -, -⟩ := later within found₁ live₁ ok₁
    have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (transition := Transition.mk (.internal processId) raw.normalize
        [(processId, ⟨next₀ (raw.normalize.view processId), finish, none⟩)] none false) (by simp [Task.own]) rfl rfl
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none, view] at tagged
    rw [show raw.normalize.normalize = (raw.normalize.set processId
        (ownChange id id id (normRecord raw.gone processId process₁))).normalize
      by rw [show ownChange id id id (normRecord raw.gone processId process₁) =
          normRecord raw.gone processId process₁ from rfl, State.set_self (Sorted.normalize within.1) record]] at tagged
    exact ⟨_, tagged⟩
  | set updated next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    have kept : max process.refCounter updated.refCounter = process.refCounter := by
      simp only [State.store, State.process, State.modify_found found, State.record_set, ↓reduceIte,
        Option.getD_some, found] at counter
      exact counter
    have stored : storeChange updated process = ownChange (fun _ => updated.pdict) id id process := by
      simp [storeChange, ownChange, kept]
    rw [show state.store processId updated = state.set processId (storeChange updated process) from
      State.modify_found found _, stored,
      State.normalize_set_clean (process' := ownChange (fun _ => updated.pdict) id id process) sorted normalized found
        live live (cleanOwn _ _)]
    refine Config.own_handle_square (computation := next₀) (pdict := fun _ => updated.pdict) (mailbox := id)
      reachable lookup rfl found live ownChange_true trivial step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ok₁ live₁
    obtain ⟨record, -, -, counter₁⟩ := later within found₁ live₁ ok₁
    have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (transition := Transition.mk (.internal processId) (raw.normalize.store processId updated)
        [(processId, ⟨next₀, finish, none⟩)] none false) (by simp [Task.own]) rfl (by
          simp only [State.store, State.process, State.modify_found record, State.record_set, ↓reduceIte,
            Option.getD_some, record]
          rw [normRecord_live live₁, ok₁.2.2, kept])
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    rw [show raw.normalize.store processId updated =
      raw.normalize.set processId (ownChange (fun _ => updated.pdict) id id (normRecord raw.gone processId process₁))
      by rw [State.store, State.modify_found record]; congr 1; simp [ownChange, normRecord_live live₁, ok₁.2.2, kept]]
      at tagged
    exact ⟨_, tagged⟩
  | receive timeout select next₀ =>
    have mailbox : (state.process processId).mailbox = process.mailbox := by simp [processOf]
    cases selected : selectMessage (select (state.view processId)) process.mailbox with
    | none =>
      exfalso
      simp only [Task.own, mailbox, selected] at head
      repeat' split at head
      all_goals simp only [List.head?_nil, List.head?_cons, Option.some.injEq, reduceCtorEq] at head
      all_goals subst head; simp [Event.local] at isLocal
    | some result =>
      obtain ⟨message, value, remaining⟩ := result
      simp only [Task.own, mailbox, selected, List.head?_cons, Option.some.injEq] at head; subst head
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
      have received : (state.modify processId fun process => { process with mailbox := remaining }) =
          state.set processId (ownChange id id (selectFrom (select (state.view processId))) process) := by
        rw [State.modify_found found]; congr 1; simp [ownChange, selectFrom, selected]
      rw [received, State.normalize_set_clean
        (process' := ownChange id id (selectFrom (select (state.view processId))) process) sorted normalized found
        live live (cleanOwn _ _)]
      refine Config.own_handle_square (computation := next₀ (some value)) (pdict := id) reachable lookup rfl found live
        (ownChange_select (select (state.view processId)) message value) ⟨_, selected⟩ step' ?_
      intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ok₁ live₁
      obtain ⟨record, view, mailbox₁, -⟩ := later within found₁ live₁ ok₁
      obtain ⟨remaining₁, selected₁⟩ := ok₁.1
      have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
        (transition := Transition.mk (.receive processId message)
          (raw.normalize.modify processId fun process => { process with mailbox := remaining₁ })
          [(processId, ⟨next₀ (some value), finish, none⟩)] none false)
        (by simp [Task.own, view, mailbox₁, selected₁]) rfl (by
          simp only [State.process, State.modify_found record, State.record_set, ↓reduceIte, Option.getD_some,
            record])
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
      rw [show (raw.normalize.modify processId fun process => { process with mailbox := remaining₁ }) =
          raw.normalize.set processId (ownChange id id (selectFrom (select (state.view processId)))
            (normRecord raw.gone processId process₁)) by
        rw [State.modify_found record]; congr 1
        simp [ownChange, selectFrom, normRecord_live live₁, selected₁]] at tagged
      exact ⟨_, tagged⟩
  | ok value =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp [Event.local, Task.ended] at isLocal
  | error exception =>
    cases exception <;> simp only [Task.own, List.head?_cons, Option.some.injEq] at head <;> subst head <;>
      simp [Event.local, Task.ended] at isLocal
  | schedule options child next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp [Event.local] at isLocal
  | send destination message next₀ =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    simp [Event.local] at isLocal
  | request query next₀ =>
    simp only [Task.own] at head
    split at head <;> simp only [List.head?_cons, Option.some.injEq] at head <;> subst head <;>
      simp [Event.local] at isLocal

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
