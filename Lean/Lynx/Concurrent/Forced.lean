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
other processes neither read nor undo. `State.Changes` relates the states
before and after such a change, by a relation between the records, either of
which may be missing, and every step of another process keeps it. -/

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

/-- Whether a record is of a live process. -/
private def liveRecord (record : Option ProcessState) : Bool := (record.map (·.exiting.isNone)).getD false

/-- Whether a signal to a process that is gone is answered to its sender. -/
private def Signal.fallsBack : Signal → Bool
  | .link | .monitor _ | .isAlive => true
  | _ => false

/-- A relation between the records of a process, either of which may be
missing, that steps of other processes cannot tell apart, and that what they
change in the record keeps. -/
private structure Unnoticed (related : Option ProcessState → Option ProcessState → Prop) : Prop where
  live : ∀ {first second}, related first second → liveRecord second = liveRecord first
  trapExit : ∀ {first second}, related first second → (second.getD {}).trapExit = (first.getD {}).trapExit
  parked : ∀ {first second}, related first second → (second.getD {}).parked = (first.getD {}).parked
  links : ∀ {first second}, related first second → ∀ entry : Entry, entry.signal = .link →
    (entry ∈ (second.getD {}).queue ↔ entry ∈ (first.getD {}).queue)
  push : ∀ {first second} entry, related first second → liveRecord first = true →
    related (first.map (·.push entry)) (second.map (·.push entry))
  eagerExit : ∀ {first second} source, related first second → liveRecord first = true →
    related (first.map (·.eagerExit source)) (second.map (·.eagerExit source))
  unpark : ∀ {first second}, related first second → (first.getD {}).parked.isSome = true →
    related (first.map ({ · with parked := none })) (second.map ({ · with parked := none })) ∧
      ∀ entry, related ((first.map ({ · with parked := none })).map (·.push entry))
        ((second.map ({ · with parked := none })).map (·.push entry))

private theorem Unseen.opt {related : ProcessState → ProcessState → Prop} (unseen : Unseen related) :
    Unnoticed (Option.Rel related) where
  live rel := by cases rel with
    | none => rfl
    | some related => simp [liveRecord, (unseen.outside related).exiting]
  trapExit rel := by cases rel with
    | none => rfl
    | some related => exact (unseen.outside related).trapExit
  parked rel := by cases rel with
    | none => rfl
    | some related => exact (unseen.outside related).parked
  links rel := by cases rel with
    | none => exact fun _ _ => Iff.rfl
    | some related => exact (unseen.outside related).links
  push entry rel _ := by cases rel with
    | none => exact .none
    | some related => exact .some (unseen.push entry related)
  eagerExit source rel _ := by cases rel with
    | none => exact .none
    | some related => exact .some (unseen.eagerExit source related)
  unpark rel _ := by cases rel with
    | none => exact ⟨.none, fun _ => .none⟩
    | some related => exact ⟨.some (unseen.unpark related), fun entry => .some (unseen.push entry (unseen.unpark related))⟩

private instance {related : ProcessState → ProcessState → Prop} : Coe (Unseen related) (Unnoticed (Option.Rel related)) :=
  ⟨Unseen.opt⟩

/-- Two states that differ only in the record of a process, related by `related`,
either of which may be missing. -/
private structure State.Changes (processId : PID) (related : Option ProcessState → Option ProcessState → Prop)
    (state state' : State) : Prop where
  others : ∀ other, other ≠ processId → state'.record other = state.record other
  related : related (state.record processId) (state'.record processId)
  sameTimers : state'.timers = state.timers
  sameElapsed : state'.elapsed = state.elapsed
  samePersistent : state'.persistent = state.persistent

/-- Two states that differ only in the record of a process, related by `related`. -/
private abbrev State.Changed (processId : PID) (related : ProcessState → ProcessState → Prop)
    (state state' : State) : Prop :=
  State.Changes processId (Option.Rel related) state state'

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

private theorem State.alive_eq (state : State) (processId : PID) :
    state.alive processId = liveRecord (state.record processId) := by
  unfold State.alive liveRecord
  cases state.record processId <;> rfl

namespace State.Changes

variable {processId : PID} {related : Option ProcessState → Option ProcessState → Prop} {state state' : State}

private theorem record_other (changed : state.Changes processId related state') {other : PID} (differ : other ≠ processId) :
    state'.record other = state.record other := changed.others other differ

private theorem process_other (changed : state.Changes processId related state') {other : PID} (differ : other ≠ processId) :
    state'.process other = state.process other := by
  simp only [State.process, changed.record_other differ]

private theorem alive (changed : state.Changes processId related state') (unseen : Unnoticed related) (other : PID) :
    state'.alive other = state.alive other := by
  rw [State.alive_eq, State.alive_eq]
  by_cases differ : other = processId
  · subst differ; exact unseen.live changed.related
  · rw [changed.record_other differ]

private theorem gone (changed : state.Changes processId related state') (unseen : Unnoticed related) :
    state'.gone = state.gone := by
  funext other; simp only [State.gone, changed.alive unseen]

/-- What another process reads of a record is the same in both. -/
private theorem process_get (changed : state.Changes processId related state') {β : Type}
    {get : ProcessState → β} (same : ∀ {first second}, related first second → get (second.getD {}) = get (first.getD {}))
    (other : PID) : get (state'.process other) = get (state.process other) := by
  by_cases differ : other = processId
  · subst differ
    exact same changed.related
  · rw [changed.process_other differ]

private theorem set (changed : state.Changes processId related state') {other : PID} (differ : other ≠ processId)
    (process : ProcessState) : (state.set other process).Changes processId related (state'.set other process) := by
  refine ⟨fun third differ' => ?_, ?_, changed.sameTimers, changed.sameElapsed, changed.samePersistent⟩
  · simp only [State.record_set]
    split
    · rfl
    · exact changed.record_other differ'
  · simp only [State.record_set, Ne.symm differ, ↓reduceIte]
    exact changed.related

private theorem setRelated (changed : state.Changes processId related state') {process process' : ProcessState}
    (related' : related (some process) (some process')) :
    (state.set processId process).Changes processId related (state'.set processId process') := by
  refine ⟨fun third differ' => ?_, ?_, changed.sameTimers, changed.sameElapsed, changed.samePersistent⟩
  · simp only [State.record_set, differ', ↓reduceIte]
    exact changed.record_other differ'
  · simp only [State.record_set, ↓reduceIte]
    exact related'

private theorem remove (changed : state.Changes processId related state') {other : PID} (differ : other ≠ processId) :
    (state.remove other).Changes processId related (state'.remove other) := by
  refine ⟨fun third differ' => ?_, ?_, changed.sameTimers, changed.sameElapsed, changed.samePersistent⟩
  · simp only [State.record_remove]
    split
    · rfl
    · exact changed.record_other differ'
  · simp only [State.record_remove, Ne.symm differ, ↓reduceIte]
    exact changed.related

private theorem modify (changed : state.Changes processId related state') {other : PID} (differ : other ≠ processId)
    (change : ProcessState → ProcessState) :
    (state.modify other change).Changes processId related (state'.modify other change) := by
  unfold State.modify
  rw [changed.record_other differ]
  split
  · exact changed.set differ _
  · exact changed

/-- Changing the record of the process in a way the relation keeps. -/
private theorem modifyRelated (changed : state.Changes processId related state') {change : ProcessState → ProcessState}
    (keeps : related ((state.record processId).map change) ((state'.record processId).map change)) :
    (state.modify processId change).Changes processId related (state'.modify processId change) := by
  refine ⟨fun third differ' => ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.record_modify, State.record_modify, ite_eq_right differ', ite_eq_right differ']
    exact changed.record_other differ'
  · rw [State.record_modify, State.record_modify, ite_eq_left rfl, ite_eq_left rfl]
    exact keeps
  · unfold State.modify; split <;> split <;> exact changed.sameTimers
  · unfold State.modify; split <;> split <;> exact changed.sameElapsed
  · unfold State.modify; split <;> split <;> exact changed.samePersistent

private theorem timers (changed : state.Changes processId related state') (timers : List Timer) :
    { state with timers }.Changes processId related { state' with timers } :=
  ⟨changed.others, changed.related, rfl, changed.sameElapsed, changed.samePersistent⟩

private theorem table_eq (changed : state.Changes processId related state') : state'.persistent.table = state.persistent.table :=
  congrArg PersistentTerms.table changed.samePersistent

private theorem staged_eq (changed : state.Changes processId related state') : state'.persistent.staged = state.persistent.staged :=
  congrArg PersistentTerms.staged changed.samePersistent

private theorem persistent (changed : state.Changes processId related state') (key : Term) :
    state'.persistent.lookup key = state.persistent.lookup key := by
  simp only [PersistentTerms.lookup, changed.table_eq]

private theorem stage (changed : state.Changes processId related state') (staged : Option Update) :
    { state with persistent.staged := staged }.Changes processId related { state' with persistent.staged := staged } :=
  ⟨changed.others, changed.related, changed.sameTimers, changed.sameElapsed, PersistentTerms.ext changed.table_eq rfl⟩

private theorem commit (changed : state.Changes processId related state') :
    state.commit.Changes processId related state'.commit := by
  unfold State.commit
  rw [changed.staged_eq]
  split
  · exact ⟨changed.others, changed.related, changed.sameTimers, changed.sameElapsed, by simp only [changed.table_eq]⟩
  · exact changed

/-- A signal falls back without changing the process, or only queues at it. -/
private theorem fallback (changed : state.Changes processId related state')
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second},
      related first second →
      related (first.map fun first => { first with links := Kernel.filter (·.1 != target) first.links })
        (second.map fun second => { second with links := Kernel.filter (·.1 != target) second.links }))
    (pushes : source = processId → signal.fallsBack = true → ∀ entry,
      related ((state.record processId).map (·.push entry)) ((state'.record processId).map (·.push entry))) :
    (state.fallback source target signal).Changes processId related (state'.fallback source target signal) := by
  by_cases same : source = processId
  · subst same
    cases signal <;> simp only [State.fallback]
    all_goals first
      | exact changed
      | exact changed.modifyRelated (pushes rfl rfl _)
      | exact changed.modifyRelated (allowed rfl _ rfl changed.related)
  · cases signal <;> simp only [State.fallback] <;> first | exact changed | exact changed.modify same _

private theorem enqueue (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second},
      related first second →
      related (first.map fun first => { first with links := Kernel.filter (·.1 != target) first.links })
        (second.map fun second => { second with links := Kernel.filter (·.1 != target) second.links }))
    (pushes : source = processId → signal.fallsBack = true → ∀ entry,
      related ((state.record processId).map (·.push entry)) ((state'.record processId).map (·.push entry))) :
    (state.enqueue source target signal).Changes processId related (state'.enqueue source target signal) := by
  unfold State.enqueue
  by_cases same : target = processId
  · subst same
    have live := unseen.live changed.related
    have pushed := unseen.push { source, signal } changed.related
    revert live pushed
    cases first : state.record target <;> cases second : state'.record target <;>
      intro live pushed <;> simp only [liveRecord, Option.map_some, Option.map_none, Option.getD_some,
        Option.getD_none] at live pushed ⊢
    · exact changed.fallback allowed pushes
    · rw [live]; exact changed.fallback allowed pushes
    · rw [← live]; exact changed.fallback allowed pushes
    · rename_i process process'
      rw [live]
      split
      · rename_i isLive
        have pushed := pushed isLive
        unfold ProcessState.push at pushed
        exact changed.setRelated pushed
      · exact changed.fallback allowed pushes
  · rw [changed.record_other same]
    split
    · split
      · exact changed.set same _
      · exact changed.fallback allowed pushes
    · exact changed.fallback allowed pushes

private theorem parked (changed : state.Changes processId related state') (unseen : Unnoticed related) (other : PID) :
    (state'.process other).parked = (state.process other).parked :=
  changed.process_get (get := (·.parked)) unseen.parked other

private theorem unpark (changed : state.Changes processId related state') (unseen : Unnoticed related) (other : PID) :
    (state.unpark other).Changes processId related (state'.unpark other) := by
  unfold State.unpark
  rw [changed.parked unseen]
  split
  · rename_i target reference parkedAt
    by_cases same : other = processId
    · subst same
      have parked : ((state.record other).getD {}).parked.isSome = true := by
        simp only [State.process] at parkedAt; simp [parkedAt]
      obtain ⟨unparked, pushes⟩ := unseen.unpark changed.related parked
      have modified := changed.modifyRelated unparked
      refine modified.enqueue unseen (fun _ _ signal => by cases signal) fun _ _ entry => ?_
      rw [State.record_modify, State.record_modify, ite_eq_left rfl, ite_eq_left rfl]
      exact pushes entry
    · exact (changed.modify same _).enqueue unseen (fun equal => absurd equal same) fun equal => absurd equal same
  · exact changed

private theorem send (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second},
      related first second →
      related (first.map fun first => { first with links := Kernel.filter (·.1 != target) first.links })
        (second.map fun second => { second with links := Kernel.filter (·.1 != target) second.links }))
    (pushes : source = processId → signal.fallsBack = true → ∀ entry, ∀ {first second}, related first second →
      related (first.map (·.push entry)) (second.map (·.push entry))) :
    (state.send source target signal).Changes processId related (state'.send source target signal) := by
  unfold State.send
  rw [changed.parked unseen]
  have keeps : ∀ {first second : State}, first.Changes processId related second →
      (first.enqueue source target signal).Changes processId related (second.enqueue source target signal) :=
    fun changed' => changed'.enqueue unseen allowed fun same falls entry => pushes same falls entry changed'.related
  split
  · split
    · exact keeps (changed.unpark unseen source)
    · exact keeps changed
  · exact keeps changed

/-- Whether a link is queued at a process is the same in both. -/
private theorem any_queue (changed : state.Changes processId related state') (unseen : Unnoticed related)
    (target : PID) (find : Entry → Bool) (only : ∀ entry, find entry = true → entry.signal = .link) :
    Kernel.any (state'.process target).queue find = Kernel.any (state.process target).queue find := by
  refine changed.process_get (get := fun process => Kernel.any process.queue find) (fun rel => ?_) target
  simp only [Kernel.any_eq]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨entry, mem, found⟩ <;> refine ⟨entry, ?_, found⟩
  · exact (unseen.links rel _ (only _ found)).mp mem
  · exact (unseen.links rel _ (only _ found)).mpr mem

private theorem eagerLink (changed : state.Changes processId related state') (unseen : Unnoticed related)
    (source target : PID) (reason : Term) : state'.eagerLink source target reason = state.eagerLink source target reason := by
  unfold State.eagerLink
  rw [changed.alive unseen, changed.process_get (get := (·.trapExit)) unseen.trapExit target,
    changed.any_queue unseen target _ fun entry found => by
      obtain ⟨_, signal⟩ := entry; cases signal <;> simp_all]

private theorem linkExit (changed : state.Changes processId related state') (unseen : Unnoticed related)
    (source target : PID) (reason : Term) :
    (state.linkExit source target reason).Changes processId related (state'.linkExit source target reason) := by
  unfold State.linkExit
  rw [changed.eagerLink unseen]
  split
  · rename_i eager
    by_cases same : target = processId
    · subst same
      have alive : state.alive target = true := by
        simp only [State.eagerLink, Bool.and_eq_true] at eager; exact eager.1.1.2
      rw [State.alive_eq] at alive
      exact changed.modifyRelated (unseen.eagerExit source changed.related alive)
    · exact changed.modify same _
  · exact changed.send unseen (fun _ _ signal => by cases signal) fun _ falls => by simp [Signal.fallsBack] at falls

private theorem answer (changed : state.Changes processId related state') (unseen : Unnoticed related)
    (other : PID) (entry : Entry) :
    (state.answer other entry).Changes processId related (state'.answer other entry) := by
  unfold State.answer
  split <;> first | exact changed |
    exact changed.send unseen (fun _ _ signal => by cases signal) fun _ falls => by simp [Signal.fallsBack] at falls

private theorem allocate (changed : state.Changes processId related state') {other : PID}
    (differ : other ≠ processId) :
    (state'.allocate other).1 = (state.allocate other).1 ∧
      (state.allocate other).2.Changes processId related (state'.allocate other).2 :=
  ⟨by simp only [State.allocate, changed.process_other differ], changed.modify differ _⟩

private theorem foldl {γ : Type} {step : State → γ → State}
    (keeps : ∀ {state state'} item, state.Changes processId related state' →
      (step state item).Changes processId related (step state' item)) :
    ∀ (items : List γ) {state state'}, state.Changes processId related state' →
      (Kernel.foldl step state items).Changes processId related (Kernel.foldl step state' items)
  | [], _, _, changed => changed
  | item :: rest, _, _, changed => by
      have := foldl keeps rest (keeps item changed)
      simpa only [Kernel.foldl_eq, List.foldl_cons] using this

private theorem terminate (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) (reason : Term) :
    (state.terminate other reason).Changes processId related (state'.terminate other reason) := by
  unfold State.terminate
  simp only [changed.process_other differ, changed.sameTimers]
  refine State.Changes.foldl (fun target changed' => ?_) _ ((changed.timers _).set differ _)
  rw [changed'.eagerLink unseen]
  split
  · exact (changed'.modify differ _).linkExit unseen _ _ _
  · exact changed'

private theorem spawnWith (changed : state.Changes processId related state') {other : PID}
    (differ : other ≠ processId) (options : SpawnOptions)
    (fresh : Kernel.append other [(state.process other).children + 1] ≠ processId) :
    (state'.spawnWith other options).1 = (state.spawnWith other options).1 ∧
      (state.spawnWith other options).2.Changes processId related (state'.spawnWith other options).2 := by
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

end State.Changes

namespace State.Changes

variable {processId : PID} {related : ProcessState → ProcessState → Prop} {state state' : State}

/-- The two records of the process. -/
private theorem records (changed : state.Changes processId (Option.Rel related) state') :
    (state.record processId = none ∧ state'.record processId = none) ∨
      ∃ process process', state.record processId = some process ∧ state'.record processId = some process' ∧
        related process process' := by
  have rel := changed.related
  generalize state.record processId = first at rel
  generalize state'.record processId = second at rel
  cases rel with
  | none => exact .inl ⟨rfl, rfl⟩
  | some related => exact .inr ⟨_, _, rfl, rfl, related⟩

end State.Changes

private theorem rel_map {β : Type} {related : β → β → Prop} {change : β → β}
    (keeps : ∀ {first second}, related first second → related (change first) (change second)) :
    ∀ {first second : Option β}, Option.Rel related first second → Option.Rel related (first.map change) (second.map change)
  | _, _, .none => .none
  | _, _, .some related' => .some (keeps related')

namespace State.Changed

variable {processId : PID} {related : ProcessState → ProcessState → Prop} {state state' : State}

private theorem setRelated (changed : state.Changed processId related state') {process process' : ProcessState}
    (related' : related process process') :
    (state.set processId process).Changed processId related (state'.set processId process') :=
  State.Changes.setRelated changed (.some related')

private theorem modifyRelated (changed : state.Changed processId related state') {change : ProcessState → ProcessState}
    (keeps : ∀ {first second}, related first second → related (change first) (change second)) :
    (state.modify processId change).Changed processId related (state'.modify processId change) := by
  refine State.Changes.modifyRelated changed ?_
  have rel := changed.related
  revert rel
  generalize state.record processId = first
  generalize state'.record processId = second
  intro rel
  exact rel_map keeps rel

private theorem send (changed : state.Changed processId related state') (unseen : Unseen related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second},
      related first second →
      related { first with links := Kernel.filter (·.1 != target) first.links }
        { second with links := Kernel.filter (·.1 != target) second.links }) :
    (state.send source target signal).Changed processId related (state'.send source target signal) :=
  State.Changes.send changed unseen (@fun same id signal _ _ rel => rel_map (allowed same id signal) rel)
    fun _ _ entry _ _ rel => rel_map (unseen.push entry) rel

private theorem enqueue (changed : state.Changed processId related state') (unseen : Unseen related)
    {source target : PID} {signal : Signal} (allowed : source = processId → ∀ id, signal = .unlink id → ∀ {first second},
      related first second →
      related { first with links := Kernel.filter (·.1 != target) first.links }
        { second with links := Kernel.filter (·.1 != target) second.links }) :
    (state.enqueue source target signal).Changed processId related (state'.enqueue source target signal) :=
  State.Changes.enqueue changed unseen (@fun same id signal _ _ rel => rel_map (allowed same id signal) rel)
    fun _ _ entry => rel_map (unseen.push entry) changed.related

end State.Changed



/-- Two answers to a request that agree but for a process's record. -/
private def Answer.Changes {β : Type} (processId : PID) (related : Option ProcessState → Option ProcessState → Prop) :
    Answer β → Answer β → Prop
  | .reply value state, .reply value' state' => value' = value ∧ state.Changes processId related state'
  | .wait waiting state, .wait waiting' state' => waiting' = waiting ∧ state.Changes processId related state'
  | .continue computation state, .continue computation' state' =>
      computation' = computation ∧ state.Changes processId related state'
  | .suspended, .suspended => True
  | _, _ => False

namespace State.Changes

variable {processId : PID} {related : Option ProcessState → Option ProcessState → Prop} {state state' : State}

private theorem request (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) {β : Type} (next : Term → Result β) (query : Request) :
    Answer.Changes processId related (state.request other next query) (state'.request other next query) := by
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
    · exact ⟨rfl, (changed.modify differ _).send unseen (fun same => absurd same differ) fun same => absurd same differ⟩
  | unlink target =>
    simp only [State.request, changed.process_other differ]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, (changed.modify differ _).send unseen (fun same => absurd same differ) fun same => absurd same differ⟩
    · exact ⟨rfl, changed⟩
  | exit target reason quirk =>
    simp only [State.request, changed.process_other differ]
    split
    · exact ⟨rfl, changed.send unseen (fun same => absurd same differ) fun same => absurd same differ⟩
    split
    · exact ⟨rfl, changed.send unseen (fun same => absurd same differ) fun same => absurd same differ⟩
    · exact ⟨rfl, changed.send unseen (fun same => absurd same differ) fun same => absurd same differ⟩
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
    · exact ⟨rfl, changed.enqueue unseen (fun same => absurd same differ) fun same => absurd same differ⟩
    · exact ⟨rfl, changed.enqueue unseen (fun same => absurd same differ) fun same => absurd same differ⟩
  | processInfo target =>
    simp only [State.request, changed.alive unseen]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed.enqueue unseen (fun same => absurd same differ) fun same => absurd same differ⟩
    · exact ⟨rfl, changed⟩
  | sendAlias alias message =>
    exact ⟨rfl, changed.send unseen (fun same => absurd same differ) fun same => absurd same differ⟩
  | startTimer destination message duration =>
    simp only [State.request]
    obtain ⟨same, allocated⟩ := changed.allocate differ
    rw [same, allocated.alive unseen]
    refine ⟨rfl, ?_⟩
    split
    · rw [allocated.sameTimers]; exact allocated.timers _
    · exact allocated
  | cancelTimer reference =>
    simp only [State.request, changed.sameTimers, changed.process_other differ]
    split
    · exact ⟨by rw [changed.sameElapsed], (changed.timers _).modify differ _⟩
    · exact ⟨rfl, changed⟩
  | persistentGet key =>
    simp only [State.request, changed.persistent]
    exact ⟨rfl, changed⟩
  | persistentPut | persistentErase | persistentAwait =>
    simp only [State.request, State.stage, changed.persistent, changed.staged_eq]
    repeat' split
    all_goals first | trivial | exact ⟨rfl, changed⟩ | exact ⟨rfl, changed.stage _⟩


private theorem exitSignal (changed : state.Changes processId related state') {target : PID}
    (differ : target ≠ processId) (source : PID) (reason : Term) (linked normalKills : Bool) :
    (state'.exitSignal target source reason linked normalKills).2 = (state.exitSignal target source reason linked normalKills).2 ∧
      (state.exitSignal target source reason linked normalKills).1.Changes processId related
        (state'.exitSignal target source reason linked normalKills).1 := by
  simp only [State.exitSignal, changed.process_other differ]
  split
  · exact ⟨rfl, changed⟩
  have removed : (if linked then state.modify target fun process =>
        { process with links := Kernel.filter (·.1 != source) process.links } else state).Changes processId related
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

private theorem handle (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) (waiting : Option Wait) (entry : Entry) :
    (state'.handle other waiting entry).2 = (state.handle other waiting entry).2 ∧
      (state.handle other waiting entry).1.Changes processId related (state'.handle other waiting entry).1 := by
  have sends : ∀ {first second : State} (signal : Signal), first.Changes processId related second →
      (first.send other entry.source signal).Changes processId related (second.send other entry.source signal) :=
    fun _ changed' => changed'.send unseen (fun same => absurd same differ) fun same => absurd same differ
  have either : ∀ {condition : Prop} [Decidable condition] {first first' second second' : State},
      first.Changes processId related first' → second.Changes processId related second' →
      (if condition then first else second).Changes processId related (if condition then first' else second') :=
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

private theorem linkPhase (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) (target : PID) :
    Option.Rel (State.Changes processId related) (state.linkPhase other target) (state'.linkPhase other target) := by
  simp only [State.linkPhase, changed.record_other differ]
  split
  · split
    · split
      · exact .some (((changed.set differ _).linkExit unseen _ _ _))
      · exact .none
    · exact .none
  · exact .none

private theorem phase (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) :
    Option.Rel (State.Changes processId related) (state.phase other) (state'.phase other) := by
  simp only [State.phase, changed.record_other differ]
  split
  · split
    · split
      · exact .none
      · exact .some ((changed.set differ _).send unseen (fun same => absurd same differ) fun same => absurd same differ)
      · split
        · exact .some ((changed.set differ _).answer unseen _ _)
        · exact .none
    · exact .none
  · exact .none

private theorem fire (changed : state.Changes processId related state') (unseen : Unnoticed related)
    (timer : Timer) :
    (state.fire timer).Changes processId related (state'.fire timer) := by
  simp only [State.fire, changed.sameTimers]
  exact (changed.timers _).enqueue unseen (fun _ _ signal => by cases signal)
    fun _ falls => by simp [Signal.fallsBack] at falls

end State.Changes

/-- Two transitions that agree but for a process's record. -/
private def Transition.Changes (processId : PID) (related : Option ProcessState → Option ProcessState → Prop)
    (transition transition' : Transition α) : Prop :=
  transition'.event = transition.event ∧ transition'.tasks = transition.tasks ∧
    transition'.finished = transition.finished ∧ transition'.exhausted = transition.exhausted ∧
    transition.state.Changes processId related transition'.state

namespace State.Changes

variable {processId : PID} {related : Option ProcessState → Option ProcessState → Prop} {state state' : State}

private theorem inertEntry (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) (entry : Entry) :
    state'.inertEntry other entry = state.inertEntry other entry := by
  simp only [State.inertEntry, State.allocated, changed.process_other differ, changed.gone unseen]

private theorem ended (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) {γ : Type}
    (finish : Except Exception γ → Option (Except Exception α)) (event : Event) (reason : Term)
    (result : Except Exception γ) :
    Transition.Changes processId related (Task.ended finish event state other reason result)
      (Task.ended finish event state' other reason result) :=
  ⟨rfl, rfl, rfl, rfl, changed.terminate unseen differ reason⟩

private theorem own (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) (task : Task α)
    (fresh : Kernel.append other [(state.process other).children + 1] ≠ processId) :
    Option.Rel (Transition.Changes processId related) (task.own state other).head? (task.own state' other).head? := by
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
    exact .some ⟨rfl, rfl, rfl, rfl, changed.send unseen (fun same => absurd same differ) fun same => absurd same differ⟩
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
    cases answer <;> cases answer' <;> simp only [Answer.Changes] at answered
    case suspended.suspended => exact .none
    all_goals obtain ⟨rfl, answered⟩ := answered
    all_goals exact .some ⟨rfl, rfl, rfl, rfl, answered⟩

private theorem handleTask (changed : state.Changes processId related state') (unseen : Unnoticed related)
    {other : PID} (differ : other ≠ processId) (task : Task α) :
    Option.Rel (Transition.Changes processId related) (task.handle state other).head?
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

end State.Changes

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
      split at mem <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;> simp
    | error exception =>
      cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;> simp [Task.ended]
    | _ => simp only [Task.own, List.mem_singleton] at mem; subst mem; simp [Task.ended]

/-- A process's own step, by its task. -/
private theorem Config.stepOf_own_of {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.own state processId).head? = some transition) :
    (Config.running state tasks finished false).stepOf (.own processId) = some (transition.event,
      if transition.exhausted then .running { elapsed := transition.state.elapsed } [] none true
      else .running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
        (transition.finished.orElse fun _ => finished) false) := by
  obtain ⟨before, after, split⟩ := splitAt_of_lookup lookup
  simp [Config.stepOf, split, head, Transition.apply, rewriteTask_of_splitAt split]

/-- Handling a signal, by the process's task. -/
private theorem Config.stepOf_handle_of {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.handle state processId).head? = some transition) :
    (Config.running state tasks finished false).stepOf (.handle processId) = some (transition.event,
      if transition.exhausted then .running { elapsed := transition.state.elapsed } [] none true
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
    {related : Option ProcessState → Option ProcessState → Prop} {task' : Task α} {first : Transition α}
    {firsts seconds : List (Transition α)} (differ : other ≠ processId)
    {elapsed : PID → Nat → Nat} (pids : ∀ entry ∈ first.tasks, entry.1 ≠ processId)
    (related' : Option.Rel (Transition.Changes processId related) firsts.head? seconds.head?)
    (head : firsts.head? = some first) (within : first.state.Within elapsed)
    (within' : ∀ second, seconds.head? = some second → second.state.Within elapsed) :
    ∃ second : Transition α, seconds.head? = some second ∧ second.event = first.event ∧
      ((if second.exhausted then Config.running { elapsed := second.state.elapsed } [] none true
        else .running second.state.normalize
          (rewriteTask other (fun _ => second.tasks) (rewriteTask processId (fun _ => [(processId, task')]) tasks))
          (second.finished.orElse fun _ => finished) false) =
        (if first.exhausted then Config.running { elapsed := first.state.elapsed } [] none true
        else .running first.state.normalize (rewriteTask other (fun _ => first.tasks) tasks)
          (first.finished.orElse fun _ => finished) false) ∨
      ∃ (raw raw' : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α)),
        raw.Changes processId related raw' ∧ raw.Within elapsed ∧ raw'.Within elapsed ∧
        Kernel.lookup processId tasks₁ = Kernel.lookup processId tasks ∧
        (if first.exhausted then Config.running { elapsed := first.state.elapsed } [] none true
          else .running first.state.normalize (rewriteTask other (fun _ => first.tasks) tasks)
            (first.finished.orElse fun _ => finished) false) = .running raw.normalize tasks₁ finished₁ false ∧
        (if second.exhausted then Config.running { elapsed := second.state.elapsed } [] none true
          else .running second.state.normalize
            (rewriteTask other (fun _ => second.tasks) (rewriteTask processId (fun _ => [(processId, task')]) tasks))
            (second.finished.orElse fun _ => finished) false) =
          .running raw'.normalize (rewriteTask processId (fun _ => [(processId, task')]) tasks₁) finished₁ false) := by
  obtain ⟨second, head', event', tasks', finished', exhausted', changed'⟩ := rel_of_some (head ▸ related')
  refine ⟨second, head', event', ?_⟩
  rw [exhausted', tasks', finished']
  split
  · left
    rw [changed'.sameElapsed]
  · right
    refine ⟨first.state, second.state, _, _, changed', within, within' _ head',
      lookup_rewriteTask (Ne.symm differ) (fun _ => pids) tasks, rfl, ?_⟩
    rw [rewriteTask_comm (Ne.symm differ) (fun _ entry mem => by
        simp only [List.mem_singleton] at mem; subst mem; exact Ne.symm differ) (fun _ => pids)]

/-- The step of another key, after a change of a live process's record that
the step cannot see and of its task: the same step, then the change. -/
private theorem Config.step_changed {state state' : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {related : Option ProcessState → Option ProcessState → Prop}
    {task' : Task α} {key : Key} {event : Event} {next : Config α}
    {elapsed : PID → Nat → Nat} (within : state.Within elapsed) (within' : state'.Within elapsed)
    (changed : state.Changes processId related state') (unseen : Unnoticed related)
    (spawns : ∀ {other : PID} {other' : Task α}, Kernel.lookup other tasks = some other' → other ≠ processId →
      Kernel.append other [(state.process other).children + 1] ≠ processId)
    (quiet : ∀ {target : PID}, key = .phase processId ∨ key = .link processId target → False)
    (owner : key.owner ≠ some processId)
    (step : (Config.running state tasks finished false).stepOf key = some (event, next)) :
    ∃ next', (Config.running state' (rewriteTask processId (fun _ => [(processId, task')]) tasks) finished false).stepOf
        key = some (event, next') ∧
      (next' = next ∨ ∃ (raw raw' : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α)),
        raw.Changes processId related raw' ∧ raw.Within elapsed ∧ raw'.Within elapsed ∧
        Kernel.lookup processId tasks₁ = Kernel.lookup processId tasks ∧
        next = .running raw.normalize tasks₁ finished₁ false ∧
        next' = .running raw'.normalize (rewriteTask processId (fun _ => [(processId, task')]) tasks₁) finished₁ false) := by
  have tasks' : ∀ {other : PID}, other ≠ processId → ∀ {other' : Task α}, Kernel.lookup other tasks = some other' →
      Kernel.lookup other (rewriteTask processId (fun _ => [(processId, task')]) tasks) = some other' := by
    intro other differ other' found
    rw [lookup_rewriteTask differ (fun _ entry mem => by
      simp only [List.mem_singleton] at mem; subst mem; exact Ne.symm differ)]
    exact found
  -- Steps that keep the tasks.
  have kept : ∀ {first second : Option State} {event' : Event},
      Option.Rel (State.Changes processId related) first second →
      (∀ raw, first = some raw → raw.Within elapsed) → (∀ raw', second = some raw' → raw'.Within elapsed) →
      first.map (fun raw => (event', Config.running raw.normalize tasks finished false)) = some (event, next) →
      ∃ next', second.map (fun raw => (event', Config.running raw.normalize
          (rewriteTask processId (fun _ => [(processId, task')]) tasks) finished false)) = some (event, next') ∧
        (next' = next ∨ ∃ (raw raw' : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α)),
          raw.Changes processId related raw' ∧ raw.Within elapsed ∧ raw'.Within elapsed ∧
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
        · rw [child]; exact spawns found differ)
      (changed.own unseen differ other' (spawns found differ)) head
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
    · subst same; exact (quiet (target := other) (.inl rfl)).elim
    · exact kept (changed.phase unseen same) (fun _ found => within.phase found)
        (fun _ found => within'.phase found) step
  | link other target =>
    by_cases same : other = processId
    · subst same; exact (quiet (.inr rfl)).elim
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
    have firing : state'.firing = state.firing := by simp only [State.firing, changed.sameTimers]
    simp only [Config.stepOf, firing, Kernel.find?_eq] at step ⊢
    cases timer : List.find? (·.reference == reference) state.firing with
    | none => simp [timer] at step
    | some timer' =>
      simp only [timer, Option.map_some, Option.some.injEq, Prod.mk.injEq] at step ⊢
      obtain ⟨rfl, rfl⟩ := step
      exact ⟨_, ⟨rfl, rfl⟩, .inr ⟨_, _, _, _, changed.fire unseen timer', within.fire timer',
        within'.fire timer', rfl, rfl, rfl⟩⟩
  | commit =>
    simp only [Config.stepOf, changed.staged_eq] at step ⊢
    cases staged : state.persistent.staged with
    | none => simp [staged] at step
    | some update =>
      simp only [staged, Option.map_some, Option.some.injEq, Prod.mk.injEq] at step ⊢
      obtain ⟨rfl, rfl⟩ := step
      exact ⟨_, ⟨rfl, rfl⟩, .inr ⟨_, _, _, _, changed.commit, within.commit, within'.commit, rfl, rfl, rfl⟩⟩

/-! ### Normalizing a live record again -/

private theorem normRecord_live {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none) :
    normRecord gone processId process = { process with
      queue := Kernel.filter (fun entry => !inert gone processId process entry) process.queue
      links := Kernel.filter (fun link => !(link.2.isSome && gone link.1)) process.links
      monitors := Kernel.filter (fun monitor => !gone monitor.2) process.monitors } := by
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
          simp [first, ← keeps, ih]
      · have differ : (key == other) = false := by simp [Ne.symm equal]
        cases first : keep (other, value) <;> cases second : keep' (other, value) <;>
          simp [first, second, List.lookup_cons, differ, ih]

private theorem lookup_filter_of_keep {β : Type} {key : PID} {keep : PID × β → Bool} :
    ∀ {entries : List (PID × β)}, (∀ entry ∈ entries, entry.1 = key → keep entry = true) →
      (entries.filter keep).lookup key = entries.lookup key
  | [], _ => rfl
  | (other, value) :: rest, kept => by
      have ih := lookup_filter_of_keep (keep := keep) fun entry mem => kept entry (List.mem_cons_of_mem _ mem)
      by_cases same : other = key
      · subst same
        simp [kept (other, value) List.mem_cons_self rfl]
      · have differ : (key == other) = false := by simp [Ne.symm same]
        by_cases keeps : keep (other, value) = true
        · simp [keeps, List.lookup_cons, differ, ih]
        · simp [keeps, List.lookup_cons, differ, ih]

/-- Whether a queued signal does nothing depends on the record only through
fields normalizing keeps, and on links only of processes not gone. -/
private theorem inert_congr {gone : PID → Bool} {processId : PID} {process process' : ProcessState}
    (refCounter : process'.refCounter = process.refCounter) (monitoring : process'.monitoring = process.monitoring)
    (aliases : process'.aliases = process.aliases) (entry : Entry) :
    inert gone processId process' entry = inert gone processId process entry := by
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
      (process' := (normRecord gone processId process).eagerExit source) ?_ ?_ ?_ entry
    · rw [normRecord_live live]; rfl
    · rw [normRecord_live live]; rfl
    · rw [normRecord_live live]; rfl
  rw [same]
  rw [normRecord_live live]
  simp only [ProcessState.eagerExit, Kernel.filter_eq, List.filter_filter]
  congr 1
  · refine List.filter_congr fun entry _ => ?_
    cases inert' : inert gone processId (process.eagerExit source) entry
    · have := mt (more entry) (by simp [inert'])
      simp [this]
    · simp only [ProcessState.eagerExit, Kernel.filter_eq] at inert'
      simp [inert']
  · refine List.filter_congr fun entry _ => ?_
    cases gone entry.fst <;> cases entry.snd.isSome <;> simp
  · simp only [Bool.and_self]

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
private def ChangedAs (processId : PID) (ok : ProcessState → Prop) (change : ProcessState → ProcessState)
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
    (hidden : Hidden ok change) : Unseen (ChangedAs processId ok change) where
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
    (timers : state'.timers = state.timers) (elapsed : state'.elapsed = state.elapsed)
    (shared : state'.persistent = state.persistent) : state' = state := by
  have processes : state'.processes = state.processes :=
    Sorted.ext sorted' sorted fun processId => by
      have := records processId; simpa [State.record, Kernel.lookup_eq] using this
  exact State.ext processes timers shared elapsed

private theorem ProcessState.finished_live {process : ProcessState} (live : process.exiting = none) :
    process.finished = false := by
  simp [ProcessState.finished, live]

/-- Normalizing drops from a record, for which processes are gone, only what it
drops for whichever processes are gone. -/
private theorem normRecord_any {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none)
    (inert' : ∀ entry ∈ process.queue, inert gone processId process entry = true →
      ∀ gone', inert gone' processId process entry = true)
    (links : ∀ link ∈ process.links, (link.2.isSome && gone link.1) = false)
    (monitors : ∀ monitor ∈ process.monitors, gone monitor.2 = false) (gone' : PID → Bool) :
    normRecord gone' processId (normRecord gone processId process) = normRecord gone' processId process := by
  have kept : Kernel.filter (fun link => !(link.2.isSome && gone link.1)) process.links = process.links := by
    rw [Kernel.filter_eq]; exact List.filter_eq_self.mpr fun link mem => by simp [links link mem]
  have keptMonitors : Kernel.filter (fun monitor => !gone monitor.2) process.monitors = process.monitors := by
    rw [Kernel.filter_eq]; exact List.filter_eq_self.mpr fun monitor mem => by simp [monitors monitor mem]
  have live₁ : (normRecord gone processId process).exiting = none := by rw [normRecord_live live]; exact live
  have same : inert gone' processId (normRecord gone processId process) = inert gone' processId process := by
    funext entry
    apply inert_congr
    · rw [normRecord_live live]
    · rw [normRecord_live live]
    · rw [normRecord_live live]
  rw [normRecord_live live₁, same, normRecord_live (gone := gone) live, normRecord_live (gone := gone') live, kept,
    keptMonitors]
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
    state.Changed processId (ChangedAs processId ok change) (state.set processId (change process)).normalize := by
  have sorted' : (state.set processId (change process)).Sorted := Sorted.insertRecord sorted _ _
  have live' : (change process).exiting = none := (hidden.exiting ok').trans live
  have gone : (state.set processId (change process)).gone = state.gone := by
    funext other
    simp only [State.gone, State.alive, State.record_set]
    by_cases same : other = processId
    · subst same; simp [found, live, live']
    · simp [same]
  refine ⟨fun other differ => ?_, ?_, rfl, rfl, rfl⟩
  · rw [State.record_normalize' sorted', gone, State.record_set, ite_eq_right differ]
    conv => rhs; rw [← normalized]
    rw [State.record_normalize' sorted]
  · rw [State.record_normalize' sorted', gone, State.record_set, ite_eq_left rfl, found]
    simp only [Option.map_some, Option.filter, ProcessState.finished_live
      (show (normRecord state.gone processId (change process)).exiting = none by rw [normRecord_live live']; exact live'),
      Bool.not_false, ↓reduceIte]
    refine .some ⟨ok', live, ?_, renormalize⟩
    rw [normRecord_live live']; exact live'

/-- A change normalizing undoes leaves the normalized state as it is. -/
private theorem State.Changes.normalize_same {raw raw' : State} {processId : PID} {process : ProcessState}
    {ok : ProcessState → Prop} {change : ProcessState → ProcessState} (sorted : raw.Sorted) (sorted' : raw'.Sorted)
    (changed : raw.Changed processId (ChangedAs processId ok change) raw') (unseen : Unseen (ChangedAs processId ok change))
    (found : raw.record processId = some process)
    (nothing : normRecord raw.gone processId (change process) = normRecord raw.gone processId process) :
    raw'.normalize = raw.normalize := by
  rcases changed.records with ⟨missing, -⟩ | ⟨first, second, found', found'', -, live₀, live', same⟩
  · rw [found] at missing; cases missing
  rw [found] at found'; cases found'
  refine State.ext_records (Sorted.normalize sorted) (Sorted.normalize sorted') (fun other => ?_)
    changed.sameTimers changed.sameElapsed changed.samePersistent
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
    (changed : raw.Changed processId (ChangedAs processId ok change) raw') (unseen : Unseen (ChangedAs processId ok change))
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
    changed.sameTimers.symm changed.sameElapsed.symm changed.samePersistent.symm)
  rw [State.record_normalize' sortedSet, gone, State.record_normalize' sorted', changed.gone unseen]
  by_cases equal : other = processId
  · subst equal
    rw [State.record_set, ite_eq_left rfl, found'']
    simp only [Option.map_some, Option.filter, same, renormalize]
  · rw [State.record_set, ite_eq_right equal, changed.record_other equal]
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
    · rfl) rfl rfl rfl

private theorem State.set_set {state : State} {processId : PID} (sorted : state.Sorted)
    (first second : ProcessState) : (state.set processId first).set processId second = state.set processId second :=
  State.ext_records (Sorted.insertRecord sorted _ _) (Sorted.insertRecord (Sorted.insertRecord sorted _ _) _ _)
    (fun other => by simp only [State.record_set]; split <;> rfl) rfl rfl rfl

private theorem State.append_set {state : State} {processId : PID} (sorted : state.Sorted)
    (process : ProcessState) (message : Term) :
    (state.set processId process).append processId message =
      state.set processId { process with mailbox := Kernel.append process.mailbox [message] } := by
  unfold State.append State.modify
  rw [State.record_set, ite_eq_left rfl]
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

private theorem clean_monitors {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (clean : normRecord gone processId process = process) (live : process.exiting = none) :
    ∀ monitor ∈ process.monitors, gone monitor.2 = false := by
  rw [normRecord_live live] at clean
  have monitors := congrArg ProcessState.monitors clean
  simp only [Kernel.filter_eq, List.filter_eq_self, Bool.not_eq_eq_eq_not, Bool.not_true] at monitors
  exact monitors

/-- A change normalizing leaves as it is when it leaves the record as it is. -/
private theorem renormalize_of_clean {gone : PID → Bool} {processId : PID} {change : ProcessState → ProcessState}
    {process : ProcessState} (clean : normRecord gone processId (change process) = change process) (gone' : PID → Bool) :
    normRecord gone' processId (normRecord gone processId (change process)) = normRecord gone' processId (change process) := by
  rw [clean]

/-- Whether a signal does nothing after a change of the reference counter alone
depends on which processes are gone only when it did before. -/
private theorem inert_any {gone : PID → Bool} {processId : PID} {process process' : ProcessState} {entry : Entry}
    (clean : inert gone processId process entry = false)
    (inert' : inert gone processId process' entry = true) (gone' : PID → Bool) :
    inert gone' processId process' entry = true := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp only [inert] at clean inert' ⊢ <;> first | exact inert' | simp_all

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

/-- Records that keep a mailbox, a dictionary and a reference counter. -/
private def Keeps (process : ProcessState) (other : ProcessState) : Prop :=
  other.mailbox = process.mailbox ∧ other.pdict = process.pdict ∧ other.refCounter = process.refCounter

private theorem hidden_store (process : ProcessState) (env : Environment) :
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
        simp [same, List.lookup_cons, differ, ih]

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
    (links : (change process).links = process.links)
    (monitors : ∀ monitor ∈ (change process).monitors, gone monitor.2 = false)
    (live' : (change process).exiting = none) :
    normRecord gone processId (change process) = change process := by
  have cleaned := clean_live clean live
  have keepMonitors : Kernel.filter (fun monitor => !gone monitor.2) (change process).monitors =
      (change process).monitors := by
    rw [Kernel.filter_eq]; exact List.filter_eq_self.mpr fun monitor mem => by simp [monitors monitor mem]
  rw [normRecord_live live', keepMonitors, funext same, queue, links]
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

namespace State.Changes

variable {processId : PID} {state state' : State} {ok : List Term → Prop} {mailbox : List Term → List Term}
  {pdict : List (Term × Term) → List (Term × Term)} {refCounter : Nat → Nat} {dict : List (Term × Term)}
  {counter : Nat}

/-- The record of the process itself, read through the change. -/
private theorem modifySelf
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') (change : ProcessState → ProcessState)
    (commutes : ∀ process, OwnOk ok dict counter process → OwnOk ok dict counter (change process) ∧
      change (ownChange pdict refCounter mailbox process) = ownChange pdict refCounter mailbox (change process)) :
    (state.modify processId change).Changed processId
      (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox)) (state'.modify processId change) :=
  changed.modifyRelated fun ⟨ok', same⟩ => by
    subst same; exact ⟨(commutes _ ok').1, (commutes _ ok').2⟩

/-- What the process's own step keeps of its record is the same in both. -/
private theorem process_self
    (changed : state.Changed processId (Same (OwnOk ok dict counter) (ownChange pdict refCounter mailbox))
      state') {β : Type} (get : ProcessState → β) (keeps : ∀ process, get (ownChange pdict refCounter mailbox process) =
        get process) : get (state'.process processId) = get (state.process processId) := by
  rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, -, rfl⟩
  · simp [State.process, first, second]
  · simp [State.process, first, second, keeps]

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
  have links := changed.process_self (·.links) fun _ => rfl
  have aliases := changed.process_self (·.aliases) fun _ => rfl
  have monitoring := changed.process_self (·.monitoring) fun _ => rfl
  have eagerExits := changed.process_self (·.eagerExits) fun _ => rfl
  have trapExit := changed.process_self (·.trapExit) fun _ => rfl
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
    exact ⟨by trivial, either (changed.appendSelf own message) changed⟩
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
    exact ⟨by trivial, either changed (modified (fun process =>
      { process with links := Kernel.append process.links [(source, none)] }) (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed)⟩
  | unlink id =>
    simp only [State.handle, links]
    exact ⟨by trivial, (either (modified (fun process =>
      { process with links := Kernel.filter (·.1 != source) process.links }) (fun _ => ⟨rfl, rfl, rfl, rfl⟩) changed)
      changed).send unseen fun _ _ => by simp⟩
  | unlinkAck id =>
    simp only [State.handle, links]
    exact ⟨by trivial, either (modified (fun process =>
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

/-- States that differ only in the record of a process that ended, by a change
normalizing forgets, normalize alike. -/
private theorem normalize_ended {change : ProcessState → ProcessState}
    (changed : state.Changed processId (Same (fun process => process.exiting.isSome = true) change) state')
    (unseen : Unseen (Same (fun process => process.exiting.isSome = true) change))
    (forgets : ∀ gone process, process.exiting.isSome = true →
      normRecord gone processId (change process) = normRecord gone processId process)
    (sorted : state.Sorted) (sorted' : state'.Sorted) : state'.normalize = state.normalize := by
  refine State.ext_records (Sorted.normalize sorted) (Sorted.normalize sorted') (fun other => ?_)
    changed.sameTimers changed.sameElapsed changed.samePersistent
  rw [State.record_normalize' sorted', State.record_normalize' sorted, changed.gone unseen]
  by_cases equal : other = processId
  · subst equal
    rcases changed.records with ⟨none₁, none₂⟩ | ⟨record, record', found₁, found₂, exiting, rfl⟩
    · rw [none₁, none₂]
    · rw [found₁, found₂]
      simp only [Option.map_some, forgets _ _ exiting]
  · rw [changed.record_other equal]

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
      · exact changed.record_other equal) changed.sameTimers changed.sameElapsed changed.samePersistent
    rw [same]
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = ownChange pdict refCounter mailbox process := by
    simp [State.process, found'']
  -- After ending, the records differ only in the dictionary and reference counter.
  have endedChanged : (state.terminate processId reason).Changed processId ended
      (state'.terminate processId reason) := by
    unfold State.terminate
    simp only [processOf, processOf', changed.sameTimers]
    refine State.Changes.foldl (fun target changed' => ?_) _ ⟨fun other differ => ?_, ?_, rfl, changed.sameElapsed, changed.samePersistent⟩
    · rw [changed'.eagerLink unseen]
      split
      · refine (State.Changed.modifyRelated changed' fun {first second} related => ?_).linkExit unseen _ _ _
        obtain ⟨ok', same⟩ := related
        subst same
        refine ⟨?_, rfl⟩
        cases exiting : first.exiting <;> simp_all
      · exact changed'
    · simp only [State.record_set, differ, ↓reduceIte]
      exact changed.record_other differ
    · simp only [State.record_set, ↓reduceIte]
      exact .some ⟨rfl, rfl⟩
  refine endedChanged.normalize_ended unseen (fun _ process exiting => ?_) sorted sorted'
  obtain ⟨reason', exiting'⟩ := Option.isSome_iff_exists.mp exiting
  unfold normRecord
  simp only [ownChange, exiting']

end State.Changes

/-! ### Forced handling against the process's own step -/

/-- A change of a record's queue, mailbox and links only. -/
private def queueChange (queue : List Entry → List Entry) (mailbox : List Term → List Term)
    (links : List (PID × Option Nat) → List (PID × Option Nat)) (process : ProcessState) : ProcessState :=
  { process with queue := queue process.queue, mailbox := mailbox process.mailbox, links := links process.links }

/-- Records whose oldest queued signal is the one being handled, which, if it
acknowledges an unlink, acknowledges one the process started. -/
private def Queued (entry : Entry) (process : ProcessState) : Prop :=
  Heads entry process ∧ ∀ id, entry.signal = .unlinkAck id → id ≤ process.unlinks

/-- How handling the oldest signal changes the queue, mailbox and links, in a
way that a process's own steps commute with. -/
private structure QueueChange (queue : List Entry → List Entry) (mailbox : List Term → List Term)
    (links : List (PID × Option Nat) → List (PID × Option Nat)) : Prop where
  push : ∀ {entries} entry, entries ≠ [] → queue (Kernel.append entries [entry]) = Kernel.append (queue entries) [entry]
  filtered : ∀ (target : PID) (entries : List (PID × Option Nat)),
    links (Kernel.filter (·.1 != target) entries) = Kernel.filter (·.1 != target) (links entries)
  relink : ∀ (target : PID) (entries : List (PID × Option Nat)),
    links (Kernel.append (Kernel.filter (·.1 != target) entries) [(target, none)]) =
      Kernel.append (Kernel.filter (·.1 != target) (links entries)) [(target, none)]
  select : ∀ {β : Type} (select : Term → Option β) {messages remaining : List Term} {message : Term} {value : β},
    selectMessage select messages = some (message, value, remaining) →
      selectMessage select (mailbox messages) = some (message, value, mailbox remaining)

private theorem QueueChange.unseen {queue : List Entry → List Entry} {mailbox : List Term → List Term}
    {links : List (PID × Option Nat) → List (PID × Option Nat)} {entry : Entry} (change : QueueChange queue mailbox links)
    (linking : ∀ (rest : List Entry) (other : Entry), other.signal = .link →
      (other ∈ queue (entry :: rest) ↔ other ∈ entry :: rest)) :
    Unseen (Same (Queued entry) (queueChange queue mailbox links)) where
  outside := by
    rintro first second ⟨⟨⟨rest, queued⟩, -⟩, rfl⟩
    refine ⟨rfl, rfl, rfl, fun other link => ?_⟩
    show other ∈ queue first.queue ↔ other ∈ first.queue
    rw [queued]; exact linking rest other link
  push := fun {first second} other ⟨⟨queued, bound⟩, same⟩ => by
    subst same
    refine ⟨⟨(Heads.push queued other).1, bound⟩, ?_⟩
    obtain ⟨rest, nonempty⟩ := queued
    have pushed := change.push (entries := first.queue) other (by rw [nonempty]; simp)
    simp only [queueChange, ProcessState.push, pushed]
  eagerExit := fun source ⟨queued, same⟩ => by
    subst same
    exact ⟨queued, by simp only [queueChange, ProcessState.eagerExit, change.filtered]⟩
  unpark := fun ⟨queued, same⟩ => by subst same; exact ⟨queued, rfl⟩

namespace State.Changes

variable {processId : PID} {state state' : State} {queue : List Entry → List Entry} {mailbox : List Term → List Term}
  {links : List (PID × Option Nat) → List (PID × Option Nat)} {entry : Entry}

private theorem queue_modify
    (changed : state.Changed processId (Same (Queued entry) (queueChange queue mailbox links)) state')
    (change : ProcessState → ProcessState)
    (queued : ∀ process, (change process).queue = process.queue ∧ (change process).unlinks = process.unlinks)
    (commutes : ∀ process, Queued entry process →
      change (queueChange queue mailbox links process) = queueChange queue mailbox links (change process)) :
    (state.modify processId change).Changed processId (Same (Queued entry) (queueChange queue mailbox links))
      (state'.modify processId change) :=
  changed.modifyRelated fun ⟨ok', same⟩ => by
    subst same
    refine ⟨?_, commutes _ ok'⟩
    simp only [Queued, Heads, (queued _).1, (queued _).2]; exact ok'

/-- A process's request, after handling its oldest signal changed its queue, mailbox and links. -/
private theorem requestSelf
    (changed : state.Changed processId (Same (Queued entry) (queueChange queue mailbox links)) state')
    (unseen : Unseen (Same (Queued entry) (queueChange queue mailbox links))) (change : QueueChange queue mailbox links)
    {process : ProcessState} (found : state.record processId = some process)
    (unlinked : ∀ target : PID, Kernel.lookup target process.links = some none →
      links (Kernel.map (fun link => if link.1 == target then (link.1, some (process.unlinks + 1)) else link)
        process.links) =
        Kernel.map (fun link => if link.1 == target then (link.1, some (process.unlinks + 1)) else link)
          (links process.links))
    (lookups : ∀ target : PID,
      (Kernel.lookup target (links process.links) == some none) = (Kernel.lookup target process.links == some none))
    {β : Type} (next : Term → Result β) (query : Request) :
    Answer.Changes processId (Option.Rel (Same (Queued entry) (queueChange queue mailbox links)))
      (state.request processId next query)
      (state'.request processId next query) := by
  rcases changed.records with ⟨missing, -⟩ | ⟨first, second, found', found'', queued, rfl⟩
  · rw [found] at missing; cases missing
  rw [found] at found'; cases found'
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = queueChange queue mailbox links process := by
    simp [State.process, found'']
  have allocated : (state'.allocate processId).1 = (state.allocate processId).1 ∧
      (state.allocate processId).2.Changed processId (Same (Queued entry) (queueChange queue mailbox links))
        (state'.allocate processId).2 := by
    refine ⟨by simp only [State.allocate, processOf, processOf']; rfl, ?_⟩
    exact changed.queue_modify _ (fun _ => ⟨rfl, rfl⟩) (fun _ _ => rfl)
  cases query with
  | monitor target alias =>
    simp only [State.request]
    obtain ⟨same, allocated⟩ := allocated
    rw [same]
    split
    · exact ⟨rfl, allocated⟩
    · exact ⟨rfl, (allocated.unpark unseen processId).queue_modify _ (fun _ => ⟨rfl, rfl⟩) (fun _ _ => rfl)⟩
  | demonitor reference flush =>
    simp only [State.request, processOf, processOf', queueChange]
    split <;> exact ⟨rfl, changed.queue_modify _ (fun _ => ⟨rfl, rfl⟩) (fun _ _ => rfl)⟩
  | link target =>
    simp only [State.request, processOf, processOf', changed.alive unseen, queueChange]
    by_cases self : target = processId
    · simp only [self, ↓reduceIte]; exact ⟨rfl, changed⟩
    simp only [self, ↓reduceIte]
    by_cases gone : (!state.alive target && !process.trapExit) = true
    · simp only [gone, ↓reduceIte]; exact ⟨rfl, changed⟩
    simp only [gone, ↓reduceIte, Bool.false_eq_true]
    have relinked := changed.queue_modify (fun process => { process with
        links := Kernel.append (Kernel.filter (·.1 != target) process.links) [(target, none)] }) (fun _ => ⟨rfl, rfl⟩)
      fun _ _ => by simp only [queueChange, change.relink]
    have lookups := lookups target
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
    have lookups := lookups target
    have unlinking := unlinked target
    generalize Kernel.lookup target process.links = found₁ at lookups unlinking ⊢
    generalize Kernel.lookup target (links process.links) = found₂ at lookups ⊢
    rcases found₁ with _ | _ | id <;> rcases found₂ with _ | _ | id' <;> simp at lookups <;>
      first
        | exact ⟨rfl, changed⟩
        | (rw [State.modify_found found, State.modify_found found'']
           refine ⟨rfl, State.Changed.send ?_ unseen fun _ _ _ _ _ ⟨queued', same⟩ => ?_⟩
           · exact changed.setRelated ⟨⟨queued.1, fun id signal => Nat.le_succ_of_le (queued.2 id signal)⟩,
               by simp only [queueChange, unlinking rfl]⟩
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
    · exact ⟨rfl, changed.queue_modify _ (fun _ => ⟨rfl, rfl⟩) (fun _ _ => rfl)⟩
  | alive target =>
    simp only [State.request, changed.alive unseen]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed.enqueue unseen fun _ _ => by simp⟩
    · exact ⟨rfl, changed.enqueue unseen fun _ _ => by simp⟩
  | processInfo target =>
    simp only [State.request, changed.alive unseen]
    split
    · exact ⟨rfl, changed⟩
    split
    · exact ⟨rfl, changed.enqueue unseen fun _ _ => by simp⟩
    · exact ⟨rfl, changed⟩
  | sendAlias alias message =>
    exact ⟨rfl, changed.send unseen fun _ _ => by simp⟩
  | startTimer destination message duration =>
    simp only [State.request]
    obtain ⟨same, allocated⟩ := allocated
    rw [same, allocated.alive unseen]
    refine ⟨rfl, ?_⟩
    split
    · rw [allocated.sameTimers]; exact allocated.timers _
    · exact allocated
  | cancelTimer reference =>
    simp only [State.request, changed.sameTimers, processOf, processOf', queueChange]
    split
    · exact ⟨by rw [changed.sameElapsed], (changed.timers _).queue_modify _ (fun _ => ⟨rfl, rfl⟩) (fun _ _ => rfl)⟩
    · exact ⟨rfl, changed⟩
  | persistentGet key =>
    simp only [State.request, changed.persistent]
    exact ⟨rfl, changed⟩
  | persistentPut | persistentErase | persistentAwait =>
    simp only [State.request, State.stage, changed.persistent, changed.staged_eq]
    repeat' split
    all_goals first | trivial | exact ⟨rfl, changed⟩ | exact ⟨rfl, changed.stage _⟩

/-- A process spawns a child, after handling its oldest signal changed its queue, mailbox and links. -/
private theorem spawnSelf
    (changed : state.Changed processId (Same (Queued entry) (queueChange queue mailbox links)) state')
    (change : QueueChange queue mailbox links) {process : ProcessState}
    (found : state.record processId = some process) (options : SpawnOptions)
    (fresh : Kernel.append processId [process.children + 1] ≠ processId) :
    (state'.spawnWith processId options).1 = (state.spawnWith processId options).1 ∧
      (state.spawnWith processId options).2.Changed processId (Same (Queued entry) (queueChange queue mailbox links))
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
      (fun _ => ⟨rfl, rfl⟩) (fun _ _ => by simp only [queueChange, change.relink])).modify fresh
    fun child => { child with links := [(processId, none)] }
  have counter : ∀ {first second : State}, first.Changed processId (Same (Queued entry) (queueChange queue mailbox links))
      second → (second.process processId).refCounter = (first.process processId).refCounter :=
    fun {first second} changed' => by
      rcases changed'.records with ⟨one, two⟩ | ⟨a, b, one, two, -, rfl⟩
      · simp [State.process, one, two]
      · simp [State.process, one, two, queueChange]
  by_cases monitor : options.monitor <;> by_cases link : options.link <;>
    simp only [monitor, link, ↓reduceIte, Bool.false_eq_true, State.allocate]
  · simp only [State.process, State.record_modify, State.record_set, ↓reduceIte, Ne.symm fresh, Option.map_some,
      Option.getD_some, queueChange]
    refine ((linked.queue_modify _ ?_ ?_).queue_modify _ ?_ ?_).modify fresh _ <;> intros <;> first | rfl | exact ⟨rfl, rfl⟩
  · simp only [State.process, State.record_set, ↓reduceIte, Ne.symm fresh, 
      Option.getD_some, queueChange]
    refine ((started.queue_modify _ ?_ ?_).queue_modify _ ?_ ?_).modify fresh _ <;> intros <;> first | rfl | exact ⟨rfl, rfl⟩
  · exact linked
  · exact started

/-- The process ends, after handling its oldest signal changed its queue,
mailbox and links in a way ending forgets. -/
private theorem terminateQueue
    (changed : state.Changed processId (Same (Queued entry) (queueChange queue mailbox links)) state')
    (change : QueueChange queue mailbox links)
    (requests : ∀ (rest : List Entry) (keep : Entry → Bool),
      (∀ entry, keep entry = true → (entry.signal matches .link | .monitor _ | .isAlive) = true) →
      Kernel.filter keep (queue (entry :: rest)) = Kernel.filter keep (entry :: rest))
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
      · exact changed.record_other equal) changed.sameTimers changed.sameElapsed changed.samePersistent
    rw [same]
  have processOf : state.process processId = process := by simp [State.process, found]
  have processOf' : state'.process processId = queueChange queue mailbox links process := by
    simp [State.process, found'']
  have endedChanged : (state.terminate processId reason).Changed processId ended
      (state'.terminate processId reason) := by
    unfold State.terminate
    simp only [processOf, processOf', changed.sameTimers, queueChange, exitLinks]
    obtain ⟨⟨rest, queued⟩, -⟩ := queued
    rw [queued, requests _ _ fun entry kept => by
      obtain ⟨_, signal⟩ := entry; cases signal <;> simp_all]
    refine State.Changes.foldl (fun target changed' => ?_) _ ⟨fun other differ => ?_, ?_, rfl, changed.sameElapsed, changed.samePersistent⟩
    · rw [changed'.eagerLink unseen]
      split
      · refine (State.Changed.modifyRelated changed' fun {first second} related => ?_).linkExit unseen _ _ _
        obtain ⟨ok', same⟩ := related
        subst same
        refine ⟨?_, rfl⟩
        cases exiting : first.exiting <;> simp_all
      · exact changed'
    · simp only [State.record_set, differ, ↓reduceIte]
      exact changed.record_other differ
    · simp only [State.record_set, ↓reduceIte]
      exact .some ⟨rfl, rfl⟩
  refine endedChanged.normalize_ended unseen (fun _ process exiting => ?_) sorted sorted'
  obtain ⟨reason', exiting'⟩ := Option.isSome_iff_exists.mp exiting
  unfold normRecord
  simp only [queueChange, exiting']
  rfl

/-- A process's own step, after handling its oldest signal changed its queue,
mailbox and links: the same transition, with related states unless it ends the process. -/
private theorem ownSelf
    (changed : state.Changed processId (Same (Queued entry) (queueChange queue mailbox links)) state')
    (unseen : Unseen (Same (Queued entry) (queueChange queue mailbox links))) (change : QueueChange queue mailbox links)
    {process : ProcessState} (found : state.record processId = some process)
    (unlinked : ∀ target : PID, Kernel.lookup target process.links = some none →
      links (Kernel.map (fun link => if link.1 == target then (link.1, some (process.unlinks + 1)) else link)
        process.links) =
        Kernel.map (fun link => if link.1 == target then (link.1, some (process.unlinks + 1)) else link)
          (links process.links))
    (lookups : ∀ target : PID,
      (Kernel.lookup target (links process.links) == some none) = (Kernel.lookup target process.links == some none))
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
      ((transition.state.Changed processId (Same (Queued entry) (queueChange queue mailbox links)) transition'.state ∧
          ∃ task₁ more, transition.tasks = (processId, task₁) :: more) ∨
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
      none false, by simp [Task.own, view], rfl, rfl, rfl, rfl, .inl ⟨changed, _, _, rfl⟩⟩
  | set updated next =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    exact ⟨Transition.mk (.internal processId) (state'.store processId updated) [(processId, ⟨next, finish, none⟩)]
      none false, rfl, rfl, rfl, rfl, rfl, .inl ⟨changed.queue_modify _ (fun _ => ⟨rfl, rfl⟩) (fun _ _ => rfl), _, _, rfl⟩⟩
  | schedule options child next =>
    have spawned := changed.spawnSelf change found options fresh
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    refine ⟨Transition.mk (.spawn processId (state.spawnWith processId options).1) (state'.spawnWith processId options).2
      [(processId, ⟨next (state.spawnWith processId options).1, finish, none⟩),
        ((state.spawnWith processId options).1, Task.child child)] none false,
      by simp only [Task.own, List.head?_cons, spawned.1], rfl, rfl, rfl, rfl, .inl ⟨spawned.2, _, _, rfl⟩⟩
  | send destination message next =>
    simp only [Task.own, List.head?_cons, Option.some.injEq] at head; subst head
    exact ⟨Transition.mk (.send processId destination message)
      (state'.send processId destination (.message message)) [(processId, ⟨next, finish, none⟩)] none false,
      rfl, rfl, rfl, rfl, rfl, .inl ⟨changed.send unseen fun _ _ => by simp, _, _, rfl⟩⟩
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
        [(processId, ⟨next (some value), finish, none⟩)] none false, ?_, rfl, rfl, rfl, rfl, .inl ⟨?_, _, _, rfl⟩⟩
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
          simp only [quiet, Bool.false_eq_true, ↓reduceIte, List.head?_cons, Option.some.injEq] at head
          subst head
          have quiet' : Kernel.any (queue process.queue) (state'.awaitedEntry processId) = false := by
            cases more : Kernel.any (queue process.queue) (state'.awaitedEntry processId)
            · rfl
            · rw [awaited more] at quiet; cases quiet
          refine ⟨Transition.mk (.timeout processId) state' [(processId, ⟨next none, finish, none⟩)] none false,
            ?_, rfl, rfl, rfl, rfl, .inl ⟨changed, _, _, rfl⟩⟩
          have quietE' : ¬∃ entry, entry ∈ queue process.queue ∧ state'.awaitedEntry processId entry = true := by
            simpa [Kernel.any_eq, List.any_eq_true] using quiet'
          simp [queueChange, noMatch _ selected quiet, quietE']
  | request query next =>
    have answered := changed.requestSelf unseen change found unlinked lookups next query
    simp only [Task.own] at head ⊢
    revert answered head
    generalize state.request processId next query = answer
    generalize state'.request processId next query = answer'
    intro head answered
    cases answer <;> cases answer' <;> unfold Answer.Changes at answered
    all_goals first
      | exact answered.elim
      | (obtain ⟨rfl, answered⟩ := answered
         simp only [List.head?_cons, Option.some.injEq] at head
         subst head
         exact ⟨_, rfl, rfl, rfl, rfl, rfl, .inl ⟨answered, _, _, rfl⟩⟩)
      | simp at head

end State.Changes

/-! ### Which tagged steps are forced -/

/-- Whether an event is reading or replacing the environment, receiving, or
resuming after a persistent term update. -/
private def Event.local : Event → Bool
  | .internal _ | .receive .. | .request _ .persistentAwait (some _) => true
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
  rcases mem with ((((⟨⟨before, ⟨other, task'⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -⟩) | ⟨update, -, key, -⟩)
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
  rcases mem with ((((⟨⟨before, ⟨other, task'⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -⟩) | ⟨update, -, key, -⟩)
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
  · cases key

private theorem Config.forced_phase {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {event : Event} {next : Config α} {forced : Bool}
    (mem : (Key.phase processId, event, next, forced) ∈ (Config.running state tasks finished false).taggedSteps) :
    forced = state.dropsDown processId := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at mem
  rcases mem with ((((⟨⟨before, ⟨other, task'⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -⟩) | ⟨update, -, key, -⟩)
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
  · cases key

/-! ### Forced changes against steps of other keys -/

/-! ### Only its process stages a persistent term update -/

/-- Close a goal that an effect leaves the persistent terms as they are. -/
local syntax "unshared" : tactic
macro_rules
  | `(tactic| unshared) => `(tactic| first
      | exact Effect.Unshared.empty | exact Effect.Unshared.modify _ _ | exact Effect.Unshared.put _ _
      | exact Effect.Unshared.retime _ | exact State.sendEffect_unshared _ _ _ _
      | exact State.enqueueEffect_unshared _ _ _ _ | exact State.unparkEffect_unshared _ _
      | exact State.terminateEffect_unshared _ _ _ | rfl
      | (refine Effect.Unshared.andThen ?_ ?_ <;> unshared)
      | (split <;> unshared))

private theorem State.spawnEffect_unshared (state : State) (processId : PID) (options : SpawnOptions) :
    (state.spawnEffect processId options).Unshared := by
  unfold State.spawnEffect; dsimp only; unshared

private theorem State.exitSignalEffect_unshared (state : State) (target source : PID) (reason : Term)
    (linked normalKills : Bool) : (state.exitSignalEffect target source reason linked normalKills).Unshared := by
  unfold State.exitSignalEffect; dsimp only; unshared

private theorem State.handleEffect_unshared (state : State) (processId : PID) (entry : Entry) :
    (state.handleEffect processId entry).Unshared := by
  unfold State.handleEffect; dsimp only
  split
  case _ => unshared
  all_goals first | exact State.exitSignalEffect_unshared _ _ _ _ _ _ | unshared

private theorem Task.handleEffect_unshared (state : State) (processId : PID) (task : Task α) :
    (task.handleEffect state processId).Unshared := by
  unfold Task.handleEffect; dsimp only
  split
  · exact Effect.Unshared.empty
  · split
    · exact ((Effect.Unshared.modify _ _).andThen (State.handleEffect_unshared _ _ _)).andThen
        (State.terminateEffect_unshared _ _ _)
    · exact (Effect.Unshared.modify _ _).andThen (State.handleEffect_unshared _ _ _)

private theorem State.phaseEffect_unshared (state : State) (processId : PID) : (state.phaseEffect processId).Unshared := by
  simp only [State.phaseEffect]
  split
  · split
    · exact (Effect.Unshared.modify _ _).andThen (State.sendEffect_unshared _ _ _ _)
    · split
      · rename_i entry rest _
        refine (Effect.Unshared.modify _ _).andThen ?_
        obtain ⟨source, signal⟩ := entry
        cases signal <;> simp only [State.answerEffect] <;>
          first | exact State.sendEffect_unshared _ _ _ _ | exact Effect.Unshared.empty
      · exact Effect.Unshared.empty
  · exact Effect.Unshared.empty

private theorem State.normalize_persistent (state : State) : state.normalize.persistent = state.persistent := rfl

private theorem State.set_persistent (state : State) (processId : PID) (process : ProcessState) :
    (state.set processId process).persistent = state.persistent := rfl

private theorem State.linkExit_persistent (state : State) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).persistent = state.persistent := by
  have linked := (Realizes.linkExit state processId target reason).persistent
  have unshared : (state.linkExitEffect processId target reason).Unshared := by
    unfold State.linkExitEffect; unshared
  rw [unshared.getD] at linked
  exact linked

/-- A request leaves the persistent terms as they are, unless it stages an
update of its own. -/
private theorem State.requestEffect_staged (state : State) (processId : PID) (query : Request) :
    (state.requestEffect processId query).Unshared ∨
      ∃ key value, state.requestEffect processId query = stageEffect processId key value := by
  cases query
  case persistentPut | persistentErase =>
    simp only [State.requestEffect]
    repeat' split
    all_goals first | exact .inl Effect.Unshared.empty | exact .inr ⟨_, _, rfl⟩
  case monitor =>
    refine .inl ?_
    simp only [State.requestEffect, State.allocate]
    exact (Effect.Unshared.modify _ _).andThen (Effect.Unshared.ite _ Effect.Unshared.empty
      ((State.unparkEffect_unshared _ _).andThen (Effect.Unshared.modify _ _)))
  case startTimer =>
    refine .inl ?_
    simp only [State.requestEffect, State.allocate]
    exact (Effect.Unshared.modify _ _).andThen (Effect.Unshared.ite _ (Effect.Unshared.retime _) Effect.Unshared.empty)
  all_goals (refine .inl ?_; simp only [State.requestEffect]; unshared)

/-- A process's own step leaves the persistent terms as they are, unless it
stages an update of its own. -/
private theorem Task.ownEffect_staged (state : State) (processId : PID) (task : Task α) :
    (task.ownEffect state processId).Unshared ∨
      ∃ key value, task.ownEffect state processId = stageEffect processId key value := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => exact .inl Effect.Unshared.empty
  | none =>
  cases computation with
  | request query next => exact State.requestEffect_staged state processId query
  | error exception => cases exception <;> exact .inl (by first | rfl | exact State.terminateEffect_unshared _ _ _)
  | schedule => exact .inl (State.spawnEffect_unshared _ _ _)
  | _ => exact .inl (by simp only [Task.ownEffect]; unshared)

/-- An effect leaving the persistent terms as they are, or staging an update
of another process, stages no update the process owns that was not staged. -/
private theorem staged_of_effect {effect : Effect} {before after : State} {processId other : PID}
    (realizes : Realizes effect before after)
    (effects : effect.Unshared ∨ ∃ key value, effect = stageEffect other key value) (differ : other ≠ processId)
    {update : Update} (staged : after.normalize.persistent.staged = some update) (owned : update.owner = processId) :
    before.persistent.staged = some update := by
  have staged : after.persistent.staged = some update := staged
  have persistent := realizes.persistent
  rcases effects with unshared | ⟨key, value, rfl⟩
  · rw [unshared.getD] at persistent; rw [persistent] at staged; exact staged
  · rw [persistent] at staged
    simp only [stageEffect, Effect.reshare, Option.getD_some, Option.some.injEq] at staged
    subst staged; exact absurd owned differ

/-- No step but a process's own stages a persistent term update that the
process owns: other processes stage their own, and every other step stages none. -/
private theorem Config.stepOf_staged {state raw : State} {tasks tasks₁ : List (PID × Task α)}
    {finished finished₁ : Option (Except Exception α)} {key : Key} {event : Event} {processId : PID}
    (notOwn : key ≠ .own processId)
    (step : (Config.running state tasks finished false).stepOf key = some (event, .running raw tasks₁ finished₁ false))
    {update : Update} (staged : raw.persistent.staged = some update) (owned : update.owner = processId) :
    state.persistent.staged = some update := by
  cases key with
  | own other =>
    have differ : other ≠ processId := fun same => notOwn (by rw [same])
    obtain ⟨task, transition, -, head, next⟩ := Config.stepOf_own step
    split at next
    · simp only [Config.running.injEq] at next
      obtain ⟨rfl, -⟩ := next
      simp at staged
    · simp only [Config.running.injEq] at next
      obtain ⟨rfl, -⟩ := next
      exact staged_of_effect (Realizes.own (List.mem_of_head? head)) (Task.ownEffect_staged _ _ _) differ staged owned
  | handle other =>
    obtain ⟨task, transition, -, head, next⟩ := Config.stepOf_handle step
    rw [Task.handle_not_exhausted (List.mem_of_head? head)] at next
    simp only [Bool.false_eq_true, ↓reduceIte, Config.running.injEq] at next
    obtain ⟨rfl, -⟩ := next
    exact staged_of_effect (other := processId ++ [0]) (Realizes.handleStep (List.mem_of_head? head))
      (.inl (Task.handleEffect_unshared _ _ _)) (by simp) staged owned
  | link other target =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨next, phase, -, rfl, -⟩ := step
    unfold State.linkPhase at phase
    repeat' split at phase
    all_goals simp only [Option.some.injEq, reduceCtorEq] at phase
    subst phase
    simpa only [State.normalize_persistent, State.linkExit_persistent, State.set_persistent] using staged
  | phase other =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨next, phase, -, rfl, -⟩ := step
    exact staged_of_effect (other := processId ++ [0]) (Realizes.phase phase) (.inl (State.phaseEffect_unshared _ _))
      (by simp) staged owned
  | unpark other =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨-, -, -, rfl, -⟩ := step
    exact staged_of_effect (other := processId ++ [0]) (Realizes.unpark _ _) (.inl (State.unparkEffect_unshared _ _))
      (by simp) staged owned
  | fire reference =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨timer, -, -, rfl, -⟩ := step
    exact staged_of_effect (other := processId ++ [0]) (Realizes.fire _ _)
      (.inl ((Effect.Unshared.retime _).andThen (State.enqueueEffect_unshared _ _ _ _))) (by simp) staged owned
  | commit =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨committed, found, -, rfl, -⟩ := step
    simp [State.normalize, State.commit, found] at staged

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
      -- No update the process owns is staged but those staged before.
      (∀ update, raw.normalize.persistent.staged = some update → update.owner = processId →
        state.persistent.staged = some update) →
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
      rfl, rfl⟩⟩ := Config.step_changed (task' := task') within within' changed hidden.unseen.opt
      (fun found differ => fresh.child found lookup) (fun {target} same => by
        rcases same with rfl | rfl <;>
          simp [Config.stepOf, State.phase, State.linkPhase, found, live] at step') owner step'
  · subst same
    exact .inl ⟨event', stepped⟩
  · have reachableMiddle := reachable₀.step (Config.step_of_stepOf step')
    rcases changedRaw.records with ⟨missing, -⟩ | ⟨process₁, process₂, found₁, -, ok₁, live₁, -, -⟩
    · exfalso
      have alive := reachableMiddle.2.2.1 _ (mem_of_lookup (lookupAfter ▸ lookup))
      rw [State.alive_normalize withinRaw.1] at alive
      simp [State.alive, missing] at alive
    rcases atMiddle raw tasks₁ finished₁ process₁ withinRaw reachableMiddle (lookupAfter ▸ lookup) found₁ ok₁ live₁
        (fun _ staged owned => Config.stepOf_staged (fun same => owner (by rw [same]; rfl)) step' staged owned) with
      ⟨event'', mem, liveChanged, renormalized⟩ | ⟨rfl, nothing⟩
    · rw [State.forced_close withinRaw.1 withinRaw'.1 changedRaw hidden.unseen found₁ liveChanged renormalized] at mem
      exact .inr ⟨key, event'', _, event', mem, stepped⟩
    · left
      refine ⟨event', ?_⟩
      rw [stepped, rewriteTask_same (lookupAfter ▸ lookup), State.Changes.normalize_same withinRaw.1 withinRaw'.1 changedRaw
        hidden.unseen found₁ nothing]

private theorem Config.tagged_own_forced {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.own state processId).head? = some transition)
    (isLocal : transition.event.local = true)
    (counter : (transition.state.process processId).refCounter = (state.process processId).refCounter) :
    (Key.own processId, transition.event, if transition.exhausted then
        Config.running { elapsed := transition.state.elapsed } [] none true
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
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running forced
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
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ keeps₁ live₁ _
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
      (hidden_store process updated) (normRecord_any live (fun entry mem inert' gone' =>
        inert_any (process := process) (process' := storeChange updated process) (cleaned.1 entry mem)
          inert' gone') cleaned.2 fun monitor mem => clean_monitors clean live monitor mem) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ keeps₁ live₁ _
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
      intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ keeps₁ live₁ _
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
    cases query
    case persistentAwait =>
      -- Resuming once the process's update is visible: no other step stages one it owns again.
      have enabled : ∀ update, state.persistent.staged = some update → update.owner ≠ processId := by
        intro update staged same
        subst same
        simp [Task.own, State.request, staged] at head
      have reply : ∀ raw : State, (∀ update, raw.persistent.staged = some update → update.owner ≠ processId) →
          raw.request processId next₀ .persistentAwait = .reply (.atom "ok") raw := by
        intro raw free
        simp only [State.request]
        split
        · rename_i update staged
          have differ : (update.owner == processId) = false := by simpa using free update staged
          simp [differ]
        · rfl
      simp only [Task.own, reply state enabled, List.head?_cons, Option.some.injEq] at head; subst head
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
      rw [show state.normalize = (state.set processId (id process)).normalize by rw [id, State.set_self sorted found]]
      refine Config.forced_other (key := .own processId) reachable lookup found live ⟨rfl, rfl, rfl⟩
        (hidden_keeps process) (renormalize_of_clean (change := id) clean) owner step' ?_
      intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ keeps₁ live₁ kept
      obtain ⟨record, -, -, -⟩ := later within found₁ live₁ keeps₁
      have free : ∀ update, raw.normalize.persistent.staged = some update → update.owner ≠ processId :=
        fun update staged same => enabled update (kept update staged same) same
      have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
        (transition := Transition.mk (.request processId .persistentAwait (some (.atom "ok"))) raw.normalize
          [(processId, ⟨next₀ (.atom "ok"), finish, none⟩)] none false)
        (by simp only [Task.own, reply raw.normalize free, List.head?_cons]) rfl rfl
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
      rw [show raw.normalize.normalize =
          (raw.normalize.set processId (id (normRecord raw.gone processId process₁))).normalize
        by rw [id, State.set_self (Sorted.normalize within.1) record]] at tagged
      exact .inl ⟨_, tagged, by rw [id, normRecord_live live₁]; exact live₁,
        normRecord_normRecord (fun _ gone => gone) _ _⟩
    all_goals
      simp only [Task.own] at head
      split at head <;> simp only [List.head?_cons, List.head?_nil, Option.some.injEq, reduceCtorEq] at head <;>
        subst head <;> simp [Event.local] at isLocal

private theorem Config.tagged_handle_forced {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {transition : Transition α}
    {entry : Entry} {rest : List Entry} (pairwise : tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1)
    (lookup : Kernel.lookup processId tasks = some task) (queue : (state.process processId).queue = entry :: rest)
    (head : (task.handle state processId).head? = some transition) (flag : task.forcedHead state processId entry = true) :
    (Key.handle processId, transition.event, if transition.exhausted then
        Config.running { elapsed := transition.state.elapsed } [] none true
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
    {entry : Entry} {rest : List Entry} (found : state.record processId = some process)
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
    rw [State.modify_found (by rw [State.record_set, ite_eq_left rfl]), State.set_set sorted]
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
    simp [ackChange, popChange, linked', queue]

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
  have keepMonitors : Kernel.filter (fun monitor => !gone monitor.2) process.monitors = process.monitors := by
    rw [Kernel.filter_eq]
    exact List.filter_eq_self.mpr fun monitor mem => by simp [clean_monitors clean live monitor mem]
  unfold ackChange ackedChange popChange
  split
  · rw [keepLinks _ fun link mem => by
        simp only [Kernel.filter_eq, List.mem_filter] at mem; exact mem.1]
    simp only [keepQueue, keepMonitors]
  · simp only [keepQueue, keepMonitors, keepLinks _ fun _ mem => mem]

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
  have twice : Kernel.filter (fun monitor : List Nat × PID => !gone monitor.2)
      (Kernel.filter (fun monitor => !gone monitor.2) process.monitors) =
      Kernel.filter (fun monitor => !gone monitor.2) process.monitors := by
    simp only [Kernel.filter_eq, List.filter_filter, Bool.and_self]
  unfold ackChange ackedChange popChange
  rw [normRecord_live live]
  split <;> split <;> (simp only [twice]; try rfl)

/-- Handling the oldest signal, a message to an alias: delivered while the alias is active. -/
private def aliasChange (alias : List Nat) (message : Term) (process : ProcessState) : ProcessState :=
  if Kernel.contains process.aliases alias then messageChange message process else popChange process

private theorem Task.handle_alias {state : State} {processId : PID} {task : Task α} {process : ProcessState}
    {source : PID} {alias : List Nat} {message : Term} {rest : List Entry} (sorted : state.Sorted)
    (found : state.record processId = some process)
    (queue : process.queue = ⟨source, .aliasMessage alias message⟩ :: rest) :
    task.handle state processId = [Transition.mk (.handle processId ⟨source, .aliasMessage alias message⟩)
      (state.set processId (aliasChange alias message process)) [(processId, task)] none false] := by
  have processOf : state.process processId = process := by simp [State.process, found]
  simp only [Task.handle, processOf, queue, State.handle]
  simp only [State.process, State.record_set, ↓reduceIte, Option.getD_some, aliasChange]
  split
  · simp only [State.append_set sorted]
    simp [messageChange, queue]
  · simp [popChange, queue]

private theorem normRecord_alias {gone : PID → Bool} {processId : PID} {process : ProcessState} {entry : Entry}
    (live : process.exiting = none) (heads : Heads entry process) (kept : inert gone processId process entry = false)
    (alias : List Nat) (message : Term) :
    normRecord gone processId (aliasChange alias message (normRecord gone processId process)) =
      normRecord gone processId (aliasChange alias message process) := by
  have aliases : (normRecord gone processId process).aliases = process.aliases := by rw [normRecord_live live]
  unfold aliasChange
  rw [aliases]
  split
  · exact normRecord_message live heads kept message
  · exact normRecord_pop live heads kept

private theorem hidden_alias {entry : Entry} (notLink : entry.signal ≠ .link) (alias : List Nat) (message : Term) :
    Hidden (Heads entry) (aliasChange alias message) where
  exiting _ := by unfold aliasChange; split <;> rfl
  trapExit _ := by unfold aliasChange; split <;> rfl
  parked _ := by unfold aliasChange; split <;> rfl
  links heads other link := by
    unfold aliasChange; split
    · exact (hidden_message notLink message).links heads other link
    · exact (hidden_pop notLink).links heads other link
  push {process} other heads := by
    obtain ⟨heads', pushed⟩ := (hidden_message notLink message).push other heads
    obtain ⟨-, popped⟩ := (hidden_pop notLink).push other heads
    refine ⟨heads', ?_⟩
    have same : (process.push other).aliases = process.aliases := rfl
    unfold aliasChange
    rw [same]
    split
    · exact pushed
    · exact popped
  eagerExit {process} source heads := by
    have same : (process.eagerExit source).aliases = process.aliases := rfl
    refine ⟨heads, ?_⟩
    unfold aliasChange
    rw [same]
    split <;> rfl
  unpark {process} heads := by
    have same : ({ process with parked := none } : ProcessState).aliases = process.aliases := rfl
    refine ⟨heads, ?_⟩
    unfold aliasChange
    rw [same]
    split <;> rfl

/-- Handling the oldest signal, a monitor: the process records its watcher. -/
private def monitorChange (reference : List Nat) (source : PID) (process : ProcessState) : ProcessState :=
  { process with queue := process.queue.tail, monitors := Kernel.append process.monitors [(reference, source)] }

private theorem Task.handle_monitor {state : State} {processId : PID} {task : Task α} {process : ProcessState}
    {source : PID} {reference : List Nat} {rest : List Entry} (sorted : state.Sorted)
    (found : state.record processId = some process)
    (queue : process.queue = ⟨source, .monitor reference⟩ :: rest) :
    task.handle state processId = [Transition.mk (.handle processId ⟨source, .monitor reference⟩)
      (state.set processId (monitorChange reference source process)) [(processId, task)] none false] := by
  have processOf : state.process processId = process := by simp [State.process, found]
  simp only [Task.handle, processOf, queue, State.handle]
  rw [State.modify_found (process := { process with queue := rest }) (by simp [State.record_set]),
    State.set_set sorted]
  simp [monitorChange, queue]

private theorem hidden_monitor {entry : Entry} (notLink : entry.signal ≠ .link) (reference : List Nat) (source : PID) :
    Hidden (Heads entry) (monitorChange reference source) where
  exiting _ := rfl
  trapExit _ := rfl
  parked _ := rfl
  links heads other link := (hidden_pop notLink).links heads other link
  push other heads := by
    obtain ⟨heads', tail⟩ := heads.push other
    exact ⟨heads', by simp only [monitorChange, tail]; rfl⟩
  eagerExit _ heads := ⟨heads, rfl⟩
  unpark heads := ⟨heads, rfl⟩

private theorem normRecord_monitor {gone : PID → Bool} {processId : PID} {process : ProcessState} {entry : Entry}
    (live : process.exiting = none) (heads : Heads entry process) (kept : inert gone processId process entry = false)
    (reference : List Nat) (source : PID) :
    normRecord gone processId (monitorChange reference source (normRecord gone processId process)) =
      normRecord gone processId (monitorChange reference source process) := by
  obtain ⟨rest, queue⟩ := heads
  have live₁ : (monitorChange reference source (normRecord gone processId process)).exiting = none := by
    rw [normRecord_live live]; exact live
  rw [normRecord_live live₁, normRecord_live (show (monitorChange reference source process).exiting = none from live)]
  have same : ∀ other : ProcessState,
      inert gone processId (monitorChange reference source other) = inert gone processId other := fun _ => rfl
  rw [same, same, funext (inert_normRecord (gone := gone) (processId := processId) live), normRecord_live live]
  simp [monitorChange, queue, kept, Kernel.filter_eq, Kernel.append_eq, List.filter_filter, List.filter_append]

/-- A monitor from a process that is gone does nothing, and neither does handling it. -/
private theorem normRecord_monitor_gone {gone : PID → Bool} {processId source : PID} {process : ProcessState}
    {reference : List Nat} (live : process.exiting = none) (heads : Heads ⟨source, .monitor reference⟩ process)
    (goneSource : gone source = true) :
    normRecord gone processId (monitorChange reference source process) = normRecord gone processId process := by
  obtain ⟨rest, queue⟩ := heads
  rw [normRecord_live (show (monitorChange reference source process).exiting = none from live), normRecord_live live]
  have same : inert gone processId (monitorChange reference source process) = inert gone processId process := rfl
  have inert' : inert gone processId process ⟨source, .monitor reference⟩ = true := by simp [inert, goneSource]
  rw [same]
  simp [monitorChange, queue, inert', goneSource, Kernel.filter_eq, Kernel.append_eq, List.filter_append]

/-- Records whose process sees the same environment and mailbox as `base`, and
holds the same monitors and aliases. -/
private def Viewed (base process : ProcessState) : Prop :=
  process.mailbox = base.mailbox ∧ process.pdict = base.pdict ∧ process.refCounter = base.refCounter ∧
    process.monitoring = base.monitoring ∧ process.aliases = base.aliases

/-- What other processes change in a record keeps what its process sees. -/
private theorem Hidden.viewed {ok : ProcessState → Prop} {change : ProcessState → ProcessState}
    (hidden : Hidden ok change) (base : ProcessState) :
    Hidden (fun process => ok process ∧ Viewed base process) change where
  exiting ok' := hidden.exiting ok'.1
  trapExit ok' := hidden.trapExit ok'.1
  parked ok' := hidden.parked ok'.1
  links ok' := hidden.links ok'.1
  push entry ok' := by
    obtain ⟨ok'', pushed⟩ := hidden.push entry ok'.1
    exact ⟨⟨ok'', ok'.2⟩, pushed⟩
  eagerExit source ok' := by
    obtain ⟨ok'', exited⟩ := hidden.eagerExit source ok'.1
    exact ⟨⟨ok'', ok'.2⟩, exited⟩
  unpark ok' := by
    obtain ⟨ok'', unparked⟩ := hidden.unpark ok'.1
    exact ⟨⟨ok'', ok'.2⟩, unparked⟩

/-- A live record keeps what its process sees through normalizing. -/
private theorem Viewed.normRecord {gone : PID → Bool} {processId : PID} {base process : ProcessState}
    (viewed : Viewed base process) (live : process.exiting = none) :
    Viewed base (normRecord gone processId process) := by
  rw [normRecord_live live]; exact viewed

/-- Whether a process is blocked depends only on what it sees. -/
private theorem Task.blocked_of_viewed {state state' : State} {processId : PID} {task : Task α}
    {process process' : ProcessState} (found : state.process processId = process)
    (found' : state'.process processId = process') (viewed : Viewed process process') :
    task.blocked state' processId = task.blocked state processId := by
  obtain ⟨mailbox, pdict, refCounter, -, -⟩ := viewed
  simp only [Task.blocked, State.view, found, found', mailbox, pdict, refCounter]

/-- A blocked process takes no step of its own. -/
private theorem Task.own_of_blocked {state : State} {processId : PID} {task : Task α}
    (blocked : task.blocked state processId = true) : task.own state processId = [] := by
  rcases task with ⟨computation, finish, _ | wait⟩
  · cases computation with
    | receive timeout select next =>
      cases timeout <;> simp only [Task.blocked, Option.isSome_none, Bool.false_or, Option.isNone_iff_eq_none,
        reduceCtorEq] at blocked
      simp [Task.own, blocked]
    | _ => simp [Task.blocked] at blocked
  · rfl

/-- Whether a signal other than an acknowledgement that does nothing yet is forced does not
depend on the state. -/
private theorem Task.forcedHead_transfer {state state' : State} {processId : PID} {task : Task α} {entry : Entry}
    (blocked : task.blocked state' processId = task.blocked state processId)
    (notAck : ∀ id, entry.signal ≠ .unlinkAck id)
    (notInert : state.inertEntry processId entry = false) (flagged : task.forcedHead state processId entry = true) :
    task.forcedHead state' processId entry = true := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp_all [Task.forcedHead]

private theorem hidden_ack_queued (source : PID) (id : Nat) :
    Hidden (Queued ⟨source, .unlinkAck id⟩) (ackChange source id) where
  exiting ok := (hidden_ack (by simp) source id).exiting ok.1
  trapExit ok := (hidden_ack (by simp) source id).trapExit ok.1
  parked ok := (hidden_ack (by simp) source id).parked ok.1
  links ok := (hidden_ack (by simp) source id).links ok.1
  push other ok := by
    obtain ⟨heads, pushed⟩ := (hidden_ack (by simp) source id).push other ok.1
    exact ⟨⟨heads, ok.2⟩, pushed⟩
  eagerExit exited ok := by
    obtain ⟨heads, exited'⟩ := (hidden_ack (by simp) source id).eagerExit exited ok.1
    exact ⟨⟨heads, ok.2⟩, exited'⟩
  unpark ok := by
    obtain ⟨heads, unparked⟩ := (hidden_ack (by simp) source id).unpark ok.1
    exact ⟨⟨heads, ok.2⟩, unparked⟩

/-- A forced handling of the oldest signal against a step of another key. -/
private theorem Config.forced_handle_other {elapsed : PID → Nat → Nat} {config : Config α} {processId : PID}
    {event event' : Event} {next middle : Config α} {key' : Key} (reachable : config.Reachable elapsed)
    (forced : (Key.handle processId, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf key' = some (event', middle)) (owner : key'.owner ≠ some processId) :
    (∃ absorbed, next.stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf key' = some (other, last) := by
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running forced
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
          Config.running { elapsed := transition.state.elapsed } [] none true
        else Config.running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
          (transition.finished.orElse fun _ => finished) false).stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        (if transition.exhausted then
            Config.running { elapsed := transition.state.elapsed } [] none true
          else Config.running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
            (transition.finished.orElse fun _ => finished) false).stepOf key' = some (other, last)) := by
    intro quiet
    have notLink : entry.signal ≠ .link := fun link => by rw [link] at quiet; cases quiet
    have kept : ∀ gone process', inert gone processId process' entry = false := fun _ _ => by
      obtain ⟨source, signal⟩ := entry; cases signal <;> simp_all [inert]
    have handled := Task.handle_quiet (task := task) found queue quiet
    rw [handled] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    refine Config.forced_other (key := .handle processId) (task' := resumeTask (resumedBy task entry) task) reachable
      lookup found live ⟨heads, rfl, rfl, rfl, rfl, rfl⟩ ((hidden_pop notLink).viewed process)
      (renormalize_of_clean (normRecord_popped clean live (by simp [popChange]) (fun _ => rfl) rfl (fun monitor mem => clean_monitors clean live monitor mem) live)) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ⟨heads₁, viewed₁⟩ live₁ _
    obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ (kept _ _)
    have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
      simp [State.process, record]
    have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (by rw [processOf₁, queue₁])
      (by rw [Task.handle_quiet record queue₁ quiet]; rfl)
      (Task.forcedHead_transfer (Task.blocked_of_viewed processOf processOf₁ (viewed₁.normRecord live₁))
        (fun _ ack => by rw [ack] at quiet; cases quiet) notInert flagged.symm)
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    exact .inl ⟨_, tagged, by rw [popChange, normRecord_live live₁]; exact live₁, normRecord_pop live₁ heads₁ (kept _ _)⟩
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | message message =>
    have fromProcess : (source != clock || task.blocked state processId) = true := by
      simpa [Task.forcedHead, notInert] using flagged
    rw [Task.handle_message sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    refine Config.forced_other (key := .handle processId) (task' := task) reachable lookup found live
      ⟨heads, rfl, rfl, rfl, rfl, rfl⟩ ((hidden_message (by simp) message).viewed process)
      (renormalize_of_clean (normRecord_popped clean live (by simp [messageChange]) (fun _ => rfl) rfl (fun monitor mem => clean_monitors clean live monitor mem) live))
      owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ⟨heads₁, viewed₁⟩ live₁ _
    obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ (by simp [inert])
    have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
      simp [State.process, record]
    have blocked := Task.blocked_of_viewed (task := task) processOf processOf₁ (viewed₁.normRecord live₁)
    have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (by rw [processOf₁, queue₁])
      (transition := Transition.mk (.handle processId ⟨source, .message message⟩)
        (raw.normalize.set processId (messageChange message (normRecord raw.gone processId process₁)))
        [(processId, task)] none false)
      (by rw [Task.handle_message (Sorted.normalize within.1) record queue₁]; rfl)
      (by simp only [Task.forcedHead, blocked, fromProcess, Bool.or_true])
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    exact .inl ⟨_, tagged, by rw [messageChange, normRecord_live live₁]; exact live₁,
      normRecord_message live₁ heads₁ (by simp [inert]) message⟩
  | aliasMessage alias message =>
    have blockedNow : task.blocked state processId = true := by
      simpa [Task.forcedHead, notInert] using flagged
    have notInert' : inert state.gone processId process ⟨source, .aliasMessage alias message⟩ = false := by
      rw [State.inertEntry_eq, processOf] at notInert; exact notInert
    rw [Task.handle_alias sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    have liveChange : ∀ other : ProcessState, other.exiting = none → (aliasChange alias message other).exiting = none :=
      fun _ live' => by unfold aliasChange; split <;> exact live'
    refine Config.forced_other (key := .handle processId) (task' := task) reachable lookup found live
      ⟨heads, rfl, rfl, rfl, rfl, rfl⟩ ((hidden_alias (by simp) alias message).viewed process)
      (renormalize_of_clean (normRecord_popped clean live (by unfold aliasChange; split <;> rfl)
        (fun _ => by unfold aliasChange; split <;> rfl) (by unfold aliasChange; split <;> rfl)
        (fun monitor mem => clean_monitors clean live monitor (by unfold aliasChange at mem; split at mem <;> exact mem))
        (liveChange _ live))) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ⟨heads₁, viewed₁⟩ live₁ _
    have kept : inert raw.gone processId process₁ ⟨source, .aliasMessage alias message⟩ = false := by
      obtain ⟨-, -, refCounter, monitoring, aliases⟩ := viewed₁
      rw [inert_congr refCounter monitoring aliases]
      simpa [inert] using notInert'
    obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ kept
    have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
      simp [State.process, record]
    have blocked := Task.blocked_of_viewed (task := task) processOf processOf₁ (viewed₁.normRecord live₁)
    have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
      (by rw [processOf₁, queue₁])
      (transition := Transition.mk (.handle processId ⟨source, .aliasMessage alias message⟩)
        (raw.normalize.set processId (aliasChange alias message (normRecord raw.gone processId process₁)))
        [(processId, task)] none false)
      (by rw [Task.handle_alias (Sorted.normalize within.1) record queue₁]; rfl)
      (by simp only [Task.forcedHead, blocked, blockedNow, Bool.or_true])
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
    exact .inl ⟨_, tagged, liveChange _ (by rw [normRecord_live live₁]; exact live₁),
      normRecord_alias live₁ heads₁ kept alias message⟩
  | monitor reference =>
    have blockedNow : task.blocked state processId = true := by
      simpa [Task.forcedHead, notInert] using flagged
    have notGone : state.gone source = false := by
      have := notInert; rw [State.inertEntry_eq, processOf] at this; simpa [inert] using this
    rw [Task.handle_monitor sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    refine Config.forced_other (key := .handle processId) (task' := task) reachable lookup found live
      ⟨heads, rfl, rfl, rfl, rfl, rfl⟩ ((hidden_monitor (by simp) reference source).viewed process)
      (renormalize_of_clean (normRecord_popped clean live rfl (fun _ => rfl) rfl (fun monitor mem => ?_) live))
      owner step' ?_
    · simp only [monitorChange, Kernel.append_eq, List.mem_append, List.mem_singleton] at mem
      rcases mem with old | rfl
      · exact clean_monitors clean live monitor old
      · exact notGone
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ⟨heads₁, viewed₁⟩ live₁ _
    cases goneSource : raw.gone source
    · have kept : inert raw.gone processId process₁ ⟨source, .monitor reference⟩ = false := by
        simp [inert, goneSource]
      obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ kept
      have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
        simp [State.process, record]
      have blocked := Task.blocked_of_viewed (task := task) processOf processOf₁ (viewed₁.normRecord live₁)
      have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1
        lookup₁ (by rw [processOf₁, queue₁])
        (transition := Transition.mk (.handle processId ⟨source, .monitor reference⟩)
          (raw.normalize.set processId (monitorChange reference source (normRecord raw.gone processId process₁)))
          [(processId, task)] none false)
        (by rw [Task.handle_monitor (Sorted.normalize within.1) record queue₁]; rfl)
        (by simp only [Task.forcedHead, blocked, blockedNow, Bool.or_true])
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
      exact .inl ⟨_, tagged, by rw [monitorChange, normRecord_live live₁]; exact live₁,
        normRecord_monitor live₁ heads₁ kept reference source⟩
    · exact .inr ⟨rfl, normRecord_monitor_gone live₁ heads₁ goneSource⟩
  | reply value => exact quietCase rfl
  | flush => exact quietCase rfl
  | unlinkAck id =>
    have bound : id ≤ process.unlinks := by simpa [Task.forcedHead, notInert, processOf] using flagged
    rw [Task.handle_ack sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    refine Config.forced_other (key := .handle processId) (task' := task) (ok := Queued ⟨source, .unlinkAck id⟩)
      reachable lookup found live ⟨heads, fun _ signal => by cases signal; exact bound⟩
      (hidden_ack_queued source id) (normRecord_ack_clean clean live) owner step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ⟨heads₁, bound₁⟩ live₁ _
    have kept : inert raw.gone processId process₁ ⟨source, .unlinkAck id⟩ = false := by simp [inert]
    obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ kept
    have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
      simp [State.process, record]
    have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1
      lookup₁ (by rw [processOf₁, queue₁])
      (by rw [Task.handle_ack (Sorted.normalize within.1) record queue₁]; rfl)
      (by simp [Task.forcedHead, processOf₁, normRecord_live live₁, bound₁ id rfl])
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
private theorem State.Changes.forced_of_same {state state' : State} {processId : PID} {ok : ProcessState → Prop}
    {change : ProcessState → ProcessState} (changed : state.Changed processId (Same ok change) state')
    (live : ∀ process, state.record processId = some process → process.exiting = none)
    (exiting : ∀ process, (change process).exiting = process.exiting) :
    state.Changed processId (ChangedAs processId ok change) state' := by
  refine ⟨changed.others, ?_, changed.sameTimers, changed.sameElapsed, changed.samePersistent⟩
  rcases changed.records with ⟨first, second⟩ | ⟨process, process', first, second, ok', rfl⟩
  · rw [first, second]; exact .none
  · rw [first, second]
    exact .some ⟨ok', live _ first, by rw [exiting]; exact live _ first, fun _ => rfl⟩

/-- Rewriting a process's task again replaces the first rewrite. -/
private theorem rewriteTask_again {processId : PID} (first : Task α) (entries : List (PID × Task α)) :
    ∀ tasks : List (PID × Task α), rewriteTask processId (fun _ => entries)
      (rewriteTask processId (fun _ => [(processId, first)]) tasks) = rewriteTask processId (fun _ => entries) tasks
  | [] => rfl
  | (other, task) :: rest => by
      by_cases same : other = processId
      · subst same; simp [rewriteTask]
      · simp [rewriteTask, same, rewriteTask_again first entries rest]

/-- A process's forced own step, a change of its own fields, against handling
its oldest signal: handling absorbs it when it ends the process, and the forced
step closes the square otherwise. -/
private theorem Config.own_handle_square {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {process : ProcessState} {task : Task α}
    {computation : Result task.β} {pdict : List (Term × Term) → List (Term × Term)} {mailbox : List Term → List Term}
    {ok : List Term → Prop} {event' : Event} {middle : Config α}
    (reachable : (Config.running state tasks finished false).Reachable elapsed)
    (lookup : Kernel.lookup processId tasks = some task) (waiting : task.wait = none)
    (found : state.record processId = some process)
    (own : OwnChange ok mailbox) (ok' : ok process.mailbox)
    (step' : (Config.running state tasks finished false).stepOf (.handle processId) = some (event', middle))
    (atMiddle : ∀ (raw : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α))
      (process₁ : ProcessState), raw.Within elapsed →
      (Config.running raw.normalize tasks₁ finished₁ false).Reachable elapsed →
      Kernel.lookup processId tasks₁ = some task → raw.record processId = some process₁ →
      OwnOk ok process.pdict process.refCounter process₁ → process₁.exiting = none →
      (∀ update, raw.normalize.persistent.staged = some update → update.owner = processId →
        state.persistent.staged = some update) →
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
    ⟨fun other differ => by rw [State.record_set, ite_eq_right differ],
      by rw [State.record_set, ite_eq_left rfl, found]; exact .some ⟨⟨ok', rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩
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
            Config.running { elapsed := transition'.state.elapsed } [] none true
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
    simp only [Task.ended, Bool.false_eq_true, ↓reduceIte, rewriteTask_again]
    rw [State.Changes.terminateSelf changedHandled reason sortedHandled.1 sortedHandled'.1
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
      related₁ live₁ fun _ staged owned => Config.stepOf_staged (by simp) step' staged owned
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
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none, rewriteTask_again]
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
  refine State.ext_records sorted' (Sorted.normalize sorted') (fun other => ?_) rfl rfl rfl
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
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running forced
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
      reachable lookup rfl found ownChange_true trivial step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ok₁ live₁ _
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
      reachable lookup rfl found ownChange_true trivial step' ?_
    intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ok₁ live₁ _
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
      refine Config.own_handle_square (computation := next₀ (some value)) (pdict := id) reachable lookup rfl found
        (ownChange_select (select (state.view processId)) message value) ⟨_, selected⟩ step' ?_
      intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ok₁ live₁ _
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
    cases query
    case persistentAwait =>
      -- Resuming once the process's update is visible: no other step stages one it owns again.
      have enabled : ∀ update, state.persistent.staged = some update → update.owner ≠ processId := by
        intro update staged same
        subst same
        simp [Task.own, State.request, staged] at head
      have reply : ∀ raw : State, (∀ update, raw.persistent.staged = some update → update.owner ≠ processId) →
          raw.request processId next₀ .persistentAwait = .reply (.atom "ok") raw := by
        intro raw free
        simp only [State.request]
        split
        · rename_i update staged
          have differ : (update.owner == processId) = false := by simpa using free update staged
          simp [differ]
        · rfl
      simp only [Task.own, reply state enabled, List.head?_cons, Option.some.injEq] at head; subst head
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
      rw [show state.normalize = state.set processId (ownChange id id id process) by
        rw [normalized]; exact (State.set_self sorted found).symm]
      refine Config.own_handle_square (computation := next₀ (.atom "ok")) (pdict := id) (mailbox := id)
        reachable lookup rfl found ownChange_true trivial step' ?_
      intro raw tasks₁ finished₁ process₁ within reachable₁ lookup₁ found₁ ok₁ live₁ kept
      obtain ⟨record, -, -, -⟩ := later within found₁ live₁ ok₁
      have free : ∀ update, raw.normalize.persistent.staged = some update → update.owner ≠ processId :=
        fun update staged same => enabled update (kept update staged same) same
      have tagged := Config.tagged_own_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1 lookup₁
        (transition := Transition.mk (.request processId .persistentAwait (some (.atom "ok"))) raw.normalize
          [(processId, ⟨next₀ (.atom "ok"), finish, none⟩)] none false)
        (by simp only [Task.own, reply raw.normalize free, List.head?_cons]) rfl rfl
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none] at tagged
      rw [show raw.normalize.normalize = (raw.normalize.set processId
          (ownChange id id id (normRecord raw.gone processId process₁))).normalize
        by rw [show ownChange id id id (normRecord raw.gone processId process₁) =
            normRecord raw.gone processId process₁ from rfl, State.set_self (Sorted.normalize within.1) record]] at tagged
      exact ⟨_, tagged⟩
    all_goals
      simp only [Task.own] at head
      split at head <;> simp only [List.head?_cons, List.head?_nil, Option.some.injEq, reduceCtorEq] at head <;>
        subst head <;> simp [Event.local] at isLocal

/-! ### Links with distinct processes

A record never holds two links with the same process: linking removes any
link with the process first, and handling a link adds one only when there is
none. -/

/-- Every record holds at most one link with each process. -/
private def State.Distinct (state : State) : Prop :=
  ∀ processId process, state.record processId = some process → (process.links.map (·.1)).Nodup

namespace State.Distinct

variable {state : State}

private theorem set (distinct : state.Distinct) {processId : PID} {process : ProcessState}
    (nodup : (process.links.map (·.1)).Nodup) : (state.set processId process).Distinct := by
  intro other process' found
  rw [State.record_set] at found
  split at found
  · cases found; exact nodup
  · exact distinct _ _ found

private theorem remove (distinct : state.Distinct) (processId : PID) : (state.remove processId).Distinct := by
  intro other process' found
  rw [State.record_remove] at found
  split at found
  · cases found
  · exact distinct _ _ found

private theorem modify (distinct : state.Distinct) {processId : PID} {change : ProcessState → ProcessState}
    (keeps : ∀ process, state.record processId = some process → (process.links.map (·.1)).Nodup →
      ((change process).links.map (·.1)).Nodup) : (state.modify processId change).Distinct := by
  unfold State.modify
  split
  · rename_i process found
    exact distinct.set (keeps _ found (distinct _ _ found))
  · exact distinct

private theorem timers (distinct : state.Distinct) (timers : List Timer) : ({ state with timers }).Distinct :=
  distinct

private theorem same (distinct : state.Distinct) {processId : PID} {change : ProcessState → ProcessState}
    (links : ∀ process, (change process).links = process.links) : (state.modify processId change).Distinct :=
  distinct.modify fun process _ nodup => by rw [links]; exact nodup

private theorem filtered (distinct : state.Distinct) {processId : PID} {keep : PID × Option Nat → Bool}
    : (state.modify processId fun process => { process with links := Kernel.filter keep process.links }).Distinct :=
  distinct.modify fun process _ nodup => by
    simp only [Kernel.filter_eq]
    exact (List.filter_sublist.map _).nodup nodup

private theorem relinked (distinct : state.Distinct) {processId target : PID} :
    (state.modify processId fun process =>
      { process with links := Kernel.append (Kernel.filter (·.1 != target) process.links) [(target, none)] }).Distinct :=
  distinct.modify fun process _ nodup => by
    simp only [Kernel.append_eq, Kernel.filter_eq, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨(List.filter_sublist.map _).nodup nodup, by simp, ?_⟩
    intro peer mem other mem'
    simp only [List.mem_singleton] at mem'
    subst mem'
    simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at mem
    obtain ⟨link, ⟨-, differ⟩, rfl⟩ := mem
    exact differ

private theorem fallback (distinct : state.Distinct) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).Distinct := by
  cases signal <;> simp only [State.fallback] <;> first | exact distinct | exact distinct.same fun _ => rfl |
    exact distinct.filtered

private theorem enqueue (distinct : state.Distinct) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).Distinct := by
  unfold State.enqueue
  split
  · rename_i process found
    split
    · refine distinct.set ?_; exact distinct (process := process) _ found
    · exact distinct.fallback _ _ _
  · exact distinct.fallback _ _ _

private theorem unpark (distinct : state.Distinct) (processId : PID) : (state.unpark processId).Distinct := by
  unfold State.unpark
  split
  · refine (distinct.same ?_).enqueue _ _ _; intro; rfl
  · exact distinct

private theorem send (distinct : state.Distinct) (source target : PID) (signal : Signal) :
    (state.send source target signal).Distinct := by
  unfold State.send
  refine State.Distinct.enqueue ?_ _ _ _
  split
  · split
    · exact distinct.unpark _
    · exact distinct
  · exact distinct

private theorem linkExit (distinct : state.Distinct) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).Distinct := by
  unfold State.linkExit
  split
  · exact distinct.modify fun process _ nodup => by
      simp only [Kernel.filter_eq]
      exact (List.filter_sublist.map _).nodup nodup
  · exact distinct.send _ _ _

private theorem foldl {γ : Type} {step : State → γ → State}
    (keeps : ∀ {state : State} item, state.Distinct → (step state item).Distinct) :
    ∀ (items : List γ) {state : State}, state.Distinct → (Kernel.foldl step state items).Distinct
  | [], _, distinct => distinct
  | item :: rest, _, distinct => by
      have := foldl keeps rest (keeps item distinct)
      simpa only [Kernel.foldl_eq, List.foldl_cons] using this

private theorem terminate (distinct : state.Distinct) (processId : PID) (reason : Term) :
    (state.terminate processId reason).Distinct := by
  unfold State.terminate
  refine State.Distinct.foldl (fun target distinct' => ?_) _ ?_
  · split
    · refine (distinct'.same ?_).linkExit _ _ _; intro; rfl
    · exact distinct'
  · refine (distinct.timers _).set ?_
    cases found : state.record processId with
    | none => simp [State.process, found]
    | some process => simpa [State.process, found] using distinct _ _ found

private theorem answer (distinct : state.Distinct) (processId : PID) (entry : Entry) :
    (state.answer processId entry).Distinct := by
  unfold State.answer
  split <;> first | exact distinct | exact distinct.send _ _ _

end State.Distinct

private theorem State.Distinct.allocated {state : State} (distinct : state.Distinct) (processId : PID) :
    (state.allocate processId).2.Distinct :=
  State.Distinct.modify (change := fun process => { process with refCounter := process.refCounter + 1 }) distinct
    fun _ _ nodup => nodup

private theorem nodup_relink (links : List (PID × Option Nat)) (target : PID) (value : Option Nat)
    (nodup : (links.map (·.1)).Nodup) :
    ((Kernel.append (Kernel.filter (·.1 != target) links) [(target, value)]).map (·.1)).Nodup := by
  simp only [Kernel.append_eq, Kernel.filter_eq, List.map_append, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  refine ⟨(List.filter_sublist.map _).nodup nodup, List.nodup_cons.mpr ⟨by simp, .nil⟩, ?_⟩
  intro peer mem other mem'
  simp only [List.mem_singleton] at mem'
  subst mem'
  simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at mem
  obtain ⟨link, ⟨-, differ⟩, rfl⟩ := mem
  exact differ

/-- Links a change keeps: the same, fewer, or another with a process after removing any. -/
local syntax "distinct_links" : tactic
macro_rules
  | `(tactic| distinct_links) => `(tactic| first
      | (intro _ _ nodup; exact nodup)
      | (intro _ _ nodup; simp only [Kernel.filter_eq]; exact (List.filter_sublist.map _).nodup nodup)
      | (intro _ _ nodup; exact nodup_relink _ _ _ nodup)
      | (intro _ _ _; simp))

/-- Steps keep links with distinct processes. -/
local syntax "distinct" : tactic
macro_rules
  | `(tactic| distinct) => `(tactic|
      (repeat' first
        | refine State.Distinct.modify ?_ (by distinct_links)
        | refine State.Distinct.enqueue ?_ _ _ _
        | refine State.Distinct.send ?_ _ _ _
        | refine State.Distinct.unpark ?_ _
        | refine State.Distinct.linkExit ?_ _ _ _
        | refine State.Distinct.terminate ?_ _ _
        | refine State.Distinct.answer ?_ _ _
        | refine State.Distinct.remove ?_ _
        | refine State.Distinct.timers ?_ _
        | refine State.Distinct.allocated ?_ _))

namespace State.Distinct

variable {state : State}

private theorem spawnWith (distinct : state.Distinct) (processId : PID) (options : SpawnOptions) :
    (state.spawnWith processId options).2.Distinct := by
  have parent : ((state.process processId).links.map (·.1)).Nodup := by
    cases found : state.record processId with
    | none => simp [State.process, found]
    | some process => simpa [State.process, found] using distinct _ _ found
  unfold State.spawnWith
  dsimp only
  by_cases monitor : options.monitor <;> by_cases link : options.link <;>
    simp only [monitor, link, ↓reduceIte, Bool.false_eq_true, State.allocate]
  all_goals
    repeat' first
      | refine State.Distinct.modify ?_ (by distinct_links)
      | refine State.Distinct.set ?_ ?_
  all_goals first | exact distinct | exact parent | simp

private theorem request (distinct : state.Distinct) (processId : PID) {β : Type} (next : Term → Result β)
    (query : Request) : ((state.request processId next query).state state).Distinct := by
  have allocated := distinct.allocated processId
  cases query with
  | persistentGet _ | persistentPut _ _ _ | persistentErase _ | persistentAwait =>
    exact State.request_persistent_of (fun _ => distinct) (by rfl)
  | monitor target alias =>
    simp only [State.request]
    generalize state.allocate processId = pair at allocated ⊢
    obtain ⟨reference, after⟩ := pair
    dsimp only at allocated ⊢
    split
    · exact allocated
    · exact (allocated.unpark _).modify fun _ _ nodup => nodup
  | demonitor reference flush =>
    simp only [State.request]
    split <;> exact distinct.modify fun _ _ nodup => nodup
  | link target =>
    simp only [State.request]
    repeat' split
    all_goals first
      | exact distinct
      | exact (distinct.modify fun _ _ nodup => nodup_relink _ _ _ nodup).send _ _ _
  | unlink target =>
    simp only [State.request]
    repeat' split
    all_goals first
      | exact distinct
      | refine (distinct.modify fun _ _ nodup => ?_).send _ _ _
        have keys : ∀ (links : List (PID × Option Nat)) (id : Nat), (Kernel.map (fun link =>
            if link.1 == target then (link.1, some id) else link) links).map (·.1) = links.map (·.1) := by
          intro links id
          simp only [Kernel.map_eq, List.map_map]
          congr 1; funext link; simp only [Function.comp]; split <;> rfl
        rw [keys]; exact nodup
  | exit target reason quirk =>
    simp only [State.request]
    repeat' split
    all_goals exact distinct.send _ _ _
  | trapExit enabled =>
    simp only [State.request]
    split
    · exact distinct
    · exact distinct.modify fun _ _ nodup => nodup
  | alive target | processInfo target =>
    simp only [State.request]
    repeat' split
    all_goals first | exact distinct | exact distinct.send _ _ _ | exact distinct.enqueue _ _ _
  | sendAlias alias message => exact distinct.send _ _ _
  | startTimer destination message duration =>
    simp only [State.request]
    generalize state.allocate processId = pair at allocated ⊢
    obtain ⟨reference, after⟩ := pair
    dsimp only at allocated ⊢
    split
    · exact allocated.timers _
    · exact allocated
  | cancelTimer reference =>
    simp only [State.request]
    split
    · exact (distinct.timers _).modify fun _ _ nodup => nodup
    · exact distinct

private theorem exitSignal (distinct : state.Distinct) (target source : PID) (reason : Term) (linked normalKills : Bool) :
    (state.exitSignal target source reason linked normalKills).1.Distinct := by
  unfold State.exitSignal
  dsimp only
  repeat' split
  all_goals first
    | exact distinct
    | exact distinct.filtered
    | (refine State.Distinct.modify ?_ fun _ _ nodup => nodup
       first | exact distinct | exact distinct.filtered)

private theorem handle (distinct : state.Distinct) (processId : PID) (waiting : Option Wait) (entry : Entry) :
    (state.handle processId waiting entry).1.Distinct := by
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | message message => exact distinct.modify fun _ _ nodup => nodup
  | aliasMessage alias message =>
    simp only [State.handle]; split
    · exact distinct.modify fun _ _ nodup => nodup
    · exact distinct
  | exit reason linked normalKills => exact distinct.exitSignal _ _ _ _ _
  | link =>
    simp only [State.handle]; split
    · exact distinct
    · rename_i missing
      refine distinct.modify fun process found nodup => ?_
      have absent : ∀ value, (source, value) ∉ process.links := by
        simpa [State.process, found, Kernel.lookup_eq] using missing
      simp only [Kernel.append_eq, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨nodup, List.nodup_cons.mpr ⟨by simp, .nil⟩, fun peer mem other mem' => ?_⟩
      simp only [List.mem_singleton] at mem'
      subst mem'
      intro same; subst same
      simp only [List.mem_map] at mem
      obtain ⟨⟨key, value⟩, inside, rfl⟩ := mem
      exact absent value inside
  | unlink id =>
    simp only [State.handle]
    split
    · exact distinct.filtered.send _ _ _
    · exact distinct.send _ _ _
  | unlinkAck id =>
    simp only [State.handle]; split
    · exact distinct.filtered
    · exact distinct
  | monitor reference => exact distinct.modify fun _ _ nodup => nodup
  | down reference reason =>
    simp only [State.handle]
    repeat' split
    all_goals (repeat' refine State.Distinct.modify ?_ fun _ _ nodup => nodup)
    all_goals exact distinct
  | isAlive => exact distinct.send _ _ _
  | reply value => simp only [State.handle]; split <;> exact distinct
  | flush => simp only [State.handle]; split <;> exact distinct

private theorem linkPhase (distinct : state.Distinct) {processId target : PID} {next : State}
    (phase : state.linkPhase processId target = some next) : next.Distinct := by
  unfold State.linkPhase at phase
  repeat' split at phase
  all_goals simp only [Option.some.injEq, reduceCtorEq] at phase
  subst phase
  rename_i process found _ _ _ _
  exact (distinct.set (by simpa using distinct _ _ found)).linkExit _ _ _

private theorem phase (distinct : state.Distinct) {processId : PID} {next : State}
    (phase : state.phase processId = some next) : next.Distinct := by
  unfold State.phase at phase
  repeat' split at phase
  all_goals simp only [Option.some.injEq, reduceCtorEq] at phase
  all_goals subst phase
  · refine (distinct.set ?_).send _ _ _
    simpa using distinct _ _ (by assumption)
  · refine (distinct.set ?_).answer _ _
    simpa using distinct _ _ (by assumption)

private theorem commit (distinct : state.Distinct) : state.commit.Distinct := by
  unfold State.commit; split <;> exact distinct

private theorem fire (distinct : state.Distinct) (timer : Timer) : (state.fire timer).Distinct :=
  (distinct.timers _).enqueue _ _ _

private theorem normalize (distinct : state.Distinct) (sorted : state.Sorted) : state.normalize.Distinct := by
  intro processId process found
  rw [State.record_normalize' sorted] at found
  cases record : state.record processId with
  | none => simp [record] at found
  | some original =>
    simp only [record, Option.map_some, Option.filter] at found
    split at found
    · cases found
      unfold normRecord
      split
      · simp
      · simp only [Kernel.filter_eq]
        exact (List.filter_sublist.map _).nodup (distinct _ _ record)
    · cases found

end State.Distinct

private theorem Task.own_distinct {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (distinct : state.Distinct) (mem : transition ∈ task.own state processId) : transition.state.Distinct := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
  cases computation with
  | ok value =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact distinct.terminate _ _
  | error exception =>
    cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;>
      first | exact distinct.terminate _ _ | exact distinct.remove _
  | get next => simp only [Task.own, List.mem_singleton] at mem; subst mem; exact distinct
  | set updated next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact distinct.modify fun _ _ nodup => nodup
  | schedule options child next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact distinct.spawnWith _ _
  | send destination message next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact distinct.send _ _ _
  | receive timeout select next =>
    simp only [Task.own] at mem
    repeat' split at mem
    all_goals simp only [List.mem_singleton, List.not_mem_nil] at mem
    all_goals subst mem
    · exact distinct.modify fun _ _ nodup => nodup
    all_goals exact distinct
  | request query next =>
    have requested := distinct.request processId next query
    simp only [Task.own] at mem
    split at mem <;> rename_i answer <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;>
      simp only [answer, Answer.state] at requested <;> exact requested

private theorem Task.handle_distinct {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (distinct : state.Distinct) (mem : transition ∈ task.handle state processId) : transition.state.Distinct := by
  simp only [Task.handle] at mem
  split at mem
  · simp at mem
  · rename_i entry rest queue
    have set : (state.set processId { state.process processId with queue := rest }).Distinct := by
      refine distinct.set ?_
      cases found : state.record processId with
      | none => simp [State.process, found]
      | some process => simpa [State.process, found] using distinct _ _ found
    have handled := set.handle processId (task.wait.map (·.1)) entry
    revert mem handled
    generalize (state.set processId { state.process processId with queue := rest }).handle processId
      (task.wait.map (·.1)) entry = triple
    obtain ⟨handled, resumed, exits⟩ := triple
    intro mem distinct'
    dsimp only at mem distinct'
    split at mem
    · simp only [List.mem_singleton] at mem; subst mem; exact distinct'.terminate _ _
    · split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> exact distinct'

/-! ### Unborn children

No record's PID extends a live process's PID with an index it has not spawned
yet, so a process never spawns a child over an existing record. -/

/-- No record extends a live record's PID with an index not spawned yet. -/
private def State.Unborn (state : State) : Prop :=
  ∀ parent process, state.record parent = some process → process.exiting = none →
    ∀ other, (state.record other).isSome → ∀ index, process.children < index → ¬parent ++ [index] <+: other

namespace State.Unborn

variable {state : State}

/-- Changing a record that keeps its children and revives no process. -/
private theorem modify (unborn : state.Unborn) {processId : PID} {change : ProcessState → ProcessState}
    (keeps : ∀ process, (change process).children = process.children ∧
      ((change process).exiting = none → process.exiting = none)) :
    (state.modify processId change).Unborn := by
  intro parent process found live other present index more
  rw [State.record_modify] at found present
  have present' : (state.record other).isSome := by
    split at present
    · rename_i same; subst same; simpa using present
    · exact present
  split at found
  · rename_i same; subst same
    cases original : state.record parent with
    | none => simp [original] at found
    | some process₀ =>
      simp only [original, Option.map_some, Option.some.injEq] at found
      subst found
      exact unborn _ _ original ((keeps _).2 live) _ present' _ (by rw [← (keeps _).1]; exact more)
  · exact unborn _ _ found live _ present' _ more

private theorem timers (unborn : state.Unborn) (timers : List Timer) : ({ state with timers }).Unborn := unborn

private theorem remove (unborn : state.Unborn) (processId : PID) : (state.remove processId).Unborn := by
  intro parent process found live other present index more
  rw [State.record_remove] at found present
  split at found
  · cases found
  · split at present
    · cases present
    · exact unborn _ _ found live _ present _ more

/-- Replacing an existing record by one that keeps its children and revives no process. -/
private theorem set (unborn : state.Unborn) {processId : PID} {process' : ProcessState} {process : ProcessState}
    (found : state.record processId = some process) (children : process'.children = process.children)
    (revives : process'.exiting = none → process.exiting = none) : (state.set processId process').Unborn := by
  intro parent record found' live other present index more
  rw [State.record_set] at found' present
  have present' : (state.record other).isSome := by
    split at present
    · rename_i same; subst same; simp [found]
    · exact present
  split at found'
  · rename_i same; subst same
    simp only [Option.some.injEq] at found'
    subst found'
    exact unborn _ _ found (revives live) _ present' _ (by rw [← children]; exact more)
  · exact unborn _ _ found' live _ present' _ more

private theorem same (unborn : state.Unborn) {processId : PID} {change : ProcessState → ProcessState}
    (children : ∀ process, (change process).children = process.children)
    (exiting : ∀ process, (change process).exiting = process.exiting) : (state.modify processId change).Unborn :=
  unborn.modify fun process => ⟨children process, fun live => by rw [← exiting]; exact live⟩

private theorem fallback (unborn : state.Unborn) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).Unborn := by
  cases signal <;> simp only [State.fallback] <;> first | exact unborn | exact unborn.same (fun _ => rfl) (fun _ => rfl)

private theorem enqueue (unborn : state.Unborn) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).Unborn := by
  unfold State.enqueue
  split
  · rename_i process found
    split
    · exact unborn.set found rfl id
    · exact unborn.fallback _ _ _
  · exact unborn.fallback _ _ _

private theorem unpark (unborn : state.Unborn) (processId : PID) : (state.unpark processId).Unborn := by
  unfold State.unpark
  split
  · refine (unborn.same ?_ ?_).enqueue _ _ _ <;> intro <;> rfl
  · exact unborn

private theorem send (unborn : state.Unborn) (source target : PID) (signal : Signal) :
    (state.send source target signal).Unborn := by
  unfold State.send
  refine State.Unborn.enqueue ?_ _ _ _
  split
  · split
    · exact unborn.unpark _
    · exact unborn
  · exact unborn

private theorem linkExit (unborn : state.Unborn) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).Unborn := by
  unfold State.linkExit
  split
  · exact unborn.same (fun _ => rfl) (fun _ => rfl)
  · exact unborn.send _ _ _

private theorem foldl {γ : Type} {step : State → γ → State}
    (keeps : ∀ {state : State} item, state.Unborn → (step state item).Unborn) :
    ∀ (items : List γ) {state : State}, state.Unborn → (Kernel.foldl step state items).Unborn
  | [], _, unborn => unborn
  | item :: rest, _, unborn => by
      have := foldl keeps rest (keeps item unborn)
      simpa only [Kernel.foldl_eq, List.foldl_cons] using this

private theorem terminate (unborn : state.Unborn) {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) (reason : Term) :
    (state.terminate processId reason).Unborn := by
  have processOf : state.process processId = process := by simp [State.process, found]
  unfold State.terminate
  refine State.Unborn.foldl (fun target unborn' => ?_) _ ?_
  · split
    · refine State.Unborn.linkExit ?_ _ _ _
      exact unborn'.modify fun process => ⟨rfl, fun live => by simpa using live⟩
    · exact unborn'
  · rw [processOf]
    exact (unborn.timers _).set (process := process) found rfl (by simp)

private theorem answer (unborn : state.Unborn) (processId : PID) (entry : Entry) :
    (state.answer processId entry).Unborn := by
  unfold State.answer
  split <;> first | exact unborn | exact unborn.send _ _ _

private theorem allocated (unborn : state.Unborn) (processId : PID) : (state.allocate processId).2.Unborn :=
  State.Unborn.same (change := fun process => { process with refCounter := process.refCounter + 1 }) unborn
    (fun _ => rfl) (fun _ => rfl)

private theorem prefix_extend {first second : PID} {index index' : Nat}
    (extends' : first ++ [index] <+: second ++ [index']) : first ++ [index] <+: second ∨ (first = second ∧ index = index') := by
  by_cases shorter : (first ++ [index]).length ≤ second.length
  · exact .inl (List.prefix_of_prefix_length_le extends' (List.prefix_append _ _) shorter)
  · have same : (first ++ [index]).length = (second ++ [index']).length := by
      have := extends'.length_le; simp at shorter this ⊢; omega
    have equal := List.append_inj (extends'.eq_of_length same) (by simpa using same)
    exact .inr ⟨equal.1, by simpa using equal.2⟩

/-- Spawning a child of a live process, whose index it has not used. -/
private theorem spawned (unborn : state.Unborn) {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) (live : process.exiting = none) :
    ((state.set processId { process with children := process.children + 1 }).set
      (processId ++ [process.children + 1]) {}).Unborn := by
  have childFresh : ∀ other, (state.record other).isSome → ¬processId ++ [process.children + 1] <+: other :=
    fun other present => unborn _ _ found live other present _ (Nat.lt_succ_self _)
  intro parent record found' live' other present index more
  simp only [State.record_set] at found' present
  have present' : other = processId ++ [process.children + 1] ∨ other = processId ∨ (state.record other).isSome := by
    split at present
    · exact .inl (by assumption)
    · split at present
      · exact .inr (.inl (by assumption))
      · exact .inr (.inr present)
  split at found'
  · -- The child spawns nothing yet.
    rename_i isChild; subst isChild
    intro extends'
    have extends'' : processId ++ [process.children + 1] <+: other := (List.prefix_append _ _).trans extends'
    rcases present' with rfl | rfl | present'
    · have := extends'.length_le; simp at this <;> omega
    · have := extends''.length_le; simp at this <;> omega
    · exact childFresh other present' extends''
  · split at found'
    · rename_i notChild isParent; subst isParent
      simp only [Option.some.injEq] at found'; subst found'
      intro extends'
      rcases present' with rfl | rfl | present'
      · rcases prefix_extend extends' with shorter | ⟨-, rfl⟩
        · have := shorter.length_le; simp at this <;> omega
        · simp at more
      · have := extends'.length_le; simp at this <;> omega
      · exact unborn _ _ found live other present' index (Nat.lt_of_succ_lt more) extends'
    · rename_i notChild notParent
      intro extends'
      rcases present' with rfl | rfl | present'
      · rcases prefix_extend extends' with shorter | ⟨same, -⟩
        · exact unborn _ _ found' live' processId (by simp [found]) index more shorter
        · exact notParent same
      · exact unborn _ _ found' live' _ (by simp [found]) index more extends'
      · exact unborn _ _ found' live' other present' index more extends'

private theorem spawnWith (unborn : state.Unborn) {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) (live : process.exiting = none) (options : SpawnOptions) :
    (state.spawnWith processId options).2.Unborn := by
  have processOf : state.process processId = process := by simp [State.process, found]
  have started := unborn.spawned found live
  unfold State.spawnWith
  dsimp only
  rw [processOf, Kernel.append_eq]
  by_cases monitor : options.monitor <;> by_cases link : options.link <;>
    simp only [monitor, link, ↓reduceIte, Bool.false_eq_true, State.allocate]
  all_goals
    repeat' refine State.Unborn.modify ?_ fun _ => ⟨rfl, id⟩
  all_goals exact started

private theorem request (unborn : state.Unborn) (processId : PID) {β : Type} (next : Term → Result β)
    (query : Request) : ((state.request processId next query).state state).Unborn := by
  have allocated := unborn.allocated processId
  have keep : ∀ {state : State} {processId : PID} {change : ProcessState → ProcessState}, state.Unborn →
      (∀ process, (change process).children = process.children ∧ (change process).exiting = process.exiting) →
      (state.modify processId change).Unborn :=
    fun unborn keeps => unborn.modify fun process => ⟨(keeps process).1, fun live => (keeps process).2 ▸ live⟩
  cases query with
  | persistentGet _ | persistentPut _ _ _ | persistentErase _ | persistentAwait =>
    exact State.request_persistent_of (fun _ => unborn) (by rfl)
  | monitor target alias =>
    simp only [State.request]
    generalize state.allocate processId = pair at allocated ⊢
    obtain ⟨reference, after⟩ := pair
    dsimp only at allocated ⊢
    split
    · exact allocated
    · exact keep (allocated.unpark _) fun _ => ⟨rfl, rfl⟩
  | demonitor reference flush =>
    simp only [State.request]
    split <;> exact keep unborn fun _ => ⟨rfl, rfl⟩
  | link target =>
    simp only [State.request]
    repeat' split
    all_goals first
      | exact unborn
      | (refine State.Unborn.send ?_ _ _ _; exact keep unborn fun _ => ⟨rfl, rfl⟩)
  | unlink target =>
    simp only [State.request]
    repeat' split
    all_goals first
      | exact unborn
      | (refine State.Unborn.send ?_ _ _ _; exact keep unborn fun _ => ⟨rfl, rfl⟩)
  | exit target reason quirk =>
    simp only [State.request]
    repeat' split
    all_goals exact unborn.send _ _ _
  | trapExit enabled =>
    simp only [State.request]
    split
    · exact unborn
    · exact keep unborn fun _ => ⟨rfl, rfl⟩
  | alive target | processInfo target =>
    simp only [State.request]
    repeat' split
    all_goals first | exact unborn | exact unborn.send _ _ _ | exact unborn.enqueue _ _ _
  | sendAlias alias message => exact unborn.send _ _ _
  | startTimer destination message duration =>
    simp only [State.request]
    generalize state.allocate processId = pair at allocated ⊢
    obtain ⟨reference, after⟩ := pair
    dsimp only at allocated ⊢
    split
    · exact allocated.timers _
    · exact allocated
  | cancelTimer reference =>
    simp only [State.request]
    split
    · exact keep (unborn.timers _) fun _ => ⟨rfl, rfl⟩
    · exact unborn

end State.Unborn

/-- A configuration whose records hold links with distinct processes. -/
private def Config.Distinct : Config α → Prop
  | .start .. => True
  | .running state .. => state.Distinct

private theorem Config.Distinct.step {elapsed : PID → Nat → Nat} {config next : Config α} {event : Event}
    (within : config.Within elapsed) (distinct : config.Distinct) (step : Step config event next) : next.Distinct := by
  cases config with
  | start env computation elapsed' =>
    simp only [Step, Config.successors] at step
    split at step
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · split at step
      · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step
        intro processId process found
        simp only [State.initial, State.record, Kernel.lookup_eq, List.lookup_cons, List.lookup_nil] at found
        split at found <;> simp only [Option.some.injEq, reduceCtorEq] at found
        subst found; simp
      · simp at step
  | running state tasks finished exhausted =>
    have within : state.Within elapsed := within
    have distinct : state.Distinct := distinct
    cases exhausted
    case true => simp [Step, Config.successors] at step
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with (((⟨before, processId, task, after, -, transition, possible, same⟩ |
      ⟨processId, process, -, phased⟩) | ⟨processId, process, -, unparked⟩) | ⟨timer, -, fired⟩) |
      ⟨update, -, committed⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
      have kept : transition.state.Distinct ∧ transition.state.Within elapsed := by
        rcases possible with possible | possible
        · exact ⟨Task.own_distinct distinct possible, within.own possible⟩
        · exact ⟨Task.handle_distinct distinct possible, within.handleStep possible⟩
      unfold Transition.apply
      split
      · intro processId process found
        simp [State.record, Kernel.lookup_eq] at found
      · exact kept.1.normalize kept.2.1
    · obtain ⟨next', phase, same⟩ := phased
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at phase
      show next'.normalize.Distinct
      rcases phase with ⟨target, -, linked⟩ | phase
      · exact (distinct.linkPhase linked).normalize (within.linkPhase linked).1
      · split at phase
        · rename_i next'' found
          simp only [List.mem_singleton] at phase; subst phase
          exact (distinct.phase found).normalize (within.phase found).1
        · simp at phase
    · cases parked : (state.process processId).parked with
      | none => simp [parked] at unparked
      | some _ =>
        simp only [parked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at unparked
        obtain ⟨-, rfl⟩ := unparked
        exact (distinct.unpark _).normalize (within.unpark _).1
    · simp only [Prod.mk.injEq] at fired
      obtain ⟨-, rfl⟩ := fired
      exact (distinct.fire _).normalize (within.fire _).1
    · simp only [Prod.mk.injEq] at committed
      obtain ⟨-, rfl⟩ := committed
      exact distinct.commit.normalize within.commit.1

namespace State.Unborn

variable {state : State}

private theorem keep (unborn : state.Unborn) {processId : PID} {change : ProcessState → ProcessState}
    (keeps : ∀ process, (change process).children = process.children ∧ (change process).exiting = process.exiting) :
    (state.modify processId change).Unborn :=
  unborn.modify fun process => ⟨(keeps process).1, fun live => (keeps process).2 ▸ live⟩

private theorem exitSignal (unborn : state.Unborn) (target source : PID) (reason : Term) (linked normalKills : Bool) :
    (state.exitSignal target source reason linked normalKills).1.Unborn := by
  unfold State.exitSignal State.append
  dsimp only
  repeat' split
  all_goals (repeat' refine State.Unborn.keep ?_ fun _ => ⟨rfl, rfl⟩)
  all_goals exact unborn

private theorem handle (unborn : state.Unborn) (processId : PID) (waiting : Option Wait) (entry : Entry) :
    (state.handle processId waiting entry).1.Unborn := by
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | message message => exact unborn.keep fun _ => ⟨rfl, rfl⟩
  | aliasMessage alias message =>
    simp only [State.handle]; split
    · exact unborn.keep fun _ => ⟨rfl, rfl⟩
    · exact unborn
  | exit reason linked normalKills => exact unborn.exitSignal _ _ _ _ _
  | link =>
    simp only [State.handle]; split
    · exact unborn
    · exact unborn.keep fun _ => ⟨rfl, rfl⟩
  | unlink id =>
    simp only [State.handle]
    split
    · refine State.Unborn.send ?_ _ _ _; exact unborn.keep fun _ => ⟨rfl, rfl⟩
    · exact unborn.send _ _ _
  | unlinkAck id =>
    simp only [State.handle]; split
    · exact unborn.keep fun _ => ⟨rfl, rfl⟩
    · exact unborn
  | monitor reference => exact unborn.keep fun _ => ⟨rfl, rfl⟩
  | down reference reason =>
    simp only [State.handle]
    repeat' split
    all_goals (repeat' refine State.Unborn.keep ?_ fun _ => ⟨rfl, rfl⟩)
    all_goals exact unborn
  | isAlive => exact unborn.send _ _ _
  | reply value => simp only [State.handle]; split <;> exact unborn
  | flush => simp only [State.handle]; split <;> exact unborn

private theorem linkPhase (unborn : state.Unborn) {processId target : PID} {next : State}
    (phase : state.linkPhase processId target = some next) : next.Unborn := by
  unfold State.linkPhase at phase
  repeat' split at phase
  all_goals simp only [Option.some.injEq, reduceCtorEq] at phase
  subst phase
  rename_i process found _ _ _ _
  refine State.Unborn.linkExit ?_ _ _ _
  exact unborn.set found rfl fun live => by simp_all

private theorem phase (unborn : state.Unborn) {processId : PID} {next : State}
    (phase : state.phase processId = some next) : next.Unborn := by
  unfold State.phase at phase
  repeat' split at phase
  all_goals simp only [Option.some.injEq, reduceCtorEq] at phase
  all_goals subst phase
  · refine State.Unborn.send ?_ _ _ _
    exact unborn.set (by assumption) (by rfl) fun live => by simp_all
  · refine State.Unborn.answer ?_ _ _
    exact unborn.set (by assumption) (by rfl) fun live => by simp_all

private theorem commit (unborn : state.Unborn) : state.commit.Unborn := by
  unfold State.commit; split <;> exact unborn

private theorem fire (unborn : state.Unborn) (timer : Timer) : (state.fire timer).Unborn :=
  (unborn.timers _).enqueue _ _ _

private theorem normalize (unborn : state.Unborn) (sorted : state.Sorted) : state.normalize.Unborn := by
  intro parent process found live other present index more
  rw [State.record_normalize' sorted] at found present
  cases record : state.record parent with
  | none => simp [record] at found
  | some original =>
    simp only [record, Option.map_some, Option.filter] at found
    split at found
    · cases found
      have keeps : (normRecord state.gone parent original).children = original.children ∧
          ((normRecord state.gone parent original).exiting = none → original.exiting = none) := by
        unfold normRecord
        split
        · exact ⟨rfl, fun live => by simp at live⟩
        · exact ⟨rfl, fun _ => by assumption⟩
      refine unborn _ _ record (keeps.2 live) other ?_ index (keeps.1 ▸ more)
      cases record' : state.record other with
      | none => simp [record'] at present
      | some _ => rfl
    · cases found

end State.Unborn

/-! Steps of a process other than ending it keep its record. -/

private def State.Present (processId : PID) (state : State) : Prop := (state.record processId).isSome

namespace State.Present

variable {processId : PID} {state : State}

private theorem modify (present : state.Present processId) (other : PID) (change : ProcessState → ProcessState) :
    (state.modify other change).Present processId := by
  unfold State.Present at *
  rw [State.record_modify]; split
  · rename_i same; subst same; simpa using present
  · exact present

private theorem set (present : state.Present processId) (other : PID) (process : ProcessState) :
    (state.set other process).Present processId := by
  unfold State.Present at *
  rw [State.record_set]; split
  · rfl
  · exact present

private theorem fallback (present : state.Present processId) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).Present processId := by
  cases signal <;> simp only [State.fallback] <;> first | exact present | exact present.modify _ _

private theorem enqueue (present : state.Present processId) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).Present processId := by
  unfold State.enqueue
  split
  · split
    · exact present.set _ _
    · exact present.fallback _ _ _
  · exact present.fallback _ _ _

private theorem send (present : state.Present processId) (source target : PID) (signal : Signal) :
    (state.send source target signal).Present processId := by
  unfold State.send State.unpark
  refine State.Present.enqueue ?_ _ _ _
  repeat' split
  all_goals first | exact present | exact (present.modify _ _).enqueue _ _ _

private theorem exitSignal (present : state.Present processId) (target source : PID) (reason : Term)
    (linked normalKills : Bool) : (state.exitSignal target source reason linked normalKills).1.Present processId := by
  unfold State.exitSignal
  dsimp only
  repeat' split
  all_goals first
    | exact present
    | exact present.modify _ _
    | exact (present.modify _ _).modify _ _

private theorem handle (present : state.Present processId) (other : PID) (waiting : Option Wait) (entry : Entry) :
    (state.handle other waiting entry).1.Present processId := by
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | exit reason linked normalKills => exact present.exitSignal _ _ _ _ _
  | _ =>
    simp only [State.handle]
    repeat' split
    all_goals first
      | exact present
      | exact present.modify _ _
      | exact present.send _ _ _
      | exact (present.modify _ _).send _ _ _
      | exact (present.modify _ _).modify _ _
      | exact ((present.modify _ _).modify _ _).modify _ _

end State.Present

private theorem Task.own_unborn {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (unborn : state.Unborn) (alive : state.alive processId = true) (mem : transition ∈ task.own state processId) :
    transition.state.Unborn := by
  obtain ⟨process, found, live⟩ := State.alive_iff.mp alive
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
  cases computation with
  | ok value =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact unborn.terminate found _
  | error exception =>
    cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;>
      first | exact unborn.terminate found _ | exact unborn.remove _
  | get next => simp only [Task.own, List.mem_singleton] at mem; subst mem; exact unborn
  | set updated next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact unborn.keep fun _ => ⟨rfl, rfl⟩
  | schedule options child next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact unborn.spawnWith found live _
  | send destination message next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact unborn.send _ _ _
  | receive timeout select next =>
    simp only [Task.own] at mem
    repeat' split at mem
    all_goals simp only [List.mem_singleton, List.not_mem_nil] at mem
    all_goals subst mem
    · exact unborn.keep fun _ => ⟨rfl, rfl⟩
    all_goals exact unborn
  | request query next =>
    have requested := unborn.request processId next query
    simp only [Task.own] at mem
    split at mem <;> rename_i answer <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;>
      simp only [answer, Answer.state] at requested <;> exact requested

private theorem Task.handle_unborn {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (unborn : state.Unborn) (mem : transition ∈ task.handle state processId) : transition.state.Unborn := by
  simp only [Task.handle] at mem
  split at mem
  · simp at mem
  · rename_i entry rest queue
    cases found : state.record processId with
    | none => simp [State.process, found] at queue
    | some process =>
    have processOf : state.process processId = process := by simp [State.process, found]
    have set : (state.set processId { state.process processId with queue := rest }).Unborn := by
      rw [processOf]; exact unborn.set found rfl id
    have found' : (state.set processId { state.process processId with queue := rest }).record processId =
        some { state.process processId with queue := rest } := by simp [State.record_set]
    have handled := set.handle processId (task.wait.map (·.1)) entry
    have recorded := State.Present.handle (state := state.set processId { state.process processId with queue := rest })
      (processId := processId) (by simp [State.Present, found']) processId (task.wait.map (·.1)) entry
    revert mem handled recorded
    generalize (state.set processId { state.process processId with queue := rest }).handle processId
      (task.wait.map (·.1)) entry = triple
    obtain ⟨handled, resumed, exits⟩ := triple
    intro mem unborn' recorded
    dsimp only at mem unborn' recorded
    split at mem
    · simp only [List.mem_singleton] at mem; subst mem
      obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp recorded
      exact unborn'.terminate recorded _
    · split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> exact unborn'

/-- A configuration whose live processes have spawned no record yet. -/
private def Config.Unborn : Config α → Prop
  | .start .. => True
  | .running state .. => state.Unborn

private theorem Config.Unborn.step {elapsed : PID → Nat → Nat} {config next : Config α} {event : Event}
    (reachable : config.Reachable elapsed) (unborn : config.Unborn) (step : Step config event next) : next.Unborn := by
  cases config with
  | start env computation elapsed' =>
    simp only [Step, Config.successors] at step
    split at step
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · split at step
      · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step
        intro parent process found live other present index more extends'
        have only : ∀ pid, ((State.initial env elapsed').record pid).isSome = true → pid = env.currentPid := by
          intro pid present
          simp only [State.initial, State.record, Kernel.lookup_eq, List.lookup_cons, List.lookup_nil] at present
          split at present
          · rename_i same; simpa using same
          · simp at present
        have one := only parent (by simp [found])
        have two := only other present
        subst one; subst two
        have := extends'.length_le; simp at this <;> omega
      · simp at step
  | running state tasks finished exhausted =>
    have within : state.Within elapsed := reachable.1.1
    have unborn : state.Unborn := unborn
    cases exhausted
    case true => simp [Step, Config.successors] at step
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with (((⟨before, processId, task, after, split, transition, possible, same⟩ |
      ⟨processId, process, -, phased⟩) | ⟨processId, process, -, unparked⟩) | ⟨timer, -, fired⟩) |
      ⟨update, -, committed⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      have alive : state.alive processId = true :=
        reachable.2.2.1 (processId, task) (by rw [eq_of_mem_splits split]; simp)
      simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
      have kept : transition.state.Unborn ∧ transition.state.Within elapsed := by
        rcases possible with possible | possible
        · exact ⟨Task.own_unborn unborn alive possible, within.own possible⟩
        · exact ⟨Task.handle_unborn unborn possible, within.handleStep possible⟩
      unfold Transition.apply
      split
      · intro parent process found
        simp [State.record, Kernel.lookup_eq] at found
      · exact kept.1.normalize kept.2.1
    · obtain ⟨next', phase, same⟩ := phased
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at phase
      show next'.normalize.Unborn
      rcases phase with ⟨target, -, linked⟩ | phase
      · exact (unborn.linkPhase linked).normalize (within.linkPhase linked).1
      · split at phase
        · rename_i next'' found
          simp only [List.mem_singleton] at phase; subst phase
          exact (unborn.phase found).normalize (within.phase found).1
        · simp at phase
    · cases parked : (state.process processId).parked with
      | none => simp [parked] at unparked
      | some _ =>
        simp only [parked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at unparked
        obtain ⟨-, rfl⟩ := unparked
        exact (unborn.unpark _).normalize (within.unpark _).1
    · simp only [Prod.mk.injEq] at fired
      obtain ⟨-, rfl⟩ := fired
      exact (unborn.fire _).normalize (within.fire _).1
    · simp only [Prod.mk.injEq] at committed
      obtain ⟨-, rfl⟩ := committed
      exact unborn.commit.normalize within.commit.1

/-! ### Dropped `DOWN`s stay dropped

A watcher drops a `DOWN` of a reference it allocated and no longer monitors.
Its reference counter only grows, and it only monitors references it allocates
next, so it keeps dropping it. -/

/-- A record has allocated the reference with the count, which it does not monitor. -/
private def Unmonitored (reference : List Nat) (count : Nat) (process : ProcessState) : Prop :=
  count ≤ process.refCounter ∧ Kernel.any process.monitoring (·.1 == reference) = false

/-- The live record of the watcher, if any, has allocated the reference and does not monitor it. -/
private def State.Covers (watcher : PID) (reference : List Nat) (count : Nat) (state : State) : Prop :=
  ∀ process, state.record watcher = some process → process.exiting = none → Unmonitored reference count process

namespace State.Covers

variable {watcher : PID} {reference : List Nat} {count : Nat} {state : State}

/-- A change that revives no process and keeps it from monitoring the reference. -/
private def Keeps (reference : List Nat) (count : Nat) (change : ProcessState → ProcessState) : Prop :=
  ∀ process, (change process).exiting = none → process.exiting = none ∧
    (Unmonitored reference count process → Unmonitored reference count (change process))

private theorem modify (covers : state.Covers watcher reference count) {processId : PID}
    {change : ProcessState → ProcessState} (keeps : Keeps reference count change) :
    (state.modify processId change).Covers watcher reference count := by
  intro process found live
  rw [State.record_modify] at found
  split at found
  · rename_i same; subst same
    cases original : state.record watcher with
    | none => simp [original] at found
    | some process₀ =>
      simp only [original, Option.map_some, Option.some.injEq] at found
      subst found
      have kept := keeps process₀ live
      exact kept.2 (covers _ original kept.1)
  · exact covers _ found live

private theorem same (covers : state.Covers watcher reference count) {processId : PID}
    {change : ProcessState → ProcessState} (refCounter : ∀ process, (change process).refCounter = process.refCounter)
    (monitoring : ∀ process, (change process).monitoring = process.monitoring)
    (exiting : ∀ process, (change process).exiting = process.exiting) :
    (state.modify processId change).Covers watcher reference count :=
  covers.modify fun process live => ⟨exiting process ▸ live, fun ⟨counted, unmonitored⟩ =>
    ⟨(refCounter process).symm ▸ counted, (monitoring process).symm ▸ unmonitored⟩⟩

private theorem set (covers : state.Covers watcher reference count) {processId : PID} {process process' : ProcessState}
    (found : state.record processId = some process) (keeps : process'.exiting = none → process.exiting = none ∧
      (Unmonitored reference count process → Unmonitored reference count process')) :
    (state.set processId process').Covers watcher reference count := by
  intro record found' live
  rw [State.record_set] at found'
  split at found'
  · rename_i same; subst same
    simp only [Option.some.injEq] at found'; subst found'
    have kept := keeps live
    exact kept.2 (covers _ found kept.1)
  · exact covers _ found' live

private theorem set_other (covers : state.Covers watcher reference count) {processId : PID}
    (differ : processId ≠ watcher) (process : ProcessState) : (state.set processId process).Covers watcher reference count := by
  intro record found live
  rw [State.record_set, ite_eq_right (Ne.symm differ)] at found
  exact covers _ found live

private theorem remove (covers : state.Covers watcher reference count) (processId : PID) :
    (state.remove processId).Covers watcher reference count := by
  intro record found live
  rw [State.record_remove] at found
  split at found
  · cases found
  · exact covers _ found live

private theorem timers (covers : state.Covers watcher reference count) (timers : List Timer) :
    ({ state with timers }).Covers watcher reference count := covers

private theorem fallback (covers : state.Covers watcher reference count) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).Covers watcher reference count := by
  cases signal <;> simp only [State.fallback] <;>
    first | exact covers | exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem enqueue (covers : state.Covers watcher reference count) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).Covers watcher reference count := by
  unfold State.enqueue
  split
  · rename_i process found
    split
    · exact covers.set found fun live => ⟨live, id⟩
    · exact covers.fallback _ _ _
  · exact covers.fallback _ _ _

private theorem unpark (covers : state.Covers watcher reference count) (processId : PID) :
    (state.unpark processId).Covers watcher reference count := by
  unfold State.unpark
  split
  · refine (covers.same ?_ ?_ ?_).enqueue _ _ _ <;> intro <;> rfl
  · exact covers

private theorem send (covers : state.Covers watcher reference count) (source target : PID) (signal : Signal) :
    (state.send source target signal).Covers watcher reference count := by
  unfold State.send
  refine State.Covers.enqueue ?_ _ _ _
  split
  · split
    · exact covers.unpark _
    · exact covers
  · exact covers

private theorem linkExit (covers : state.Covers watcher reference count) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).Covers watcher reference count := by
  unfold State.linkExit
  split
  · exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · exact covers.send _ _ _

private theorem foldl {γ : Type} {step : State → γ → State}
    (keeps : ∀ {state : State} item, state.Covers watcher reference count → (step state item).Covers watcher reference count) :
    ∀ (items : List γ) {state : State}, state.Covers watcher reference count →
      (Kernel.foldl step state items).Covers watcher reference count
  | [], _, covers => covers
  | item :: rest, _, covers => by
      have := foldl keeps rest (keeps item covers)
      simpa only [Kernel.foldl_eq, List.foldl_cons] using this

private theorem terminate (covers : state.Covers watcher reference count) {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) (reason : Term) :
    (state.terminate processId reason).Covers watcher reference count := by
  have processOf : state.process processId = process := by simp [State.process, found]
  unfold State.terminate
  refine State.Covers.foldl (fun target covers' => ?_) _ ?_
  · split
    · refine State.Covers.linkExit ?_ _ _ _
      exact covers'.modify fun process live => ⟨by simpa using live, id⟩
    · exact covers'
  · rw [processOf]
    exact (covers.timers _).set (process := process) found fun live => by simp at live

private theorem answer (covers : state.Covers watcher reference count) (processId : PID) (entry : Entry) :
    (state.answer processId entry).Covers watcher reference count := by
  unfold State.answer
  split <;> first | exact covers | exact covers.send _ _ _

private theorem allocated (covers : state.Covers watcher reference count) (processId : PID) :
    (state.allocate processId).2.Covers watcher reference count :=
  covers.modify fun _ live => ⟨live, fun ⟨counted, unmonitored⟩ => ⟨Nat.le_succ_of_le counted, unmonitored⟩⟩

private theorem modify_other (covers : state.Covers watcher reference count) {processId : PID}
    (differ : processId ≠ watcher) (change : ProcessState → ProcessState) :
    (state.modify processId change).Covers watcher reference count := by
  intro process found live
  rw [State.record_modify, ite_eq_right (Ne.symm differ)] at found
  exact covers _ found live

private theorem any_filter_false {β : Type} {list : List (List Nat × β)} {reference other : List Nat}
    (unmonitored : Kernel.any list (·.1 == reference) = false) :
    Kernel.any (Kernel.filter (·.1 != other) list) (·.1 == reference) = false := by
  simp only [Kernel.any_eq, Kernel.filter_eq, List.any_eq_false, List.mem_filter] at unmonitored ⊢
  exact fun entry inside => unmonitored entry inside.1

/-- Monitoring a reference other than the one dropped. -/
private theorem monitor (covers : state.Covers watcher reference count) {processId : PID} {fresh : List Nat}
    {target : PID} {change : ProcessState → ProcessState} (differ : processId = watcher → fresh ≠ reference)
    (refCounter : ∀ process, (change process).refCounter = process.refCounter)
    (exiting : ∀ process, (change process).exiting = process.exiting)
    (monitoring : ∀ process, (change process).monitoring = Kernel.append process.monitoring [(fresh, target)]) :
    (state.modify processId change).Covers watcher reference count := by
  by_cases same : processId = watcher
  · refine covers.modify fun process live => ⟨exiting process ▸ live, fun ⟨counted, unmonitored⟩ =>
      ⟨(refCounter process).symm ▸ counted, ?_⟩⟩
    rw [monitoring]
    simp only [Kernel.any_eq, Kernel.append_eq, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      at unmonitored ⊢
    rw [unmonitored, Bool.false_or, beq_eq_false_iff_ne]
    exact differ same
  · exact covers.modify_other same _

/-- A reference a live process allocates next is not one its record allocated already. -/
private theorem allocated_fresh (covers : state.Covers watcher reference count) (shape : reference = watcher ++ [count])
    {processId : PID} {process : ProcessState} (found : state.record processId = some process)
    (live : process.exiting = none) : processId = watcher → (state.allocate processId).1 ≠ reference := by
  intro same; subst same
  have counted := (covers _ found live).1
  simp only [State.allocate, State.process, found, Option.getD_some, Kernel.append_eq, shape]
  intro equal
  have := List.append_inj_right' equal rfl
  simp at this; omega

private theorem request (covers : state.Covers watcher reference count) (shape : reference = watcher ++ [count])
    {processId : PID} {process : ProcessState} (found : state.record processId = some process)
    (live : process.exiting = none) {β : Type} (next : Term → Result β) (query : Request) :
    ((state.request processId next query).state state).Covers watcher reference count := by
  have allocated := covers.allocated processId
  have fresh := covers.allocated_fresh shape found live
  cases query with
  | persistentGet _ | persistentPut _ _ _ | persistentErase _ | persistentAwait =>
    exact State.request_persistent_of (fun _ => covers) (by rfl)
  | monitor target alias =>
    simp only [State.request]
    split
    · exact allocated
    · exact State.Covers.monitor (allocated.unpark _) fresh (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | demonitor reference' flush =>
    simp only [State.request]
    split <;> exact covers.modify fun _ live => ⟨live, fun ⟨counted, unmonitored⟩ =>
      ⟨counted, any_filter_false unmonitored⟩⟩
  | link target =>
    simp only [State.request]
    repeat' split
    all_goals first
      | exact covers
      | (refine State.Covers.send ?_ _ _ _; exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  | unlink target =>
    simp only [State.request]
    repeat' split
    all_goals first
      | exact covers
      | (refine State.Covers.send ?_ _ _ _; exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  | exit target reason quirk =>
    simp only [State.request]
    repeat' split
    all_goals exact covers.send _ _ _
  | trapExit enabled =>
    simp only [State.request]
    split
    · exact covers
    · exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | alive target | processInfo target =>
    simp only [State.request]
    repeat' split
    all_goals first | exact covers | exact covers.send _ _ _ | exact covers.enqueue _ _ _
  | sendAlias alias message => exact covers.send _ _ _
  | startTimer destination message duration =>
    simp only [State.request]
    split
    · exact allocated.timers _
    · exact allocated
  | cancelTimer reference' =>
    simp only [State.request]
    split
    · exact (covers.timers _).same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    · exact covers

private theorem exitSignal (covers : state.Covers watcher reference count) (target source : PID) (reason : Term)
    (linked normalKills : Bool) : (state.exitSignal target source reason linked normalKills).1.Covers watcher reference count := by
  unfold State.exitSignal State.append
  dsimp only
  repeat' split
  all_goals (repeat' refine State.Covers.same ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  all_goals exact covers

private theorem handle (covers : state.Covers watcher reference count) (processId : PID) (waiting : Option Wait)
    (entry : Entry) : (state.handle processId waiting entry).1.Covers watcher reference count := by
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | exit reason linked normalKills => exact covers.exitSignal _ _ _ _ _
  | down reference' reason =>
    simp only [State.handle]
    repeat' split
    all_goals (repeat' first
      | refine State.Covers.same ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      | refine State.Covers.modify ?_ fun _ live => ⟨live, fun ⟨counted, unmonitored⟩ =>
          ⟨counted, any_filter_false unmonitored⟩⟩)
    all_goals exact covers
  | _ =>
    simp only [State.handle]
    repeat' split
    all_goals first
      | exact covers
      | exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      | exact covers.send _ _ _
      | (refine State.Covers.send ?_ _ _ _; exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

private theorem spawnWith (covers : state.Covers watcher reference count) (shape : reference = watcher ++ [count])
    {processId : PID} {process : ProcessState} (found : state.record processId = some process)
    (live : process.exiting = none) (child : Kernel.append processId [process.children + 1] ≠ watcher)
    (options : SpawnOptions) : (state.spawnWith processId options).2.Covers watcher reference count := by
  have processOf : state.process processId = process := by simp [State.process, found]
  have counted : processId = watcher → count ≤ process.refCounter := fun same => by
    subst same; exact (covers _ found live).1
  unfold State.spawnWith
  dsimp only
  rw [processOf]
  by_cases monitor : options.monitor <;> by_cases link : options.link <;>
    simp only [monitor, link, ↓reduceIte, Bool.false_eq_true, State.allocate]
  all_goals (repeat' first
    | refine State.Covers.same ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | refine State.Covers.monitor ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | refine State.Covers.modify ?_ fun _ live => ⟨live, fun ⟨counted, unmonitored⟩ =>
        ⟨Nat.le_succ_of_le counted, unmonitored⟩⟩
    | refine State.Covers.set_other ?_ child _
    | refine State.Covers.set ?_ found fun live => ⟨live, id⟩)
  all_goals first
    | exact covers
    | (intro same; subst same
       have counted := counted rfl
       rw [shape, Kernel.append_eq]
       intro equal
       have := List.append_inj_right' equal rfl
       simp [State.process, State.record_modify, State.record_set] at this
       omega)

end State.Covers

namespace State.Covers

variable {watcher : PID} {reference : List Nat} {count : Nat} {state : State}

private theorem linkPhase (covers : state.Covers watcher reference count) {processId target : PID} {next : State}
    (phase : state.linkPhase processId target = some next) : next.Covers watcher reference count := by
  unfold State.linkPhase at phase
  repeat' split at phase
  all_goals simp only [Option.some.injEq, reduceCtorEq] at phase
  subst phase
  rename_i process found _ _ _ _
  refine State.Covers.linkExit ?_ _ _ _
  exact covers.set found fun live => by simp_all

private theorem phase (covers : state.Covers watcher reference count) {processId : PID} {next : State}
    (phase : state.phase processId = some next) : next.Covers watcher reference count := by
  unfold State.phase at phase
  repeat' split at phase
  all_goals simp only [Option.some.injEq, reduceCtorEq] at phase
  all_goals subst phase
  · refine State.Covers.send ?_ _ _ _
    exact covers.set (by assumption) fun live => by simp_all
  · refine State.Covers.answer ?_ _ _
    exact covers.set (by assumption) fun live => by simp_all

private theorem commit (covers : state.Covers watcher reference count) : state.commit.Covers watcher reference count := by
  unfold State.commit; split <;> exact covers

private theorem fire (covers : state.Covers watcher reference count) (timer : Timer) :
    (state.fire timer).Covers watcher reference count :=
  (covers.timers _).enqueue _ _ _

private theorem normalize (covers : state.Covers watcher reference count) (sorted : state.Sorted) :
    state.normalize.Covers watcher reference count := by
  intro process found live
  rw [State.record_normalize' sorted] at found
  cases record : state.record watcher with
  | none => simp [record] at found
  | some original =>
    simp only [record, Option.map_some, Option.filter] at found
    split at found
    · cases found
      unfold normRecord at live ⊢
      split
      · rename_i exiting; rw [exiting] at live; simp at live
      · rename_i exiting; exact covers original record exiting
    · cases found

end State.Covers

private theorem Task.own_covers {state : State} {processId watcher : PID} {reference : List Nat} {count : Nat}
    {task : Task α} {transition : Transition α} (covers : state.Covers watcher reference count)
    (shape : reference = watcher ++ [count]) (unborn : state.Unborn) (present : (state.record watcher).isSome)
    (alive : state.alive processId = true) (mem : transition ∈ task.own state processId) :
    transition.state.Covers watcher reference count := by
  obtain ⟨process, found, live⟩ := State.alive_iff.mp alive
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
  cases computation with
  | ok value =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact covers.terminate found _
  | error exception =>
    cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;>
      first | exact covers.terminate found _ | exact covers.remove _
  | get next => simp only [Task.own, List.mem_singleton] at mem; subst mem; exact covers
  | set updated next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem
    exact covers.modify fun _ live => ⟨live, fun ⟨counted, unmonitored⟩ =>
      ⟨Nat.le_trans counted (Nat.le_max_left _ _), unmonitored⟩⟩
  | schedule options child next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem
    refine covers.spawnWith shape found live (fun same => ?_) _
    obtain ⟨_, record⟩ := Option.isSome_iff_exists.mp present
    exact unborn _ _ found live watcher present _ (Nat.lt_succ_self _)
      (by rw [← same, Kernel.append_eq]; exact List.prefix_refl _)
  | send destination message next =>
    simp only [Task.own, List.mem_singleton] at mem; subst mem; exact covers.send _ _ _
  | receive timeout select next =>
    simp only [Task.own] at mem
    repeat' split at mem
    all_goals simp only [List.mem_singleton, List.not_mem_nil] at mem
    all_goals subst mem
    · exact covers.same (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    all_goals exact covers
  | request query next =>
    have requested := covers.request shape found live next query
    simp only [Task.own] at mem
    split at mem <;> rename_i answer <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;>
      simp only [answer, Answer.state] at requested <;> exact requested

private theorem Task.handle_covers {state : State} {processId watcher : PID} {reference : List Nat} {count : Nat}
    {task : Task α} {transition : Transition α} (covers : state.Covers watcher reference count)
    (mem : transition ∈ task.handle state processId) : transition.state.Covers watcher reference count := by
  simp only [Task.handle] at mem
  split at mem
  · simp at mem
  · rename_i entry rest queue
    cases found : state.record processId with
    | none => simp [State.process, found] at queue
    | some process =>
    have processOf : state.process processId = process := by simp [State.process, found]
    have set : (state.set processId { state.process processId with queue := rest }).Covers watcher reference count := by
      rw [processOf]; exact covers.set found fun live => ⟨live, id⟩
    have found' : (state.set processId { state.process processId with queue := rest }).record processId =
        some { state.process processId with queue := rest } := by simp [State.record_set]
    have handled := set.handle processId (task.wait.map (·.1)) entry
    have recorded := State.Present.handle (state := state.set processId { state.process processId with queue := rest })
      (processId := processId) (by simp [State.Present, found']) processId (task.wait.map (·.1)) entry
    revert mem handled recorded
    generalize (state.set processId { state.process processId with queue := rest }).handle processId
      (task.wait.map (·.1)) entry = triple
    obtain ⟨handled, resumed, exits⟩ := triple
    intro mem covers' recorded
    dsimp only at mem covers' recorded
    split at mem
    · simp only [List.mem_singleton] at mem; subst mem
      obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp recorded
      exact covers'.terminate recorded _
    · split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> exact covers'

/-- A step from a configuration a run reaches keeps a watcher dropping a `DOWN`. -/
private theorem Config.covers_step {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key : Key} {event : Event} {middle : State}
    {tasks' : List (PID × Task α)} {finished' : Option (Except Exception α)} {watcher : PID}
    {reference : List Nat} {count : Nat}
    (reachable : (Config.running state tasks finished false).Reachable elapsed) (unborn : state.Unborn)
    (covers : state.Covers watcher reference count) (shape : reference = watcher ++ [count])
    (present : (state.record watcher).isSome)
    (step : (Config.running state tasks finished false).stepOf key = some (event, .running middle tasks' finished' false)) :
    middle.Covers watcher reference count := by
  have within : state.Within elapsed := reachable.1.1
  have tasked : ∀ {processId : PID} {task : Task α}, Kernel.lookup processId tasks = some task →
      state.alive processId = true := fun lookup => reachable.2.2.1 _ (mem_of_lookup lookup)
  cases key with
  | own processId =>
    obtain ⟨task, transition, lookup, head, next⟩ := Config.stepOf_own step
    split at next
    · cases next
    · simp only [Config.running.injEq] at next
      rw [next.1]
      exact (Task.own_covers covers shape unborn present (tasked lookup) (List.mem_of_head? head)).normalize
        (within.own (List.mem_of_head? head)).1
  | handle processId =>
    obtain ⟨task, transition, lookup, head, next⟩ := Config.stepOf_handle step
    split at next
    · cases next
    · simp only [Config.running.injEq] at next
      rw [next.1]
      exact (Task.handle_covers covers (List.mem_of_head? head)).normalize
        (within.handleStep (List.mem_of_head? head)).1
  | phase processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨next, phase, -, rfl, -⟩ := step
    exact (covers.phase phase).normalize (within.phase phase).1
  | link processId target =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨next, phase, -, rfl, -⟩ := step
    exact (covers.linkPhase phase).normalize (within.linkPhase phase).1
  | unpark processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨-, -, -, rfl, -⟩ := step
    exact (covers.unpark _).normalize (within.unpark _).1
  | fire reference' =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨timer, -, -, rfl, -⟩ := step
    exact (covers.fire _).normalize (within.fire _).1
  | commit =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq, Config.running.injEq] at step
    obtain ⟨update, -, -, rfl, -⟩ := step
    exact covers.commit.normalize within.commit.1

private theorem QueueChange.hidden {queue : List Entry → List Entry} {mailbox : List Term → List Term}
    {links : List (PID × Option Nat) → List (PID × Option Nat)} {entry : Entry} (change : QueueChange queue mailbox links)
    (linking : ∀ (rest : List Entry) (other : Entry), other.signal = .link →
      (other ∈ queue (entry :: rest) ↔ other ∈ entry :: rest)) :
    Hidden (Queued entry) (queueChange queue mailbox links) where
  exiting _ := rfl
  trapExit _ := rfl
  parked _ := rfl
  links := fun {process} ⟨⟨rest, queued⟩, _⟩ other link => by
    show other ∈ queue process.queue ↔ other ∈ process.queue
    rw [queued]; exact linking rest other link
  push := fun {process} other queued => by
    refine ⟨⟨(Heads.push queued.1 other).1, queued.2⟩, ?_⟩
    obtain ⟨⟨rest, nonempty⟩, -⟩ := queued
    have pushed := change.push (entries := process.queue) other (by rw [nonempty]; simp)
    simp only [queueChange, ProcessState.push, pushed]
  eagerExit := fun _ queued => ⟨queued, by simp only [queueChange, ProcessState.eagerExit, change.filtered]⟩
  unpark := fun queued => ⟨queued, rfl⟩

private theorem lookup_rewriteTask_head {processId : PID} {task : Task α} {more : List (PID × Task α)} :
    ∀ {tasks : List (PID × Task α)} {original : Task α}, Kernel.lookup processId tasks = some original →
      Kernel.lookup processId (rewriteTask processId (fun _ => (processId, task) :: more) tasks) = some task
  | [], _, found => by simp [Kernel.lookup_eq] at found
  | (key, task') :: rest, original, found => by
    simp only [Kernel.lookup_eq, List.lookup_cons] at found
    by_cases same : key = processId
    · subst same; simp [rewriteTask, Kernel.lookup_eq]
    · have differ : (processId == key) = false := by simp [Ne.symm same]
      simp only [differ] at found
      have := lookup_rewriteTask_head (task := task) (more := more) (by simpa [Kernel.lookup_eq] using found)
      simp only [Kernel.lookup_eq] at this
      simp [rewriteTask, same, Kernel.lookup_eq, List.lookup_cons, differ, this]

/-- Clearing the records and timers of states with the same elapsed times. -/
private theorem State.cleared {state state' : State} (elapsed : state'.elapsed = state.elapsed) :
    ({ elapsed := state'.elapsed } : State) = { elapsed := state.elapsed } := by
  cases state; cases state'; simp_all

/-- A forced handling of the oldest signal, a change of the queue, mailbox and
links, against the process's own step: the own step absorbs it when it ends the
process, and the forced handling closes the square otherwise. -/
private theorem Config.handle_own_square {elapsed : PID → Nat → Nat} {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {process : ProcessState} {task : Task α}
    {entry : Entry} {rest : List Entry} {queue : List Entry → List Entry} {mailbox : List Term → List Term}
    {links : List (PID × Option Nat) → List (PID × Option Nat)} {event' : Event} {middle : Config α}
    (reachable : (Config.running state tasks finished false).Reachable elapsed)
    (lookup : Kernel.lookup processId tasks = some task)
    (found : state.record processId = some process)
    (queued : process.queue = entry :: rest)
    (bound : ∀ id, entry.signal = .unlinkAck id → id ≤ process.unlinks) (change : QueueChange queue mailbox links)
    (linking : ∀ (rest : List Entry) (other : Entry), other.signal = .link →
      (other ∈ queue (entry :: rest) ↔ other ∈ entry :: rest))
    (requests : ∀ (rest : List Entry) (keep : Entry → Bool),
      (∀ entry, keep entry = true → (entry.signal matches .link | .monitor _ | .isAlive) = true) →
      Kernel.filter keep (queue (entry :: rest)) = Kernel.filter keep (entry :: rest))
    (exitLinks : ∀ entries : List (PID × Option Nat),
      Kernel.foldl (fun links (peer, unlinking) => if unlinking.isNone then insertPid peer links else links) []
        (links entries) =
      Kernel.foldl (fun links (peer, unlinking) => if unlinking.isNone then insertPid peer links else links) [] entries)
    (unlinked : ∀ target : PID, Kernel.lookup target process.links = some none →
      links (Kernel.map (fun link => if link.1 == target then (link.1, some (process.unlinks + 1)) else link)
        process.links) =
        Kernel.map (fun link => if link.1 == target then (link.1, some (process.unlinks + 1)) else link)
          (links process.links))
    (lookups : ∀ target : PID,
      (Kernel.lookup target (links process.links) == some none) = (Kernel.lookup target process.links == some none))
    (awaited : Kernel.any (queue process.queue)
        ((state.set processId (queueChange queue mailbox links process)).awaitedEntry processId) = true →
      Kernel.any process.queue (state.awaitedEntry processId) = true)
    (noMatch : ∀ {β : Type} (select : Term → Option β), selectMessage select process.mailbox = none →
      Kernel.any process.queue (state.awaitedEntry processId) = false →
      selectMessage select (mailbox process.mailbox) = none)
    (step' : (Config.running state tasks finished false).stepOf (.own processId) = some (event', middle))
    (atMiddle : ∀ (raw : State) (tasks₁ : List (PID × Task α)) (finished₁ : Option (Except Exception α))
      (process₁ : ProcessState), raw.Within elapsed →
      (Config.running raw.normalize tasks₁ finished₁ false).Reachable elapsed →
      (∃ task₁, Kernel.lookup processId tasks₁ = some task₁) → raw.record processId = some process₁ →
      Queued entry process₁ → process₁.exiting = none →
      ∃ event'', (Key.handle processId, event'', .running (raw.normalize.set processId
          (queueChange queue mailbox links (normRecord raw.gone processId process₁))).normalize tasks₁ finished₁ false,
          true) ∈ (Config.running raw.normalize tasks₁ finished₁ false).taggedSteps ∧
        normRecord raw.gone processId (queueChange queue mailbox links (normRecord raw.gone processId process₁)) =
          normRecord raw.gone processId (queueChange queue mailbox links process₁)) :
    (∃ absorbed, (Config.running (state.set processId (queueChange queue mailbox links process)) tasks finished
        false).stepOf (.own processId) = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        (Config.running (state.set processId (queueChange queue mailbox links process)) tasks finished false).stepOf
          (.own processId) = some (other, last) := by
  have within := reachable.1.1
  let change' := queueChange queue mailbox links
  have changed : state.Changed processId (Same (Queued entry) change') (state.set processId (change' process)) :=
    ⟨fun other differ => by rw [State.record_set, ite_eq_right differ],
      by rw [State.record_set, ite_eq_left rfl, found]; exact .some ⟨⟨⟨rest, queued⟩, bound⟩, rfl⟩, rfl, rfl, rfl⟩
  have unseen := change.unseen linking
  have within' : (state.set processId (change' process)).Within elapsed := within.set _ _
  have fresh : Kernel.append processId [process.children + 1] ≠ processId := by
    simp
  obtain ⟨task₀, transition, lookup₀, head, rfl⟩ := Config.stepOf_own step'
  rw [lookup] at lookup₀; cases lookup₀
  obtain ⟨transition', head', event₁, tasks₁, finished₁, exhausted₁, related⟩ :=
    changed.ownSelf unseen change found unlinked lookups awaited noMatch fresh head
  have stepped := Config.stepOf_own_of (state := state.set processId (change' process)) (finished := finished) lookup
    head'
  rw [event₁, tasks₁, finished₁, exhausted₁] at stepped
  have sortedOwn := within.own (List.mem_of_head? head)
  have sortedOwn' := within'.own (List.mem_of_head? head')
  by_cases exhausted : transition.exhausted = true
  · left
    refine ⟨transition.event, ?_⟩
    rw [stepped]
    simp only [exhausted, ↓reduceIte, State.cleared (sortedOwn'.2.trans sortedOwn.2.symm)]
  simp only [exhausted, Bool.false_eq_true, ↓reduceIte] at stepped step' ⊢
  rcases related with ⟨changedRaw, task₁, more, continues⟩ | ⟨reason, ended, ended'⟩ | exhausted'
  · right
    have reachableMiddle := reachable.step (Config.step_of_stepOf step')
    have lookupMiddle : Kernel.lookup processId (rewriteTask processId (fun _ => transition.tasks) tasks) =
        some task₁ := by
      rw [continues]; exact lookup_rewriteTask_head lookup
    have alive := reachableMiddle.2.2.1 _ (mem_of_lookup lookupMiddle)
    rw [State.alive_normalize sortedOwn.1] at alive
    obtain ⟨process₁, found₁, live₁⟩ := State.alive_iff.mp alive
    have queued₁ : Queued entry process₁ := by
      rcases changedRaw.records with ⟨missing, -⟩ | ⟨first, second, found₂, -, ok₁, -⟩
      · rw [found₁] at missing; cases missing
      · rw [found₁] at found₂; cases found₂; exact ok₁
    obtain ⟨event'', mem, renormalized⟩ := atMiddle transition.state _ _ process₁ sortedOwn reachableMiddle
      ⟨_, lookupMiddle⟩ found₁ queued₁ live₁
    have forcedChanged := changedRaw.forced_of_same (fun _ found₂ => by
      rw [found₁] at found₂; cases found₂; exact live₁) (fun _ => rfl)
    have liveNormal : (normRecord transition.state.gone processId process₁).exiting = none := by
      rw [normRecord_live live₁]; exact live₁
    rw [State.forced_close sortedOwn.1 sortedOwn'.1 forcedChanged (change.hidden linking).unseen found₁ liveNormal
      renormalized] at mem
    exact ⟨.handle processId, event'', _, transition.event, mem, stepped⟩
  · left
    refine ⟨transition.event, ?_⟩
    rw [stepped, ended, ended']
    have sortedEnded := ended ▸ sortedOwn
    have sortedEnded' := ended' ▸ sortedOwn'
    rw [State.Changes.terminateQueue changed change requests exitLinks reason within.1 within'.1 sortedEnded.1
      sortedEnded'.1]
  · exact absurd exhausted' exhausted

private theorem messageChange_queue (message : Term) :
    QueueChange List.tail (fun messages => Kernel.append messages [message]) id where
  push := fun {entries} other nonempty => by
    cases entries with
    | nil => exact absurd rfl nonempty
    | cons head rest => simp [Kernel.append_eq]
  filtered _ _ := rfl
  relink _ _ := rfl
  select := by
    intro β select messages remaining selected value found
    exact selectMessage_append found

/-- The links after handling an acknowledgement of an unlink. -/
private def ackLinks (source : PID) (id : Nat) (links : List (PID × Option Nat)) : List (PID × Option Nat) :=
  if Kernel.lookup source links == some (some id) then Kernel.filter (unacked source id) links else links

private theorem ackChange_eq (source : PID) (id : Nat) (process : ProcessState) :
    ackChange source id process = queueChange List.tail _root_.id (ackLinks source id) process := by
  unfold ackChange ackedChange popChange queueChange ackLinks
  split <;> rfl

private theorem lookup_unacked_other {source target : PID} (differ : target ≠ source) (id : Nat) :
    ∀ links : List (PID × Option Nat), Kernel.lookup target (Kernel.filter (unacked source id) links) =
      Kernel.lookup target links := by
  intro links
  simp only [Kernel.lookup_eq, Kernel.filter_eq]
  exact lookup_filter_of_keep fun link _ same => by simp [unacked, same, differ]

private theorem ackLinks_queue (source : PID) (id : Nat) :
    QueueChange List.tail _root_.id (ackLinks source id) where
  push := fun {entries} other nonempty => by
    cases entries with
    | nil => exact absurd rfl nonempty
    | cons head rest => simp [Kernel.append_eq]
  filtered target links := by
    unfold ackLinks
    by_cases same : target = source
    · subst same
      have none : Kernel.lookup target (Kernel.filter (·.1 != target) links) = none := lookup_filter_self _ _
      simp only [none, reduceCtorEq, beq_iff_eq, ↓reduceIte]
      split
      · simp only [Kernel.filter_eq, List.filter_filter]
        refine List.filter_congr fun link _ => ?_
        by_cases key : link.1 = target <;> simp [unacked, key]
      · rfl
    · have kept : Kernel.lookup source (Kernel.filter (·.1 != target) links) = Kernel.lookup source links := by
        simp only [Kernel.lookup_eq, Kernel.filter_eq]
        exact lookup_filter_of_keep fun link _ equal => by simp [equal, Ne.symm same]
      rw [kept]
      split
      · simp only [Kernel.filter_eq, List.filter_filter, Bool.and_comm]
      · rfl
  relink target links := by
    unfold ackLinks
    by_cases same : target = source
    · subst same
      have relinked : Kernel.lookup target (Kernel.append (Kernel.filter (·.1 != target) links) [(target, none)]) =
          some none := by
        have none : Kernel.lookup target (Kernel.filter (·.1 != target) links) = none := lookup_filter_self _ _
        simp only [Kernel.lookup_eq, Kernel.append_eq, Kernel.filter_eq] at none ⊢
        rw [List.lookup_append, none]; simp
      simp only [relinked, reduceCtorEq, beq_iff_eq, Option.some.injEq, ↓reduceIte]
      split
      · congr 1
        simp only [Kernel.filter_eq, List.filter_filter]
        refine List.filter_congr fun link _ => ?_
        by_cases key : link.1 = target <;> simp [unacked, key]
      · rfl
    · have kept : Kernel.lookup source (Kernel.append (Kernel.filter (·.1 != target) links) [(target, none)]) =
          Kernel.lookup source links := by
        simp only [Kernel.lookup_eq, Kernel.append_eq, Kernel.filter_eq]
        rw [List.lookup_append]
        rw [lookup_filter_of_keep fun link _ equal => by simp [equal, Ne.symm same]]
        cases found : List.lookup source links with
        | some _ => rfl
        | none =>
          have differ : (source == target) = false := by simp [Ne.symm same]
          simp [List.lookup_cons, differ]
      rw [kept]
      split
      · simp only [Kernel.filter_eq, Kernel.append_eq, List.filter_append, List.filter_filter, Bool.and_comm]
        simp [unacked]
      · rfl
  select := by
    intro β select messages remaining selected value found
    exact found

private theorem ackChange_clean {gone : PID → Bool} {processId source : PID} {id : Nat} {process : ProcessState}
    (clean : normRecord gone processId process = process) (live : process.exiting = none) :
    normRecord gone processId (ackChange source id process) = ackChange source id process := by
  have cleaned := clean_live clean live
  have live' : (ackChange source id process).exiting = none := (ackChange_fields source id process).1.trans live
  rw [normRecord_live live', inert_ack]
  have keepLinks : ∀ links : List (PID × Option Nat), (∀ link ∈ links, link ∈ process.links) →
      Kernel.filter (fun link => !(link.2.isSome && gone link.1)) links = links := fun links sub => by
    rw [Kernel.filter_eq]; exact List.filter_eq_self.mpr fun link mem => by simp [cleaned.2 link (sub link mem)]
  have keepQueue : Kernel.filter (fun entry => !inert gone processId process entry) process.queue.tail =
      process.queue.tail := by
    rw [Kernel.filter_eq]
    exact List.filter_eq_self.mpr fun entry mem => by simp [cleaned.1 entry (List.mem_of_mem_tail mem)]
  have keepMonitors : Kernel.filter (fun monitor => !gone monitor.2) process.monitors = process.monitors := by
    rw [Kernel.filter_eq]
    exact List.filter_eq_self.mpr fun monitor mem => by simp [clean_monitors clean live monitor mem]
  unfold ackChange ackedChange popChange
  split
  · rw [keepLinks _ fun link mem => by
        simp only [Kernel.filter_eq, List.mem_filter] at mem; exact mem.1]
    simp only [keepQueue, keepMonitors]
  · simp only [keepQueue, keepMonitors, keepLinks _ fun _ mem => mem]

/-- Exit links skip the link being removed. -/
private theorem exitLinks_unacked (source : PID) (id : Nat) :
    ∀ (links : List (PID × Option Nat)) (start : List PID),
      Kernel.foldl (fun links (peer, unlinking) => if unlinking.isNone then insertPid peer links else links) start
        (Kernel.filter (unacked source id) links) =
      Kernel.foldl (fun links (peer, unlinking) => if unlinking.isNone then insertPid peer links else links) start links
  | [], _ => rfl
  | (peer, unlinking) :: rest, start => by
    have ih := exitLinks_unacked source id rest
    simp only [Kernel.foldl_eq, Kernel.filter_eq] at ih ⊢
    by_cases kept : unacked source id (peer, unlinking) = true
    · simp only [List.filter_cons, kept, ↓reduceIte, List.foldl_cons]; exact ih _
    · have removed : peer = source ∧ unlinking = some id := by
        cases h₁ : peer == source <;> cases h₂ : unlinking == some id <;> simp_all [unacked]
      obtain ⟨rfl, rfl⟩ := removed
      simp only [List.filter_cons, unacked, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.foldl_cons, Option.isNone_some]
      exact ih start

/-- Marking a link being removed changes only its value. -/
private theorem lookup_unlinking {target : PID} {id : Nat} :
    ∀ (links : List (PID × Option Nat)) (other : PID),
      Kernel.lookup other (Kernel.map (fun link => if link.1 == target then (link.1, some id) else link) links) =
        if other = target then (Kernel.lookup other links).map fun _ => some id else Kernel.lookup other links
  | [], _ => by simp [Kernel.lookup_eq, Kernel.map_eq]
  | (peer, value) :: rest, other => by
    have ih := lookup_unlinking (target := target) (id := id) rest other
    simp only [Kernel.lookup_eq, Kernel.map_eq] at ih ⊢
    rw [List.map_cons]
    by_cases equal : peer = target
    · subst equal
      rw [ite_eq_left (by simp), List.lookup_cons, List.lookup_cons]
      by_cases same : other = peer
      · subst same; simp
      · have differ : (other == peer) = false := by simp [same]
        rw [differ]; simp only [same, ↓reduceIte] at ih ⊢; exact ih
    · rw [ite_eq_right (by simp [equal]), List.lookup_cons, List.lookup_cons]
      by_cases same : other = peer
      · subst same
        have differ : other ≠ target := equal
        simp [differ]
      · have differ : (other == peer) = false := by simp [same]
        rw [differ]; exact ih

private theorem lookup_none_of_not_mem {β : Type} {key : PID} :
    ∀ {entries : List (PID × β)}, key ∉ entries.map (·.1) → entries.lookup key = none
  | [], _ => rfl
  | (other, value) :: rest, missing => by
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    have differ : (key == other) = false := by simp [missing.1]
    simp [List.lookup_cons, differ, lookup_none_of_not_mem missing.2]

/-- Removing the only link with a process leaves none. -/
private theorem lookup_unacked_self {source : PID} {id : Nat} :
    ∀ {links : List (PID × Option Nat)}, (links.map (·.1)).Nodup →
      Kernel.lookup source links = some (some id) → Kernel.lookup source (Kernel.filter (unacked source id) links) = none
  | [], _, found => by simp [Kernel.lookup_eq] at found
  | (peer, value) :: rest, nodup, found => by
    simp only [List.map_cons, List.nodup_cons] at nodup
    simp only [Kernel.lookup_eq, Kernel.filter_eq, List.lookup_cons] at found ⊢
    by_cases same : source = peer
    · subst same
      simp only [beq_self_eq_true, Option.some.injEq] at found
      subst found
      simp only [List.filter_cons, unacked, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
      refine lookup_none_of_not_mem fun mem => nodup.1 ?_
      simp only [List.mem_map, List.mem_filter] at mem ⊢
      obtain ⟨link, ⟨inside, -⟩, same⟩ := mem
      exact ⟨link, inside, same⟩
    · have differ : (source == peer) = false := by simp [same]
      simp only [differ] at found
      have unacked' : unacked source id (peer, value) = true := by simp [unacked, Ne.symm same]
      simp only [List.filter_cons, unacked', ↓reduceIte, List.lookup_cons, differ]
      have := lookup_unacked_self (source := source) (id := id) nodup.2 (by simpa [Kernel.lookup_eq] using found)
      simpa [Kernel.lookup_eq, Kernel.filter_eq] using this

/-- A forced handling of the oldest signal against the process's own step. -/
private theorem Config.forced_handle_own {elapsed : PID → Nat → Nat} {config : Config α} {processId : PID}
    {event event' : Event} {next middle : Config α} (reachable : config.Reachable elapsed) (distinct : config.Distinct)
    (forced : (Key.handle processId, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf (.own processId) = some (event', middle)) :
    (∃ absorbed, next.stepOf (.own processId) = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf (.own processId) = some (other, last) := by
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running forced
  have step := reachable.stepOf forced
  obtain ⟨task, transition, lookup, head, -⟩ := Config.stepOf_handle step
  have flagged := Config.forced_handle reachable.2.1 lookup forced
  rw [Config.stepOf_handle_of (finished := finished) lookup head] at step
  simp only [Option.some.injEq, Prod.mk.injEq] at step
  obtain ⟨rfl, rfl⟩ := step
  have sorted := reachable.1.1.1
  have normalized := reachable.1.2.1
  have alive := reachable.2.2.1 _ (mem_of_lookup lookup)
  obtain ⟨process, found, live⟩ := State.alive_iff.mp alive
  have clean := (Clean.of_normalized sorted normalized found).1
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
  -- A process waiting for a reply or marker takes no own step.
  have running : task.wait = none := by
    obtain ⟨task₀, own, lookup₀, head₀, -⟩ := Config.stepOf_own step'
    rw [lookup] at lookup₀; cases lookup₀
    obtain ⟨computation, finish, wait⟩ := task
    cases wait with
    | none => rfl
    | some => simp [Task.own] at head₀
  have notBlocked : task.blocked state processId = false := by
    obtain ⟨task₀, own, lookup₀, head₀, -⟩ := Config.stepOf_own step'
    rw [lookup] at lookup₀; cases lookup₀
    cases blocked : task.blocked state processId
    · rfl
    · simp [Task.own_of_blocked blocked] at head₀
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | message message =>
    have fromProcess : (source != clock) = true := by simpa [Task.forcedHead, notInert, notBlocked] using flagged
    have notClock : source ≠ clock := by simpa using fromProcess
    rw [Task.handle_message sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    have changed : messageChange message process =
        queueChange List.tail (fun messages => Kernel.append messages [message]) id process := rfl
    rw [rewriteTask_same lookup, State.normalize_set_clean (process' := messageChange message process) sorted
      normalized found live live (normRecord_popped clean live (by simp [messageChange]) (fun _ => rfl) rfl (fun monitor mem => clean_monitors clean live monitor mem) live),
      changed]
    refine Config.handle_own_square reachable lookup found queue (fun _ signal => by cases signal)
      (messageChange_queue message) ?_ ?_
      (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) ?_ ?_ step' ?_
    · intro rest' other link
      simp only [List.tail_cons, List.mem_cons]
      constructor
      · exact .inr
      · rintro (same | inside)
        · subst same; cases link
        · exact inside
    · intro rest' keep requests'
      simp only [List.tail_cons, Kernel.filter_eq, List.filter_cons]
      cases kept : keep ⟨source, .message message⟩
      · rfl
      · simpa using requests' _ kept
    · intro _
      simp only [Kernel.any_eq, List.any_eq_true]
      exact ⟨⟨source, .message message⟩, by simp [queue], by simp [State.awaitedEntry, notInert, notClock]⟩
    · intro _ _ _ quiet
      simp only [Kernel.any_eq, List.any_eq_false] at quiet
      exact absurd (quiet ⟨source, .message message⟩ (by simp [queue]))
        (by simp [State.awaitedEntry, notInert, notClock])
    · intro raw tasks₁ finished₁ process₁ within reachable₁ ⟨task₁, lookup₁⟩ found₁ heads₁ live₁
      obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁.1 (by simp [inert])
      have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
        simp [State.process, record]
      have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1
        lookup₁ (by rw [processOf₁, queue₁])
        (transition := Transition.mk (.handle processId ⟨source, .message message⟩)
          (raw.normalize.set processId (messageChange message (normRecord raw.gone processId process₁)))
          [(processId, task₁)] none false)
        (by rw [Task.handle_message (Sorted.normalize within.1) record queue₁]; rfl)
        (by simp only [Task.forcedHead, fromProcess, Bool.true_or, Bool.or_true])
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none, rewriteTask_same lookup₁] at tagged
      exact ⟨_, tagged, normRecord_message live₁ heads₁.1 (by simp [inert]) message⟩
  | unlinkAck id =>
    have bound : id ≤ process.unlinks := by simpa [Task.forcedHead, notInert, processOf] using flagged
    rw [Task.handle_ack sorted found queue] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none]
    rw [rewriteTask_same lookup, State.normalize_set_clean (process' := ackChange source id process) sorted
      normalized found live ((ackChange_fields source id process).1.trans live) (ackChange_clean clean live),
      ackChange_eq]
    have nodup : (process.links.map (·.1)).Nodup := distinct _ _ found
    refine Config.handle_own_square reachable lookup found queue (fun _ signal => by cases signal; exact bound)
      (ackLinks_queue source id) ?_ ?_ ?_ ?_ ?_ ?_ (fun _ selected _ => selected) step' ?_
    · intro rest' other link
      simp only [List.tail_cons, List.mem_cons]
      constructor
      · exact .inr
      · rintro (same | inside)
        · subst same; cases link
        · exact inside
    · intro rest' keep requests'
      simp only [List.tail_cons, Kernel.filter_eq, List.filter_cons]
      cases kept : keep ⟨source, .unlinkAck id⟩
      · rfl
      · simpa using requests' _ kept
    · intro links
      unfold ackLinks; split
      · exact exitLinks_unacked source id links []
      · rfl
    · -- A process unlinks with a new id, which no acknowledgement it has carries.
      intro target unlinked'
      unfold ackLinks
      have mapped := lookup_unlinking (target := target) (id := process.unlinks + 1) process.links source
      by_cases same : source = target
      · subst same
        rw [ite_eq_left rfl, unlinked'] at mapped
        rw [mapped, unlinked']
        have fresh : process.unlinks + 1 ≠ id := by omega
        simp [fresh]
      · rw [ite_eq_right same] at mapped
        rw [mapped]
        split
        · simp only [Kernel.filter_eq, Kernel.map_eq, List.filter_map]
          congr 1
          refine List.filter_congr fun link _ => ?_
          simp only [Function.comp]
          split
          · rename_i key
            simp only [beq_iff_eq] at key
            have differ : (target == source) = false := by simp [Ne.symm same]
            simp [unacked, key, differ]
          · rfl
        · rfl
    · intro target
      unfold ackLinks
      split
      · rename_i linked
        by_cases same : target = source
        · subst same
          have found' : Kernel.lookup target process.links = some (some id) := by simpa using linked
          rw [lookup_unacked_self nodup found', found']
          rfl
        · rw [lookup_unacked_other same]
      · rfl
    · intro more
      simp only [Kernel.any_eq, List.any_eq_true] at more ⊢
      obtain ⟨other, inside, awaited'⟩ := more
      refine ⟨other, List.mem_of_mem_tail (by simpa [queueChange] using inside), ?_⟩
      have gone : (state.set processId (queueChange List.tail _root_.id (ackLinks source id) process)).gone =
          state.gone := by
        funext peer
        simp only [State.gone, State.alive, State.record_set]
        by_cases equal : peer = processId
        · subst equal; simp [found, queueChange]
        · simp [equal]
      have processSet : (state.set processId (queueChange List.tail _root_.id (ackLinks source id) process)).process
          processId = queueChange List.tail _root_.id (ackLinks source id) process := by
        simp [State.process, State.record_set]
      simp only [State.awaitedEntry, State.inertEntry_eq, gone, processSet] at awaited' ⊢
      rw [processOf]
      exact awaited'
    · intro raw tasks₁ finished₁ process₁ within reachable₁ ⟨task₁, lookup₁⟩ found₁ ⟨heads₁, bound₁⟩ live₁
      have kept : inert raw.gone processId process₁ ⟨source, .unlinkAck id⟩ = false := by simp [inert]
      obtain ⟨record, rest₁, queue₁⟩ := State.normalize_heads within.1 found₁ live₁ heads₁ kept
      have processOf₁ : raw.normalize.process processId = normRecord raw.gone processId process₁ := by
        simp [State.process, record]
      have tagged := Config.tagged_handle_forced (state := raw.normalize) (finished := finished₁) reachable₁.2.1
        lookup₁ (by rw [processOf₁, queue₁])
        (transition := Transition.mk (.handle processId ⟨source, .unlinkAck id⟩)
          (raw.normalize.set processId (ackChange source id (normRecord raw.gone processId process₁)))
          [(processId, task₁)] none false)
        (by rw [Task.handle_ack (Sorted.normalize within.1) record queue₁]; rfl)
        (by simp [Task.forcedHead, processOf₁, normRecord_live live₁, bound₁ id rfl])
      simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_none, rewriteTask_same lookup₁, ackChange_eq]
        at tagged
      refine ⟨_, tagged, ?_⟩
      rw [← ackChange_eq, ← ackChange_eq]
      exact normRecord_ack_kept live₁ heads₁
  | reply value =>
    simp [Task.forcedHead, notInert, running] at flagged
  | flush =>
    simp [Task.forcedHead, notInert, running] at flagged
  | _ => simp [Task.forcedHead, notInert, notBlocked] at flagged

/-- Only own steps, handling and phases are forced. -/
private theorem Config.forced_keys {config : Config α} {key : Key} {event : Event} {next : Config α}
    (forced : (key, event, next, true) ∈ config.taggedSteps) :
    (∃ processId, key = .own processId) ∨ (∃ processId, key = .handle processId) ∨
      ∃ processId, key = .phase processId := by
  match config with
  | .start .. => simp [Config.taggedSteps] at forced
  | .running _ _ _ true => simp [Config.taggedSteps] at forced
  | .running state tasks finished false =>
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.mk.injEq] at forced
  rcases forced with ((((⟨⟨before, ⟨other, task⟩, after⟩, split, own | handle⟩ | ⟨⟨other, _⟩, -, link | phase⟩) |
    ⟨⟨other, _⟩, -, unpark⟩) | ⟨timer, firing, key, -, -, flag⟩) | ⟨update, -, key, -, -, flag⟩)
  · obtain ⟨transition, -, rfl, -⟩ := own; exact .inl ⟨_, rfl⟩
  · obtain ⟨transition, -, rfl, -⟩ := handle; exact .inr (.inl ⟨_, rfl⟩)
  · obtain ⟨target, -, found⟩ := link
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨_, _, -, -, -, flag⟩ := found; cases flag
  · split at phase
    · simp only [List.mem_singleton, Prod.mk.injEq] at phase
      obtain ⟨rfl, -⟩ := phase; exact .inr (.inr ⟨_, rfl⟩)
    · simp at phase
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at unpark
    obtain ⟨_, _, -, -, -, flag⟩ := unpark; cases flag
  · cases flag
  · cases flag

/-! ### Forced phases against steps of other keys

A process that ended sends a `DOWN` its watcher drops, then normalization drops
it, so the phase only removes the `DOWN` from the record, or the record once
nothing is left. Other steps neither read nor change that record. -/

/-- A record that ended, after it sent its next `DOWN`. -/
private def popDown (process : ProcessState) : ProcessState :=
  { process with exiting := process.exiting.map fun exiting => { exiting with downs := exiting.downs.tail } }

private theorem normRecord_popDown_kept {gone : PID → Bool} {processId : PID} {process : ProcessState}
    {exiting : Exiting} {down : List Nat × PID} {rest : List (List Nat × PID)}
    (ended : process.exiting = some exiting) (downs : exiting.downs = down :: rest) (kept : gone down.2 = false) :
    normRecord gone processId (popDown process) = popDown (normRecord gone processId process) := by
  obtain ⟨reason, links, downs'⟩ := exiting
  simp only at downs; subst downs
  simp [normRecord, popDown, ended, Kernel.filter_eq, kept]

private theorem normRecord_popDown_gone {gone : PID → Bool} {processId : PID} {process : ProcessState}
    {exiting : Exiting} {down : List Nat × PID} {rest : List (List Nat × PID)}
    (ended : process.exiting = some exiting) (downs : exiting.downs = down :: rest) (dropped : gone down.2 = true) :
    normRecord gone processId (popDown process) = normRecord gone processId process := by
  obtain ⟨reason, links, downs'⟩ := exiting
  simp only at downs; subst downs
  simp [normRecord, popDown, ended, Kernel.filter_eq, dropped]

/-- What a clean record of a process that ended holds besides its queue, children and exiting. -/
private theorem Clean.ended {gone : PID → Bool} {processId : PID} {process : ProcessState} {exiting : Exiting}
    (clean : Clean gone processId process) (ended : process.exiting = some exiting) :
    process.trapExit = false ∧ process.parked = none ∧
      Kernel.filter (fun down => !gone down.2) exiting.downs = exiting.downs := by
  have equal := clean.1
  unfold normRecord at equal
  rw [ended] at equal
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg ProcessState.trapExit equal; simp at this; first | exact this | exact this.symm
  · have := congrArg ProcessState.parked equal; simp at this; first | exact this | exact this.symm
  · have := congrArg ProcessState.exiting equal
    rw [ended] at this
    simp only [Option.some.injEq] at this
    exact congrArg Exiting.downs this

/-- Queuing a signal a live process drops is undone by normalizing. -/
private theorem State.normalize_push_inert {state : State} (sorted : state.Sorted) {processId : PID}
    {process : ProcessState} (found : state.record processId = some process) (live : process.exiting = none)
    {entry : Entry} (dropped : inert state.gone processId process entry = true) :
    (state.set processId { process with queue := Kernel.append process.queue [entry] }).normalize = state.normalize := by
  have gone : (state.set processId { process with queue := Kernel.append process.queue [entry] }).gone = state.gone := by
    funext other
    by_cases same : other = processId
    · subst same; simp [State.gone, State.alive, State.record_set, found, live]
    · simp [State.gone, State.alive, State.record_set, same]
  have sorted' : (state.set processId { process with queue := Kernel.append process.queue [entry] }).Sorted :=
    Lynx.Concurrent.Sorted.insertRecord sorted processId _
  refine State.ext_records (Sorted.normalize sorted) (Sorted.normalize sorted') (fun other => ?_) rfl rfl rfl
  rw [State.record_normalize' sorted', State.record_normalize' sorted, gone, State.record_set]
  split
  · rename_i same; subst same
    rw [found]
    simp only [Option.map_some]
    have live' : ({ process with queue := Kernel.append process.queue [entry] } : ProcessState).exiting = none := live
    rw [normRecord_live live, normRecord_live live']
    have same : inert state.gone other { process with queue := Kernel.append process.queue [entry] } =
        inert state.gone other process := funext fun _ => rfl
    rw [same]
    simp [Kernel.filter_eq, Kernel.append_eq, List.filter_append, dropped]
  · rfl

/-- The phase sending a `DOWN` its live watcher drops, normalized, only removes it from the record. -/
private theorem State.phase_drops {state : State} (sorted : state.Sorted) {processId watcher : PID}
    {process watcherProcess : ProcessState} {exiting : Exiting} {reference : List Nat}
    {rest : List (List Nat × PID)} {next : State}
    (found : state.record processId = some process) (ended : process.exiting = some exiting)
    (links : exiting.links = []) (downs : exiting.downs = (reference, watcher) :: rest)
    (parked : process.parked = none)
    (foundWatcher : state.record watcher = some watcherProcess) (live : watcherProcess.exiting = none)
    (dropped : state.inertEntry watcher { source := processId, signal := .down reference exiting.reason } = true)
    (phase : state.phase processId = some next) :
    next.normalize = (state.set processId (popDown process)).normalize := by
  have differ : watcher ≠ processId := fun same => by
    subst same; rw [found] at foundWatcher; cases foundWatcher; rw [ended] at live; cases live
  simp only [State.phase, found, ended, links, downs, Option.some.injEq] at phase
  subst phase
  have popped : { process with exiting := some { reason := exiting.reason, links := [], downs := rest } } =
      popDown process := by
    obtain ⟨reason, links', downs'⟩ := exiting
    simp only at links downs; subst links downs
    simp [popDown, ended]
  rw [popped]
  have base : (state.set processId (popDown process)).Sorted :=
    Lynx.Concurrent.Sorted.insertRecord sorted processId (popDown process)
  have parked' : ((state.set processId (popDown process)).process processId).parked = none := by
    simp [State.process, State.record_set, popDown, parked]
  have watched : (state.set processId (popDown process)).record watcher = some watcherProcess := by
    rw [State.record_set, ite_eq_right differ, foundWatcher]
  unfold State.send
  rw [parked']
  dsimp only
  unfold State.enqueue
  rw [watched]
  dsimp only
  rw [ite_eq_left (by simp [live])]
  refine State.normalize_push_inert base watched live ?_
  rw [State.inertEntry_eq] at dropped
  have gone : (state.set processId (popDown process)).gone = state.gone := by
    funext other
    by_cases same : other = processId
    · subst same; simp [State.gone, State.alive, State.record_set, found, popDown, ended]
    · simp [State.gone, State.alive, State.record_set, same]
  have processOf : state.process watcher = watcherProcess := by simp [State.process, foundWatcher]
  rw [gone]; rw [processOf] at dropped; exact dropped

private theorem rewriteTask_missing {processId : PID} {change : Task α → List (PID × Task α)} :
    ∀ {tasks : List (PID × Task α)}, Kernel.lookup processId tasks = none → rewriteTask processId change tasks = tasks
  | [], _ => rfl
  | (other, task) :: rest, missing => by
    have differ : other ≠ processId := fun same => by
      subst same; simp [Kernel.lookup_eq] at missing
    have missing' : Kernel.lookup processId rest = none := by
      have differ' : (processId == other) = false := by simp [Ne.symm differ]
      simpa [Kernel.lookup_eq, List.lookup_cons, differ'] using missing
    simp [rewriteTask, differ, rewriteTask_missing missing']

/-- A record that ended and has nothing left keeps nothing when normalized. -/
private theorem finished_normRecord {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (finished : process.finished = true) : (normRecord gone processId process).finished = true := by
  unfold ProcessState.finished at finished
  split at finished
  · rename_i reason exiting ended
    simp only [List.isEmpty_iff] at finished
    simp [normRecord, ended, finished, ProcessState.finished, Kernel.filter_eq]
  · cases finished

/-- The phase of a process that has a record, tagged with whether it is forced. -/
private theorem Config.tagged_phase {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {process : ProcessState} {next : State}
    (found : state.record processId = some process) (phase : state.phase processId = some next) :
    (Key.phase processId, Event.phase processId, Config.running next.normalize tasks finished false,
      state.dropsDown processId) ∈ (Config.running state tasks finished false).taggedSteps := by
  simp only [Config.taggedSteps, Kernel.append_eq, Kernel.flatMap_eq, List.mem_append, List.mem_flatMap]
  refine .inl (.inl (.inl (.inr ⟨(processId, process), ?_, ?_⟩)))
  · exact mem_of_lookup found
  · simp [phase]

private theorem dropLast_append_of_getLast? : ∀ {l : List Nat} {a : Nat}, l.getLast? = some a → l.dropLast ++ [a] = l
  | [], _, h => by simp at h
  | [b], _, h => by simp at h; simp [h]
  | b :: c :: rest, a, h => by
    have ih := dropLast_append_of_getLast? (l := c :: rest) (a := a) (by simpa [List.getLast?_cons_cons] using h)
    simp only [List.dropLast_cons_cons, List.cons_append, ih]

/-- A forced phase, a `DOWN` its watcher drops, against any other step. -/
private theorem Config.forced_phase_square {elapsed : PID → Nat → Nat} {config : Config α} {processId : PID}
    {key' : Key} {event event' : Event} {next middle : Config α} (reachable : config.Reachable elapsed)
    (unborn : config.Unborn) (forced : (Key.phase processId, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf key' = some (event', middle)) (differ : key' ≠ .phase processId) :
    (∃ absorbed, next.stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf key' = some (other, last) := by
  obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running forced
  have reachable₀ := reachable
  obtain ⟨⟨within, normalized, -⟩, fresh⟩ := reachable
  have unborn : state.Unborn := unborn
  have flag := Config.forced_phase forced
  have stepped := reachable₀.stepOf forced
  simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at stepped
  obtain ⟨phased, phase, -, rfl⟩ := stepped
  -- The process ended, signaled its links, and sends a `DOWN` its watcher drops.
  cases record : state.record processId with
  | none => simp [State.phase, record] at phase
  | some process =>
  have processOf : state.process processId = process := by simp [State.process, record]
  unfold State.dropsDown at flag
  rw [processOf] at flag
  cases ended : process.exiting with
  | none => simp [ended] at flag
  | some exiting =>
  obtain ⟨reason, links, downs⟩ := exiting
  cases links with
  | cons => simp [ended] at flag
  | nil =>
  cases downs with
  | nil => simp [ended] at flag
  | cons down rest =>
  obtain ⟨reference, watcher⟩ := down
  simp only [ended] at flag
  have clean := Clean.of_normalized within.1 normalized record
  obtain ⟨trapped, parked, keptDowns⟩ := clean.ended ended
  have watcherKept : state.gone watcher = false := by
    have mem : (reference, watcher) ∈ Kernel.filter (fun down => !state.gone down.2)
        ((reference, watcher) :: rest) := by rw [keptDowns]; exact List.mem_cons_self
    simp only [Kernel.filter_eq, List.mem_filter, Bool.not_eq_true'] at mem
    exact mem.2
  obtain ⟨watcherProcess, foundWatcher, watcherLive⟩ :=
    State.alive_iff.mp (by simpa [State.gone] using watcherKept)
  have watcherOf : state.process watcher = watcherProcess := by simp [State.process, foundWatcher]
  have dropped : state.inertEntry watcher { source := processId, signal := .down reference reason } = true := by
    simpa [State.keepEntry, watcherOf, watcherLive] using flag
  -- The reference the watcher allocated, which it no longer monitors.
  have allocated := dropped
  simp only [State.inertEntry, State.allocated, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at allocated
  obtain ⟨⟨dropLast, counted⟩, unmonitored⟩ := allocated
  cases last : reference.getLast? with
  | none => simp [last] at counted
  | some count =>
  simp only [last, Bool.and_eq_true, decide_eq_true_eq] at counted
  have shape : reference = watcher ++ [count] := by
    rw [← dropLast]; exact (dropLast_append_of_getLast? last).symm
  have covers : state.Covers watcher reference count := fun record found live => by
    rw [foundWatcher] at found; cases found
    exact ⟨by simpa [watcherOf] using counted.2, by simpa [watcherOf] using unmonitored⟩
  -- After the phase, the record only lost the `DOWN`, or is gone with nothing left.
  have popped := State.phase_drops within.1 record ended rfl rfl parked foundWatcher watcherLive dropped phase
  have gone₀ : (state.set processId (popDown process)).gone = state.gone := by
    funext other
    by_cases same : other = processId
    · subst same; simp [State.gone, State.alive, State.record_set, record, popDown, ended]
    · simp [State.gone, State.alive, State.record_set, same]
  have cleanPopped : normRecord state.gone processId (popDown process) = popDown process := by
    rw [normRecord_popDown_kept ended rfl watcherKept, clean.1]
  have sortedSet : (state.set processId (popDown process)).Sorted :=
    Lynx.Concurrent.Sorted.insertRecord within.1 processId _
  have records₀ : ∀ other, (state.set processId (popDown process)).normalize.record other =
      if other = processId then (some (popDown process)).filter (!·.finished) else state.record other := by
    intro other
    rw [State.record_normalize' sortedSet, gone₀, State.record_set]
    split
    · rename_i same; subst same; simp only [Option.map_some, cleanPopped]
    · have := congrArg (·.record other) normalized
      simp only [State.record_normalize' within.1] at this
      exact this
  -- Steps of other keys neither read nor change the record.
  let after : Option ProcessState := (some (popDown process)).filter (!·.finished)
  let related : Option ProcessState → Option ProcessState → Prop := fun first second =>
    first = some process ∧ second = after
  have endedAfter : ∀ record, after = some record → record = popDown process ∧ record.finished = false := by
    intro record found
    simp only [after, Option.filter] at found
    split at found
    · rename_i kept; cases found; exact ⟨rfl, by simpa using kept⟩
    · cases found
  have emptied : after = none → process.queue = [] := by
    intro missing
    simp only [after, Option.filter] at missing
    split at missing
    · cases missing
    · rename_i done
      simp only [Bool.not_eq_true', ProcessState.finished, popDown, ended, Option.map_some,
        List.tail_cons] at done
      cases rest with
      | nil => simpa using done
      | cons => simp at done
  have unseen : Unnoticed related := {
    live := by
      rintro _ _ ⟨rfl, rfl⟩
      cases found : after with
      | none => simp [liveRecord, ended]
      | some record => obtain ⟨rfl, -⟩ := endedAfter _ found; simp [liveRecord, popDown, ended]
    trapExit := by
      rintro _ _ ⟨rfl, rfl⟩
      cases found : after with
      | none => simp [trapped]
      | some record => obtain ⟨rfl, -⟩ := endedAfter _ found; rfl
    parked := by
      rintro _ _ ⟨rfl, rfl⟩
      cases found : after with
      | none => simp [parked]
      | some record => obtain ⟨rfl, -⟩ := endedAfter _ found; rfl
    links := by
      rintro _ _ ⟨rfl, rfl⟩ entry -
      cases found : after with
      | none => simp [emptied found]
      | some record => obtain ⟨rfl, -⟩ := endedAfter _ found; rfl
    push := by rintro _ _ entry ⟨rfl, rfl⟩ live; simp [liveRecord, ended] at live
    eagerExit := by rintro _ _ source ⟨rfl, rfl⟩ live; simp [liveRecord, ended] at live
    unpark := by rintro _ _ ⟨rfl, rfl⟩ unparked; simp [parked] at unparked }
  have changed : state.Changes processId related (state.set processId (popDown process)).normalize := by
    refine ⟨fun other differ => ?_, ⟨record, ?_⟩, rfl, rfl, rfl⟩
    · rw [records₀, ite_eq_right differ]
    · rw [records₀, ite_eq_left rfl]
  have missing : Kernel.lookup processId tasks = none := by
    cases found : Kernel.lookup processId tasks with
    | none => rfl
    | some task =>
      have := fresh.2.1 _ (mem_of_lookup found)
      simp [State.alive, record, ended] at this
  have quiet : ∀ {target : PID}, key' = .phase processId ∨ key' = .link processId target → False := by
    intro target same
    rcases same with rfl | rfl
    · exact differ rfl
    · simp [Config.stepOf, State.linkPhase, record, ended] at step'
  have owner : key'.owner ≠ some processId := by
    intro owned
    cases key' <;> simp only [Key.owner, Option.some.injEq, reduceCtorEq] at owned <;> subst owned
    · obtain ⟨_, _, found, -⟩ := Config.stepOf_own step'; rw [missing] at found; cases found
    · obtain ⟨_, _, found, -⟩ := Config.stepOf_handle step'; rw [missing] at found; cases found
  have spawns : ∀ {other : PID} {other' : Task α}, Kernel.lookup other tasks = some other' → other ≠ processId →
      Kernel.append other [(state.process other).children + 1] ≠ processId := by
    intro other other' found _ same
    obtain ⟨parent, foundParent, liveParent⟩ := State.alive_iff.mp (fresh.2.1 _ (mem_of_lookup found))
    have parentOf : state.process other = parent := by simp [State.process, foundParent]
    rw [parentOf, Kernel.append_eq] at same
    exact unborn _ _ foundParent liveParent processId (by simp [record]) _ (Nat.lt_succ_self _)
      (by rw [same]; exact List.prefix_refl _)
  obtain ⟨next', stepped, same | ⟨raw, raw', tasks₁, finished₁, changedRaw, withinRaw, withinRaw', lookup₁,
      rfl, rfl⟩⟩ := Config.step_changed (task' := ⟨(.error .exhausted : Result Unit), fun _ => none, none⟩)
    within ((within.set _ _).normalize) changed unseen spawns quiet owner step'
  · rw [rewriteTask_missing missing] at stepped
    subst same
    exact .inl ⟨event', by rw [← popped] at stepped; exact stepped⟩
  rw [rewriteTask_missing missing, rewriteTask_missing (lookup₁.trans missing), ← popped] at stepped
  have goneRaw : raw'.gone = raw.gone := changedRaw.gone unseen
  obtain ⟨othersRaw, ⟨foundRaw, foundRaw'⟩, timersRaw, elapsedRaw, sharedRaw⟩ := changedRaw
  have normalizedRecords : ∀ other, other ≠ processId → raw'.normalize.record other = raw.normalize.record other := by
    intro other differ'
    rw [State.record_normalize' withinRaw'.1, State.record_normalize' withinRaw.1, goneRaw, othersRaw other differ']
  -- What normalizing after the other step leaves of the record after the phase.
  have afterRaw : raw'.normalize.record processId =
      (some (normRecord raw.gone processId (popDown process))).filter (!·.finished) := by
    rw [State.record_normalize' withinRaw'.1, goneRaw, foundRaw']
    cases found : after with
    | none =>
      simp only [after, Option.filter] at found
      split at found
      · cases found
      · rename_i done
        have done' : (popDown process).finished = true := by simpa using done
        simp [Option.filter, finished_normRecord done']
    | some record =>
      obtain ⟨rfl, -⟩ := endedAfter _ found
      rfl
  cases watcherGone : raw.gone watcher with
  | true =>
    -- The watcher ended: normalizing drops the `DOWN` from the record either way.
    refine .inl ⟨event', ?_⟩
    rw [stepped]
    congr 3
    refine State.ext_records (Sorted.normalize withinRaw.1) (Sorted.normalize withinRaw'.1) (fun other => ?_)
      timersRaw elapsedRaw sharedRaw
    by_cases same : other = processId
    · subst same
      rw [afterRaw, State.record_normalize' withinRaw.1, foundRaw, Option.map_some,
        normRecord_popDown_gone ended rfl watcherGone]
    · exact normalizedRecords other same
  | false =>
    -- The watcher still drops the `DOWN`, so the phase stays forced after the other step.
    have sortedMiddle : raw.normalize.Sorted := Sorted.normalize withinRaw.1
    have goneMiddle : raw.normalize.gone = raw.gone := funext (State.gone_normalize withinRaw.1)
    let kept := normRecord raw.gone processId process
    have keptEnded : kept.exiting =
        some ⟨reason, [], (reference, watcher) :: Kernel.filter (fun down => !raw.gone down.2) rest⟩ := by
      simp [kept, normRecord, ended, Kernel.filter_eq, watcherGone]
    have foundMiddle : raw.normalize.record processId = some kept := by
      rw [State.record_normalize' withinRaw.1, foundRaw, Option.map_some]
      have going : kept.finished = false := by simp [ProcessState.finished, keptEnded]
      show (some kept).filter (fun record => !record.finished) = some kept
      simp [Option.filter, going]
    have parkedMiddle : kept.parked = none := by simp [kept, normRecord, ended]
    obtain ⟨watcherMiddle, foundWatcherMiddle, liveWatcherMiddle⟩ := State.alive_iff.mp
      (show raw.normalize.alive watcher = true by
        rw [State.alive_normalize withinRaw.1]; simpa [State.gone] using watcherGone)
    have watcherMiddleOf : raw.normalize.process watcher = watcherMiddle := by
      simp [State.process, foundWatcherMiddle]
    have coversMiddle := Config.covers_step reachable₀ unborn covers shape (by simp [foundWatcher]) step'
    obtain ⟨countedMiddle, unmonitoredMiddle⟩ := coversMiddle _ foundWatcherMiddle liveWatcherMiddle
    have droppedMiddle : raw.normalize.inertEntry watcher
        { source := processId, signal := .down reference reason } = true := by
      simp only [State.inertEntry, State.allocated, watcherMiddleOf, dropLast, beq_self_eq_true, Bool.true_and,
        last, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      exact ⟨⟨counted.1, countedMiddle⟩, unmonitoredMiddle⟩
    cases phaseMiddle : raw.normalize.phase processId with
    | none => simp [State.phase, foundMiddle, keptEnded] at phaseMiddle
    | some phasedMiddle =>
    have tagged := Config.tagged_phase (tasks := tasks₁) (finished := finished₁) foundMiddle phaseMiddle
    have forcedMiddle : raw.normalize.dropsDown processId = true := by
      simp [State.dropsDown, State.process, foundMiddle, keptEnded, State.keepEntry, 
        droppedMiddle]
    rw [forcedMiddle] at tagged
    refine .inr ⟨_, _, _, event', tagged, ?_⟩
    rw [stepped, State.phase_drops sortedMiddle foundMiddle keptEnded rfl rfl parkedMiddle foundWatcherMiddle
      liveWatcherMiddle droppedMiddle phaseMiddle]
    congr 3
    -- Popping the `DOWN` after normalizing is normalizing after popping it.
    have sortedPopped : (raw.normalize.set processId (popDown kept)).Sorted :=
      Lynx.Concurrent.Sorted.insertRecord sortedMiddle processId _
    have gonePopped : (raw.normalize.set processId (popDown kept)).gone = raw.gone := by
      funext other
      have middle := congrFun goneMiddle other
      by_cases same : other = processId
      · subst same
        have goneP : raw.gone other = true := by
          simpa [State.gone, State.alive, foundMiddle, keptEnded] using middle.symm
        rw [goneP]
        simp [State.gone, State.alive, State.record_set, popDown, keptEnded]
      · simpa [State.gone, State.alive, State.record_set, same] using middle
    have keptPop : popDown kept = normRecord raw.gone processId (popDown process) :=
      (normRecord_popDown_kept ended rfl watcherGone).symm
    refine State.ext_records (Sorted.normalize sortedPopped) (Sorted.normalize withinRaw'.1) (fun other => ?_)
      (by simp [State.normalize_eq, State.set, timersRaw]) (by simp [State.normalize_eq, State.set, elapsedRaw])
      (by simpa [State.normalize_eq, State.set] using sharedRaw)
    rw [State.record_normalize' sortedPopped, gonePopped, State.record_set]
    split
    · rename_i same; subst same
      rw [afterRaw, Option.map_some, keptPop, normRecord_normRecord (fun _ gone => gone)]
    · rename_i differ'
      rw [normalizedRecords other differ', ← goneMiddle, ← State.record_normalize' sortedMiddle,
        State.normalize_normalize withinRaw.1]

/-- Every other step absorbs a forced step, or commutes with it into a
configuration where a forced step closes the square. -/
private theorem Config.forced_square {elapsed : PID → Nat → Nat} {config : Config α} {key key' : Key}
    {event event' : Event} {next middle : Config α} (reachable : config.Reachable elapsed) (distinct : config.Distinct)
    (unborn : config.Unborn) (forced : (key, event, next, true) ∈ config.taggedSteps)
    (step' : config.stepOf key' = some (event', middle)) (differ : key' ≠ key) :
    (∃ absorbed, next.stepOf key' = some (absorbed, middle)) ∨
      ∃ key'' event'' last other, (key'', event'', last, true) ∈ middle.taggedSteps ∧
        next.stepOf key' = some (other, last) := by
  rcases Config.forced_keys forced with ⟨processId, rfl⟩ | ⟨processId, rfl⟩ | ⟨processId, rfl⟩
  · by_cases handling : key' = .handle processId
    · subst handling; exact Config.forced_own_handle reachable forced step'
    · refine Config.forced_own_other reachable forced step' fun owner => ?_
      cases key' <;> simp only [Key.owner, Option.some.injEq, reduceCtorEq] at owner <;> subst owner
      · exact differ rfl
      · exact handling rfl
  · by_cases owning : key' = .own processId
    · subst owning; exact Config.forced_handle_own reachable distinct forced step'
    · refine Config.forced_handle_other reachable forced step' fun owner => ?_
      cases key' <;> simp only [Key.owner, Option.some.injEq, reduceCtorEq] at owner <;> subst owner
      · exact owning rfl
      · exact differ rfl
  · exact Config.forced_phase_square reachable unborn forced step' differ

/-- What every configuration a run reaches satisfies, with links with distinct
processes and children not spawned yet without records. -/
private def Config.Ready (elapsed : PID → Nat → Nat) (config : Config α) : Prop :=
  config.Reachable elapsed ∧ config.Distinct ∧ config.Unborn

private theorem Config.Ready.step {elapsed : PID → Nat → Nat} {config next : Config α} {event : Event}
    (ready : config.Ready elapsed) (step : Step config event next) : next.Ready elapsed :=
  ⟨ready.1.step step, Config.Distinct.step ready.1.1.1 ready.2.1 step, Config.Unborn.step ready.1 ready.2.2 step⟩

/-- Every run reaching a terminal configuration can take a forced step first. -/
private theorem forced_first {elapsed : PID → Nat → Nat} {outcome : Outcome α} :
    ∀ {first last : Config α} {events : List Event}, Run first events last →
    ∀ {key : Key} {event : Event} {next : Config α}, first.Ready elapsed →
      (key, event, next, true) ∈ first.taggedSteps → Terminal last outcome → Reaches next last := by
  intro first last events run
  induction run with
  | refl =>
    intro key event next ready forced terminal
    have step := Config.step_of_stepOf (ready.1.stepOf forced)
    simp [Step, terminal.successors_eq_nil] at step
  | step step rest ih =>
    rename_i first event' middle events last
    intro key event next ready forced terminal
    obtain ⟨state, tasks, finished, rfl⟩ := Config.Reachable.running forced
    obtain ⟨key', forced', mem'⟩ := Config.tagged_of_step step
    have step' := ready.1.stepOf mem'
    by_cases same : key' = key
    · subst same
      rw [ready.1.stepOf forced] at step'
      simp only [Option.some.injEq, Prod.mk.injEq] at step'
      obtain ⟨-, rfl⟩ := step'
      exact ⟨_, rest⟩
    · rcases Config.forced_square ready.1 ready.2.1 ready.2.2 forced step' same with ⟨absorbed, after⟩ |
        ⟨key'', event'', last', other, forcedNext, after⟩
      · exact ⟨_, .step (Config.step_of_stepOf after) rest⟩
      · exact Reaches.step (Config.step_of_stepOf after)
          (ih (ready.step step) forcedNext terminal)

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
      first.Ready elapsed → checkSleep accept depth sleep first = true → Run first events last →
      Terminal last outcome →
      (∀ key ∈ sleep, ∃ event next, first.stepOf key = some (event, next)) →
      (∀ key ∈ sleep, ∀ event next, first.stepOf key = some (event, next) → ¬Reaches next last) →
      accept outcome = true := by
  intro depth
  induction depth with
  | zero => intro _ _ _ _ _ _ checked; simp [checkSleep] at checked
  | succ depth ih =>
    intro sleep first last events outcome ready checked run terminal awake asleep
    unfold checkSleep at checked
    simp only [Bool.and_eq_true] at checked
    obtain ⟨distinctTasks, checked⟩ := checked
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
          exact ih (ready.step step) (checked _ step) rest terminal (by simp) (by simp)
    · rename_i tagged nonempty
      cases run with
      | refl =>
        exfalso
        obtain ⟨⟨key, event, next, forced⟩, mem⟩ := List.exists_mem_of_ne_nil _ nonempty
        have := Config.step_of_stepOf (ready.1.stepOf mem)
        simp [Step, terminal.successors_eq_nil] at this
      | step step rest =>
      obtain ⟨state, tasks, finished, rfl⟩ : ∃ state tasks finished, first = .running state tasks finished false := by
        obtain ⟨⟨key, event, next, forced⟩, mem⟩ := List.exists_mem_of_ne_nil _ nonempty
        exact Config.Reachable.running mem
      split at checked
      · -- A step every run can take first, keeping the same steps asleep.
        rename_i key event next forced found
        have mem := List.mem_of_find?_eq_some (by simpa [Kernel.find?_eq] using found)
        have isForced : forced = true := by simpa using List.find?_some (by simpa [Kernel.find?_eq] using found)
        subst isForced
        have reaches := forced_first (.step step rest) ready mem terminal
        have found' := ready.1.stepOf mem
        have notAsleep : key ∉ sleep := fun slept => asleep key slept event next found' reaches
        obtain ⟨events', run'⟩ := reaches
        -- A step asleep before the forced step reaches after it only what it reached before.
        have after : ∀ key' ∈ sleep, ∀ event₀ next₀,
            (Config.running state tasks finished false).stepOf key' = some (event₀, next₀) →
            ∃ event'' next'', next.stepOf key' = some (event'', next'') ∧
              (Reaches next'' last → Reaches next₀ last) := by
          intro key' slept event₀ next₀ step₀
          have differ : key' ≠ key := fun same => notAsleep (same ▸ slept)
          rcases Config.forced_square ready.1 ready.2.1 ready.2.2 mem step₀ differ with ⟨absorbed, after⟩ |
              ⟨key'', event'', last', other, forced', after⟩
          · exact ⟨_, _, after, id⟩
          · exact ⟨_, _, after, Reaches.step (Config.step_of_stepOf
              ((ready.step (Config.step_of_stepOf step₀)).1.stepOf forced'))⟩
        refine ih (ready.step (Config.step_of_stepOf found')) checked run' terminal
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
          exact ready.1.stepOf mem
        obtain ⟨key, forced, mem⟩ := Config.tagged_of_step step
        refine explore_sound (goal := accept outcome = true)
          (fun key event next mem sleep' visited stays reaches asleep' => ?_)
          (fun key event next mem key' stays event' next' after reaches => ?_)
          (fun key event event' next next' mem mem' => ?_)
          (fun key slept event next mem => asleep key slept event next (tagged' _ _ _ mem))
          ⟨key, _, _, Config.mem_steps.mpr ⟨forced, mem⟩, _, rest⟩ checked
        · obtain ⟨events', run'⟩ := reaches
          have step := tagged' _ _ _ mem
          refine ih (ready.step (Config.step_of_stepOf step)) visited run' terminal (fun key' slept => ?_) asleep'
          obtain ⟨-, -, -, event₃, last', after, -⟩ :=
            Config.stays ready.1.1 distinctTasks tagged' step (stays key' slept)
          exact ⟨event₃, last', after⟩
        · have step := tagged' _ _ _ mem
          obtain ⟨event₀, next₀, step₀, event₃, last', after', back⟩ :=
            Config.stays ready.1.1 distinctTasks tagged' step stays
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
    ⟨⟨⟨rfl, trivial, trivial⟩, trivial⟩, trivial, trivial⟩ checked run terminal (by simp) (by simp)

end Lynx.Concurrent
