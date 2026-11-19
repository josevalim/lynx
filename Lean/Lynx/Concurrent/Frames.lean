module

public import Lynx.Concurrent.Diamond
import all Lynx.Concurrent.Diamond
import Lynx.Term.Induction

/-! Steps that `Config.apart` lets commute without evaluating them. Each step
does an effect on the records it changes (`Effect`), a function of their old
records decided at the configuration. Frames describe the effects: what each
writes, and what its decisions and changes read. -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-! ### Effects -/

/-- What a step does to records and timers: the change of each record it
touches (the first entry of a process counts), and the timers, if it changes them. -/
private structure Effect where
  records : List (PID × (Option ProcessState → Option ProcessState)) := []
  timers : Option (List Timer → List Timer) := none

/-- The first change of a process in a list of changes. -/
private def changeOf : List (PID × (Option ProcessState → Option ProcessState)) → PID →
    Option ProcessState → Option ProcessState
  | [], _ => id
  | (other, change) :: rest, processId => if other = processId then change else changeOf rest processId

/-- How an effect changes the record of a process. -/
private def Effect.record (effect : Effect) (processId : PID) : Option ProcessState → Option ProcessState :=
  changeOf effect.records processId

private theorem changeOf_of_missing {changes : List (PID × (Option ProcessState → Option ProcessState))}
    {processId : PID} (missing : processId ∉ changes.map (·.1)) : changeOf changes processId = id := by
  induction changes with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨other, change⟩ := head
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    simp [changeOf, Ne.symm missing.1, ih missing.2]

/-- Replace or remove the record of a process. -/
private def State.put (state : State) (processId : PID) : Option ProcessState → State
  | some process => state.set processId process
  | none => state.remove processId

private theorem State.record_put (state : State) (processId other : PID) (record : Option ProcessState) :
    (state.put processId record).record other = if other = processId then record else state.record other := by
  cases record <;> simp [State.put, State.record_set, State.record_remove]

/-- The state after an effect. -/
private def Effect.apply (effect : Effect) (state : State) : State :=
  (effect.records.map (·.1)).foldl (fun changed processId =>
      changed.put processId (effect.record processId (state.record processId)))
    { state with timers := (effect.timers.getD id) state.timers }

private theorem foldl_put_record (change : PID → Option ProcessState) (processId : PID) :
    ∀ (processes : List PID) (start : State),
      (processes.foldl (fun changed other => changed.put other (change other)) start).record processId =
        if processId ∈ processes then change processId else start.record processId
  | [], start => by simp
  | head :: rest, start => by
      simp only [List.foldl_cons, foldl_put_record change processId rest, State.record_put, List.mem_cons]
      by_cases inside : processId ∈ rest
      · simp [inside]
      · by_cases equal : processId = head
        · subst equal; simp [inside]
        · simp [inside, equal]

private theorem Effect.record_apply (effect : Effect) (state : State) (processId : PID) :
    (effect.apply state).record processId = effect.record processId (state.record processId) := by
  simp only [Effect.apply, foldl_put_record]
  split
  · rfl
  · rename_i missing
    simp only [Effect.record, changeOf_of_missing missing]
    rfl



/-- One effect after another. -/
private def Effect.andThen (first second : Effect) : Effect where
  records := (first.records.map fun (processId, change) => (processId, second.record processId ∘ change)) ++
    second.records
  timers := match first.timers, second.timers with
    | some change, some change' => some (change' ∘ change)
    | some change, none => some change
    | none, change' => change'

private theorem changeOf_append (first second : List (PID × (Option ProcessState → Option ProcessState)))
    (outer : PID → Option ProcessState → Option ProcessState) (processId : PID)
    (outer_eq : ∀ processId, outer processId = changeOf second processId) :
    changeOf ((first.map fun (other, change) => (other, outer other ∘ change)) ++ second) processId =
      changeOf second processId ∘ changeOf first processId := by
  induction first with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨other, change⟩ := head
    by_cases equal : other = processId
    · subst equal; simp [changeOf, outer_eq]
    · simp [changeOf, equal, ih]

private theorem Effect.record_andThen (first second : Effect) (processId : PID) :
    (first.andThen second).record processId = second.record processId ∘ first.record processId := by
  simp only [Effect.record, Effect.andThen]
  exact changeOf_append _ _ _ _ fun _ => rfl

private theorem Effect.timers_andThen (first second : Effect) :
    ((first.andThen second).timers.getD id) = (second.timers.getD id) ∘ (first.timers.getD id) := by
  simp only [Effect.andThen]
  cases first.timers <;> cases second.timers <;> rfl

/-- Change the record of a process that has one. -/
private def Effect.modify (processId : PID) (change : ProcessState → ProcessState) : Effect :=
  { records := [(processId, Option.map change)] }

private theorem Effect.record_modify (processId other : PID) (change : ProcessState → ProcessState) :
    (Effect.modify processId change).record other = if other = processId then Option.map change else id := by
  by_cases equal : other = processId
  · subst equal; simp [Effect.record, Effect.modify, changeOf]
  · simp [Effect.record, Effect.modify, changeOf, Ne.symm equal, equal]

/-! ### Fields -/

/-- Which fields of a record a frame has, by bit: `Field.mailbox` is `2 ^ Part.mailbox.bit`, and so on. -/
private abbrev Mask := Nat → Bool

/-- The bits of the queue's ends and of liveness. -/
private def headBit : Nat := 0
private def tailBit : Nat := 1
private def liveBit : Nat := 16

/-- A field of a record other than its queue. -/
private inductive Part where
  | mailbox | pdict | refCounter | children | links | monitors | monitoring | aliases | trapExit
  | cancels | unlinks | parked | eagerExits | exiting

/-- The bit of a field in frames: `Field.mailbox` is `2 ^ Part.mailbox.bit`, and so on. -/
private def Part.bit : Part → Nat
  | .mailbox => 2 | .pdict => 3 | .refCounter => 4 | .children => 5 | .links => 6 | .monitors => 7
  | .monitoring => 8 | .aliases => 9 | .trapExit => 10 | .cancels => 11 | .unlinks => 12 | .parked => 13
  | .eagerExits => 14 | .exiting => 15

private def Part.type : Part → Type
  | .mailbox => List Term | .pdict => List (Term × Term) | .refCounter | .children | .cancels | .unlinks => Nat
  | .links => List (PID × Option Nat) | .monitors | .monitoring => List (List Nat × PID)
  | .aliases => List (List Nat) | .trapExit => Bool | .parked => Option (PID × List Nat)
  | .eagerExits => List PID | .exiting => Option Exiting

/-- A field of a record. -/
private def ProcessState.get (process : ProcessState) : (part : Part) → part.type
  | .mailbox => process.mailbox | .pdict => process.pdict | .refCounter => process.refCounter
  | .children => process.children | .links => process.links | .monitors => process.monitors
  | .monitoring => process.monitoring | .aliases => process.aliases | .trapExit => process.trapExit
  | .cancels => process.cancels | .unlinks => process.unlinks | .parked => process.parked
  | .eagerExits => process.eagerExits | .exiting => process.exiting

private theorem ProcessState.ext_get {first second : ProcessState} (queue : first.queue = second.queue)
    (same : ∀ part, first.get part = second.get part) : first = second := by
  cases first; cases second
  have := same .mailbox; have := same .pdict; have := same .refCounter; have := same .children
  have := same .links; have := same .monitors; have := same .monitoring; have := same .aliases
  have := same .trapExit; have := same .cancels; have := same .unlinks; have := same .parked
  have := same .eagerExits; have := same .exiting
  simp_all [ProcessState.get]

/-- Two records agree on the fields of a mask. Reading the head of a queue
without its tail reads only its oldest signal. -/
private def ProcessState.Same (mask : Mask) (first second : ProcessState) : Prop :=
  (mask tailBit → first.queue = second.queue) ∧
  (mask headBit → first.queue.head? = second.queue.head?) ∧
  (∀ part, mask part.bit → first.get part = second.get part)

private theorem ProcessState.Same.refl (mask : Mask) (process : ProcessState) : process.Same mask process :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

private theorem ProcessState.Same.symm {mask : Mask} {first second : ProcessState}
    (same : first.Same mask second) : second.Same mask first :=
  ⟨fun x => (same.1 x).symm, fun x => (same.2.1 x).symm, fun part x => (same.2.2 part x).symm⟩


/-! ### Changes within frames -/

/-- How a change may change a queue, given which ends its frame writes: it
removes at most the oldest signal, only when it writes the head, and appends
signals, only when it writes the tail. -/
private def QueueChange (head tail : Bool) (reads : Mask) (base : ProcessState)
    (change : ProcessState → ProcessState) : Prop :=
  ∃ dropped added, dropped ≤ 1 ∧ (head = false → dropped = 0) ∧ (tail = false → added = []) ∧
    ∀ process, process.Same reads base → (change process).queue = process.queue.drop dropped ++ added

/-- A change of records agreeing with `base` on `reads`: it keeps the fields
outside `writes`, what it writes of a field depends only on `reads` and the
field, and it changes the queue as its frame says. Reading the tail of a queue
reads its head, and reading its head reads a queue that has one. -/
private def Framed (reads writes : Mask) (base : ProcessState) (change : ProcessState → ProcessState) : Prop :=
  (∀ process, process.Same reads base → ∀ part, writes part.bit = false →
    (change process).get part = process.get part) ∧
  (∀ process process', process.Same reads base → process'.Same reads base → ∀ part, writes part.bit →
    process.get part = process'.get part → (change process).get part = (change process').get part) ∧
  QueueChange (writes headBit) (writes tailBit) reads base change ∧
  (reads tailBit → reads headBit) ∧
  (reads headBit → reads tailBit ∨ base.queue ≠ []) ∧
  (writes headBit → base.queue ≠ []) ∧
  (writes liveBit = false → ∀ process, process.Same reads base →
    (change process).exiting.isSome = process.exiting.isSome)

/-- A change within its frame keeps what a frame it writes nothing of reads. -/
private theorem Framed.keeps {reads writes reads' : Mask} {base : ProcessState} {change : ProcessState → ProcessState}
    (framed : Framed reads writes base change) (apart : ∀ bit, writes bit → reads' bit → False)
    (nonempty : reads' headBit → reads' tailBit ∨ base.queue ≠ []) (tail : reads' tailBit → reads' headBit) :
    (change base).Same reads' base := by
  obtain ⟨keeps, -, ⟨dropped, added, -, noHead, noTail, queue⟩, -, -, -, -⟩ := framed
  have self := ProcessState.Same.refl reads base
  refine ⟨fun inside => ?_, fun inside => ?_, fun part inside => ?_⟩
  · have head := tail inside
    cases written : writes headBit
    · cases written' : writes tailBit
      · rw [queue base self, noHead written, noTail written']; simp
      · exact (apart _ written' inside).elim
    · exact (apart _ written head).elim
  · cases written : writes headBit
    · rw [queue base self, noHead written]
      cases written' : writes tailBit
      · rw [noTail written']; simp
      · cases equal : base.queue with
        | nil => exact absurd equal ((nonempty inside).resolve_left fun read => apart _ written' read)
        | cons _ _ => rfl
    · exact (apart _ written inside).elim
  · cases written : writes part.bit
    · exact keeps base self part written
    · exact (apart _ written inside).elim

/-- Removing at most one oldest signal and appending commute, when at most one
of them removes and at most one appends. -/
private theorem drop_append_comm {queue added added' : List Entry} {dropped dropped' : Nat}
    (one : dropped ≤ 1) (one' : dropped' ≤ 1) (drops : dropped = 0 ∨ dropped' = 0)
    (adds : added = [] ∨ added' = []) (nonempty : dropped = 1 → queue ≠ [])
    (nonempty' : dropped' = 1 → queue ≠ []) :
    (queue.drop dropped' ++ added').drop dropped ++ added = (queue.drop dropped ++ added).drop dropped' ++ added' := by
  rcases (by omega : dropped = 0 ∨ dropped = 1) with rfl | rfl <;>
    rcases (by omega : dropped' = 0 ∨ dropped' = 1) with rfl | rfl
  · rcases adds with rfl | rfl <;> simp
  · obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil (nonempty' rfl)
    rcases adds with rfl | rfl <;> simp
  · obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil (nonempty rfl)
    rcases adds with rfl | rfl <;> simp
  · simp at drops

/-- Two changes within frames apart commute. -/
private theorem Framed.comm {reads writes reads' writes' : Mask} {base : ProcessState}
    {change change' : ProcessState → ProcessState}
    (framed : Framed reads writes base change) (framed' : Framed reads' writes' base change')
    (apart : ∀ bit, writes bit → reads' bit ∨ writes' bit → False) (apart' : ∀ bit, writes' bit → reads bit → False) :
    change (change' base) = change' (change base) := by
  have disjoint : ∀ bit, writes bit → writes' bit → False := fun bit one two => apart bit one (.inr two)
  have apartReads : ∀ bit, writes bit → reads' bit → False := fun bit one two => apart bit one (.inl two)
  have same : (change' base).Same reads base := framed'.keeps apart' framed.2.2.2.2.1 framed.2.2.2.1
  have same' : (change base).Same reads' base := framed.keeps apartReads framed'.2.2.2.2.1 framed'.2.2.2.1
  have self := ProcessState.Same.refl reads base
  have self' := ProcessState.Same.refl reads' base
  obtain ⟨keeps, depends, ⟨dropped, added, one, noHead, noTail, queue⟩, -, nonempty, pops, -⟩ := framed
  obtain ⟨keeps', depends', ⟨dropped', added', one', noHead', noTail', queue'⟩, -, nonempty', pops', -⟩ := framed'
  refine ProcessState.ext_get ?_ fun part => ?_
  · rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
    have drops : dropped = 0 ∨ dropped' = 0 := by
      cases head : writes headBit
      · exact .inl (noHead head)
      · cases head' : writes' headBit
        · exact .inr (noHead' head')
        · exact (disjoint _ head head').elim
    have adds : added = [] ∨ added' = [] := by
      cases tail : writes tailBit
      · exact .inl (noTail tail)
      · cases tail' : writes' tailBit
        · exact .inr (noTail' tail')
        · exact (disjoint _ tail tail').elim
    have popsNonempty : dropped = 1 → base.queue ≠ [] := fun is => by
      cases head : writes headBit
      · rw [noHead head] at is; simp at is
      · exact pops head
    have popsNonempty' : dropped' = 1 → base.queue ≠ [] := fun is => by
      cases head : writes' headBit
      · rw [noHead' head] at is; simp at is
      · exact pops' head
    exact drop_append_comm one one' drops adds popsNonempty popsNonempty'
  · cases written : writes part.bit
    · cases written' : writes' part.bit
      · rw [keeps _ same part written, keeps' _ self' part written', keeps' _ same' part written',
          keeps _ self part written]
      · rw [keeps _ same part written, depends' _ _ same' self' part written' (keeps _ self part written)]
    · cases written' : writes' part.bit
      · rw [depends _ _ same self part written (keeps' _ self' part written'), keeps' _ same' part written']
      · exact (disjoint _ written written').elim

/-! ### Frames of a step, per process -/

/-- The fields a step reads of a process's record, over all its frames. -/
private def readsOf (frames : List Frame) (processId : PID) : Mask :=
  fun bit => frames.any fun entry => entry.1 == processId && entry.2.1.testBit bit

/-- The fields a step writes of a process's record, over all its frames. -/
private def writesOf (frames : List Frame) (processId : PID) : Mask :=
  fun bit => frames.any fun entry => entry.1 == processId && entry.2.2.testBit bit

private theorem testBit_and_zero {first second : Nat} (zero : first &&& second = 0) {bit : Nat}
    (one : first.testBit bit = true) (two : second.testBit bit = true) : False := by
  have := congrArg (Nat.testBit · bit) zero
  simp [Nat.testBit_and, one, two] at this

/-- Frames that `framesApart` accepts are apart for every process, over all their frames. -/
private theorem apart_of_framesApart {frames frames' : List Frame} (apart : framesApart frames frames' = true)
    (processId : PID) :
    (∀ bit, writesOf frames processId bit → readsOf frames' processId bit ∨ writesOf frames' processId bit → False) ∧
    (∀ bit, writesOf frames' processId bit → readsOf frames processId bit → False) := by
  simp only [framesApart, Kernel.all_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, beq_iff_eq] at apart
  constructor
  · intro bit written read
    simp only [writesOf, readsOf, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at written read
    obtain ⟨entry, mem, same, bitWritten⟩ := written
    rcases read with ⟨entry', mem', same', bitRead⟩ | ⟨entry', mem', same', bitRead⟩
    · rcases apart entry mem entry' mem' with differ | ⟨zero, -⟩
      · exact differ (same.trans same'.symm)
      · exact testBit_and_zero zero bitWritten (by simp [Nat.testBit_or, bitRead])
    · rcases apart entry mem entry' mem' with differ | ⟨zero, -⟩
      · exact differ (same.trans same'.symm)
      · exact testBit_and_zero zero bitWritten (by simp [Nat.testBit_or, bitRead])
  · intro bit written read
    simp only [writesOf, readsOf, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at written read
    obtain ⟨entry', mem', same', bitWritten⟩ := written
    obtain ⟨entry, mem, same, bitRead⟩ := read
    rcases apart entry mem entry' mem' with differ | ⟨-, zero⟩
    · exact differ (same.trans same'.symm)
    · exact testBit_and_zero zero bitWritten bitRead

/-! ### Effects within frames -/

/-- Whether a record, or its absence, is of a live process, as `State.alive` reads it. -/
private def liveOf : Option ProcessState → Bool
  | some process => process.exiting.isNone
  | none => false

/-- Two records, or their absence, agree on a mask: alike live, when it reads
liveness, and agreeing on its fields when both exist. -/
private def RecordSame (mask : Mask) (record record' : Option ProcessState) : Prop :=
  (mask liveBit → liveOf record = liveOf record') ∧
  ∀ process process', record = some process → record' = some process' → process.Same mask process'

private theorem RecordSame.refl (mask : Mask) (record : Option ProcessState) : RecordSame mask record record :=
  ⟨fun _ => rfl, fun process process' found found' => by
    rw [found] at found'; simp only [Option.some.injEq] at found'; subst found'
    exact ProcessState.Same.refl _ _⟩

private theorem Part.bit_lt (part : Part) : part.bit < 17 := by cases part <;> decide

/-- An effect within the frames of a step at a state: it changes only records
the frames name, and each within its frame, unless the frames write every
field of the record, as when the step ends or starts the process. -/
private def Effect.InFrames (effect : Effect) (frames : List Frame) (state : State) : Prop :=
  ∀ processId, effect.record processId = id ∨
    (∀ bit, bit < 17 → writesOf frames processId bit) ∨
    ∃ change, effect.record processId = Option.map change ∧
      (∃ bit, bit < 17 ∧ (readsOf frames processId bit ∨ writesOf frames processId bit)) ∧
      ∀ process, state.record processId = some process →
        Framed (readsOf frames processId) (writesOf frames processId) process change

/-- An effect keeps what frames it writes nothing of read. -/
private theorem Effect.InFrames.keeps {effect : Effect} {frames frames' : List Frame} {state : State}
    (framed : effect.InFrames frames state)
    (apart : ∀ processId bit, writesOf frames processId bit → readsOf frames' processId bit → False)
    (nonempty : ∀ processId process, state.record processId = some process →
      readsOf frames' processId headBit → readsOf frames' processId tailBit ∨ process.queue ≠ [])
    (tail : ∀ processId, readsOf frames' processId tailBit → readsOf frames' processId headBit)
    (processId : PID) :
    RecordSame (readsOf frames' processId) (state.record processId) ((effect.apply state).record processId) := by
  rw [Effect.record_apply]
  rcases framed processId with same | all | ⟨change, equal, -, framed⟩
  · rw [same]; exact RecordSame.refl _ _
  · refine ⟨fun read => (apart processId liveBit (all liveBit (by decide)) read).elim,
      fun process process' _ _ => ⟨fun read => ?_, fun read => ?_, fun part read => ?_⟩⟩
    · exact (apart processId tailBit (all tailBit (by decide)) read).elim
    · exact (apart processId headBit (all headBit (by decide)) read).elim
    · exact (apart processId part.bit (all part.bit part.bit_lt) read).elim
  · rw [equal]
    cases found : state.record processId with
    | none => exact ⟨fun _ => rfl, fun _ _ none => by simp at none⟩
    | some process =>
      have keeps := (framed process found).keeps (apart processId)
        (fun read => nonempty processId process found read) (tail processId)
      refine ⟨fun read => ?_, fun process₁ process₂ found₁ found₂ => ?_⟩
      · simp only [Option.map_some, liveOf]
        cases written : writesOf frames processId liveBit
        · have := (framed process found).2.2.2.2.2.2 written process (ProcessState.Same.refl _ _)
          cases equal : process.exiting <;> cases equal' : (change process).exiting <;> simp_all
        · exact (apart processId liveBit written read).elim
      · simp only [Option.some.injEq, Option.map_some] at found₁ found₂; subst found₁; subst found₂
        exact keeps.symm

/-- A change within a frame that reads and writes nothing of a record leaves it as it is. -/
private theorem Framed.id {reads writes : Mask} {base : ProcessState} {change : ProcessState → ProcessState}
    (framed : Framed reads writes base change) (unused : ∀ bit, bit < 17 → reads bit = false ∧ writes bit = false)
    (process : ProcessState) : change process = process := by
  obtain ⟨keeps, -, ⟨dropped, added, -, noHead, noTail, queue⟩, -⟩ := framed
  have same : process.Same reads base :=
    ⟨fun read => by simp [(unused tailBit (by decide)).1] at read,
      fun read => by simp [(unused headBit (by decide)).1] at read,
      fun part read => by simp [(unused part.bit part.bit_lt).1] at read⟩
  have queueSame : (change process).queue = process.queue := by
    rw [queue process same, noHead (unused headBit (by decide)).2, noTail (unused tailBit (by decide)).2]; simp
  exact ProcessState.ext_get queueSame fun part => keeps process same part (unused _ part.bit_lt).2

/-- Two effects within frames apart change every record alike in either order. -/
private theorem Effect.record_comm {effect effect' : Effect} {frames frames' : List Frame} {state : State}
    (framed : effect.InFrames frames state) (framed' : effect'.InFrames frames' state)
    (apart : ∀ processId bit, writesOf frames processId bit →
      readsOf frames' processId bit ∨ writesOf frames' processId bit → False)
    (apart' : ∀ processId bit, writesOf frames' processId bit → readsOf frames processId bit → False)
    (processId : PID) :
    effect.record processId (effect'.record processId (state.record processId)) =
      effect'.record processId (effect.record processId (state.record processId)) := by
  rcases framed processId with same | all | ⟨change, equal, used, inside⟩ <;>
    rcases framed' processId with same' | all' | ⟨change', equal', used', inside'⟩
  all_goals first
    | (rw [same]; rfl)
    | (rw [same']; rfl)
    | exact (apart processId 0 (all 0 (by decide)) (.inr (all' 0 (by decide)))).elim
    | skip
  · obtain ⟨bit, lower, used'⟩ := used'
    exact (apart processId bit (all bit lower) used').elim
  · obtain ⟨bit, lower, read | written⟩ := used
    · exact (apart' processId bit (all' bit lower) read).elim
    · exact (apart processId bit written (.inr (all' bit lower))).elim
  · rw [equal, equal']
    cases found : state.record processId with
    | none => rfl
    | some process =>
      simp only [Option.map_some]
      exact congrArg some ((inside process found).comm (inside' process found) (apart processId)
        (apart' processId))

/-! ### Operations as effects -/

/-- A state is an effect applied to another: the same records by PID and timers. -/
private def Realizes (effect : Effect) (before after : State) : Prop :=
  (∀ processId, after.record processId = effect.record processId (before.record processId)) ∧
    after.timers = (effect.timers.getD id) before.timers ∧ after.elapsed = before.elapsed

private theorem Realizes.refl (state : State) : Realizes {} state state :=
  ⟨fun _ => rfl, rfl, rfl⟩

private theorem Realizes.andThen {first second : Effect} {before middle after : State}
    (one : Realizes first before middle) (two : Realizes second middle after) :
    Realizes (first.andThen second) before after :=
  ⟨fun processId => by rw [two.1, one.1, Effect.record_andThen]; rfl,
    by rw [two.2.1, one.2.1, Effect.timers_andThen]; rfl, two.2.2.trans one.2.2⟩

private theorem Realizes.modify (state : State) (processId : PID) (change : ProcessState → ProcessState) :
    Realizes (Effect.modify processId change) state (state.modify processId change) := by
  refine ⟨fun other => ?_, ?_, ?_⟩
  · rw [Effect.record_modify]
    unfold State.modify
    split
    · rename_i process found
      rw [State.record_set]
      by_cases same : other = processId
      · subst same; simp [found]
      · simp [same]
    · rename_i missing
      by_cases same : other = processId
      · subst same; simp [missing]
      · simp [same]
  · unfold State.modify; split <;> rfl
  · unfold State.modify; split <;> rfl

/-- Replacing an existing record by a change of it. -/
private theorem Realizes.set {state : State} {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) (change : ProcessState → ProcessState) :
    Realizes (Effect.modify processId change) state (state.set processId (change process)) := by
  have := Realizes.modify state processId change
  unfold State.modify at this
  rw [found] at this
  exact this

/-- Changing only the timers. -/
private def Effect.retime (change : List Timer → List Timer) : Effect := { timers := some change }

private theorem Realizes.retime (state : State) (change : List Timer → List Timer) :
    Realizes (Effect.retime change) state { state with timers := change state.timers } :=
  ⟨fun _ => rfl, rfl, rfl⟩

/-- Queue a signal at a record. -/
private def queueAt (source : PID) (signal : Signal) (process : ProcessState) : ProcessState :=
  { process with queue := Kernel.append process.queue [{ source, signal }] }

/-- The effect of a sender's fallback for a signal to a process that is gone. -/
private def State.fallbackEffect (state : State) (source target : PID) : Signal → Effect
  | .link => .modify source (queueAt target (.exit (.atom "noproc") true false))
  | .monitor reference => .modify source (queueAt target (.down reference (.atom "noproc")))
  | .unlink _ => .modify source fun process => { process with links := Kernel.filter (·.1 != target) process.links }
  | .isAlive => .modify source (queueAt target (.reply (.atom "false")))
  | _ => {}

private theorem Realizes.fallback (state : State) (source target : PID) (signal : Signal) :
    Realizes (state.fallbackEffect source target signal) state (state.fallback source target signal) := by
  cases signal <;> simp only [State.fallbackEffect, State.fallback] <;>
    first
      | exact Realizes.modify _ _ _
      | exact Realizes.refl _

/-- The effect of `State.enqueue`. -/
private def State.enqueueEffect (state : State) (source target : PID) (signal : Signal) : Effect :=
  match state.record target with
  | some process =>
      if process.exiting.isNone then .modify target (queueAt source signal)
      else state.fallbackEffect source target signal
  | none => state.fallbackEffect source target signal

private theorem Realizes.enqueue (state : State) (source target : PID) (signal : Signal) :
    Realizes (state.enqueueEffect source target signal) state (state.enqueue source target signal) := by
  unfold State.enqueueEffect State.enqueue
  cases found : state.record target with
  | none => exact Realizes.fallback _ _ _ _
  | some process =>
    simp only
    split
    · exact Realizes.set found (queueAt source signal)
    · exact Realizes.fallback _ _ _ _

/-- The effect of `State.unpark`. -/
private def State.unparkEffect (state : State) (processId : PID) : Effect :=
  match (state.process processId).parked with
  | some (target, reference) =>
      (Effect.modify processId fun process => { process with parked := none }).andThen
        ((state.modify processId fun process => { process with parked := none }).enqueueEffect processId target
          (.monitor reference))
  | none => {}

private theorem Realizes.unpark (state : State) (processId : PID) :
    Realizes (state.unparkEffect processId) state (state.unpark processId) := by
  unfold State.unparkEffect State.unpark
  cases parked : (state.process processId).parked with
  | none => exact Realizes.refl _
  | some found =>
    obtain ⟨target, reference⟩ := found
    exact (Realizes.modify _ _ _).andThen (Realizes.enqueue _ _ _ _)

/-- The effect of `State.send`. -/
private def State.sendEffect (state : State) (source target : PID) (signal : Signal) : Effect :=
  match (state.process source).parked with
  | some (parked, _) =>
      if parked == target then (state.unparkEffect source).andThen ((state.unpark source).enqueueEffect source target signal)
      else state.enqueueEffect source target signal
  | none => state.enqueueEffect source target signal

private theorem Realizes.send (state : State) (source target : PID) (signal : Signal) :
    Realizes (state.sendEffect source target signal) state (state.send source target signal) := by
  unfold State.sendEffect State.send
  cases parked : (state.process source).parked with
  | none => exact Realizes.enqueue _ _ _ _
  | some found =>
    obtain ⟨other, reference⟩ := found
    simp only
    split
    · exact (Realizes.unpark _ _).andThen (Realizes.enqueue _ _ _ _)
    · exact Realizes.enqueue _ _ _ _

/-! ### Normalizing a record by which processes are gone -/

/-- `State.inertEntry` for a record, given which processes are gone. -/
private def inert (gone : PID → Bool) (processId : PID) (process : ProcessState) (entry : Entry) : Bool :=
  let allocated (reference : List Nat) : Bool := reference.dropLast == processId && match reference.getLast? with
    | some count => 1 ≤ count && count ≤ process.refCounter
    | none => false
  match entry.signal with
  | .down reference _ => allocated reference && !Kernel.any process.monitoring (·.1 == reference)
  | .aliasMessage alias _ => allocated alias &&
      !Kernel.contains process.aliases alias && !Kernel.any process.monitoring (·.1 == alias)
  | .unlinkAck id => gone entry.source || Kernel.lookup entry.source process.links != some (some id)
  | .isAlive | .monitor _ => gone entry.source
  | _ => false

/-- `State.normalizeRecord` for a record, given which processes are gone. -/
private def normRecord (gone : PID → Bool) (processId : PID) (process : ProcessState) : ProcessState :=
  match process.exiting with
  | some exiting =>
      { queue := Kernel.filter (fun entry => (entry.signal matches .link | .monitor _ | .isAlive) &&
          !gone entry.source) process.queue
        refCounter := process.refCounter, children := process.children
        exiting := some { exiting with
          links := Kernel.filter (fun target => !gone target) exiting.links
          downs := Kernel.filter (fun down => !gone down.2) exiting.downs } }
  | none =>
      { process with
        queue := Kernel.filter (fun entry => !inert gone processId process entry) process.queue
        links := Kernel.filter (fun link => !(link.2.isSome && gone link.1)) process.links }

private theorem State.normalizeRecord_eq {state : State} {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) :
    state.normalizeRecord processId process = normRecord state.gone processId process := by
  have same : state.process processId = process := by simp [State.process, found]
  unfold State.normalizeRecord normRecord
  cases exiting : process.exiting with
  | some exiting' => rfl
  | none =>
    simp only
    congr 2
    funext entry
    obtain ⟨source, signal⟩ := entry
    cases signal <;> simp only [State.keepEntry, State.inertEntry, State.allocated, same, inert, exiting,
      Option.isSome_none, Bool.false_and, Bool.or_false] <;> rfl

private theorem inert_mono {gone gone' : PID → Bool} (more : ∀ processId, gone processId → gone' processId)
    {processId : PID} {process : ProcessState} {entry : Entry}
    (inside : inert gone processId process entry = true) : inert gone' processId process entry = true := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp only [inert, Bool.or_eq_true] at inside ⊢ <;> try exact inside
  · rcases inside with left | right
    · exact .inl (more _ left)
    · exact .inr right
  · exact more _ inside
  · exact more _ inside

/-- Normalizing again, with more processes gone, is normalizing once. -/
private theorem normRecord_normRecord {gone gone' : PID → Bool} (more : ∀ processId, gone processId → gone' processId)
    (processId : PID) (process : ProcessState) :
    normRecord gone' processId (normRecord gone processId process) = normRecord gone' processId process := by
  have keep : ∀ target, (!gone' target && !gone target) = !gone' target := by
    intro target
    cases going : gone' target <;> cases going' : gone target <;> simp
    exact absurd (more _ going') (by simp [going])
  unfold normRecord
  cases exiting : process.exiting with
  | some exiting' =>
    simp only [Kernel.filter_eq, List.filter_filter]
    have queue : ∀ entry : Entry, ((match entry.signal with
          | .link | .monitor _ | .isAlive => true
          | _ => false) && !gone' entry.source &&
        ((match entry.signal with
          | .link | .monitor _ | .isAlive => true
          | _ => false) && !gone entry.source)) =
        ((match entry.signal with
          | .link | .monitor _ | .isAlive => true
          | _ => false) && !gone' entry.source) := by
      intro entry
      have := keep entry.source
      cases entry.signal <;> simp_all
    simp only [queue, keep]
  | none =>
    simp only [exiting, Kernel.filter_eq, List.filter_filter]
    congr 1
    · refine List.filter_congr fun entry _ => ?_
      cases inside : inert gone processId process entry
      · simp only [Bool.not_false, Bool.and_true]
        obtain ⟨source, signal⟩ := entry
        cases signal <;> simp only [inert] at inside ⊢
        cases going : gone' source
        · have going' : gone source = false := by
            cases g : gone source
            · rfl
            · exact absurd (more _ g) (by simp [going])
          simp only [Bool.false_or, Kernel.lookup_eq]
          rw [lookup_filter_of_key fun value _ => by simp [going']]
        · simp
      · simp [inert_mono more inside]
    · refine List.filter_congr fun link _ => ?_
      cases unlinking : link.2.isSome
      · simp
      · simp only [Bool.true_and]; exact keep link.1

/-- Replace the record of a process by a given one. -/
private def Effect.put (processId : PID) (process : ProcessState) : Effect :=
  { records := [(processId, fun _ => some process)] }

private theorem Realizes.put (state : State) (processId : PID) (process : ProcessState) :
    Realizes (Effect.put processId process) state (state.set processId process) := by
  refine ⟨fun other => ?_, rfl, rfl⟩
  rw [State.record_set]
  by_cases same : other = processId
  · subst same; simp [Effect.put, Effect.record, changeOf]
  · simp [Effect.put, Effect.record, changeOf, Ne.symm same, same]

/-- The effect of `State.linkExit`. -/
private def State.linkExitEffect (state : State) (processId target : PID) (reason : Term) : Effect :=
  if state.eagerLink processId target reason then
    Effect.modify target fun process => { process with
      links := Kernel.filter (·.1 != processId) process.links
      eagerExits := insertPid processId process.eagerExits }
  else state.sendEffect processId target (.exit reason true false)

private theorem Realizes.linkExit (state : State) (processId target : PID) (reason : Term) :
    Realizes (state.linkExitEffect processId target reason) state (state.linkExit processId target reason) := by
  unfold State.linkExitEffect State.linkExit
  split
  · exact Realizes.modify _ _ _
  · exact Realizes.send _ _ _ _

/-- The effect of `State.answer`. -/
private def State.answerEffect (state : State) (processId : PID) (entry : Entry) : Effect :=
  match entry.signal with
  | .link => state.sendEffect processId entry.source (.exit (.atom "noproc") true false)
  | .monitor reference => state.sendEffect processId entry.source (.down reference (.atom "noproc"))
  | .isAlive => state.sendEffect processId entry.source (.reply (.atom "false"))
  | _ => {}

private theorem Realizes.answer (state : State) (processId : PID) (entry : Entry) :
    Realizes (state.answerEffect processId entry) state (state.answer processId entry) := by
  unfold State.answerEffect State.answer
  obtain ⟨source, signal⟩ := entry
  cases signal <;> first | exact Realizes.send _ _ _ _ | exact Realizes.refl _

/-- The effect of a fold of operations, each realizing an effect. -/
private def chainEffect (step : State → γ → State) (effect : State → γ → Effect) : State → List γ → Effect
  | _, [] => {}
  | state, item :: rest => (effect state item).andThen (chainEffect step effect (step state item) rest)

private theorem Realizes.foldl {step : State → γ → State} {effect : State → γ → Effect}
    (each : ∀ state item, Realizes (effect state item) state (step state item)) :
    ∀ (items : List γ) (state : State), Realizes (chainEffect step effect state items) state (items.foldl step state)
  | [], state => Realizes.refl state
  | item :: rest, state => (each state item).andThen (Realizes.foldl each rest (step state item))

/-- The effect of a link exit of a process that ended, applied as it is sent. -/
private def State.eagerExitEffect (processId : PID) (reason : Term) (state : State) (target : PID) : Effect :=
  if state.eagerLink processId target reason then
    (Effect.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
      { exiting with links := Kernel.filter (· != target) exiting.links } }).andThen
      ((state.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
        { exiting with links := Kernel.filter (· != target) exiting.links } }).linkExitEffect processId target reason)
  else {}

/-- The effect of `State.terminate`. -/
private def State.terminateEffect (state : State) (processId : PID) (reason : Term) : Effect :=
  let process := state.process processId
  let links := Kernel.foldl (fun links (peer, unlinking) =>
    if unlinking.isNone then insertPid peer links else links) [] process.links
  let queue := Kernel.filter (fun entry => match entry.signal with
    | .link | .monitor _ | .isAlive => true
    | _ => false) process.queue
  let retimed : State := { state with timers := Kernel.filter (·.destination != processId) state.timers }
  let ended := retimed.set processId { process with
    mailbox := [], queue, parked := none, exiting := some { reason, links, downs := process.monitors } }
  let exit (state : State) (target : PID) : State := if state.eagerLink processId target reason then
      (state.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
        { exiting with links := Kernel.filter (· != target) exiting.links } }).linkExit processId target reason
    else state
  -- It changes the timers only when one is to the process, as its frames say.
  let retime := if Kernel.any state.timers (·.destination == processId) then
      Effect.retime (Kernel.filter (·.destination != processId)) else {}
  (retime.andThen (Effect.put processId { process with
    mailbox := [], queue, parked := none, exiting := some { reason, links, downs := process.monitors } })).andThen
    (chainEffect exit (State.eagerExitEffect processId reason) ended links)

private theorem Realizes.terminate (state : State) (processId : PID) (reason : Term) :
    Realizes (state.terminateEffect processId reason) state (state.terminate processId reason) := by
  unfold State.terminateEffect State.terminate
  simp only [Kernel.foldl_eq]
  have retimed : Realizes (if Kernel.any state.timers (·.destination == processId) then
      Effect.retime (Kernel.filter (·.destination != processId)) else {}) state
      { state with timers := Kernel.filter (·.destination != processId) state.timers } := by
    split
    · exact Realizes.retime _ _
    · rename_i none
      have kept : Kernel.filter (·.destination != processId) state.timers = state.timers := by
        simp only [Kernel.filter_eq, Kernel.any_eq, Bool.not_eq_true, List.any_eq_false] at none ⊢
        exact List.filter_eq_self.mpr fun timer mem => by simpa using none timer mem
      rw [kept]; exact Realizes.refl _
  refine (retimed.andThen (Realizes.put _ _ _)).andThen (Realizes.foldl (fun state target => ?_) _ _)
  unfold State.eagerExitEffect
  split
  · exact (Realizes.modify _ _ _).andThen (Realizes.linkExit _ _ _ _)
  · exact Realizes.refl _

/-- Allocate a reference. -/
private def allocateEffect (processId : PID) : Effect :=
  .modify processId fun process => { process with refCounter := process.refCounter + 1 }

private theorem Realizes.allocate (state : State) (processId : PID) :
    Realizes (allocateEffect processId) state (state.allocate processId).2 :=
  Realizes.modify _ _ _

/-- The effect of `State.request`. -/
private def State.requestEffect (state : State) (processId : PID) : Request → Effect
  | .monitor target alias =>
      let (reference, allocated) := state.allocate processId
      (allocateEffect processId).andThen (if target = processId then {} else
        (allocated.unparkEffect processId).andThen (.modify processId fun process =>
          { process with
            monitoring := Kernel.append process.monitoring [(reference, target)]
            aliases := if alias then Kernel.append process.aliases [reference] else process.aliases
            parked := some (target, reference) }))
  | .demonitor reference _ =>
      .modify processId fun process =>
        { process with
          monitoring := Kernel.filter (·.1 != reference) process.monitoring
          aliases := Kernel.erase process.aliases reference
          parked := match process.parked with
            | some (_, parked) => if parked == reference then none else process.parked
            | none => none }
  | .link target =>
      if target = processId then {} else
      let process := state.process processId
      if Kernel.contains process.eagerExits target then {} else
      if !state.alive target && !process.trapExit then {} else
      match Kernel.lookup target process.links with
      | some none => {}
      | _ =>
          let change := fun process : ProcessState =>
            { process with links := Kernel.append (Kernel.filter (·.1 != target) process.links) [(target, none)] }
          (Effect.modify processId change).andThen ((state.modify processId change).sendEffect processId target .link)
  | .unlink target =>
      if target = processId then {} else
      let process := state.process processId
      match Kernel.lookup target process.links with
      | some none =>
          let id := process.unlinks + 1
          let change := fun process : ProcessState =>
            { process with
              unlinks := id
              links := Kernel.map (fun link => if link.1 == target then (link.1, some id) else link) process.links }
          (Effect.modify processId change).andThen ((state.modify processId change).sendEffect processId target (.unlink id))
      | _ => {}
  | .exit target reason quirk =>
      if target != processId then state.sendEffect processId target (.exit reason false false)
      else if quirk && (isKill reason || !(state.process processId).trapExit) then
        state.sendEffect processId processId (.exit reason false true)
      else state.sendEffect processId processId (.exit reason false false)
  | .trapExit enabled =>
      let process := state.process processId
      if enabled && !process.eagerExits.isEmpty then {} else
      .modify processId fun process => { process with trapExit := enabled }
  | .alive target =>
      if target = processId then {}
      else if state.alive target then state.sendEffect processId target .isAlive
      else state.enqueueEffect processId processId .flush
  | .sendAlias alias message => state.sendEffect processId alias.dropLast (.aliasMessage alias message)
  | .startTimer destination message duration =>
      let (reference, allocated) := state.allocate processId
      (allocateEffect processId).andThen (if allocated.alive destination then
        .retime (insertTimer { reference, destination, message, duration }) else {})
  | .cancelTimer reference =>
      match Kernel.find? (·.reference == reference) state.timers with
      | some _ =>
          (Effect.retime (Kernel.filter (·.reference != reference))).andThen
            (.modify processId fun process => { process with cancels := process.cancels + 1 })
      | none => {}

private theorem Realizes.request (state : State) (processId : PID) (next : Term → Result β) (query : Request) :
    Realizes (state.requestEffect processId query) state (state.request processId next query).state := by
  cases query with
  | monitor target alias =>
    simp only [State.requestEffect, State.request]
    split
    · exact (Realizes.allocate _ _).andThen (Realizes.refl _)
    · exact (Realizes.allocate _ _).andThen ((Realizes.unpark _ _).andThen (Realizes.modify _ _ _))
  | demonitor reference flush =>
    simp only [State.requestEffect, State.request]
    split <;> exact Realizes.modify _ _ _
  | link target =>
    simp only [State.requestEffect, State.request]
    by_cases self : target = processId
    · simp only [self, ↓reduceIte]; exact Realizes.refl _
    · simp only [self, ↓reduceIte]
      by_cases eager : Kernel.contains (state.process processId).eagerExits target = true
      · simp only [eager, ↓reduceIte]; exact Realizes.refl _
      · simp only [eager, Bool.false_eq_true, ↓reduceIte]
        by_cases dead : (!state.alive target && !(state.process processId).trapExit) = true
        · simp only [dead, ↓reduceIte]; exact Realizes.refl _
        · simp only [dead, Bool.false_eq_true, ↓reduceIte]
          cases found : Kernel.lookup target (state.process processId).links with
          | none => exact (Realizes.modify _ _ _).andThen (Realizes.send _ _ _ _)
          | some unlinking =>
            cases unlinking with
            | none => exact Realizes.refl _
            | some _ => exact (Realizes.modify _ _ _).andThen (Realizes.send _ _ _ _)
  | unlink target =>
    simp only [State.requestEffect, State.request]
    by_cases self : target = processId
    · simp only [self, ↓reduceIte]; exact Realizes.refl _
    · simp only [self, ↓reduceIte]
      cases found : Kernel.lookup target (state.process processId).links with
      | none => exact Realizes.refl _
      | some unlinking =>
        cases unlinking with
        | none => exact (Realizes.modify _ _ _).andThen (Realizes.send _ _ _ _)
        | some _ => exact Realizes.refl _
  | exit target reason quirk =>
    simp only [State.requestEffect, State.request]
    repeat' split
    all_goals exact Realizes.send _ _ _ _
  | trapExit enabled =>
    simp only [State.requestEffect, State.request]
    split
    · exact Realizes.refl _
    · exact Realizes.modify _ _ _
  | alive target =>
    simp only [State.requestEffect, State.request]
    repeat' split
    all_goals first | exact Realizes.refl _ | exact Realizes.send _ _ _ _ | exact Realizes.enqueue _ _ _ _
  | sendAlias alias message => exact Realizes.send _ _ _ _
  | startTimer destination message duration =>
    simp only [State.requestEffect, State.request]
    split
    · exact (Realizes.allocate _ _).andThen (Realizes.retime _ _)
    · exact (Realizes.allocate _ _).andThen (Realizes.refl _)
  | cancelTimer reference =>
    simp only [State.requestEffect, State.request]
    cases found : Kernel.find? (·.reference == reference) state.timers with
    | none => exact Realizes.refl _
    | some timer => exact (Realizes.retime _ _).andThen (Realizes.modify _ _ _)

/-- The effect of `State.spawnWith`: the parent's record changes and the child's starts. -/
private def State.spawnEffect (state : State) (processId : PID) (options : SpawnOptions) : Effect :=
  let process := state.process processId
  let child := Kernel.append processId [process.children + 1]
  let started := (state.set processId { process with children := process.children + 1 }).set child {}
  let linked := if options.link then
      (started.modify processId fun process =>
        { process with links := Kernel.append process.links [(child, none)] }).modify child fun other =>
          { other with links := [(processId, none)] }
    else started
  let linkedEffect : Effect := if options.link then
      (Effect.modify processId fun process =>
        { process with links := Kernel.append process.links [(child, none)] }).andThen
        (Effect.modify child fun other => { other with links := [(processId, none)] })
    else {}
  let monitoredEffect : Effect := if options.monitor then
      let (reference, allocated) := linked.allocate processId
      (allocateEffect processId).andThen ((Effect.modify processId fun process =>
        { process with monitoring := Kernel.append process.monitoring [(reference, child)] }).andThen
        (Effect.modify child fun other => { other with monitors := [(reference, processId)] }))
    else {}
  (((Effect.put processId { process with children := process.children + 1 }).andThen (Effect.put child {})).andThen
    linkedEffect).andThen monitoredEffect

private theorem Realizes.spawn (state : State) (processId : PID) (options : SpawnOptions) :
    Realizes (state.spawnEffect processId options) state (state.spawnWith processId options).2 := by
  unfold State.spawnEffect State.spawnWith
  dsimp only
  have base := (Realizes.put state processId { state.process processId with
    children := (state.process processId).children + 1 }).andThen (Realizes.put _ (Kernel.append processId
    [(state.process processId).children + 1]) {})
  split <;> split
  · exact (base.andThen ((Realizes.modify _ _ _).andThen (Realizes.modify _ _ _))).andThen
      ((Realizes.allocate _ _).andThen ((Realizes.modify _ _ _).andThen (Realizes.modify _ _ _)))
  · exact (base.andThen ((Realizes.modify _ _ _).andThen (Realizes.modify _ _ _))).andThen (Realizes.refl _)
  · exact (base.andThen (Realizes.refl _)).andThen
      ((Realizes.allocate _ _).andThen ((Realizes.modify _ _ _).andThen (Realizes.modify _ _ _)))
  · exact (base.andThen (Realizes.refl _)).andThen (Realizes.refl _)

/-- The effect of `State.exitSignal`. -/
private def State.exitSignalEffect (state : State) (target source : PID) (reason : Term) (linked : Bool)
    (normalKills : Bool) : Effect :=
  let process := state.process target
  let link := Kernel.lookup source process.links
  if linked && link.isNone then {} else
  let unlinked : Effect := if linked then
      .modify target fun process => { process with links := Kernel.filter (·.1 != source) process.links }
    else {}
  if linked && link != some none then unlinked
  else if process.trapExit && !(!linked && isKill reason) then
    unlinked.andThen (.modify target fun process =>
      { process with mailbox := Kernel.append process.mailbox [.tuple #[.atom "EXIT", .pid source, reason]] })
  else unlinked

private theorem Realizes.exitSignal (state : State) (target source : PID) (reason : Term) (linked normalKills : Bool) :
    Realizes (state.exitSignalEffect target source reason linked normalKills) state
      (state.exitSignal target source reason linked normalKills).1 := by
  unfold State.exitSignalEffect State.exitSignal
  dsimp only
  split
  · exact Realizes.refl _
  · split
    · split
      · exact Realizes.modify _ _ _
      · simp_all
    · cases linked
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false, Bool.true_and]
        split
        · exact (Realizes.refl _).andThen (Realizes.modify _ _ _)
        · split <;> exact Realizes.refl _
      · simp only [↓reduceIte, Bool.true_and, Bool.not_true, Bool.and_false, Bool.false_eq_true]
        split
        · exact (Realizes.modify _ _ _).andThen (Realizes.modify _ _ _)
        · split <;> exact Realizes.modify _ _ _

/-- Append a handled message to a mailbox. -/
private def appendEffect (processId : PID) (message : Term) : Effect :=
  .modify processId fun process => { process with mailbox := Kernel.append process.mailbox [message] }

private theorem Realizes.append (state : State) (processId : PID) (message : Term) :
    Realizes (appendEffect processId message) state (state.append processId message) :=
  Realizes.modify _ _ _

/-- The effect of `State.handle`. -/
private def State.handleEffect (state : State) (processId : PID) (entry : Entry) : Effect :=
  let process := state.process processId
  let source := entry.source
  match entry.signal with
  | .message message => appendEffect processId message
  | .aliasMessage alias message =>
      if Kernel.contains process.aliases alias then appendEffect processId message else {}
  | .exit reason linked normalKills => state.exitSignalEffect processId source reason linked normalKills
  | .link =>
      if (Kernel.lookup source process.links).isSome then {}
      else .modify processId fun process => { process with links := Kernel.append process.links [(source, none)] }
  | .unlink id =>
      let change := fun process : ProcessState => { process with links := Kernel.filter (·.1 != source) process.links }
      if Kernel.lookup source process.links == some none then
        (Effect.modify processId change).andThen ((state.modify processId change).sendEffect processId source (.unlinkAck id))
      else state.sendEffect processId source (.unlinkAck id)
  | .unlinkAck id =>
      if Kernel.lookup source process.links == some (some id) then
        .modify processId fun process => { process with links := Kernel.filter (·.1 != source) process.links }
      else {}
  | .monitor reference =>
      .modify processId fun process => { process with monitors := Kernel.append process.monitors [(reference, source)] }
  | .down reference reason =>
      let cleared : Effect := if isNormal reason && Kernel.contains process.eagerExits source then
          .modify processId fun process => { process with eagerExits := Kernel.filter (· != source) process.eagerExits }
        else {}
      cleared.andThen (if Kernel.any process.monitoring (·.1 == reference) then
        (Effect.modify processId fun process =>
          { process with monitoring := Kernel.filter (·.1 != reference) process.monitoring
                         aliases := Kernel.erase process.aliases reference }).andThen
          (appendEffect processId (.tuple #[.atom "DOWN", .reference reference, .atom "process", .pid source, reason]))
        else {})
  | .isAlive => state.sendEffect processId source (.reply (.atom "true"))
  | .reply _ | .flush => {}

private theorem Realizes.handle (state : State) (processId : PID) (waiting : Option Wait) (entry : Entry) :
    Realizes (state.handleEffect processId entry) state (state.handle processId waiting entry).1 := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp only [State.handleEffect, State.handle]
  · exact Realizes.append _ _ _
  · split
    · exact Realizes.append _ _ _
    · exact Realizes.refl _
  · exact Realizes.exitSignal _ _ _ _ _ _
  · split
    · exact Realizes.refl _
    · exact Realizes.modify _ _ _
  · split
    · exact (Realizes.modify _ _ _).andThen (Realizes.send _ _ _ _)
    · exact Realizes.send _ _ _ _
  · split
    · exact Realizes.modify _ _ _
    · exact Realizes.refl _
  · exact Realizes.modify _ _ _
  · rename_i reference reason
    have cleared : Realizes (if isNormal reason && Kernel.contains (state.process processId).eagerExits source then
          Effect.modify processId fun process => { process with eagerExits := Kernel.filter (· != source) process.eagerExits }
        else {}) state (if isNormal reason && Kernel.contains (state.process processId).eagerExits source then
          state.modify processId fun process =>
            { process with eagerExits := Kernel.filter (· != source) process.eagerExits }
        else state) := by
      split
      · exact Realizes.modify _ _ _
      · exact Realizes.refl _
    by_cases active : Kernel.any (state.process processId).monitoring (·.1 == reference) = true
    · simp only [active, ↓reduceIte]
      exact cleared.andThen ((Realizes.modify _ _ _).andThen (Realizes.append _ _ _))
    · simp only [active, Bool.false_eq_true, ↓reduceIte]
      exact cleared.andThen (Realizes.refl _)
  · exact Realizes.send _ _ _ _
  · split <;> exact Realizes.refl _
  · split <;> exact Realizes.refl _




/-- Replace the `DOWN`s a process that ended has left to send. -/
private def setDowns (rest : List (List Nat × PID)) (process : ProcessState) : ProcessState :=
  { process with exiting := process.exiting.map fun exiting => { exiting with downs := rest } }

/-- The effect of `State.phase`. -/
private def State.phaseEffect (state : State) (processId : PID) : Effect :=
  let process := state.process processId
  match process.exiting with
  | some exiting =>
    match exiting.downs with
    | (reference, watcher) :: rest =>
        (Effect.modify processId (setDowns rest)).andThen
          ((state.modify processId (setDowns rest)).sendEffect processId watcher (.down reference exiting.reason))
    | [] =>
      match process.queue with
      | entry :: rest =>
          let change := fun process : ProcessState => { process with queue := process.queue.drop 1 }
          (Effect.modify processId change).andThen ((state.modify processId change).answerEffect processId entry)
      | [] => {}
  | none => {}

private theorem Realizes.phase {state next : State} {processId : PID} (phase : state.phase processId = some next) :
    Realizes (state.phaseEffect processId) state next := by
  unfold State.phase at phase
  split at phase
  · rename_i process found
    have same : state.process processId = process := by simp [State.process, found]
    split at phase
    · rename_i exiting exits
      split at phase
      · simp at phase
      · rename_i reference watcher rest links downs
        simp only [Option.some.injEq] at phase; subst phase
        have equal : setDowns rest process = { process with exiting := some { exiting with downs := rest } } := by
          simp [setDowns, exits]
        have modified : state.modify processId (setDowns rest) =
            state.set processId { process with exiting := some { exiting with downs := rest } } := by
          simp [State.modify, found, equal]
        simp only [State.phaseEffect, same, exits, downs]
        rw [modified]
        have set := Realizes.set found (setDowns rest)
        rw [equal] at set
        exact set.andThen (Realizes.send _ _ _ _)
      · rename_i links downs
        split at phase
        · rename_i entry rest queue
          simp only [Option.some.injEq] at phase; subst phase
          have modified : state.modify processId (fun process => { process with queue := process.queue.drop 1 }) =
              state.set processId { process with queue := rest } := by simp [State.modify, found, queue]
          simp only [State.phaseEffect, same, exits, downs, queue]
          rw [modified]
          have set := Realizes.set found (fun process => { process with queue := process.queue.drop 1 })
          simp only [exits, queue, List.drop_succ_cons, List.drop_zero] at set ⊢
          exact set.andThen (Realizes.answer _ _ _)
        · simp at phase
    · simp at phase
  · simp at phase

/-- The effect of `State.fire`. -/
private def State.fireEffect (state : State) (timer : Timer) : Effect :=
  (Effect.retime (Kernel.filter (·.reference != timer.reference))).andThen
    ({ state with timers := Kernel.filter (·.reference != timer.reference) state.timers }.enqueueEffect clock
      timer.destination (.message timer.message))

private theorem Realizes.fire (state : State) (timer : Timer) :
    Realizes (state.fireEffect timer) state (state.fire timer) :=
  (Realizes.retime _ _).andThen (Realizes.enqueue _ _ _ _)

/-- The effect of a process's own step, given its computation. -/
private def Task.ownEffect (state : State) (processId : PID) : Task α → Effect
  | ⟨_, _, some _⟩ => {}
  | ⟨computation, _, none⟩ =>
    match computation with
    | .error .exhausted => { records := [(processId, fun _ => none)] }
    | .ok _ => state.terminateEffect processId (.atom "normal")
    | .error exception => state.terminateEffect processId (exitReason exception)
    | .get _ => {}
    | .set updated _ => .modify processId fun process =>
        { process with pdict := updated.pdict, refCounter := max process.refCounter updated.refCounter }
    | Result.schedule options _ _ => state.spawnEffect processId options
    | .send destination message _ => state.sendEffect processId destination (.message message)
    | .receive _ select _ =>
        match selectMessage (select (state.view processId)) (state.process processId).mailbox with
        | some (_, _, remaining) => .modify processId fun process => { process with mailbox := remaining }
        | none => {}
    | .request query _ => state.requestEffect processId query

private theorem Realizes.remove (state : State) (processId : PID) :
    Realizes { records := [(processId, fun _ => none)] } state (state.remove processId) := by
  refine ⟨fun other => ?_, rfl, rfl⟩
  rw [State.record_remove]
  by_cases same : other = processId
  · subst same; simp [Effect.record, changeOf]
  · simp [Effect.record, changeOf, Ne.symm same, same]

private theorem Realizes.own {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.own state processId) :
    Realizes (task.ownEffect state processId) state transition.state := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    cases computation with
    | ok =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      exact Realizes.terminate _ _ _
    | error exception =>
      cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;>
        first | exact Realizes.remove _ _ | exact Realizes.terminate _ _ _
    | get =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      exact Realizes.refl _
    | set =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      exact Realizes.modify _ _ _
    | schedule =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      exact Realizes.spawn _ _ _
    | send =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      exact Realizes.send _ _ _ _
    | receive timeout select next =>
      simp only [Task.own] at mem
      simp only [Task.ownEffect]
      split at mem
      · rename_i found
        simp only [List.mem_singleton] at mem; subst mem
        simp only [found]
        exact Realizes.modify _ _ _
      · rename_i found
        simp only [found]
        split at mem
        · simp at mem
        · split at mem
          · simp at mem
          · simp only [List.mem_singleton] at mem; subst mem
            exact Realizes.refl _
    | request query next =>
      have := Realizes.request state processId next query
      simp only [Task.own] at mem
      split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> rename_i found <;>
        simpa [Task.ownEffect, found, Answer.state] using this

/-- The effect of handling the oldest queued signal. -/
private def Task.handleEffect (state : State) (processId : PID) (task : Task α) : Effect :=
  let process := state.process processId
  match process.queue with
  | [] => {}
  | entry :: rest =>
    let popped := state.set processId { process with queue := rest }
    let (_, _, exits) := popped.handle processId (task.wait.map (·.1)) entry
    let handled := (Effect.modify processId fun process => { process with queue := process.queue.drop 1 }).andThen
      (popped.handleEffect processId entry)
    match exits with
    | some reason => handled.andThen
        ((popped.handle processId (task.wait.map (·.1)) entry).1.terminateEffect processId reason)
    | none => handled

private theorem Realizes.handleStep {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.handle state processId) :
    Realizes (task.handleEffect state processId) state transition.state := by
  simp only [Task.handle] at mem
  simp only [Task.handleEffect]
  cases queue : (state.process processId).queue with
  | nil => simp [queue] at mem
  | cons entry rest =>
    simp only [queue] at mem ⊢
    have found : state.record processId = some (state.process processId) := by
      cases record : state.record processId with
      | none => simp [State.process, record] at queue
      | some process => simp [State.process, record]
    have popped := Realizes.set found (fun process => { process with queue := process.queue.drop 1 })
    simp only [queue, List.drop_succ_cons, List.drop_zero] at popped
    have handled := popped.andThen (Realizes.handle (state.set processId { state.process processId with queue := rest })
      processId (task.wait.map (·.1)) entry)
    generalize (State.set _ _ _).handle _ _ _ = result at mem handled ⊢
    obtain ⟨handledState, resumed, exits⟩ := result
    dsimp only at mem handled ⊢
    cases exits with
    | some reason =>
      simp only [List.mem_singleton] at mem; subst mem
      exact handled.andThen (Realizes.terminate _ _ _)
    | none =>
      simp only at mem ⊢
      split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> exact handled

/-! ### Composing changes within frames -/

/-- The union of two masks. -/
private def Mask.union (first second : Mask) : Mask := fun bit => first bit || second bit

private theorem ProcessState.Same.left {first second : Mask} {process base : ProcessState}
    (same : process.Same (first.union second) base) : process.Same first base :=
  ⟨fun read => same.1 (by simp [Mask.union, read]), fun read => same.2.1 (by simp [Mask.union, read]),
    fun part read => same.2.2 part (by simp [Mask.union, read])⟩

private theorem ProcessState.Same.right {first second : Mask} {process base : ProcessState}
    (same : process.Same (first.union second) base) : process.Same second base :=
  ⟨fun read => same.1 (by simp [Mask.union, read]), fun read => same.2.1 (by simp [Mask.union, read]),
    fun part read => same.2.2 part (by simp [Mask.union, read])⟩

/-- A change within its frame takes records agreeing with the base on its reads
and another frame's reads to records agreeing with its image on the other's
reads, when the other's reads of its writes are read by it too. -/
private theorem Framed.same {reads writes reads' : Mask} {base process : ProcessState}
    {change : ProcessState → ProcessState} (framed : Framed reads writes base change)
    (same : process.Same (reads.union reads') base)
    (popped : reads' headBit → writes headBit → reads tailBit) :
    (change process).Same reads' (change base) := by
  obtain ⟨keeps, depends, ⟨dropped, added, -, noHead, -, queue⟩, -, -, -, -⟩ := framed
  have mine := same.left
  have self := ProcessState.Same.refl reads base
  refine ⟨fun read => ?_, fun read => ?_, fun part read => ?_⟩
  · rw [queue _ mine, queue _ self, same.1 (by simp [Mask.union, read])]
  · rw [queue _ mine, queue _ self]
    cases head : writes headBit
    · rw [noHead head]
      have first : process.queue.head? = base.queue.head? := same.2.1 (by simp [Mask.union, read])
      cases equal : process.queue <;> cases equal' : base.queue <;> simp_all
    · rw [same.1 (by simp [Mask.union, popped read head])]
  · cases written : writes part.bit
    · rw [keeps _ mine part written, keeps _ self part written]
      exact same.right.2.2 part read
    · exact depends _ _ mine self part written (same.2.2 part (by simp [Mask.union, read]))

/-- Two changes within frames, one after the other, are within the union of
their frames, when the second reads of what the first writes only what the
first reads too, they do not both remove a queue's head, and what the second
reads of a queue is there before the first. -/
private theorem Framed.comp {reads writes reads' writes' : Mask} {base : ProcessState}
    {change change' : ProcessState → ProcessState}
    (framed : Framed reads writes base change) (framed' : Framed reads' writes' (change base) change')
    (popped : reads' headBit → writes headBit → reads tailBit)
    (once : writes headBit → writes' headBit → False)
    (appended : writes tailBit → writes' headBit → False)
    (nonempty : reads' headBit → (reads.union reads') tailBit ∨ base.queue ≠ []) :
    Framed (reads.union reads') (writes.union writes') base (change' ∘ change) := by
  -- The second removes a head only from a queue the first appended nothing to.
  have pops'' : writes' headBit → base.queue ≠ [] := fun popping empty => by
    obtain ⟨-, -, ⟨dropped, added, -, -, noTail, queue⟩, -⟩ := framed
    have none : added = [] := by
      cases tail : writes tailBit
      · exact noTail tail
      · exact (appended tail popping).elim
    have := framed'.2.2.2.2.2.1 popping
    rw [queue base (ProcessState.Same.refl _ _), empty, none] at this
    simp at this
  have through : ∀ process, process.Same (reads.union reads') base →
      (change process).Same reads' (change base) := fun process same => framed.same same popped
  obtain ⟨keeps, depends, queue, tail, head, pops, live⟩ := framed
  obtain ⟨keeps', depends', queue', tail', head', pops', live'⟩ := framed'
  have self := ProcessState.Same.refl reads base
  have self' := ProcessState.Same.refl reads' (change base)
  refine ⟨fun process same part written => ?_, fun process process' same same' part written equal => ?_,
    ?_, fun read => ?_, fun read => ?_, fun written => ?_, fun written process same => ?_⟩
  · simp only [Mask.union, Bool.or_eq_false_iff] at written
    simp only [Function.comp]
    rw [keeps' _ (through _ same) part written.2, keeps _ same.left part written.1]
  · simp only [Function.comp]
    have first : (change process).get part = (change process').get part := by
      cases mine : writes part.bit
      · rw [keeps _ same.left part mine, keeps _ same'.left part mine, equal]
      · exact depends _ _ same.left same'.left part mine equal
    cases theirs : writes' part.bit
    · rw [keeps' _ (through _ same) part theirs, keeps' _ (through _ same') part theirs, first]
    · exact depends' _ _ (through _ same) (through _ same') part theirs first
  · obtain ⟨dropped, added, one, noHead, noTail, queue⟩ := queue
    obtain ⟨dropped', added', one', noHead', noTail', queue'⟩ := queue'
    by_cases popping : writes' headBit = true
    · have empty : added = [] := by
        cases tail : writes tailBit
        · exact noTail tail
        · exact (appended tail popping).elim
      have first : dropped = 0 := by
        cases head : writes headBit
        · exact noHead head
        · exact (once head popping).elim
      refine ⟨dropped', added', one', fun none => ?_, fun none => ?_, fun process same => ?_⟩
      · simp [Mask.union, popping] at none
      · simp only [Mask.union, Bool.or_eq_false_iff] at none; exact noTail' none.2
      · simp only [Function.comp]
        rw [queue' _ (through _ same), queue _ same.left, empty, first]; simp
    · have second : dropped' = 0 := noHead' (by simpa using popping)
      refine ⟨dropped, added ++ added', one, fun none => ?_, fun none => ?_, fun process same => ?_⟩
      · simp only [Mask.union, Bool.or_eq_false_iff] at none; exact noHead none.1
      · simp only [Mask.union, Bool.or_eq_false_iff] at none; rw [noTail none.1, noTail' none.2]; rfl
      · simp only [Function.comp]
        rw [queue' _ (through _ same), queue _ same.left, second]; simp
  · simp only [Mask.union, Bool.or_eq_true] at read ⊢
    rcases read with read | read
    · exact .inl (tail read)
    · exact .inr (tail' read)
  · rcases (by simpa [Mask.union] using read : reads headBit ∨ reads' headBit) with read | read
    · rcases head read with tail | nonempty
      · exact .inl (by simp [Mask.union, tail])
      · exact .inr nonempty
    · exact nonempty read
  · simp only [Mask.union, Bool.or_eq_true] at written
    rcases written with written | written
    · exact pops written
    · exact pops'' written
  · simp only [Mask.union, Bool.or_eq_false_iff] at written
    simp only [Function.comp]
    rw [live' written.2 _ (through _ same), live written.1 _ same.left]

private theorem ProcessState.Same.mono {mask mask' : Mask} {process base : ProcessState}
    (same : process.Same mask' base) (fewer : ∀ bit, mask bit → mask' bit) : process.Same mask base :=
  ⟨fun read => same.1 (fewer _ read), fun read => same.2.1 (fewer _ read),
    fun part read => same.2.2 part (fewer _ read)⟩

/-- A change within a frame is within a larger one. -/
private theorem Framed.mono {reads writes reads' writes' : Mask} {base : ProcessState}
    {change : ProcessState → ProcessState} (framed : Framed reads writes base change)
    (moreReads : ∀ bit, reads bit → reads' bit) (moreWrites : ∀ bit, writes bit → writes' bit)
    (tail : reads' tailBit → reads' headBit) (nonempty : reads' headBit → reads' tailBit ∨ base.queue ≠ [])
    (pops : writes' headBit → base.queue ≠ []) :
    Framed reads' writes' base change := by
  obtain ⟨keeps, depends, ⟨dropped, added, one, noHead, noTail, queue⟩, -, -, -, live⟩ := framed
  have fewer : ∀ {process : ProcessState}, process.Same reads' base → process.Same reads base :=
    fun same => same.mono moreReads
  have unwritten : ∀ {bit}, writes' bit = false → writes bit = false := fun {bit} none => by
    cases written : writes bit
    · rfl
    · simp [moreWrites bit written] at none
  refine ⟨fun process same part none => keeps process (fewer same) part (unwritten none),
    fun process process' same same' part _ equal => ?_,
    ⟨dropped, added, one, fun none => noHead (unwritten none), fun none => noTail (unwritten none),
      fun process same => queue process (fewer same)⟩, tail, nonempty, pops,
    fun none process same => live (unwritten none) process (fewer same)⟩
  cases written : writes part.bit
  · rw [keeps _ (fewer same) part written, keeps _ (fewer same') part written, equal]
  · exact depends _ _ (fewer same) (fewer same') part written equal

/-! ### Frames of record changes -/

/-- The fields of a frame mask, by bit. -/
private def bitsOf (mask : Nat) : Mask := mask.testBit

/-- Queueing a signal writes the queue's tail and reads nothing. -/
private theorem Framed.queueAt (source : PID) (signal : Signal) (base : ProcessState) :
    Framed (bitsOf 0) (bitsOf Field.queueTail) base (queueAt source signal) := by
  refine ⟨fun process _ part none => ?_, fun process process' _ _ part written _ => ?_,
    ⟨0, [{ source, signal }], by decide, fun _ => rfl, fun none => ?_, fun process _ => ?_⟩,
    fun read => ?_, fun read => ?_, fun written => ?_, fun _ process _ => rfl⟩
  · cases part <;> rfl
  · cases part <;> simp (config := { decide := true }) [Field.queueTail] at written
  · simp (config := { decide := true }) [bitsOf, Field.queueTail, tailBit] at none
  · simp [Concurrent.queueAt, Kernel.append_eq]
  · simp (config := { decide := true }) [bitsOf, tailBit] at read
  · simp (config := { decide := true }) [bitsOf, headBit] at read
  · simp (config := { decide := true }) [bitsOf, Field.queueTail, headBit] at written

/-- Prove that a change updating some fields of a record, as functions of the
fields its frame reads and of themselves, is within its frame, for masks given
as numbers. The queue is kept. -/
local syntax "framed_update" : tactic
macro_rules
  | `(tactic| framed_update) => `(tactic|
      refine ⟨fun process _ part none => ?_, fun process process' same same' part written equal => ?_,
        ⟨0, [], by decide, fun _ => rfl, fun _ => rfl, fun process _ => by simp⟩,
        fun read => ?_, fun read => ?_, fun written => ?_, fun _ process _ => ?_⟩ <;>
      first
        | (cases part <;> first | rfl | (simp (config := { decide := true }) [bitsOf] at none; done))
        | (cases part <;> first
            | ((simp_all [ProcessState.get] <;> rfl); done)
            | (simp (config := { decide := true }) [bitsOf] at written; done))
        | (simp (config := { decide := true }) [bitsOf, tailBit, headBit] at read)
        | (simp (config := { decide := true }) [bitsOf, headBit] at written)
        | simp)

private example (base : ProcessState) :
    Framed (bitsOf 0) (bitsOf Field.parked) base (fun process => { process with parked := none }) := by
  framed_update

private example (base : ProcessState) (target : PID) :
    Framed (bitsOf Field.links) (bitsOf Field.links) base
      (fun process => { process with links := Kernel.filter (·.1 != target) process.links }) := by
  framed_update

private example (base : ProcessState) (target : PID) (reference : List Nat) :
    Framed (bitsOf (Field.monitoring ||| Field.aliases)) (bitsOf (Field.monitoring ||| Field.aliases)) base
      (fun process => { process with
          monitoring := Kernel.filter (·.1 != reference) process.monitoring
          aliases := Kernel.erase process.aliases reference }) := by
  framed_update

private example (base : ProcessState) (processId : PID) :
    Framed (bitsOf (Field.links ||| Field.eagerExits)) (bitsOf (Field.links ||| Field.eagerExits)) base
      (fun process => { process with
          links := Kernel.filter (·.1 != processId) process.links
          eagerExits := insertPid processId process.eagerExits }) := by
  framed_update

/-! ### Composing effects within frames -/

private theorem readsOf_append (frames frames' : List Frame) (processId : PID) :
    readsOf (frames ++ frames') processId = (readsOf frames processId).union (readsOf frames' processId) := by
  funext bit; simp [readsOf, Mask.union, List.any_append]

private theorem writesOf_append (frames frames' : List Frame) (processId : PID) :
    writesOf (frames ++ frames') processId = (writesOf frames processId).union (writesOf frames' processId) := by
  funext bit; simp [writesOf, Mask.union, List.any_append]

/-- Frames that read a queue's tail only with its head, and, unless they write
the whole record, read its head without its tail, or remove it, only where
there is one. -/
private def WellFramed (frames : List Frame) (state : State) : Prop :=
  ∀ processId, (readsOf frames processId tailBit → readsOf frames processId headBit) ∧
    ∀ process, state.record processId = some process → ¬ (∀ bit, bit < 17 → writesOf frames processId bit) →
      (readsOf frames processId headBit → readsOf frames processId tailBit ∨ process.queue ≠ []) ∧
      (writesOf frames processId headBit → process.queue ≠ [])

/-- Two effects within frames, one after the other, are within both frames,
when the second reads of what the first writes only what the first reads, and
they neither both remove a queue's head nor remove it after appending to it. -/
private theorem Effect.InFrames.andThen {effect effect' : Effect} {frames frames' : List Frame} {state : State}
    (framed : effect.InFrames frames state) (framed' : effect'.InFrames frames' (effect.apply state))
    (wellFramed : WellFramed (frames ++ frames') state)
    (popped : ∀ processId, readsOf frames' processId headBit → writesOf frames processId headBit →
      readsOf frames processId tailBit)
    (once : ∀ processId, writesOf frames processId headBit → writesOf frames' processId headBit → False)
    (appended : ∀ processId, writesOf frames processId tailBit → writesOf frames' processId headBit → False) :
    (effect.andThen effect').InFrames (frames ++ frames') state := by
  intro processId
  rw [Effect.record_andThen, readsOf_append, writesOf_append]
  have bits := wellFramed processId
  rw [readsOf_append, writesOf_append] at bits
  by_cases all : ∀ bit, bit < 17 → (writesOf frames processId).union (writesOf frames' processId) bit
  · exact .inr (.inl all)
  have widen : ∀ {reads writes : Mask} {process : ProcessState} {change : ProcessState → ProcessState},
      state.record processId = some process → Framed reads writes process change →
      (∀ bit, reads bit → (readsOf frames processId).union (readsOf frames' processId) bit) →
      (∀ bit, writes bit → (writesOf frames processId).union (writesOf frames' processId) bit) →
      Framed ((readsOf frames processId).union (readsOf frames' processId))
        ((writesOf frames processId).union (writesOf frames' processId)) process change :=
    fun found framed moreReads moreWrites => framed.mono moreReads moreWrites bits.1
      (fun read => ((bits.2 _ found all).1 read)) (fun written => ((bits.2 _ found all).2 written))
  have left : ∀ bit, readsOf frames processId bit → (readsOf frames processId).union (readsOf frames' processId) bit :=
    fun bit read => by simp [Mask.union, read]
  have right : ∀ bit, readsOf frames' processId bit → (readsOf frames processId).union (readsOf frames' processId) bit :=
    fun bit read => by simp [Mask.union, read]
  have left' : ∀ bit, writesOf frames processId bit →
      (writesOf frames processId).union (writesOf frames' processId) bit := fun bit written => by simp [Mask.union, written]
  have right' : ∀ bit, writesOf frames' processId bit →
      (writesOf frames processId).union (writesOf frames' processId) bit := fun bit written => by simp [Mask.union, written]
  rcases framed processId with same | all | ⟨change, equal, used, inside⟩
  · -- The first leaves the record: the second is within its own frames.
    have keep : (effect.apply state).record processId = state.record processId := by
      rw [Effect.record_apply, same]; rfl
    rw [same]
    rcases framed' processId with same' | all' | ⟨change', equal', used', inside'⟩
    · exact .inl (by rw [same']; rfl)
    · exact .inr (.inl fun bit lower => right' bit (all' bit lower))
    · refine .inr (.inr ⟨change', by rw [equal']; rfl, ?_, fun process found => ?_⟩)
      · obtain ⟨bit, lower, read | written⟩ := used'
        · exact ⟨bit, lower, .inl (right bit read)⟩
        · exact ⟨bit, lower, .inr (right' bit written)⟩
      · rw [keep] at inside'
        exact widen found (inside' process found) right right'
  · exact .inr (.inl fun bit lower => left' bit (all bit lower))
  · rcases framed' processId with same' | all' | ⟨change', equal', used', inside'⟩
    · refine .inr (.inr ⟨change, by rw [same', equal]; rfl, ?_, fun process found => ?_⟩)
      · obtain ⟨bit, lower, read | written⟩ := used
        · exact ⟨bit, lower, .inl (left bit read)⟩
        · exact ⟨bit, lower, .inr (left' bit written)⟩
      · exact widen found (inside process found) left left'
    · exact .inr (.inl fun bit lower => right' bit (all' bit lower))
    · refine .inr (.inr ⟨change' ∘ change, by rw [equal, equal']; funext record; cases record <;> rfl, ?_,
        fun process found => ?_⟩)
      · obtain ⟨bit, lower, read | written⟩ := used
        · exact ⟨bit, lower, .inl (left bit read)⟩
        · exact ⟨bit, lower, .inr (left' bit written)⟩
      · have after : (effect.apply state).record processId = some (change process) := by
          rw [Effect.record_apply, equal, found]; rfl
        exact (inside process found).comp (inside' _ after) (popped processId)
          (once processId) (appended processId) (fun read => (bits.2 _ found all).1 (by simp [Mask.union, read]))

/-! ### Frames of steps -/




/-- An effect changing one record by a change within a frame given by one entry. -/
private theorem Effect.InFrames.modify {processId : PID} {change : ProcessState → ProcessState}
    {reads writes : Nat} {state : State} {frames : List Frame}
    (inside : (processId, reads, writes) ∈ frames)
    (used : ∃ bit, bit < 17 ∧ (reads.testBit bit ∨ writes.testBit bit))
    (framed : ∀ process, state.record processId = some process →
      Framed (readsOf frames processId) (writesOf frames processId) process change) :
    (Effect.modify processId change).InFrames frames state := by
  intro other
  rw [Effect.record_modify]
  by_cases same : other = processId
  · subst same
    simp only [↓reduceIte]
    refine .inr (.inr ⟨change, rfl, ?_, framed⟩)
    obtain ⟨bit, lower, read | written⟩ := used
    · exact ⟨bit, lower, .inl (List.any_eq_true.mpr ⟨_, inside, by simp [read]⟩)⟩
    · exact ⟨bit, lower, .inr (List.any_eq_true.mpr ⟨_, inside, by simp [written]⟩)⟩
  · simp [same]

/-- The empty effect is within any frames. -/
private theorem Effect.InFrames.empty (frames : List Frame) (state : State) : ({} : Effect).InFrames frames state :=
  fun _ => .inl rfl

/-- A change within the frame of one entry is within all the frames of its
process, when none of them reads or removes the queue's head. -/
private theorem Framed.widen {frames : List Frame} {processId : PID} {reads writes reads' writes' : Nat}
    {base : ProcessState} {change : ProcessState → ProcessState}
    (framed : Framed (bitsOf reads') (bitsOf writes') base change)
    (fewerReads : ∀ bit, reads'.testBit bit → reads.testBit bit)
    (fewerWrites : ∀ bit, writes'.testBit bit → writes.testBit bit)
    (inside : (processId, reads, writes) ∈ frames)
    (quiet : ∀ entry ∈ frames, entry.1 = processId →
      entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false) :
    Framed (readsOf frames processId) (writesOf frames processId) base change := by
  have none : ∀ {bit}, (bit = headBit ∨ bit = tailBit) → readsOf frames processId bit = false := by
    intro bit is
    simp only [readsOf, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
    intro entry mem same
    have := quiet entry mem same
    rcases is with rfl | rfl <;> simp [this]
  have noPop : writesOf frames processId headBit = false := by
    simp only [writesOf, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
    intro entry mem same
    simp [(quiet entry mem same).2.2]
  refine framed.mono (fun bit read => List.any_eq_true.mpr ⟨_, inside, by simpa [bitsOf] using fewerReads bit read⟩)
    (fun bit written => List.any_eq_true.mpr ⟨_, inside, by simpa [bitsOf] using fewerWrites bit written⟩)
    (fun read => by rw [none (.inr rfl)] at read; simp at read)
    (fun read => by rw [none (.inl rfl)] at read; simp at read)
    (fun written => by rw [noPop] at written; simp at written)

/-- Queueing a signal is within its frames. -/
private theorem Effect.InFrames.enqueue (state : State) (source target : PID) (signal : Signal) :
    (state.enqueueEffect source target signal).InFrames (state.enqueueFrames source target signal) state := by
  have quiet : ∀ entry ∈ state.enqueueFrames source target signal, ∀ processId, entry.1 = processId →
      entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false := by
    intro entry mem _ _
    simp only [State.enqueueFrames, State.appendFrames] at mem
    split at mem <;> (try split at mem) <;> (try split at mem) <;>
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at mem <;>
      (try rcases mem with rfl | rfl) <;> (try subst mem) <;> (dsimp only; decide)
  have queued : ∀ (receiver sender : PID) (appended : Signal) (reads : Nat),
      (receiver, reads, Field.queueTail) ∈ state.enqueueFrames source target signal →
      (Effect.modify receiver (queueAt sender appended)).InFrames (state.enqueueFrames source target signal) state :=
    fun receiver sender appended reads inside => Effect.InFrames.modify inside ⟨1, by decide, .inr (by decide)⟩
      fun process _ => (Framed.queueAt sender appended process).widen (by simp [Nat.zero_testBit])
        (fun _ written => written) inside (quiet · · receiver)
  have fallback : state.alive target = false →
      (state.fallbackEffect source target signal).InFrames (state.enqueueFrames source target signal) state := by
    intro dead
    have frames : state.enqueueFrames source target signal = (target, Field.live, 0) :: match signal with
        | .link => state.appendFrames target source (.exit (.atom "noproc") true false)
        | .monitor reference => state.appendFrames target source (.down reference (.atom "noproc"))
        | .unlink _ => [(source, Field.links, Field.links)]
        | .isAlive => state.appendFrames target source (.reply (.atom "false"))
        | _ => [] := by unfold State.enqueueFrames; rw [dead]; rfl
    cases signal <;> simp only [State.fallbackEffect]
    all_goals first
      | exact Effect.InFrames.empty _ _
      | (apply queued source target _ Field.live
         rw [frames]; simp [State.appendFrames])
      | skip
    rename_i id
    have inside : (source, Field.links, Field.links) ∈ state.enqueueFrames source target (.unlink id) := by
      rw [frames]; simp
    refine Effect.InFrames.modify inside ⟨6, by decide, .inl (by decide)⟩ fun process _ => ?_
    have framed : Framed (bitsOf Field.links) (bitsOf Field.links) process
        (fun process => { process with links := Kernel.filter (·.1 != target) process.links }) := by
      framed_update
    exact framed.widen (fun _ read => read) (fun _ written => written) inside (quiet · · source)
  unfold State.enqueueEffect
  cases found : state.record target with
  | some process =>
    simp only
    split
    · rename_i alive
      have : state.alive target = true := by simp [State.alive, found, alive]
      apply queued target source signal (if signal matches .unlinkAck _ then
        Field.live ||| Field.links ||| Field.unlinks else Field.live)
      simp only [State.enqueueFrames, this, ↓reduceIte, State.appendFrames]
      cases signal <;> simp
    · rename_i exiting
      have : state.alive target = false := by
        simp only [State.alive, found]; cases equal : process.exiting <;> simp_all
      exact fallback this
  | none =>
    have : state.alive target = false := by simp [State.alive, found]
    exact fallback this

private theorem State.enqueueFrames_congr {state other : State} {source target : PID} (signal : Signal)
    (alive : other.alive target = state.alive target) :
    other.enqueueFrames source target signal = state.enqueueFrames source target signal := by
  simp only [State.enqueueFrames, State.appendFrames, alive]

private theorem State.alive_modify (state : State) (processId target : PID) (change : ProcessState → ProcessState)
    (live : ∀ process, (change process).exiting.isSome = process.exiting.isSome) :
    (state.modify processId change).alive target = state.alive target := by
  unfold State.modify
  split
  · rename_i process found
    simp only [State.alive, State.record_set]
    by_cases same : target = processId
    · subst same; simp only [↓reduceIte, found]
      have := live process
      cases equal : (change process).exiting <;> cases equal' : process.exiting <;> simp_all
    · simp [same]
  · rfl

private theorem State.alive_fallback (state : State) (source target other : PID) (signal : Signal) :
    (state.fallback source target signal).alive other = state.alive other := by
  cases signal <;> simp only [State.fallback] <;> first | rfl | exact State.alive_modify _ _ _ _ fun _ => rfl

private theorem State.alive_enqueue (state : State) (source target other : PID) (signal : Signal) :
    (state.enqueue source target signal).alive other = state.alive other := by
  unfold State.enqueue
  split
  · rename_i process found
    split
    · rename_i exiting
      simp only [State.alive, State.record_set]
      by_cases same : other = target
      · subst same; simp [found, exiting]
      · simp [same]
    · exact State.alive_fallback _ _ _ _ _
  · exact State.alive_fallback _ _ _ _ _

private theorem State.alive_unpark (state : State) (processId other : PID) :
    (state.unpark processId).alive other = state.alive other := by
  unfold State.unpark
  split
  · rw [State.alive_enqueue]; exact State.alive_modify _ _ _ _ fun _ => rfl
  · rfl

private theorem Effect.InFrames.congr {effect : Effect} {frames : List Frame} {state other : State}
    (framed : effect.InFrames frames state) (same : ∀ processId, other.record processId = state.record processId) :
    effect.InFrames frames other := by
  intro processId
  rcases framed processId with same' | all | ⟨change, equal, used, inside⟩
  · exact .inl same'
  · exact .inr (.inl all)
  · exact .inr (.inr ⟨change, equal, used, fun process found => inside process (by rw [← same]; exact found)⟩)

/-- Frames that read none of the fields of a mask. -/
private theorem readsOf_false {frames : List Frame} {processId : PID} {bit : Nat}
    (none : ∀ entry ∈ frames, entry.2.1.testBit bit = false) : readsOf frames processId bit = false := by
  simp only [readsOf, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
  intro entry mem _
  simp [none entry mem]

private theorem writesOf_false {frames : List Frame} {processId : PID} {bit : Nat}
    (none : ∀ entry ∈ frames, entry.2.2.testBit bit = false) : writesOf frames processId bit = false := by
  simp only [writesOf, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
  intro entry mem _
  simp [none entry mem]

/-- The fields of frames as powers of two. -/
private theorem fields_pow : Field.queueHead = 2 ^ 0 ∧ Field.queueTail = 2 ^ 1 ∧ Field.mailbox = 2 ^ 2 ∧
    Field.pdict = 2 ^ 3 ∧ Field.refCounter = 2 ^ 4 ∧ Field.children = 2 ^ 5 ∧ Field.links = 2 ^ 6 ∧
    Field.monitors = 2 ^ 7 ∧ Field.monitoring = 2 ^ 8 ∧ Field.aliases = 2 ^ 9 ∧ Field.trapExit = 2 ^ 10 ∧
    Field.cancels = 2 ^ 11 ∧ Field.unlinks = 2 ^ 12 ∧ Field.parked = 2 ^ 13 ∧ Field.eagerExits = 2 ^ 14 ∧
    Field.exiting = 2 ^ 15 ∧ Field.live = 2 ^ 16 := by decide

/-- Read off the fields of a mask built from fields. -/
local syntax "mask_bits" : tactic
macro_rules
  | `(tactic| mask_bits) => `(tactic|
      (obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := fields_pow
       simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, Nat.testBit_or,
         Nat.testBit_two_pow, Nat.zero_testBit, Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true] at *
       try omega))

/-- The entries of `State.enqueueFrames` read only liveness, links and unlinks,
and write only the queue's tail and links. -/
private theorem enqueueFrames_bits {state : State} {source target : PID} {signal : Signal} {entry : Frame}
    (mem : entry ∈ state.enqueueFrames source target signal) :
    (∀ bit, entry.2.1.testBit bit → bit = 16 ∨ bit = 6 ∨ bit = 12) ∧
      ∀ bit, entry.2.2.testBit bit → bit = 1 ∨ bit = 6 := by
  simp only [State.enqueueFrames, State.appendFrames] at mem
  split at mem <;> (try split at mem) <;> (try split at mem) <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at mem <;>
    (try rcases mem with rfl | rfl) <;> (try subst mem) <;> dsimp only <;>
    exact ⟨fun bit set => by mask_bits, fun bit set => by mask_bits⟩

/-- An effect within frames is within larger well-formed frames. -/
private theorem Effect.InFrames.mono {effect : Effect} {frames frames' : List Frame} {state : State}
    (framed : effect.InFrames frames state)
    (moreReads : ∀ processId bit, readsOf frames processId bit → readsOf frames' processId bit)
    (moreWrites : ∀ processId bit, writesOf frames processId bit → writesOf frames' processId bit)
    (wellFramed : WellFramed frames' state) : effect.InFrames frames' state := by
  intro processId
  by_cases all' : ∀ bit, bit < 17 → writesOf frames' processId bit
  · exact .inr (.inl all')
  rcases framed processId with same | all | ⟨change, equal, used, inside⟩
  · exact .inl same
  · exact .inr (.inl fun bit lower => moreWrites _ _ (all bit lower))
  · refine .inr (.inr ⟨change, equal, ?_, fun process found => ?_⟩)
    · obtain ⟨bit, lower, read | written⟩ := used
      · exact ⟨bit, lower, .inl (moreReads _ _ read)⟩
      · exact ⟨bit, lower, .inr (moreWrites _ _ written)⟩
    · exact (inside process found).mono (moreReads _) (moreWrites _) (wellFramed processId).1
        ((wellFramed processId).2 _ found all').1 ((wellFramed processId).2 _ found all').2

/-- Frames that read no queue's head or tail and remove no head are well formed. -/
private theorem WellFramed.quiet {frames : List Frame} {state : State}
    (quiet : ∀ entry ∈ frames, entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧
      entry.2.2.testBit headBit = false) : WellFramed frames state :=
  fun processId => ⟨fun read => by rw [readsOf_false fun entry mem => (quiet entry mem).2.1] at read; simp at read,
    fun _ _ _ => ⟨fun read => by rw [readsOf_false fun entry mem => (quiet entry mem).1] at read; simp at read,
      fun written => by rw [writesOf_false fun entry mem => (quiet entry mem).2.2] at written; simp at written⟩⟩

private theorem readsOf_mono {frames frames' : List Frame} (sub : ∀ entry ∈ frames, entry ∈ frames')
    (processId : PID) (bit : Nat) (read : readsOf frames processId bit) : readsOf frames' processId bit := by
  simp only [readsOf, List.any_eq_true] at read ⊢
  obtain ⟨entry, mem, set⟩ := read
  exact ⟨entry, sub entry mem, set⟩

private theorem writesOf_mono {frames frames' : List Frame} (sub : ∀ entry ∈ frames, entry ∈ frames')
    (processId : PID) (bit : Nat) (written : writesOf frames processId bit) : writesOf frames' processId bit := by
  simp only [writesOf, List.any_eq_true] at written ⊢
  obtain ⟨entry, mem, set⟩ := written
  exact ⟨entry, sub entry mem, set⟩


private theorem writesOf_bits {frames : List Frame} {processId : PID} {bit : Nat}
    (written : writesOf frames processId bit) : ∃ entry ∈ frames, entry.2.2.testBit bit := by
  simp only [writesOf, List.any_eq_true, Bool.and_eq_true] at written
  obtain ⟨entry, mem, -, set⟩ := written
  exact ⟨entry, mem, set⟩

/-- Queueing a monitor signal writes only the queue's tail. -/
private theorem enqueueFrames_monitor {state : State} {source target : PID} {reference : List Nat} {entry : Frame}
    (mem : entry ∈ state.enqueueFrames source target (.monitor reference)) : ∀ bit, entry.2.2.testBit bit → bit = 1 := by
  simp only [State.enqueueFrames, State.appendFrames] at mem
  split at mem <;> simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at mem <;>
    (try rcases mem with rfl | rfl) <;> (try subst mem) <;> dsimp only <;> intro bit set <;> mask_bits

private theorem Realizes.records {effect : Effect} {before after : State} (realizes : Realizes effect before after) :
    ∀ processId, after.record processId = (effect.apply before).record processId := fun processId => by
  rw [realizes.1, Effect.record_apply]

/-- Clearing a parked monitor signal is within a frame writing it. -/
private theorem Effect.InFrames.unparked (state : State) (processId : PID) :
    (Effect.modify processId fun process => { process with parked := none }).InFrames
      [(processId, Field.parked, Field.parked)] state := by
  refine Effect.InFrames.modify (List.mem_singleton.mpr rfl) ⟨13, by decide, .inl (by decide)⟩ fun process _ => ?_
  have framed : Framed (bitsOf Field.parked) (bitsOf Field.parked) process
      (fun process => { process with parked := none }) := by framed_update
  exact framed.widen (fun _ read => read) (fun _ written => written) (List.mem_singleton.mpr rfl)
    fun entry mem _ => by simp only [List.mem_singleton] at mem; subst mem; dsimp only; decide

/-- The entries of `State.enqueueFrames` read no queue and remove no head. -/
private theorem enqueueFrames_quiet {state : State} {source target : PID} {signal : Signal} {entry : Frame}
    (mem : entry ∈ state.enqueueFrames source target signal) :
    entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false := by
  obtain ⟨reads, writes⟩ := enqueueFrames_bits mem
  refine ⟨?_, ?_, ?_⟩
  · cases set : entry.2.1.testBit headBit
    · rfl
    · have := reads _ set; simp [headBit] at this
  · cases set : entry.2.1.testBit tailBit
    · rfl
    · have := reads _ set; simp [tailBit] at this
  · cases set : entry.2.2.testBit headBit
    · rfl
    · have := writes _ set; simp [headBit] at this

/-- Sending a parked monitor signal is within its frames. -/
private theorem Effect.InFrames.unpark (state : State) (source target : PID) (reference : List Nat)
    (parked : (state.process source).parked = some (target, reference)) :
    (state.unparkEffect source).InFrames
      ([(source, Field.parked, Field.parked)] ++ state.enqueueFrames source target (.monitor reference)) state := by
  let unparked := state.modify source fun process => { process with parked := none }
  have first := Effect.InFrames.unparked state source
  have second : (unparked.enqueueEffect source target (.monitor reference)).InFrames
      (state.enqueueFrames source target (.monitor reference))
      ((Effect.modify source fun process => { process with parked := none }).apply state) := by
    have equal : unparked.enqueueFrames source target (.monitor reference) =
        state.enqueueFrames source target (.monitor reference) :=
      State.enqueueFrames_congr _ (State.alive_modify _ _ _ _ fun _ => rfl)
    rw [← equal]
    exact (Effect.InFrames.enqueue unparked _ _ _).congr fun other =>
      ((Realizes.modify state source _).records other).symm
  have parkedBits : ∀ {other bit}, writesOf [(source, Field.parked, Field.parked)] other bit → bit = 13 := by
    intro other bit written
    obtain ⟨entry, mem, set⟩ := writesOf_bits written
    simp only [List.mem_singleton] at mem; subst mem; dsimp only at set; mask_bits
  have unparkFramed := first.andThen second
    (WellFramed.quiet fun entry mem => by
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with rfl | mem
      · dsimp only; decide
      · exact enqueueFrames_quiet mem)
    (fun other _ written => by have := parkedBits written; simp [headBit] at this)
    (fun other written _ => by have := parkedBits written; simp [headBit] at this)
    (fun other written _ => by have := parkedBits written; simp [tailBit] at this)
  have unparkEq : state.unparkEffect source = (Effect.modify source fun process => { process with parked := none }).andThen
      (unparked.enqueueEffect source target (.monitor reference)) := by
    simp only [State.unparkEffect, parked]; rfl
  rw [← unparkEq] at unparkFramed
  exact unparkFramed

/-- Sending a signal is within its frames. -/
private theorem Effect.InFrames.send (state : State) (source target : PID) (signal : Signal) :
    (state.sendEffect source target signal).InFrames (state.sendFrames source target signal) state := by
  have quietEnqueue : ∀ {signal : Signal} {entry : Frame}, entry ∈ state.enqueueFrames source target signal →
      entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false :=
    fun mem => enqueueFrames_quiet mem
  have quiet : ∀ entry ∈ state.sendFrames source target signal,
      entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false := by
    intro entry mem
    simp only [State.sendFrames] at mem
    split at mem
    · split at mem
      · simp only [List.mem_cons, Kernel.append_eq, List.mem_append] at mem
        rcases mem with rfl | mem | mem
        · dsimp only; decide
        · exact quietEnqueue mem
        · exact quietEnqueue mem
      · simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · dsimp only; decide
        · exact quietEnqueue mem
    · simp only [List.mem_cons] at mem
      rcases mem with rfl | mem
      · dsimp only; decide
      · exact quietEnqueue mem
  have wellFramed : WellFramed (state.sendFrames source target signal) state := WellFramed.quiet quiet
  have inside : ∀ {signal'} entry, entry ∈ state.enqueueFrames source target signal' →
      (signal' = signal ∨ ∃ parked reference, (state.process source).parked = some (parked, reference) ∧
        parked = target ∧ signal' = .monitor reference) →
      entry ∈ state.sendFrames source target signal := by
    intro signal' entry mem which
    simp only [State.sendFrames]
    rcases which with rfl | ⟨parked, reference, found, rfl, rfl⟩
    · split
      · split <;> simp [Kernel.append_eq, mem]
      · simp [mem]
    · simp [found, Kernel.append_eq, mem]
  have direct : (state.enqueueEffect source target signal).InFrames (state.sendFrames source target signal) state :=
    (Effect.InFrames.enqueue state source target signal).mono
      (readsOf_mono fun entry mem => inside entry mem (.inl rfl))
      (writesOf_mono fun entry mem => inside entry mem (.inl rfl)) wellFramed
  unfold State.sendEffect
  cases parked : (state.process source).parked with
  | none => exact direct
  | some found =>
    obtain ⟨other, reference⟩ := found
    simp only
    split
    · rename_i same
      have same : other = target := eq_of_beq same
      subst same
      have unparkFramed := Effect.InFrames.unpark state source other reference parked
      have third : ((state.unpark source).enqueueEffect source other signal).InFrames
          (state.enqueueFrames source other signal) ((state.unparkEffect source).apply state) := by
        have equal : (state.unpark source).enqueueFrames source other signal = state.enqueueFrames source other signal :=
          State.enqueueFrames_congr _ (State.alive_unpark _ _ _)
        rw [← equal]
        exact (Effect.InFrames.enqueue _ _ _ _).congr fun processId => ((Realizes.unpark state source).records processId).symm
      have writeBits : ∀ {processId bit}, writesOf ([(source, Field.parked, Field.parked)] ++
          state.enqueueFrames source other (.monitor reference)) processId bit → bit = 13 ∨ bit = 1 := by
        intro processId bit written
        obtain ⟨entry, mem, set⟩ := writesOf_bits written
        simp only [List.mem_append, List.mem_singleton] at mem
        rcases mem with rfl | mem
        · dsimp only at set; left; mask_bits
        · right; exact enqueueFrames_monitor mem _ set
      have total := unparkFramed.andThen third
        (WellFramed.quiet fun entry mem => by
          simp only [List.mem_append, List.mem_singleton] at mem
          rcases mem with (rfl | mem) | mem
          · dsimp only; decide
          · exact enqueueFrames_quiet mem
          · exact enqueueFrames_quiet mem)
        (fun processId _ written => by have := writeBits written; simp [headBit] at this)
        (fun processId written _ => by have := writeBits written; simp [headBit] at this)
        (fun processId _ written => by
          obtain ⟨entry, mem, set⟩ := writesOf_bits written
          have := (enqueueFrames_bits mem).2 _ set; simp [headBit] at this)
      refine total.mono (readsOf_mono fun entry mem => ?_) (writesOf_mono fun entry mem => ?_) wellFramed <;>
        (simp only [List.mem_append, List.mem_singleton] at mem
         rcases mem with (rfl | mem) | mem
         · simp [State.sendFrames, parked]
         · exact inside entry mem (.inr ⟨other, reference, parked, rfl, rfl⟩)
         · exact inside entry mem (.inl rfl))
    · exact direct

/-- Firing a timer is within its frames. -/
private theorem Effect.InFrames.fire (state : State) (timer : Timer) :
    (state.fireEffect timer).InFrames (state.enqueueFrames clock timer.destination (.message timer.message)) state := by
  let retimed : State := { state with timers := Kernel.filter (·.reference != timer.reference) state.timers }
  have second : (retimed.enqueueEffect clock timer.destination (.message timer.message)).InFrames
      (state.enqueueFrames clock timer.destination (.message timer.message))
      ((Effect.retime (Kernel.filter (·.reference != timer.reference))).apply state) :=
    (Effect.InFrames.enqueue retimed _ _ _).congr fun processId =>
      ((Realizes.retime state _).records processId).symm
  have total := (Effect.InFrames.empty [] state).andThen (effect := Effect.retime _) second
    (WellFramed.quiet fun _ mem => enqueueFrames_quiet (List.nil_append _ ▸ mem))
    (fun _ _ written => by simp [writesOf] at written)
    (fun _ written => by simp [writesOf] at written)
    (fun _ written => by simp [writesOf] at written)
  exact total

/-! ### Frames of own steps -/

/-- Changing one record within the one frame of its process, reading no queue. -/
private theorem Effect.InFrames.single {processId : PID} {reads writes : Nat} {change : ProcessState → ProcessState}
    {state : State} (framed : ∀ base, Framed (bitsOf reads) (bitsOf writes) base change)
    (used : ∃ bit, bit < 17 ∧ (reads.testBit bit ∨ writes.testBit bit))
    (quiet : reads.testBit headBit = false ∧ reads.testBit tailBit = false ∧ writes.testBit headBit = false) :
    (Effect.modify processId change).InFrames [(processId, reads, writes)] state :=
  Effect.InFrames.modify (List.mem_singleton.mpr rfl) used fun process _ =>
    (framed process).widen (fun _ read => read) (fun _ written => written) (List.mem_singleton.mpr rfl)
      fun entry mem _ => by simp only [List.mem_singleton] at mem; subst mem; exact quiet

/-- An effect within frames is within frames with more entries that read no queue. -/
private theorem Effect.InFrames.more {effect : Effect} {frames more : List Frame} {state : State}
    (framed : effect.InFrames frames state)
    (quiet : ∀ entry ∈ frames ++ more, entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧
      entry.2.2.testBit headBit = false) : effect.InFrames (frames ++ more) state :=
  framed.mono (readsOf_mono fun _ mem => List.mem_append_left _ mem)
    (writesOf_mono fun _ mem => List.mem_append_left _ mem) (WellFramed.quiet quiet)

private theorem Effect.InFrames.receiveStep (state : State) (processId : PID) (reads : Nat) (remaining : List Term)
    (quiet : reads.testBit headBit = false ∧ reads.testBit tailBit = false)
    (mailbox : reads.testBit 2 = true) :
    (Effect.modify processId fun process => { process with mailbox := remaining }).InFrames
      [(processId, reads, Field.mailbox)] state := by
  refine Effect.InFrames.single (fun base => ?_) ⟨2, by decide, .inr (by decide)⟩ ⟨quiet.1, quiet.2, by decide⟩
  have widen : ∀ bit, (Field.mailbox).testBit bit → reads.testBit bit := fun bit set => by
    have : bit = 2 := by mask_bits
    subst this; exact mailbox
  exact (show Framed (bitsOf Field.mailbox) (bitsOf Field.mailbox) base
      (fun process => { process with mailbox := remaining }) by framed_update).mono
    (fun bit read => widen bit read) (fun _ written => written)
    (fun read => by simp [bitsOf, quiet.2] at read) (fun read => by simp [bitsOf, quiet.1] at read)
    (fun written => by simp [bitsOf] at written; contradiction)

private theorem Effect.InFrames.demonitorStep (state : State) (processId : PID) (reference : List Nat) :
    (Effect.modify processId fun process =>
      { process with
        monitoring := Kernel.filter (·.1 != reference) process.monitoring
        aliases := Kernel.erase process.aliases reference
        parked := match process.parked with
          | some (_, parked) => if parked == reference then none else process.parked
          | none => none }).InFrames
      [(processId, Field.monitoring ||| Field.aliases ||| Field.parked,
        Field.monitoring ||| Field.aliases ||| Field.parked)] state :=
  Effect.InFrames.single (fun _ => by framed_update) ⟨8, by decide, .inl (by decide)⟩ (by decide)

/-- Effects changing records alike are within the same frames. -/
private theorem Effect.InFrames.of_record {effect effect' : Effect} {frames : List Frame} {state : State}
    (framed : effect.InFrames frames state) (same : ∀ processId, effect'.record processId = effect.record processId) :
    effect'.InFrames frames state := fun processId => by rw [same]; exact framed processId

private theorem Effect.record_retime (change : List Timer → List Timer) (processId : PID) :
    (Effect.retime change).record processId = id := rfl

private theorem Effect.InFrames.cancelTimerStep (state : State) (processId : PID) (change : List Timer → List Timer) :
    ((Effect.retime change).andThen (.modify processId fun process => { process with cancels := process.cancels + 1 })).InFrames
      [(processId, Field.cancels, Field.cancels)] state :=
  (Effect.InFrames.single (state := state) (change := fun process => { process with cancels := process.cancels + 1 })
    (fun _ => by framed_update) ⟨11, by decide, .inl (by decide)⟩ (by decide)).of_record
    fun processId => by rw [Effect.record_andThen, Effect.record_retime]; rfl

private theorem Effect.InFrames.startTimerStep (state : State) (processId destination : PID) (retime : Effect)
    (untimed : ∀ processId, retime.record processId = id) :
    ((allocateEffect processId).andThen retime).InFrames
      [(processId, Field.refCounter, Field.refCounter), (destination, Field.live, 0)] state := by
  have first : (allocateEffect processId).InFrames [(processId, Field.refCounter, Field.refCounter)] state :=
    Effect.InFrames.single (fun _ => by framed_update) ⟨4, by decide, .inl (by decide)⟩ (by decide)
  refine (first.more (more := [(destination, Field.live, 0)]) fun entry mem => ?_).of_record fun other => ?_
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> (dsimp only; decide)
  · rw [Effect.record_andThen, untimed]; rfl

/-- Frames whose every field is a field of some entry of other frames for the same process. -/
private def Covered (frames frames' : List Frame) : Prop :=
  ∀ entry ∈ frames, ∀ bit,
    (entry.2.1.testBit bit → ∃ entry' ∈ frames', entry'.1 = entry.1 ∧ entry'.2.1.testBit bit) ∧
    (entry.2.2.testBit bit → ∃ entry' ∈ frames', entry'.1 = entry.1 ∧ entry'.2.2.testBit bit)

/-- An effect within frames is within well-formed frames covering them. -/
private theorem Effect.InFrames.cover {effect : Effect} {frames frames' : List Frame} {state : State}
    (framed : effect.InFrames frames state) (covered : Covered frames frames') (wellFramed : WellFramed frames' state) :
    effect.InFrames frames' state := by
  refine framed.mono (fun processId bit read => ?_) (fun processId bit written => ?_) wellFramed
  · simp only [readsOf, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at read ⊢
    obtain ⟨entry, mem, same, set⟩ := read
    obtain ⟨entry', mem', same', set'⟩ := (covered entry mem bit).1 set
    exact ⟨entry', mem', same'.trans same, set'⟩
  · simp only [writesOf, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at written ⊢
    obtain ⟨entry, mem, same, set⟩ := written
    obtain ⟨entry', mem', same', set'⟩ := (covered entry mem bit).2 set
    exact ⟨entry', mem', same'.trans same, set'⟩


private theorem State.process_modify_keeps {β : Type} {state : State} {processId other : PID}
    {change : ProcessState → ProcessState} {get : ProcessState → β}
    (keeps : ∀ process, get (change process) = get process) :
    get ((state.modify processId change).process other) = get (state.process other) := by
  unfold State.modify
  split
  · rename_i process found
    simp only [State.process, State.record_set]
    by_cases same : other = processId
    · subst same; simp [found, keeps]
    · simp [same]
  · rfl

/-- Frames that remove no queue's head. -/
private theorem noPop {frames : List Frame} (none : ∀ entry ∈ frames, entry.2.2.testBit headBit = false)
    (processId : PID) (written : writesOf frames processId headBit) : False := by
  rw [writesOf_false none] at written; simp at written

/-- Requesting a monitor of another process is within its frames. -/
private theorem Effect.InFrames.monitorStep (state : State) (processId target : PID) (alias : Bool)
    (other : ¬ target = processId) :
    (state.requestEffect processId (.monitor target alias)).InFrames
      ((processId, Field.refCounter ||| Field.parked ||| Field.monitoring ||| Field.aliases,
        Field.refCounter ||| Field.parked ||| Field.monitoring ||| Field.aliases) ::
        match (state.process processId).parked with
        | some (parked, reference) => state.enqueueFrames processId parked (.monitor reference)
        | none => []) state := by
  let allocated := (state.allocate processId).2
  let reference := (state.allocate processId).1
  let change := fun process : ProcessState => { process with
    monitoring := Kernel.append process.monitoring [(reference, target)]
    aliases := if alias then Kernel.append process.aliases [reference] else process.aliases
    parked := some (target, reference) }
  have unfolded : state.requestEffect processId (.monitor target alias) =
      (allocateEffect processId).andThen ((allocated.unparkEffect processId).andThen (.modify processId change)) := by
    simp only [State.requestEffect, other, ↓reduceIte]; rfl
  have parkedSame : (allocated.process processId).parked = (state.process processId).parked :=
    State.process_modify_keeps (get := (·.parked)) fun _ => rfl
  have first : (allocateEffect processId).InFrames [(processId, Field.refCounter, Field.refCounter)] state :=
    Effect.InFrames.single (fun _ => by framed_update) ⟨4, by decide, .inl (by decide)⟩ (by decide)
  let unparkFrames : List Frame := match (state.process processId).parked with
    | some (parked, reference) =>
        [(processId, Field.parked, Field.parked)] ++ state.enqueueFrames processId parked (.monitor reference)
    | none => []
  have second : (allocated.unparkEffect processId).InFrames unparkFrames ((allocateEffect processId).apply state) := by
    have back : ∀ other, ((allocateEffect processId).apply state).record other = allocated.record other :=
      fun other => ((Realizes.allocate state processId).records other).symm
    cases parked : (state.process processId).parked with
    | none =>
      have : allocated.unparkEffect processId = {} := by simp only [State.unparkEffect, parkedSame, parked]
      rw [this]; exact Effect.InFrames.empty _ _
    | some found =>
      obtain ⟨parkedTarget, parkedReference⟩ := found
      have framed := Effect.InFrames.unpark allocated processId parkedTarget parkedReference (parkedSame.trans parked)
      have equal : allocated.enqueueFrames processId parkedTarget (.monitor parkedReference) =
          state.enqueueFrames processId parkedTarget (.monitor parkedReference) :=
        State.enqueueFrames_congr _ (State.alive_modify _ _ _ _ fun _ => rfl)
      simp only [unparkFrames, parked]
      rw [← equal]
      exact framed.congr back
  have third : (Effect.modify processId change).InFrames
      [(processId, Field.parked ||| Field.monitoring ||| Field.aliases, Field.parked ||| Field.monitoring ||| Field.aliases)]
      (((allocateEffect processId).andThen (allocated.unparkEffect processId)).apply state) :=
    Effect.InFrames.single (fun _ => by simp only [change]; framed_update) ⟨8, by decide, .inl (by decide)⟩ (by decide)
  have quietUnpark : ∀ entry ∈ unparkFrames,
      entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false := by
    intro entry mem
    simp only [unparkFrames] at mem
    split at mem
    · simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with rfl | mem
      · dsimp only; decide
      · exact enqueueFrames_quiet mem
    · simp at mem
  have quiet : ∀ entry ∈ [(processId, Field.refCounter, Field.refCounter)] ++ unparkFrames ++
      [(processId, Field.parked ||| Field.monitoring ||| Field.aliases, Field.parked ||| Field.monitoring ||| Field.aliases)],
      entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false := by
    intro entry mem
    simp only [List.mem_append, List.mem_singleton] at mem
    rcases mem with (rfl | mem) | rfl
    · dsimp only; decide
    · exact quietUnpark entry mem
    · dsimp only; decide
  have total := (first.andThen second
    (WellFramed.quiet fun entry mem => quiet entry (List.mem_append_left _ mem))
    (fun processId _ written => (noPop (fun entry mem => by simp only [List.mem_singleton] at mem; subst mem; dsimp only; decide) processId written).elim)
    (fun processId written _ => (noPop (fun entry mem => by simp only [List.mem_singleton] at mem; subst mem; dsimp only; decide) processId written).elim)
    (fun processId _ written => (noPop (fun entry mem => (quietUnpark entry mem).2.2) processId written).elim)).andThen third
    (WellFramed.quiet quiet)
    (fun processId _ written => (noPop (fun entry mem => (quiet entry (List.mem_append_left _ mem)).2.2) processId written).elim)
    (fun processId written _ => (noPop (fun entry mem => (quiet entry (List.mem_append_left _ mem)).2.2) processId written).elim)
    (fun processId _ written => (noPop (fun entry mem => by simp only [List.mem_singleton] at mem; subst mem; dsimp only; decide) processId written).elim)
  rw [unfolded]
  refine (total.of_record fun other => ?_).cover ?_ (WellFramed.quiet fun entry mem => ?_)
  · simp only [Effect.record_andThen]; rfl
  · intro entry mem bit
    have head : (processId, Field.refCounter ||| Field.parked ||| Field.monitoring ||| Field.aliases,
        Field.refCounter ||| Field.parked ||| Field.monitoring ||| Field.aliases) ∈
        (processId, Field.refCounter ||| Field.parked ||| Field.monitoring ||| Field.aliases,
          Field.refCounter ||| Field.parked ||| Field.monitoring ||| Field.aliases) ::
          (match (state.process processId).parked with
          | some (parked, reference) => state.enqueueFrames processId parked (.monitor reference)
          | none => []) := List.mem_cons_self
    simp only [List.mem_append, List.mem_singleton] at mem
    rcases mem with (rfl | mem) | rfl
    · exact ⟨fun set => ⟨_, head, rfl, by dsimp only at set ⊢; mask_bits⟩,
        fun set => ⟨_, head, rfl, by dsimp only at set ⊢; mask_bits⟩⟩
    · simp only [unparkFrames] at mem
      split at mem
      · rename_i parked
        simp only [List.mem_append, List.mem_singleton] at mem
        rcases mem with rfl | mem
        · exact ⟨fun set => ⟨_, List.mem_cons_self, rfl, by dsimp only at set ⊢; mask_bits⟩,
            fun set => ⟨_, List.mem_cons_self, rfl, by dsimp only at set ⊢; mask_bits⟩⟩
        · exact ⟨fun set => ⟨entry, List.mem_cons_of_mem _ mem, rfl, set⟩,
            fun set => ⟨entry, List.mem_cons_of_mem _ mem, rfl, set⟩⟩
      · simp at mem
    · exact ⟨fun set => ⟨_, head, rfl, by dsimp only at set ⊢; mask_bits⟩,
        fun set => ⟨_, head, rfl, by dsimp only at set ⊢; mask_bits⟩⟩
  · simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · dsimp only; decide
    · split at mem
      · exact enqueueFrames_quiet mem
      · simp at mem

/-- Queueing a `flush` to a live process itself, as asking whether a dead
process is alive does, is within its frames. -/
private theorem Effect.InFrames.flushStep (state : State) (processId target : PID)
    (alive : state.alive processId = true) :
    (state.enqueueEffect processId processId .flush).InFrames
      [(target, Field.live, 0), (processId, Field.live, Field.queueTail)] state := by
  have effect : state.enqueueEffect processId processId .flush = .modify processId (queueAt processId .flush) := by
    unfold State.enqueueEffect
    simp only [State.alive] at alive
    split
    · rename_i process found
      rw [found] at alive; simp only at alive; simp [alive]
    · rename_i found
      rw [found] at alive; simp at alive
  rw [effect]
  have inside : (processId, Field.live, Field.queueTail) ∈ [(target, Field.live, 0), (processId, Field.live, Field.queueTail)] := by simp
  refine Effect.InFrames.modify inside ⟨1, by decide, .inr (by decide)⟩ fun process _ =>
    (Framed.queueAt processId .flush process).widen (reads := Field.live)
      (fun _ read => by simp [bitsOf, Nat.zero_testBit] at read) (fun _ written => written) inside
      fun entry mem _ => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> (dsimp only; decide)

/-! ### Frames of handling a signal -/

private theorem Effect.InFrames.ite {first second : Effect} {frames : List Frame} {state : State} (condition : Prop)
    [Decidable condition] (framed : first.InFrames frames state) (framed' : second.InFrames frames state) :
    (if condition then first else second).InFrames frames state := by
  split
  · exact framed
  · exact framed'

/-- Frames that read and remove no queue. -/
private def QuietFrames (frames : List Frame) : Prop :=
  ∀ entry ∈ frames, entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧
    entry.2.2.testBit headBit = false ∧ entry.2.2.testBit tailBit = false

/-- Two effects within frames reading and changing no queue compose within both. -/
private theorem Effect.InFrames.andThen_quiet {effect effect' : Effect} {frames frames' : List Frame} {state : State}
    (framed : effect.InFrames frames state) (framed' : effect'.InFrames frames' (effect.apply state))
    (quiet : QuietFrames frames) (quiet' : QuietFrames frames') :
    (effect.andThen effect').InFrames (frames ++ frames') state := by
  have both : QuietFrames (frames ++ frames') := fun entry mem => by
    rcases List.mem_append.mp mem with mem | mem
    · exact quiet entry mem
    · exact quiet' entry mem
  refine framed.andThen framed' (WellFramed.quiet fun entry mem => ⟨(both entry mem).1, (both entry mem).2.1,
      (both entry mem).2.2.1⟩) (fun processId read _ => ?_) (fun processId written _ => ?_) (fun processId written _ => ?_)
  · rw [readsOf_false fun entry mem => (quiet' entry mem).1] at read; simp at read
  · rw [writesOf_false fun entry mem => (quiet entry mem).2.2.1] at written; simp at written
  · rw [writesOf_false fun entry mem => (quiet entry mem).2.2.2] at written; simp at written

/-- Removing the oldest signal of a queue that has one reads and writes its head. -/
private theorem Framed.pop (base : ProcessState) (nonempty : base.queue ≠ []) :
    Framed (bitsOf Field.queueHead) (bitsOf Field.queueHead) base
      (fun process => { process with queue := process.queue.drop 1 }) := by
  refine ⟨fun process _ part none => ?_, fun process process' _ _ part written _ => ?_,
    ⟨1, [], by decide, fun none => by simp [bitsOf] at none; contradiction, fun _ => rfl, fun process _ => by simp⟩,
    fun read => by simp [bitsOf, tailBit] at read; contradiction, fun _ => .inr nonempty, fun _ => nonempty,
    fun _ process _ => rfl⟩
  · cases part <;> first | rfl | (simp [bitsOf, Part.bit] at none; contradiction)
  · cases part <;> simp [bitsOf, Part.bit] at written <;> contradiction

private theorem readsOf_single (processId : PID) (reads writes : Nat) :
    readsOf [(processId, reads, writes)] processId = bitsOf reads := by
  funext bit; simp [readsOf, bitsOf]

private theorem writesOf_single (processId : PID) (reads writes : Nat) :
    writesOf [(processId, reads, writes)] processId = bitsOf writes := by
  funext bit; simp [writesOf, bitsOf]

/-- Handling the oldest queued signal by a change reading and writing no queue
is within the frames of the change and of the head. -/
private theorem Effect.InFrames.handleWith {state : State} {processId : PID} {entry : Entry} {rest : List Entry}
    {effect : Effect} {frames : List Frame} (queue : (state.process processId).queue = entry :: rest)
    (framed : effect.InFrames frames
      ((Effect.modify processId fun process => { process with queue := process.queue.drop 1 }).apply state))
    (quiet : QuietFrames frames) :
    ((Effect.modify processId fun process => { process with queue := process.queue.drop 1 }).andThen effect).InFrames
      ([(processId, Field.queueHead, Field.queueHead)] ++ frames) state := by
  have nonempty : ∀ process, state.record processId = some process → process.queue ≠ [] := fun process found => by
    simp [State.process, found] at queue; simp [queue]
  have first : (Effect.modify processId fun process => { process with queue := process.queue.drop 1 }).InFrames
      [(processId, Field.queueHead, Field.queueHead)] state :=
    Effect.InFrames.modify (List.mem_singleton.mpr rfl) ⟨0, by decide, .inl (by decide)⟩ fun process found => by
      rw [readsOf_single, writesOf_single]; exact Framed.pop process (nonempty process found)
  have headOnly : ∀ {other bit}, (readsOf [(processId, Field.queueHead, Field.queueHead)] other bit ∨
      writesOf [(processId, Field.queueHead, Field.queueHead)] other bit) → other = processId ∧ bit = 0 := by
    intro other bit set
    simp only [readsOf, writesOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at set
    rcases set with ⟨same, set⟩ | ⟨same, set⟩ <;> exact ⟨same.symm, by mask_bits⟩
  refine first.andThen framed (fun other => ⟨fun read => ?_, fun process found _ => ⟨fun read => ?_, fun written => ?_⟩⟩)
    (fun other read _ => ?_) (fun other _ written => ?_) (fun other written _ => ?_)
  · rw [readsOf_append] at read ⊢
    simp only [Mask.union, Bool.or_eq_true] at read ⊢
    rcases read with read | read
    · have := (headOnly (.inl read)).2; simp [tailBit] at this
    · rw [readsOf_false fun entry mem => (quiet entry mem).2.1] at read; simp at read
  · rw [readsOf_append] at read
    simp only [Mask.union, Bool.or_eq_true] at read
    rcases read with read | read
    · obtain ⟨rfl, -⟩ := headOnly (.inl read); exact .inr (nonempty process found)
    · rw [readsOf_false fun entry mem => (quiet entry mem).1] at read; simp at read
  · rw [writesOf_append] at written
    simp only [Mask.union, Bool.or_eq_true] at written
    rcases written with written | written
    · obtain ⟨rfl, -⟩ := headOnly (.inr written); exact nonempty process found
    · rw [writesOf_false fun entry mem => (quiet entry mem).2.2.1] at written; simp at written
  · rw [readsOf_false fun entry mem => (quiet entry mem).1] at read; simp at read
  · rw [writesOf_false fun entry mem => (quiet entry mem).2.2.1] at written; simp at written
  · have := (headOnly (.inr written)).2; simp [tailBit] at this

/-- Frames for one process within the fields of one entry for it. -/
private theorem Covered.single {frames : List Frame} {processId : PID} {reads writes : Nat}
    (inside : ∀ entry ∈ frames, entry.1 = processId ∧
      ∀ bit, (entry.2.1.testBit bit → reads.testBit bit) ∧ (entry.2.2.testBit bit → writes.testBit bit)) :
    Covered frames [(processId, reads, writes)] := fun entry mem bit =>
  ⟨fun set => ⟨_, List.mem_singleton.mpr rfl, (inside entry mem).1.symm, ((inside entry mem).2 bit).1 set⟩,
    fun set => ⟨_, List.mem_singleton.mpr rfl, (inside entry mem).1.symm, ((inside entry mem).2 bit).2 set⟩⟩

/-- The frame of handling a signal: the head, and fields reading and writing no queue. -/
private theorem WellFramed.handle {state : State} {processId : PID} {entry : Entry} {rest : List Entry}
    {reads writes : Nat} (queue : (state.process processId).queue = entry :: rest)
    (quiet : reads.testBit tailBit = false) :
    WellFramed [(processId, Field.queueHead ||| reads, Field.queueHead ||| writes)] state := by
  have nonempty : ∀ process, state.record processId = some process → process.queue ≠ [] := fun process found => by
    simp [State.process, found] at queue; simp [queue]
  intro other
  refine ⟨fun read => ?_, fun process found _ => ⟨fun read => ?_, fun written => ?_⟩⟩
  · simp only [readsOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at read
    have := read.2; rw [Nat.testBit_or, quiet] at this
    have : Field.queueHead.testBit tailBit = false := by decide
    simp_all
  · simp only [readsOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at read
    obtain ⟨rfl, -⟩ := read; exact .inr (nonempty process found)
  · simp only [writesOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at written
    obtain ⟨rfl, -⟩ := written; exact nonempty process found



/-- Handling a signal that does not end the process removes it, then handles it. -/
private theorem Task.handleEffect_of_continues {state : State} {processId : PID} {task : Task α} {entry : Entry}
    {rest : List Entry} (queue : (state.process processId).queue = entry :: rest)
    (continues : ((state.set processId { state.process processId with queue := rest }).handle processId
      (task.wait.map (·.1)) entry).2.2 = none) :
    task.handleEffect state processId =
      (Effect.modify processId fun process => { process with queue := process.queue.drop 1 }).andThen
        ((state.set processId { state.process processId with queue := rest }).handleEffect processId entry) := by
  simp only [Task.handleEffect, queue]
  split
  · rename_i equal; rw [equal] at continues; simp at continues
  · rfl

/-- Frames, listed, that read and remove no queue. -/
local syntax "quiet_frames" : tactic
macro_rules
  | `(tactic| quiet_frames) => `(tactic|
      (intro entry mem
       simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_singleton] at mem
       repeat' (first | (subst mem) | (rcases mem with mem | mem))
       all_goals (dsimp only; decide)))

/-- Read off that every field of frames for one process is a field of an entry. -/
local syntax "covered_single" : tactic
macro_rules
  | `(tactic| covered_single) => `(tactic|
      (intro entry mem
       simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_singleton] at mem
       repeat' (first | (subst mem) | (rcases mem with mem | mem))
       all_goals exact ⟨rfl, fun bit => ⟨fun set => by dsimp only at set ⊢; mask_bits,
         fun set => by dsimp only at set ⊢; mask_bits⟩⟩))

/-- Handling a signal in a confined step is within its frames. -/
private theorem Effect.InFrames.handle {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {frames : List Frame} {timers : Bool}
    (confined : Config.confined (.running state tasks finished false) (.handle processId) = true)
    (found : task.handleFrames state processId = some (frames, timers)) :
    (task.handleEffect state processId).InFrames frames state := by
  simp only [Config.confined] at confined
  simp only [Task.handleFrames] at found
  cases queue : (state.process processId).queue with
  | nil => simp [queue] at confined
  | cons entry rest =>
    simp only [queue] at confined found ⊢
    obtain ⟨source, signal⟩ := entry
    let popped := state.set processId { state.process processId with queue := rest }
    cases signal with
    | message message =>
      rw [Task.handleEffect_of_continues queue (by simp only [State.handle]; try split <;> rfl)]
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      rw [← found.1]
      refine (Effect.InFrames.handleWith queue (frames := [(processId, 0, Field.mailbox)])
        (Effect.InFrames.single (fun _ => by framed_update) ⟨2, by decide, .inr (by decide)⟩ (by decide))
        (by intro entry mem; simp only [List.mem_singleton] at mem; subst mem; dsimp only; decide)).cover
        (Covered.single (by covered_single)) (WellFramed.handle queue (by decide))
    | aliasMessage alias message =>
      rw [Task.handleEffect_of_continues queue (by simp only [State.handle]; try split <;> rfl)]
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      rw [← found.1]
      refine (Effect.InFrames.handleWith queue (frames := [(processId, 0, Field.mailbox)]) ?_
        (by intro entry mem; simp only [List.mem_singleton] at mem; subst mem; dsimp only; decide)).cover
        (Covered.single (by covered_single)) (WellFramed.handle queue (by decide))
      simp only [State.handleEffect]
      split
      · exact Effect.InFrames.single (fun _ => by framed_update) ⟨2, by decide, .inr (by decide)⟩ (by decide)
      · exact Effect.InFrames.empty _ _
    | monitor reference =>
      rw [Task.handleEffect_of_continues queue (by simp only [State.handle]; try split <;> rfl)]
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      rw [← found.1]
      refine (Effect.InFrames.handleWith queue (frames := [(processId, Field.monitors, Field.monitors)])
        (Effect.InFrames.single (fun _ => by framed_update) ⟨7, by decide, .inr (by decide)⟩ (by decide))
        (by intro entry mem; simp only [List.mem_singleton] at mem; subst mem; dsimp only; decide)).cover
        (Covered.single (by covered_single)) (WellFramed.handle queue (by decide))
    | down reference reason =>
      rw [Task.handleEffect_of_continues queue (by simp only [State.handle]; try split <;> rfl)]
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      rw [← found.1]
      have restFramed : ∀ (state' : State) (monitored : Bool),
          (if monitored then
            (Effect.modify processId fun process =>
              { process with monitoring := Kernel.filter (·.1 != reference) process.monitoring
                             aliases := Kernel.erase process.aliases reference }).andThen
              (appendEffect processId (.tuple #[.atom "DOWN", .reference reference, .atom "process", .pid source, reason]))
            else {}).InFrames ([(processId, Field.monitoring ||| Field.aliases, Field.monitoring ||| Field.aliases)] ++
              [(processId, 0, Field.mailbox)]) state' := by
        intro state' monitored
        split
        · exact Effect.InFrames.andThen_quiet
            (Effect.InFrames.single (fun _ => by framed_update) ⟨8, by decide, .inr (by decide)⟩ (by decide))
            (Effect.InFrames.single (fun _ => by framed_update) ⟨2, by decide, .inr (by decide)⟩ (by decide))
            (by quiet_frames) (by quiet_frames)
        · exact Effect.InFrames.empty _ _
      cases normal : isNormal reason
      · simp only [normal, Bool.false_eq_true, ↓reduceIte, Nat.or_zero] at found ⊢
        apply Effect.InFrames.cover (Effect.InFrames.handleWith queue (frames := [] ++
          ([(processId, Field.monitoring ||| Field.aliases, Field.monitoring ||| Field.aliases)] ++
            [(processId, 0, Field.mailbox)])) ?inner (by quiet_frames))
        · exact Covered.single (by covered_single)
        · exact WellFramed.handle queue (by decide)
        case inner =>
          simp only [State.handleEffect, normal, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact Effect.InFrames.andThen_quiet (Effect.InFrames.empty _ _) (restFramed _ _) (by quiet_frames) (by quiet_frames)
      · simp only [normal, ↓reduceIte] at found ⊢
        apply Effect.InFrames.cover (Effect.InFrames.handleWith queue (frames := [(processId, Field.eagerExits, Field.eagerExits)] ++
          ([(processId, Field.monitoring ||| Field.aliases, Field.monitoring ||| Field.aliases)] ++
            [(processId, 0, Field.mailbox)])) ?inner (by quiet_frames))
        · exact Covered.single (by covered_single)
        · exact WellFramed.handle queue (by decide)
        case inner =>
          simp only [State.handleEffect, normal, Bool.true_and]
          refine Effect.InFrames.andThen_quiet ?_ (restFramed _ _) (by quiet_frames) (by quiet_frames)
          split
          · exact Effect.InFrames.single (fun _ => by framed_update) ⟨14, by decide, .inr (by decide)⟩ (by decide)
          · exact Effect.InFrames.empty _ _
    | _ => simp at confined

/-! ### Frames of a process ending -/

private theorem mem_insertPid {processId other : PID} :
    ∀ {pids : List PID}, other ∈ insertPid processId pids ↔ other = processId ∨ other ∈ pids
  | [] => by simp [insertPid]
  | first :: rest => by
    unfold insertPid
    split
    · simp
    · simp only [List.mem_cons, mem_insertPid (pids := rest)]; exact or_left_comm

private theorem State.process_modify_other (state : State) {processId other : PID}
    (change : ProcessState → ProcessState) (differ : other ≠ processId) :
    (state.modify processId change).process other = state.process other := by
  unfold State.modify
  split
  · simp only [State.process, State.record_set, differ, ↓reduceIte]
  · rfl

/-- The frame of one eager link exit of a process that ended, on its own record and its target's. -/
private def eagerFrames (processId target : PID) : List Frame :=
  [(processId, Field.exiting, Field.exiting),
    (target, Field.live ||| Field.trapExit ||| Field.links ||| Field.eagerExits, Field.links ||| Field.eagerExits)]

private theorem eagerFrames_quiet (processId target : PID) : QuietFrames (eagerFrames processId target) := by
  intro entry mem
  simp only [eagerFrames, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with mem | mem <;> subst mem <;> (dsimp only; decide)

/-- A link exit of a process that ended, applied as it is sent, is within its frame. -/
private theorem Effect.InFrames.eagerExit (state : State) (processId target : PID) (reason : Term)
    (ended : state.alive processId = false) :
    (State.eagerExitEffect processId reason state target).InFrames (eagerFrames processId target) state := by
  unfold State.eagerExitEffect
  split
  · rename_i eager
    have differ : target ≠ processId := fun same => by
      subst same; simp [State.eagerLink, ended] at eager
    let change := fun process : ProcessState => { process with exiting := process.exiting.map fun (exiting : Exiting) =>
      { exiting with links := Kernel.filter (· != target) exiting.links } }
    have still : (state.modify processId change).eagerLink processId target reason = true := by
      have alive : (state.modify processId change).alive target = state.alive target :=
        State.alive_modify _ _ _ _ fun process => by simp only [change]; cases process.exiting <;> rfl
      simp only [State.eagerLink, alive, State.process_modify_other _ _ differ] at eager ⊢
      exact eager
    have link : (state.modify processId change).linkExitEffect processId target reason =
        .modify target fun process => { process with
          links := Kernel.filter (·.1 != processId) process.links
          eagerExits := insertPid processId process.eagerExits } := by
      unfold State.linkExitEffect; rw [still]; rfl
    rw [link]
    exact Effect.InFrames.andThen_quiet (frames := [(processId, Field.exiting, Field.exiting)])
      (Effect.InFrames.single (fun _ => by framed_update) ⟨15, by decide, .inr (by decide)⟩ (by decide))
      (Effect.InFrames.single (fun _ => by framed_update) ⟨6, by decide, .inr (by decide)⟩ (by decide))
      (by quiet_frames) (by quiet_frames)
  · exact Effect.InFrames.empty _ _

private theorem eagerFrames_flatMap_quiet (processId : PID) (targets : List PID) :
    QuietFrames (targets.flatMap (eagerFrames processId)) := fun entry mem => by
  obtain ⟨target, -, mem⟩ := List.mem_flatMap.mp mem
  exact eagerFrames_quiet processId target entry mem

/-- The link exits of a process that ended, applied as they are sent, are within their frames. -/
private theorem Effect.InFrames.eagerExits (processId : PID) (reason : Term) (step : State → PID → State)
    (realizes : ∀ state target, Realizes (State.eagerExitEffect processId reason state target) state (step state target))
    (keepsEnded : ∀ state target, state.alive processId = false → (step state target).alive processId = false) :
    ∀ (targets : List PID) (state : State), state.alive processId = false →
      (chainEffect step (State.eagerExitEffect processId reason) state targets).InFrames
        (targets.flatMap (eagerFrames processId)) state
  | [], _, _ => Effect.InFrames.empty _ _
  | target :: rest, state, ended => by
    simp only [chainEffect, List.flatMap_cons]
    exact Effect.InFrames.andThen_quiet (Effect.InFrames.eagerExit state processId target reason ended)
      ((Effect.InFrames.eagerExits processId reason step realizes keepsEnded rest (step state target)
        (keepsEnded _ _ ended)).congr fun other => ((realizes state target).records other).symm)
      (eagerFrames_quiet _ _) (eagerFrames_flatMap_quiet _ _)

private theorem all_testBit {bit : Nat} (lower : bit < 17) : Field.all.testBit bit = true := by
  rw [show Field.all = 2 ^ 17 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simpa using lower

/-- Frames writing all of one record, then frames reading and changing no queue, are well formed. -/
private theorem WellFramed.allThen {processId : PID} {frames : List Frame} {state : State}
    (quiet : ∀ entry ∈ frames, entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧
      entry.2.2.testBit headBit = false) :
    WellFramed ([(processId, Field.all, Field.all)] ++ frames) state := by
  intro other
  have first : ∀ {bit}, (readsOf [(processId, Field.all, Field.all)] other bit ∨
      writesOf [(processId, Field.all, Field.all)] other bit) → other = processId := by
    intro bit set
    simp only [readsOf, writesOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at set
    rcases set with ⟨same, -⟩ | ⟨same, -⟩ <;> exact same.symm
  refine ⟨fun read => ?_, fun process _ notAll => ⟨fun read => ?_, fun written => ?_⟩⟩
  · rw [readsOf_append] at read ⊢
    simp only [Mask.union, Bool.or_eq_true] at read ⊢
    rcases read with read | read
    · have := first (.inl read); subst this
      left; simp [readsOf, all_testBit (show headBit < 17 by decide)]
    · rw [readsOf_false fun entry mem => (quiet entry mem).2.1] at read; simp at read
  · exfalso; rw [readsOf_append] at read
    simp only [Mask.union, Bool.or_eq_true] at read
    rcases read with read | read
    · have := first (.inl read); subst this
      exact notAll fun bit lower => by
        rw [writesOf_append]; simp [Mask.union, writesOf, all_testBit lower]
    · rw [readsOf_false fun entry mem => (quiet entry mem).1] at read; simp at read
  · exfalso; rw [writesOf_append] at written
    simp only [Mask.union, Bool.or_eq_true] at written
    rcases written with written | written
    · have := first (.inr written); subst this
      exact notAll fun bit lower => by
        rw [writesOf_append]; simp [Mask.union, writesOf, all_testBit lower]
    · rw [writesOf_false fun entry mem => (quiet entry mem).2.2] at written; simp at written

/-- The frame of an eager link exit in `State.endFrames`, reading the queue's head
only while a link from the process is queued. -/
private def eagerFrame (state : State) (processId target : PID) : Frame :=
  (target, Field.live ||| Field.trapExit ||| (if Kernel.any (state.process target).queue
      (fun entry => entry.source == processId && entry.signal matches .link) then Field.queueHead else 0) |||
    Field.links ||| Field.eagerExits, Field.links ||| Field.eagerExits)

private theorem endFrames_eq (state : State) (processId : PID) :
    (state.endFrames processId).1 = (processId, Field.all, Field.all) ::
      Kernel.filterMap (fun (target, unlinking) =>
        if unlinking.isNone then some (eagerFrame state processId target) else none)
        (state.process processId).links := rfl

private theorem mem_eagerFrame {state : State} {processId : PID} {entry : Frame}
    (mem : entry ∈ Kernel.filterMap (fun (target, unlinking) =>
      if unlinking.isNone then some (eagerFrame state processId target) else none) (state.process processId).links) :
    ∃ target, entry = eagerFrame state processId target := by
  simp only [Kernel.filterMap_eq, List.mem_filterMap] at mem
  obtain ⟨⟨target, unlinking⟩, -, found⟩ := mem
  split at found
  · simp only [Option.some.injEq] at found; exact ⟨target, found.symm⟩
  · simp at found

private theorem eagerFrame_mem {state : State} {processId target : PID}
    (inside : (target, none) ∈ (state.process processId).links) :
    eagerFrame state processId target ∈ Kernel.filterMap (fun (target, unlinking) =>
      if unlinking.isNone then some (eagerFrame state processId target) else none) (state.process processId).links := by
  simp only [Kernel.filterMap_eq, List.mem_filterMap]
  exact ⟨(target, none), inside, by simp⟩

private theorem eagerFrame_bits (state : State) (processId target : PID) :
    (eagerFrame state processId target).2.1.testBit tailBit = false ∧
      (eagerFrame state processId target).2.2.testBit headBit = false ∧
      ((eagerFrame state processId target).2.1.testBit headBit = true → (state.process target).queue ≠ []) ∧
      ∀ bit, ((bit = 16 ∨ bit = 10 ∨ bit = 6 ∨ bit = 14) → (eagerFrame state processId target).2.1.testBit bit) ∧
        ((bit = 6 ∨ bit = 14) → (eagerFrame state processId target).2.2.testBit bit) := by
  simp only [eagerFrame]
  split
  · rename_i linking
    refine ⟨by decide, by decide, fun _ empty => ?_, fun bit => ⟨fun set => ?_, fun set => ?_⟩⟩
    · rw [empty] at linking; simp [Kernel.any_eq] at linking
    · rcases set with rfl | rfl | rfl | rfl <;> decide
    · rcases set with rfl | rfl <;> decide
  · refine ⟨by decide, by decide, fun read => by simp at read; contradiction, fun bit => ⟨fun set => ?_, fun set => ?_⟩⟩
    · rcases set with rfl | rfl | rfl | rfl <;> decide
    · rcases set with rfl | rfl <;> decide

/-! ### Frames of the phases of a process that ended -/

/-- The entries of `State.sendFrames` read no queue and remove no head. -/
private theorem sendFrames_quiet {state : State} {source target : PID} {signal : Signal} {entry : Frame}
    (mem : entry ∈ state.sendFrames source target signal) :
    entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧ entry.2.2.testBit headBit = false := by
  simp only [State.sendFrames] at mem
  split at mem
  · split at mem
    · simp only [List.mem_cons, Kernel.append_eq, List.mem_append] at mem
      rcases mem with mem | mem | mem
      · subst mem; dsimp only; decide
      · exact enqueueFrames_quiet mem
      · exact enqueueFrames_quiet mem
    · simp only [List.mem_cons] at mem
      rcases mem with mem | mem
      · subst mem; dsimp only; decide
      · exact enqueueFrames_quiet mem
  · simp only [List.mem_cons] at mem
    rcases mem with mem | mem
    · subst mem; dsimp only; decide
    · exact enqueueFrames_quiet mem

private theorem State.sendFrames_congr {state other : State} {source target : PID} (signal : Signal)
    (parked : (other.process source).parked = (state.process source).parked)
    (alive : other.alive target = state.alive target) :
    other.sendFrames source target signal = state.sendFrames source target signal := by
  simp only [State.sendFrames, parked, State.enqueueFrames_congr _ alive]

/-- A change of a record, then a send, is within the frame of the change and the send's frames. -/
private theorem Effect.InFrames.thenSend {state : State} {processId source target : PID} {signal : Signal}
    {reads writes : Nat} {change : ProcessState → ProcessState}
    (first : (Effect.modify processId change).InFrames [(processId, reads, writes)] state)
    (quiet : reads.testBit tailBit = false ∧ writes.testBit tailBit = false)
    (head : reads.testBit headBit = true ∨ writes.testBit headBit = true →
      ∀ process, state.record processId = some process → process.queue ≠ [])
    (parked : ((state.modify processId change).process source).parked = (state.process source).parked)
    (alive : (state.modify processId change).alive target = state.alive target) :
    ((Effect.modify processId change).andThen ((state.modify processId change).sendEffect source target signal)).InFrames
      ([(processId, reads, writes)] ++ state.sendFrames source target signal) state := by
  have second := (Effect.InFrames.send (state.modify processId change) source target signal).congr
    fun other => ((Realizes.modify state processId change).records other).symm
  rw [State.sendFrames_congr _ parked alive] at second
  refine first.andThen second (fun other => ⟨fun read => ?_, fun process found _ => ⟨fun read => ?_, fun written => ?_⟩⟩)
    (fun other read _ => ?_) (fun other _ written => ?_) (fun other _ written => ?_)
  · rw [readsOf_append] at read
    simp only [Mask.union, Bool.or_eq_true] at read
    rcases read with read | read
    · simp only [readsOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true] at read
      rw [quiet.1] at read; simp at read
    · rw [readsOf_false fun entry mem => (sendFrames_quiet mem).2.1] at read; simp at read
  · rw [readsOf_append] at read
    simp only [Mask.union, Bool.or_eq_true] at read
    rcases read with read | read
    · simp only [readsOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at read
      obtain ⟨same, set⟩ := read; subst same
      exact .inr (head (.inl set) process found)
    · rw [readsOf_false fun entry mem => (sendFrames_quiet mem).1] at read; simp at read
  · rw [writesOf_append] at written
    simp only [Mask.union, Bool.or_eq_true] at written
    rcases written with written | written
    · simp only [writesOf, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at written
      obtain ⟨same, set⟩ := written; subst same
      exact head (.inr set) process found
    · rw [writesOf_false fun entry mem => (sendFrames_quiet mem).2.2] at written; simp at written
  · rw [readsOf_false fun entry mem => (sendFrames_quiet mem).1] at read; simp at read
  · rw [writesOf_false fun entry mem => (sendFrames_quiet mem).2.2] at written; simp at written
  · rw [writesOf_false fun entry mem => (sendFrames_quiet mem).2.2] at written; simp at written

/-- Frames of a record with a queued signal, reading no tail, and then frames
reading no queue and removing no head, are well formed. -/
private theorem WellFramed.headThen {state : State} {processId : PID} {reads writes : Nat} {frames : List Frame}
    (nonempty : ∀ process, state.record processId = some process → process.queue ≠ [])
    (tail : reads.testBit tailBit = false)
    (quiet : ∀ entry ∈ frames, entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧
      entry.2.2.testBit headBit = false) :
    WellFramed ((processId, reads, writes) :: frames) state := by
  intro other
  refine ⟨fun read => ?_, fun process found _ => ⟨fun read => ?_, fun written => ?_⟩⟩
  · simp only [readsOf, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at read
    rcases read with ⟨-, set⟩ | read
    · rw [tail] at set; simp at set
    · have := readsOf_false (frames := frames) (processId := other) fun entry mem => (quiet entry mem).2.1
      simp only [readsOf] at this; rw [this] at read; simp at read
  · simp only [readsOf, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at read
    rcases read with ⟨same, -⟩ | read
    · subst same; exact .inr (nonempty process found)
    · have := readsOf_false (frames := frames) (processId := other) fun entry mem => (quiet entry mem).1
      simp only [readsOf] at this; rw [this] at read; simp at read
  · simp only [writesOf, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at written
    rcases written with ⟨same, -⟩ | written
    · subst same; exact nonempty process found
    · have := writesOf_false (frames := frames) (processId := other) fun entry mem => (quiet entry mem).2.2
      simp only [writesOf] at this; rw [this] at written; simp at written

/-- The next phase of a process that ended is within its frames. -/
private theorem Effect.InFrames.phaseStep {state : State} {processId : PID} {frames : List Frame} {timers : Bool}
    (found : state.phaseFrames processId = some (frames, timers)) :
    (state.phaseEffect processId).InFrames frames state := by
  unfold State.phaseFrames at found
  cases record : state.record processId with
  | none => simp [record] at found
  | some process =>
    have same : state.process processId = process := by simp [State.process, record]
    simp only [record] at found
    cases exits : process.exiting with
    | none => simp [exits] at found
    | some exiting =>
      simp only [exits] at found
      simp only [State.phaseEffect, same, exits]
      -- The frames of the last phase write the whole record.
      have last : ∀ {reads writes : Nat} {frames : List Frame} {effect : Effect},
          effect.InFrames ([(processId, reads, writes)] ++ frames) state →
          (∀ entry ∈ frames, entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧
            entry.2.2.testBit headBit = false) → reads < 2 ^ 17 → writes < 2 ^ 17 →
          effect.InFrames ((processId, Field.all, Field.all) :: frames) state := by
        intro reads writes frames effect framed quiet lowReads lowWrites
        have below : ∀ {mask bit : Nat}, mask < 2 ^ 17 → mask.testBit bit = true → bit < 17 := by
          intro mask bit low set
          apply Classical.byContradiction; intro high
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le low (Nat.pow_le_pow_right (by decide) (by omega)))] at set
          simp at set
        refine framed.cover (fun entry mem bit => ?_) (WellFramed.allThen quiet)
        rcases List.mem_append.mp mem with mem | mem
        · simp only [List.mem_singleton] at mem; subst mem
          exact ⟨fun set => ⟨_, List.mem_cons_self, rfl, all_testBit (below lowReads set)⟩,
            fun set => ⟨_, List.mem_cons_self, rfl, all_testBit (below lowWrites set)⟩⟩
        · exact ⟨fun set => ⟨entry, List.mem_cons_of_mem _ mem, rfl, set⟩,
            fun set => ⟨entry, List.mem_cons_of_mem _ mem, rfl, set⟩⟩
      cases downs : exiting.downs with
      | cons down rest =>
        obtain ⟨reference, watcher⟩ := down
        simp only [downs, Option.some.injEq, Prod.mk.injEq] at found ⊢
        rw [← found.1]
        have sent := Effect.InFrames.thenSend (state := state) (processId := processId)
          (reads := Field.exiting) (writes := Field.exiting)
          (change := setDowns rest) (source := processId) (target := watcher)
          (signal := .down reference exiting.reason)
          (Effect.InFrames.single (fun _ => by delta setDowns; framed_update) ⟨15, by decide, .inr (by decide)⟩
            (by decide))
          (by decide) (fun set => absurd set (by decide))
          (State.process_modify_keeps (get := (·.parked)) fun _ => rfl)
          (State.alive_modify _ _ _ _ fun process => by simp only [setDowns]; cases process.exiting <;> rfl)
        split
        · exact last sent (fun _ mem => sendFrames_quiet mem) (by decide) (by decide)
        · exact sent
      | nil =>
        cases queue : process.queue with
        | nil =>
          simp only [downs, queue, Option.some.injEq, Prod.mk.injEq] at found ⊢
          rw [← found.1]
          exact Effect.InFrames.empty _ _
        | cons entry rest =>
          simp only [downs, queue, Option.some.injEq, Prod.mk.injEq] at found ⊢
          rw [← found.1]
          have nonempty : ∀ process', state.record processId = some process' → process'.queue ≠ [] :=
            fun process' found' => by rw [record] at found'; cases found'; simp [queue]
          let pop := fun process : ProcessState => { process with queue := process.queue.drop 1 }
          have first : (Effect.modify processId pop).InFrames [(processId, Field.queueHead, Field.queueHead)] state :=
            Effect.InFrames.modify (List.mem_singleton.mpr rfl) ⟨0, by decide, .inl (by decide)⟩ fun process' found' => by
              rw [readsOf_single, writesOf_single]; exact Framed.pop process' (nonempty process' found')
          have parked : ((state.modify processId pop).process processId).parked =
              (state.process processId).parked := State.process_modify_keeps (get := (·.parked)) fun _ => rfl
          have alive : (state.modify processId pop).alive entry.source = state.alive entry.source :=
            State.alive_modify _ _ _ _ fun _ => rfl
          -- Not the last phase: the head, and what answering sends.
          have answered : ∀ {frames : List Frame} {effect : Effect},
              effect.InFrames ([(processId, Field.queueHead, Field.queueHead)] ++ frames) state →
              (∀ entry ∈ frames, entry.2.1.testBit headBit = false ∧ entry.2.1.testBit tailBit = false ∧
                entry.2.2.testBit headBit = false) →
              effect.InFrames ((if rest.isEmpty then (processId, Field.all, Field.all)
                else (processId, Field.exiting ||| Field.queueHead, Field.queueHead)) :: frames) state := by
            intro frames effect framed quiet
            split
            · exact last framed quiet (by decide) (by decide)
            · refine framed.cover (fun frame mem bit => ?_) (WellFramed.headThen nonempty (by decide) quiet)
              rcases List.mem_append.mp mem with mem | mem
              · simp only [List.mem_singleton] at mem; subst mem
                exact ⟨fun set => ⟨_, List.mem_cons_self, rfl, by dsimp only at set ⊢; mask_bits⟩,
                  fun set => ⟨_, List.mem_cons_self, rfl, by dsimp only at set ⊢; mask_bits⟩⟩
              · exact ⟨fun set => ⟨frame, List.mem_cons_of_mem _ mem, rfl, set⟩,
                  fun set => ⟨frame, List.mem_cons_of_mem _ mem, rfl, set⟩⟩
          have sends : ∀ signal, ((Effect.modify processId pop).andThen
              ((state.modify processId pop).sendEffect processId entry.source signal)).InFrames
              ((if rest.isEmpty then (processId, Field.all, Field.all)
                else (processId, Field.exiting ||| Field.queueHead, Field.queueHead)) ::
                state.sendFrames processId entry.source signal) state := fun signal =>
            answered (Effect.InFrames.thenSend (source := processId) first (by decide) (fun _ => nonempty) parked alive)
              fun _ mem => sendFrames_quiet mem
          obtain ⟨source, signal⟩ := entry
          cases signal with
          | link => exact sends _
          | monitor reference => exact sends _
          | isAlive => exact sends _
          | _ =>
            refine answered (frames := []) (first.of_record fun other => ?_) (fun _ mem => by simp at mem)
            rw [Effect.record_andThen]; rfl

/-! ### Effects decided by what frames read

A step's effect depends on its state only through what its frames read: at
another state agreeing on them, the step has the same effect. -/

private theorem State.fallbackEffect_congr (state other : State) (source target : PID) (signal : Signal) :
    other.fallbackEffect source target signal = state.fallbackEffect source target signal := by
  cases signal <;> rfl

private theorem State.enqueueEffect_congr {state other : State} {source target : PID} (signal : Signal)
    (alive : other.alive target = state.alive target) :
    other.enqueueEffect source target signal = state.enqueueEffect source target signal := by
  unfold State.enqueueEffect
  simp only [State.alive] at alive
  rw [State.fallbackEffect_congr state other]
  cases found : state.record target <;> cases found' : other.record target <;> simp only [found, found'] at alive ⊢
  · rename_i process
    cases exiting : process.exiting <;> simp_all
  · rename_i process
    cases exiting : process.exiting <;> simp_all
  · rename_i process process'
    cases exiting : process.exiting <;> cases exiting' : process'.exiting <;> simp_all

private theorem State.unparkEffect_congr {state other : State} {processId : PID}
    (parked : (other.process processId).parked = (state.process processId).parked)
    (alive : ∀ target reference, (state.process processId).parked = some (target, reference) →
      (other.modify processId fun process => { process with parked := none }).alive target =
        (state.modify processId fun process => { process with parked := none }).alive target) :
    other.unparkEffect processId = state.unparkEffect processId := by
  unfold State.unparkEffect
  rw [parked]
  cases found : (state.process processId).parked with
  | none => rfl
  | some found' =>
    obtain ⟨target, reference⟩ := found'
    simp only
    rw [State.enqueueEffect_congr _ (alive target reference found)]

private theorem State.sendEffect_congr {state other : State} {source target : PID} (signal : Signal)
    (parked : (other.process source).parked = (state.process source).parked)
    (alive : other.alive target = state.alive target) :
    other.sendEffect source target signal = state.sendEffect source target signal := by
  have kept : ∀ (state : State), (state.modify source fun process => { process with parked := none }).alive target =
      state.alive target := fun state => State.alive_modify state source target _ fun _ => rfl
  unfold State.sendEffect
  rw [parked]
  split
  · rename_i parkedTarget reference found
    split
    · rename_i same
      have same : parkedTarget = target := eq_of_beq same
      subst same
      have unparked := State.unparkEffect_congr (state := state) (other := other) (processId := source) parked
        fun target' reference' found' => by
          rw [found] at found'; simp only [Option.some.injEq, Prod.mk.injEq] at found'
          rw [← found'.1, kept, kept, alive]
      rw [unparked, State.enqueueEffect_congr (state := state.unpark source) _
        (by rw [State.alive_unpark, State.alive_unpark]; exact alive)]
    · rw [State.enqueueEffect_congr _ alive]
  · rw [State.enqueueEffect_congr _ alive]

private theorem State.alive_send (state : State) (source target other : PID) (signal : Signal) :
    (state.send source target signal).alive other = state.alive other := by
  unfold State.send
  simp only
  rw [State.alive_enqueue]
  split
  · split
    · exact State.alive_unpark _ _ _
    · rfl
  · rfl

private theorem mem_eagerTargets {processId : PID} :
    ∀ {links : List (PID × Option Nat)} {pids : List PID},
      processId ∈ Kernel.foldl (fun pids (peer, unlinking) =>
        if unlinking.isNone then insertPid peer pids else pids) pids links →
      processId ∈ pids ∨ (processId, none) ∈ links
  | [], _, mem => .inl (by simpa [Kernel.foldl_eq] using mem)
  | (peer, unlinking) :: rest, pids, mem => by
    simp only [Kernel.foldl_eq, List.foldl_cons] at mem
    rcases mem_eagerTargets (links := rest) (by simpa [Kernel.foldl_eq] using mem) with inside | inside
    · split at inside
      · rename_i none
        rcases mem_insertPid.mp inside with same | inside
        · subst same; cases unlinking <;> simp_all
        · exact .inl inside
      · exact .inl inside
    · exact .inr (List.mem_cons_of_mem _ inside)

/-- An effect changing only the record of one process, within frames writing all of it. -/
private theorem Effect.InFrames.onlyAll {effect : Effect} {processId : PID} {state : State}
    (only : ∀ other, other ≠ processId → effect.record other = id)
    (allWritten : ∀ bit, bit < 17 → writesOf [(processId, Field.all, Field.all)] processId bit) :
    effect.InFrames [(processId, Field.all, Field.all)] state := fun other => by
  by_cases same : other = processId
  · subst same; exact .inr (.inl allWritten)
  · exact .inl (only other same)

/-- A process ending is within its frames. -/
private theorem Effect.InFrames.terminateStep (state : State) (processId : PID) (reason : Term)
    (alive : state.alive processId = true) :
    (state.terminateEffect processId reason).InFrames (state.endFrames processId).1 state := by
  have found : state.record processId = some (state.process processId) := by
    simp only [State.alive] at alive
    cases record : state.record processId with
    | none => rw [record] at alive; simp at alive
    | some process => simp [State.process, record]
  let process := state.process processId
  let links := Kernel.foldl (fun links (peer, unlinking) =>
    if unlinking.isNone then insertPid peer links else links) [] process.links
  -- The ending record, written whole.
  have allWritten : ∀ bit, bit < 17 → writesOf [(processId, Field.all, Field.all)] processId bit := by
    intro bit lower
    simp only [writesOf, List.any_cons, List.any_nil, Bool.or_false, beq_self_eq_true, Bool.true_and]
    exact all_testBit lower
  let exit (state : State) (target : PID) : State := if state.eagerLink processId target reason then
      (state.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
        { exiting with links := Kernel.filter (· != target) exiting.links } }).linkExit processId target reason
    else state
  have realizes : ∀ state target,
      Realizes (State.eagerExitEffect processId reason state target) state (exit state target) := by
    intro state target
    unfold State.eagerExitEffect
    simp only [exit]
    split
    · exact (Realizes.modify _ _ _).andThen (Realizes.linkExit _ _ _ _)
    · exact Realizes.refl _
  have keepsEnded : ∀ state target, state.alive processId = false → (exit state target).alive processId = false := by
    intro state target ended
    simp only [exit]
    split
    · unfold State.linkExit
      split
      · refine (State.alive_modify _ _ _ _ ?_).trans ((State.alive_modify _ _ _ _ ?_).trans ended)
        · intro process; rfl
        · intro process; cases process.exiting <;> rfl
      · refine (State.alive_send _ _ _ _ _).trans ((State.alive_modify _ _ _ _ ?_).trans ended)
        intro process; cases process.exiting <;> rfl
    · exact ended
  unfold State.terminateEffect
  dsimp only
  refine Effect.InFrames.cover (Effect.InFrames.andThen (frames := [(processId, Field.all, Field.all)])
    (frames' := links.flatMap (eagerFrames processId))
    (Effect.InFrames.onlyAll ?only allWritten) ?chain ?wellFramed ?popped ?once ?appended) ?covered ?wellFramed'
  case only =>
    intro other differ
    rw [Effect.record_andThen]
    have put : ∀ (process : ProcessState), (Effect.put processId process).record other = id := fun _ => by
      simp [Effect.put, Effect.record, changeOf, Ne.symm differ, differ]
    rw [put]
    split <;> rfl
  case chain =>
    refine (Effect.InFrames.eagerExits processId reason exit realizes keepsEnded links _ ?dead).congr ?records
    case dead => simp [State.alive, State.record_set]
    case records =>
      intro other
      rw [Effect.record_apply, Effect.record_andThen, State.record_set]
      have retimed : (if Kernel.any state.timers (·.destination == processId) then
          Effect.retime (Kernel.filter (·.destination != processId)) else {}).record other = id := by split <;> rfl
      rw [retimed]
      by_cases same : other = processId
      · subst same; simp [Effect.put, Effect.record, changeOf]
      · simp [Effect.put, Effect.record, changeOf, Ne.symm same, same, State.record]
  case wellFramed => exact WellFramed.allThen fun entry mem =>
    ⟨(eagerFrames_flatMap_quiet _ _ entry mem).1, (eagerFrames_flatMap_quiet _ _ entry mem).2.1,
      (eagerFrames_flatMap_quiet _ _ entry mem).2.2.1⟩
  case popped =>
    intro other read _
    rw [readsOf_false fun entry mem => (eagerFrames_flatMap_quiet processId links entry mem).1] at read; simp at read
  case once =>
    intro other _ written
    rw [writesOf_false fun entry mem => (eagerFrames_flatMap_quiet processId links entry mem).2.2.1] at written
    simp at written
  case appended =>
    intro other _ written
    rw [writesOf_false fun entry mem => (eagerFrames_flatMap_quiet processId links entry mem).2.2.1] at written
    simp at written
  case covered =>
    rw [endFrames_eq]
    intro entry mem bit
    have head : (processId, Field.all, Field.all) ∈ (processId, Field.all, Field.all) ::
        Kernel.filterMap (fun (target, unlinking) =>
          if unlinking.isNone then some (eagerFrame state processId target) else none)
          (state.process processId).links := List.mem_cons_self
    rcases List.mem_append.mp mem with mem | mem
    · simp only [List.mem_singleton] at mem; subst mem
      exact ⟨fun set => ⟨_, head, rfl, set⟩, fun set => ⟨_, head, rfl, set⟩⟩
    · obtain ⟨target, inside, mem⟩ := List.mem_flatMap.mp mem
      simp only [eagerFrames, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with mem | mem <;> subst mem
      · have exiting : ∀ {mask : Nat}, mask = Field.exiting → mask.testBit bit → Field.all.testBit bit := by
          intro mask equal set; subst equal
          have : bit = 15 := by mask_bits
          subst this; decide
        exact ⟨fun set => ⟨_, head, rfl, exiting rfl set⟩, fun set => ⟨_, head, rfl, exiting rfl set⟩⟩
      · have linked : (target, none) ∈ (state.process processId).links := by
          rcases mem_eagerTargets inside with none | linked
          · simp at none
          · exact linked
        have entry' := List.mem_cons_of_mem (processId, Field.all, Field.all) (eagerFrame_mem linked)
        obtain ⟨-, -, -, bits⟩ := eagerFrame_bits state processId target
        refine ⟨fun set => ⟨_, entry', rfl, (bits bit).1 ?_⟩, fun set => ⟨_, entry', rfl, (bits bit).2 ?_⟩⟩ <;>
          (dsimp only at set; mask_bits)
  case wellFramed' =>
    rw [endFrames_eq]
    intro other
    have allOf : other = processId →
        ∀ bit, bit < 17 → writesOf ((processId, Field.all, Field.all) :: Kernel.filterMap
          (fun (target, unlinking) => if unlinking.isNone then some (eagerFrame state processId target) else none)
          (state.process processId).links) other bit := by
      intro same bit lower
      simp only [writesOf, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact .inl ⟨same.symm, all_testBit lower⟩
    refine ⟨fun read => ?_, fun process found notAll => ⟨fun read => ?_, fun written => ?_⟩⟩
    · simp only [readsOf, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at read ⊢
      rcases read with ⟨same, -⟩ | ⟨entry, mem, same, set⟩
      · exact .inl ⟨same, all_testBit (by decide)⟩
      · obtain ⟨target, rfl⟩ := mem_eagerFrame mem
        rw [(eagerFrame_bits state processId target).1] at set; simp at set
    · simp only [readsOf, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at read
      rcases read with ⟨same, -⟩ | ⟨entry, mem, same, set⟩
      · exact (notAll (allOf same.symm)).elim
      · obtain ⟨target, rfl⟩ := mem_eagerFrame mem
        right
        have := (eagerFrame_bits state processId target).2.2.1 set
        simp only [eagerFrame] at same; subst same
        simpa [State.process, found] using this
    · simp only [writesOf, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at written
      rcases written with ⟨same, -⟩ | ⟨entry, mem, same, set⟩
      · exact (notAll (allOf same.symm)).elim
      · obtain ⟨target, rfl⟩ := mem_eagerFrame mem
        rw [(eagerFrame_bits state processId target).2.1] at set; simp at set

/-! ### Views alike -/

private theorem Term.identicalList_refl : ∀ (terms : List Term), (∀ term ∈ terms, term.identical term = true) →
    Term.identicalList terms terms = true
  | [], _ => by simp [Term.identicalList]
  | term :: rest, same => by
    simp only [Term.identicalList, Bool.and_eq_true]
    exact ⟨same term List.mem_cons_self, Term.identicalList_refl rest fun term mem => same term (List.mem_cons_of_mem _ mem)⟩

private theorem Term.identicalEntries_refl : ∀ (entries : List (Term × Term)),
    (∀ key value, (key, value) ∈ entries → key.identical key = true ∧ value.identical value = true) →
    Term.identicalEntries entries entries = true
  | [], _ => by simp [Term.identicalEntries]
  | (key, value) :: rest, same => by
    simp only [Term.identicalEntries, Bool.and_eq_true]
    have := same key value List.mem_cons_self
    exact ⟨⟨this.1, this.2⟩, Term.identicalEntries_refl rest fun key value mem => same key value (List.mem_cons_of_mem _ mem)⟩

private theorem Term.identical_refl (term : Term) : term.identical term = true := by
  induction term using Term.induct with
  | function module name arity captures same =>
    simp only [Term.identical, beq_self_eq_true, Bool.true_and]
    exact Term.identicalList_refl _ fun term mem => same term (by simpa using mem)
  | tuple terms same =>
    simp only [Term.identical]
    exact Term.identicalList_refl _ fun term mem => same term (by simpa using mem)
  | map entries same =>
    simp only [Term.identical]
    exact Term.identicalEntries_refl _ same
  | cons head tail sameHead sameTail => simp [Term.identical, sameHead, sameTail]
  | _ => simp [Term.identical]

private theorem OwnView.identical_refl (view : OwnView) : view.identical view = true := by
  cases view with
  | env env =>
    simp [OwnView.identical, environmentIdentical, Term.identicalEntries_refl _ fun key value _ =>
      ⟨Term.identical_refl key, Term.identical_refl value⟩]
  | receive env message timesOut =>
    simp only [OwnView.identical, environmentIdentical, beq_self_eq_true, Bool.true_and, Bool.and_true,
      Term.identicalEntries_refl _ fun key value _ => ⟨Term.identical_refl key, Term.identical_refl value⟩]
    cases message <;> simp [optionIdentical, Term.identical_refl]
  | answer shape =>
    cases shape with
    | reply value => simp [OwnView.identical, Answer.Shape.identical, Term.identical_refl]
    | wait waiting => cases waiting <;> simp [OwnView.identical, Answer.Shape.identical, Wait.identical, Term.identical_refl]
    | «continue» => rfl
  | _ => simp [OwnView.identical]

private theorem handleViewIdentical_refl (view : Option (Option Term × Option Term)) :
    handleViewIdentical view view = true := by
  rcases view with _ | ⟨exits, resumed⟩
  · rfl
  · cases exits <;> cases resumed <;> simp [handleViewIdentical, optionIdentical, Term.identical_refl]

/-- Two states agree on what frames read: the records the frames read exist in
both or neither, and agree on the fields read. -/
private def Agree (frames : List Frame) (state other : State) : Prop :=
  ∀ processId, (∃ bit, bit < 17 ∧ readsOf frames processId bit) →
    (other.record processId).isSome = (state.record processId).isSome ∧
    RecordSame (readsOf frames processId) (state.record processId) (other.record processId)

private theorem readsOf_of_mem {frames : List Frame} {entry : Frame} (mem : entry ∈ frames) {bit : Nat}
    (set : entry.2.1.testBit bit = true) : readsOf frames entry.1 bit :=
  List.any_eq_true.mpr ⟨entry, mem, by simp [set]⟩

private theorem Agree.alive {frames : List Frame} {state other : State} (agree : Agree frames state other)
    {entry : Frame} (mem : entry ∈ frames) (read : entry.2.1.testBit liveBit = true) :
    other.alive entry.1 = state.alive entry.1 := by
  have := (agree entry.1 ⟨liveBit, by decide, readsOf_of_mem mem read⟩).2.1 (readsOf_of_mem mem read)
  simp only [State.alive]
  cases found : state.record entry.1 <;> cases found' : other.record entry.1 <;>
    simp_all [liveOf]

private theorem Agree.get {frames : List Frame} {state other : State} (agree : Agree frames state other)
    {entry : Frame} (mem : entry ∈ frames) (part : Part) (read : entry.2.1.testBit part.bit = true) :
    (other.process entry.1).get part = (state.process entry.1).get part := by
  obtain ⟨exists', same⟩ := agree entry.1 ⟨part.bit, part.bit_lt, readsOf_of_mem mem read⟩
  simp only [State.process]
  cases found : state.record entry.1 <;> cases found' : other.record entry.1 <;> simp only [found, found'] at exists' ⊢ <;>
    first | rfl | (simp at exists'; done) | exact ((same.2 _ _ found found').2.2 part (readsOf_of_mem mem read)).symm

private theorem Agree.head {frames : List Frame} {state other : State} (agree : Agree frames state other)
    {entry : Frame} (mem : entry ∈ frames) (read : entry.2.1.testBit headBit = true) :
    (other.process entry.1).queue.head? = (state.process entry.1).queue.head? := by
  obtain ⟨exists', same⟩ := agree entry.1 ⟨headBit, by decide, readsOf_of_mem mem read⟩
  simp only [State.process]
  cases found : state.record entry.1 <;> cases found' : other.record entry.1 <;> simp only [found, found'] at exists' ⊢ <;>
    first | rfl | (simp at exists'; done) | exact ((same.2 _ _ found found').2.1 (readsOf_of_mem mem read)).symm

private theorem Agree.queue {frames : List Frame} {state other : State} (agree : Agree frames state other)
    {entry : Frame} (mem : entry ∈ frames) (read : entry.2.1.testBit tailBit = true) :
    (other.process entry.1).queue = (state.process entry.1).queue := by
  obtain ⟨exists', same⟩ := agree entry.1 ⟨tailBit, by decide, readsOf_of_mem mem read⟩
  simp only [State.process]
  cases found : state.record entry.1 <;> cases found' : other.record entry.1 <;> simp only [found, found'] at exists' ⊢ <;>
    first | rfl | (simp at exists'; done) | exact ((same.2 _ _ found found').1 (readsOf_of_mem mem read)).symm

private theorem Agree.mono {frames frames' : List Frame} {state other : State} (agree : Agree frames state other)
    (sub : ∀ entry ∈ frames', entry ∈ frames) : Agree frames' state other := by
  intro processId used
  obtain ⟨bit, lower, read⟩ := used
  obtain ⟨exists', same⟩ := agree processId ⟨bit, lower, readsOf_mono sub _ _ read⟩
  refine ⟨exists', fun read => same.1 (readsOf_mono sub _ _ read), fun process process' found found' => ?_⟩
  exact (same.2 process process' found found').mono (readsOf_mono sub processId)

/-- What the frames of sending read: the sender's parked monitor signal, and whether the target is alive. -/
private theorem enqueueFrames_live (state : State) (source target : PID) (signal : Signal) :
    ∃ entry ∈ state.enqueueFrames source target signal, entry.1 = target ∧ entry.2.1.testBit liveBit = true := by
  simp only [State.enqueueFrames, State.appendFrames]
  split
  · split <;> exact ⟨_, List.mem_cons_self, rfl, by dsimp only; decide⟩
  · exact ⟨_, List.mem_cons_self, rfl, by dsimp only; decide⟩

private theorem sendFrames_reads (state : State) (source target : PID) (signal : Signal) :
    (∃ entry ∈ state.sendFrames source target signal, entry.1 = source ∧ entry.2.1.testBit 13 = true) ∧
    ∃ entry ∈ state.sendFrames source target signal, entry.1 = target ∧ entry.2.1.testBit liveBit = true := by
  obtain ⟨entry, mem, same, read⟩ := enqueueFrames_live state source target signal
  simp only [State.sendFrames]
  split
  · split
    · exact ⟨⟨_, List.mem_cons_self, rfl, by dsimp only; decide⟩,
        ⟨entry, List.mem_cons_of_mem _ (by simp [Kernel.append_eq, mem]), same, read⟩⟩
    · exact ⟨⟨_, List.mem_cons_self, rfl, by dsimp only; decide⟩, ⟨entry, List.mem_cons_of_mem _ mem, same, read⟩⟩
  · exact ⟨⟨_, List.mem_cons_self, rfl, by dsimp only; decide⟩, ⟨entry, List.mem_cons_of_mem _ mem, same, read⟩⟩

/-- Sending decides the same at a state agreeing on what its frames read. -/
private theorem State.sendEffect_agree {state other : State} {source target : PID} {signal : Signal}
    {frames : List Frame} (agree : Agree frames state other)
    (sub : ∀ entry ∈ state.sendFrames source target signal, entry ∈ frames) :
    other.sendEffect source target signal = state.sendEffect source target signal := by
  obtain ⟨⟨parkedEntry, parkedMem, parkedSame, parkedRead⟩, ⟨liveEntry, liveMem, liveSame, liveRead⟩⟩ :=
    sendFrames_reads state source target signal
  have parked := agree.get (sub _ parkedMem) .parked parkedRead
  have alive := agree.alive (sub _ liveMem) liveRead
  rw [parkedSame] at parked; rw [liveSame] at alive
  exact State.sendEffect_congr _ parked alive

/-- A confined own step reads the same view at a state agreeing on what its
frames read, with the same timers when it uses them, and queued signals none of
which are inert in either. -/
private theorem Task.ownView_agree {state other : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {frames : List Frame}
    {timers : Bool} (confined : Config.confined (.running state tasks finished false) (.own processId) = true)
    (lookup : Kernel.lookup processId tasks = some task)
    (found : task.ownFrames state processId = some (frames, timers)) (agree : Agree frames state other)
    (timed : timers = true → other.timers = state.timers)
    (awaited : readsOf frames processId tailBit →
      Kernel.any (other.process processId).queue (other.awaitedEntry processId) =
        Kernel.any (state.process processId).queue (state.awaitedEntry processId)) :
    task.ownView other processId = task.ownView state processId := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => rfl
  | none =>
  simp only [Config.confined, lookup] at confined
  have head : ∀ {reads writes : Nat} {rest : List Frame}, frames = (processId, reads, writes) :: rest →
      (processId, reads, writes) ∈ frames := fun equal => equal ▸ List.mem_cons_self
  cases computation with
  | receive timeout select next =>
    simp only [Task.ownFrames] at found
    dsimp only at confined
    cases selected : selectMessage (select (state.view processId)) (state.process processId).mailbox with
    | some => simp [selected] at confined
    | none =>
      simp only [selected] at found
      -- Every frame of the receive reads the environment and the mailbox.
      have facts : ∀ {reads : Nat}, frames = [(processId, reads, 0)] → reads.testBit 3 = true →
          reads.testBit 4 = true → reads.testBit 2 = true →
          other.view processId = state.view processId ∧
            (other.process processId).mailbox = (state.process processId).mailbox := by
        intro reads equal pdict refCounter mailbox
        have inside : (processId, reads, 0) ∈ frames := by rw [equal]; exact List.mem_cons_self
        have samePdict := agree.get inside .pdict pdict
        have sameCounter := agree.get inside .refCounter refCounter
        have sameMailbox := agree.get inside .mailbox mailbox
        simp only [ProcessState.get] at samePdict sameCounter sameMailbox
        exact ⟨by simp [State.view, samePdict, sameCounter], sameMailbox⟩
      cases timeout with
      | infinity =>
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨view, mailbox⟩ := facts found.1.symm (by decide) (by decide) (by decide)
        simp only [Task.ownView, view, mailbox]
      | _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨view, mailbox⟩ := facts found.1.symm (by decide) (by decide) (by decide)
        have tail : readsOf frames processId tailBit := by
          rw [← found.1]; simp [readsOf]; decide
        simp only [Task.ownView, view, mailbox, awaited tail]
  | request query next =>
    have counter : ∀ {reads writes : Nat} {rest : List Frame}, frames = (processId, reads, writes) :: rest →
        reads.testBit 4 = true → (other.process processId).refCounter = (state.process processId).refCounter :=
      fun equal set => agree.get (head equal) .refCounter set
    cases query with
    | monitor target alias =>
      simp only [Task.ownFrames, State.requestFrames] at found
      have same : (other.process processId).refCounter = (state.process processId).refCounter := by
        split at found
        · simp only [Option.some.injEq, Prod.mk.injEq] at found
          exact counter found.1.symm (by decide)
        · simp only [Option.some.injEq, Prod.mk.injEq] at found
          exact counter found.1.symm (by decide)
      simp only [Task.ownView, State.request, State.allocate, same]
      split <;> rfl
    | demonitor reference flush =>
      simp only [Task.ownFrames, State.requestFrames, Option.some.injEq, Prod.mk.injEq] at found
      have same := agree.get (head found.1.symm) .monitoring (by dsimp only [Part.bit]; decide)
      simp only [ProcessState.get] at same
      simp only [Task.ownView, State.request, same]
      split <;> simp [Answer.shape]
    | startTimer destination message duration =>
      simp only [Task.ownFrames, State.requestFrames, Option.some.injEq, Prod.mk.injEq] at found
      have same := counter found.1.symm (by decide)
      simp only [Task.ownView, State.request, State.allocate, same]
      split <;> simp [Answer.shape]
    | cancelTimer reference =>
      simp only [Task.ownFrames, State.requestFrames, Option.some.injEq, Prod.mk.injEq] at found
      have same := agree.get (head found.1.symm) .cancels (by dsimp only [Part.bit]; decide)
      simp only [ProcessState.get] at same
      simp only [Task.ownView, same, timed found.2.symm]
    | alive target =>
      simp only [Task.ownFrames, State.requestFrames] at found
      simp only [Task.ownView, State.request]
      by_cases self : target = processId
      · subst self; simp [Answer.shape]
      · have differ : (target == processId) = false := by simpa using self
        simp only [differ, self, Bool.false_eq_true, ↓reduceIte] at found ⊢
        have alive : other.alive target = state.alive target := by
          split at found
          · simp only [Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨-, ⟨entry, mem, same, read⟩⟩ := sendFrames_reads state processId target .isAlive
            rw [← same]; exact agree.alive (found.1 ▸ mem) read
          · simp only [Option.some.injEq, Prod.mk.injEq] at found
            have := agree.alive (entry := (target, Field.live, 0)) (by rw [← found.1]; exact List.mem_cons_self)
              (by dsimp only; decide)
            exact this
        rw [alive]
        split <;> simp [Answer.shape]
    | sendAlias alias message => rfl
    | _ => simp at confined
  | _ => first | rfl | simp at confined

/-! ### Termination decided by what its frames read -/

/-- Removing a target from the links a process that ended has left to signal. -/
private def exitingWithout (target : PID) (process : ProcessState) : ProcessState :=
  { process with exiting := process.exiting.map fun (exiting : Exiting) =>
    { exiting with links := Kernel.filter (· != target) exiting.links } }

/-- Removing the link to a process that ended, applying its exit as it is sent. -/
private def linkRemoved (processId : PID) (process : ProcessState) : ProcessState :=
  { process with
    links := Kernel.filter (·.1 != processId) process.links
    eagerExits := insertPid processId process.eagerExits }

/-- A link exit of a process that ended, decided by whether it is applied as it is sent. -/
private theorem State.eagerExitEffect_eq (state : State) (processId target : PID) (reason : Term)
    (ended : state.alive processId = false) :
    State.eagerExitEffect processId reason state target =
      if state.eagerLink processId target reason then
        (Effect.modify processId (exitingWithout target)).andThen (.modify target (linkRemoved processId))
      else {} := by
  unfold State.eagerExitEffect
  split
  · rename_i eager
    have differ : target ≠ processId := fun same => by
      subst same; simp [State.eagerLink, ended] at eager
    have still : (state.modify processId (exitingWithout target)).eagerLink processId target reason = true := by
      have alive : (state.modify processId (exitingWithout target)).alive target = state.alive target :=
        State.alive_modify _ _ _ _ fun process => by simp only [exitingWithout]; cases process.exiting <;> rfl
      simp only [State.eagerLink, alive, State.process_modify_other _ _ differ] at eager ⊢
      exact eager
    have link : (state.modify processId (exitingWithout target)).linkExitEffect processId target reason =
        .modify target (linkRemoved processId) := by
      unfold State.linkExitEffect; rw [still]; rfl
    exact congrArg _ link
  · rfl

/-- Whether a link exit is applied as it is sent reads only liveness, trapping and queues. -/
private theorem State.eagerLink_modify (state : State) (changed processId target : PID) (reason : Term)
    (change : ProcessState → ProcessState)
    (live : ∀ process, (change process).exiting.isSome = process.exiting.isSome)
    (trap : ∀ process, (change process).trapExit = process.trapExit)
    (queue : ∀ process, (change process).queue = process.queue) :
    (state.modify changed change).eagerLink processId target reason = state.eagerLink processId target reason := by
  have trap' := State.process_modify_keeps (state := state) (processId := changed) (other := target)
    (get := (·.trapExit)) trap
  have queue' := State.process_modify_keeps (state := state) (processId := changed) (other := target)
    (get := (·.queue)) queue
  simp only [State.eagerLink, State.alive_modify _ _ _ _ live]
  try simp only at trap' queue'
  rw [trap', queue']

/-- Whether a link exit is applied as it is sent, which other link exits of
the same process that ended do not change. -/
private theorem State.eagerLink_exit (state : State) (processId target other : PID) (reason : Term)
    (ended : state.alive processId = false) :
    (if state.eagerLink processId target reason then
        (state.modify processId (exitingWithout target)).linkExit processId target reason
      else state).eagerLink processId other reason = state.eagerLink processId other reason := by
  split
  · rename_i eager
    have differ : target ≠ processId := fun same => by
      subst same; simp [State.eagerLink, ended] at eager
    unfold State.linkExit
    have still : (state.modify processId (exitingWithout target)).eagerLink processId target reason = true := by
      have alive : (state.modify processId (exitingWithout target)).alive target = state.alive target :=
        State.alive_modify _ _ _ _ fun process => by simp only [exitingWithout]; cases process.exiting <;> rfl
      simp only [State.eagerLink, alive, State.process_modify_other _ _ differ] at eager ⊢
      exact eager
    rw [still]
    simp only [↓reduceIte]
    refine (State.eagerLink_modify _ _ _ _ _ _ ?_ ?_ ?_).trans (State.eagerLink_modify _ _ _ _ _ _ ?_ ?_ ?_) <;>
      intro process <;> first | rfl | (simp only [exitingWithout]; cases process.exiting <;> rfl)
  · rfl

/-- A link exit of a process that ended, applied as it is sent, as `State.terminate` folds them. -/
private def State.eagerExit (processId : PID) (reason : Term) (state : State) (target : PID) : State :=
  if state.eagerLink processId target reason then
    (state.modify processId (exitingWithout target)).linkExit processId target reason
  else state

private theorem State.alive_eagerExit (state : State) (processId target other : PID) (reason : Term) :
    (State.eagerExit processId reason state target).alive other = state.alive other := by
  unfold State.eagerExit
  split
  · unfold State.linkExit
    split
    · refine (State.alive_modify _ _ _ _ ?_).trans (State.alive_modify _ _ _ _ ?_) <;> intro process
      · rfl
      · simp only [exitingWithout]; cases process.exiting <;> rfl
    · refine (State.alive_send _ _ _ _ _).trans (State.alive_modify _ _ _ _ ?_)
      intro process; simp only [exitingWithout]; cases process.exiting <;> rfl
  · rfl

/-- The link exits of a process that ended, each decided as at the start. -/
private def eagerChain (processId : PID) (eager : PID → Bool) : List PID → Effect
  | [] => {}
  | target :: rest =>
      (if eager target then
        (Effect.modify processId (exitingWithout target)).andThen (.modify target (linkRemoved processId))
      else {}).andThen (eagerChain processId eager rest)

private theorem chainEffect_eagerExit (processId : PID) (reason : Term) :
    ∀ (targets : List PID) (state : State), state.alive processId = false →
      chainEffect (State.eagerExit processId reason) (State.eagerExitEffect processId reason) state targets =
        eagerChain processId (fun target => state.eagerLink processId target reason) targets
  | [], _, _ => rfl
  | target :: rest, state, ended => by
    simp only [chainEffect, eagerChain]
    rw [State.eagerExitEffect_eq state processId target reason ended,
      chainEffect_eagerExit processId reason rest _ ((State.alive_eagerExit _ _ _ _ _).trans ended)]
    congr 2
    funext other
    exact State.eagerLink_exit state processId target other reason ended

private theorem eagerChain_congr {processId : PID} {eager eager' : PID → Bool} :
    ∀ {targets : List PID}, (∀ target ∈ targets, eager' target = eager target) →
      eagerChain processId eager' targets = eagerChain processId eager targets
  | [], _ => rfl
  | target :: rest, same => by
    simp only [eagerChain, same target List.mem_cons_self,
      eagerChain_congr fun target mem => same target (List.mem_cons_of_mem _ mem)]

/-- A process ending decides the same at a state where its record, whether a
timer is to it, and whether each link exit is applied as it is sent are the same. -/
private theorem State.terminateEffect_congr {state other : State} {processId : PID} {reason : Term}
    (process : other.process processId = state.process processId)
    (timed : Kernel.any other.timers (·.destination == processId) = Kernel.any state.timers (·.destination == processId))
    (eager : ∀ target, (target, none) ∈ (state.process processId).links → target ≠ processId →
      other.eagerLink processId target reason = state.eagerLink processId target reason) :
    other.terminateEffect processId reason = state.terminateEffect processId reason := by
  -- The link exits are decided once the process ended, which changes only its own record.
  have ended : ∀ (state : State) (timers : List Timer) (record : ProcessState), record.exiting.isSome →
      ∀ target, ({ state with timers }.set processId record).eagerLink processId target reason =
        if target = processId then false else state.eagerLink processId target reason := by
    intro state timers record exiting target
    split
    · rename_i same; subst same
      simp only [State.eagerLink, State.alive, State.record_set, ↓reduceIte]
      cases equal : record.exiting <;> simp_all
    · rename_i differ
      simp only [State.eagerLink, State.alive, State.process, State.record_set, differ, ↓reduceIte]
      rfl
  unfold State.terminateEffect
  dsimp only
  rw [process, timed]
  erw [chainEffect_eagerExit processId reason _ _ (by simp [State.alive, State.record_set]),
    chainEffect_eagerExit processId reason _ _ (by simp [State.alive, State.record_set])]
  congr 1
  refine eagerChain_congr fun target mem => ?_
  rw [ended _ _ _ rfl, ended _ _ _ rfl]
  split
  · rfl
  · rename_i differ
    have linked : (target, none) ∈ (state.process processId).links := by
      rcases mem_eagerTargets mem with none | linked
      · simp at none
      · exact linked
    exact eager target linked differ

/-- A record agreeing on every field, its queue included, is the same record. -/
private theorem Agree.process {frames : List Frame} {state other : State} (agree : Agree frames state other)
    {entry : Frame} (mem : entry ∈ frames) (all : entry.2.1 = Field.all) :
    other.process entry.1 = state.process entry.1 := by
  refine ProcessState.ext_get (agree.queue mem (by rw [all]; decide)) fun part => agree.get mem part ?_
  rw [all]; exact all_testBit part.bit_lt

/-- A confined own step has the same effect at a state agreeing on what its
frames read, with the same timers when it uses them, where the process is
alike alive, and where, when it ends, a timer is to it and each of its link
exits is applied as it is sent alike. -/
private theorem Task.ownEffect_agree {state other : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α} {frames : List Frame}
    {timers : Bool} (confined : Config.confined (.running state tasks finished false) (.own processId) = true)
    (lookup : Kernel.lookup processId tasks = some task)
    (found : task.ownFrames state processId = some (frames, timers)) (agree : Agree frames state other)
    (timed : timers = true → other.timers = state.timers)
    (timedTo : frames = (state.endFrames processId).1 →
      Kernel.any other.timers (·.destination == processId) = Kernel.any state.timers (·.destination == processId))
    (eager : frames = (state.endFrames processId).1 → ∀ target reason,
      (target, none) ∈ (state.process processId).links → target ≠ processId →
      other.eagerLink processId target reason = state.eagerLink processId target reason) :
    task.ownEffect other processId = task.ownEffect state processId := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => rfl
  | none =>
  simp only [Config.confined, lookup] at confined
  have head : ∀ {reads writes : Nat} {rest : List Frame}, frames = (processId, reads, writes) :: rest →
      (processId, reads, writes) ∈ frames := fun equal => equal ▸ List.mem_cons_self
  have ending : ∀ reason, frames = (state.endFrames processId).1 →
      other.terminateEffect processId reason = state.terminateEffect processId reason := by
    intro reason equal
    have inside : (processId, Field.all, Field.all) ∈ frames := by
      rw [equal, endFrames_eq]; exact List.mem_cons_self
    exact State.terminateEffect_congr (agree.process inside rfl) (timedTo equal) fun target linked differ =>
      eager equal target reason linked differ
  cases computation with
  | ok =>
    simp only [Task.ownFrames, Option.some.injEq] at found
    exact ending _ (congrArg Prod.fst found).symm
  | error exception =>
    cases exception with
    | exhausted => simp at confined
    | _ =>
      simp only [Task.ownFrames, Option.some.injEq] at found
      exact ending _ (congrArg Prod.fst found).symm
  | send destination message =>
    simp only [Task.ownFrames, Option.some.injEq, Prod.mk.injEq] at found
    exact State.sendEffect_agree agree fun entry mem => found.1 ▸ mem
  | receive timeout select next =>
    simp only [Task.ownFrames] at found
    dsimp only at confined
    cases selected : selectMessage (select (state.view processId)) (state.process processId).mailbox with
    | some => simp [selected] at confined
    | none =>
      simp only [selected] at found
      have facts : ∀ {reads : Nat}, frames = [(processId, reads, 0)] → reads.testBit 3 = true →
          reads.testBit 4 = true → reads.testBit 2 = true →
          other.view processId = state.view processId ∧
            (other.process processId).mailbox = (state.process processId).mailbox := by
        intro reads equal pdict refCounter mailbox
        have inside : (processId, reads, 0) ∈ frames := by rw [equal]; exact List.mem_cons_self
        have samePdict := agree.get inside .pdict pdict
        have sameCounter := agree.get inside .refCounter refCounter
        have sameMailbox := agree.get inside .mailbox mailbox
        simp only [ProcessState.get] at samePdict sameCounter sameMailbox
        exact ⟨by simp [State.view, samePdict, sameCounter], sameMailbox⟩
      have same : other.view processId = state.view processId ∧
          (other.process processId).mailbox = (state.process processId).mailbox := by
        cases timeout <;> simp only [Option.some.injEq, Prod.mk.injEq] at found <;>
          exact facts found.1.symm (by decide) (by decide) (by decide)
      simp only [Task.ownEffect, same.1, same.2, selected]
  | request query next =>
    have counter : ∀ {reads writes : Nat} {rest : List Frame}, frames = (processId, reads, writes) :: rest →
        reads.testBit 4 = true → (other.process processId).refCounter = (state.process processId).refCounter :=
      fun equal set => agree.get (head equal) .refCounter set
    cases query with
    | monitor target alias =>
      simp only [Task.ownFrames, State.requestFrames] at found
      simp only [Task.ownEffect, State.requestEffect, State.allocate]
      by_cases self : target = processId
      · subst self
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
        have same := counter found.1.symm (by decide)
        simp only [same, ↓reduceIte]
      · have differ : (target == processId) = false := by simpa using self
        simp only [differ, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
        have same := counter found.1.symm (by decide)
        have parked := agree.get (head found.1.symm) .parked (by dsimp only [Part.bit]; decide)
        simp only [ProcessState.get] at parked
        simp only [self, ↓reduceIte, same]
        -- Allocating keeps the parked monitor signal, and whether its target is alive.
        let allocate := fun process : ProcessState => { process with refCounter := process.refCounter + 1 }
        have unparked : (other.modify processId allocate).unparkEffect processId =
            (state.modify processId allocate).unparkEffect processId := by
          refine State.unparkEffect_congr ?_ fun parkedTarget reference found' => ?_
          · exact (State.process_modify_keeps (change := allocate) (get := (·.parked)) fun _ => rfl).trans
              (parked.trans (State.process_modify_keeps (change := allocate) (get := (·.parked)) fun _ => rfl).symm)
          · rw [State.process_modify_keeps (state := state) (change := allocate) (get := (·.parked))
              (fun _ => rfl)] at found'
            have inside : ∃ entry ∈ frames, entry.1 = parkedTarget ∧ entry.2.1.testBit liveBit = true := by
              obtain ⟨entry, mem, same, read⟩ := enqueueFrames_live state processId parkedTarget (.monitor reference)
              refine ⟨entry, ?_, same, read⟩
              rw [← found.1]; simp only [found']; exact List.mem_cons_of_mem _ mem
            obtain ⟨entry, mem, sameTarget, read⟩ := inside
            have alive := agree.alive mem read
            rw [sameTarget] at alive
            refine (State.alive_modify _ _ _ _ ?_).trans ((State.alive_modify _ _ _ _ ?_).trans
              (alive.trans ((State.alive_modify _ _ _ _ ?_).trans (State.alive_modify _ _ _ _ ?_)).symm)) <;>
              intro process <;> rfl
        rw [unparked]
    | demonitor reference flush => rfl
    | startTimer destination message duration =>
      simp only [Task.ownFrames, State.requestFrames, Option.some.injEq, Prod.mk.injEq] at found
      have same := counter found.1.symm (by decide)
      have alive : other.alive destination = state.alive destination :=
        agree.alive (entry := (destination, Field.live, 0)) (by rw [← found.1]; simp) (by dsimp only; decide)
      have alive' : (other.modify processId fun process => { process with refCounter := process.refCounter + 1 }).alive
          destination = (state.modify processId fun process =>
            { process with refCounter := process.refCounter + 1 }).alive destination := by
        refine (State.alive_modify _ _ _ _ ?_).trans (alive.trans (State.alive_modify _ _ _ _ ?_).symm) <;>
          intro process <;> rfl
      try simp only [ProcessState.get] at same
      simp only [Task.ownEffect, State.requestEffect, State.allocate, same, alive']
      rfl
    | cancelTimer reference =>
      simp only [Task.ownFrames, State.requestFrames, Option.some.injEq, Prod.mk.injEq] at found
      simp only [Task.ownEffect, State.requestEffect, timed found.2.symm]
    | alive target =>
      simp only [Task.ownFrames, State.requestFrames] at found
      simp only [Task.ownEffect, State.requestEffect]
      by_cases same : target = processId
      · simp [same]
      · have differ : (target == processId) = false := by simpa using same
        simp only [differ, same, Bool.false_eq_true, ↓reduceIte] at found ⊢
        split at found
        · rename_i targetAlive
          simp only [Option.some.injEq, Prod.mk.injEq] at found
          have alive : other.alive target = state.alive target := by
            obtain ⟨-, ⟨entry, mem, same, read⟩⟩ := sendFrames_reads state processId target .isAlive
            rw [← same]; exact agree.alive (found.1 ▸ mem) read
          rw [alive, targetAlive]
          exact State.sendEffect_agree agree fun entry mem => found.1 ▸ mem
        · rename_i targetDead
          simp only [Option.some.injEq, Prod.mk.injEq] at found
          have alive : other.alive target = state.alive target :=
            agree.alive (entry := (target, Field.live, 0)) (by rw [← found.1]; exact List.mem_cons_self)
              (by dsimp only; decide)
          simp only [Bool.not_eq_true] at targetDead
          rw [alive, targetDead]
          have self : other.alive processId = state.alive processId :=
            agree.alive (entry := (processId, Field.live, Field.queueTail))
              (by rw [← found.1]; simp) (by dsimp only; decide)
          exact State.enqueueEffect_congr _ self
    | sendAlias alias message =>
      simp only [Task.ownFrames, State.requestFrames, Option.some.injEq, Prod.mk.injEq] at found
      exact State.sendEffect_agree agree fun entry mem => found.1 ▸ mem
    | _ => simp at confined
  | _ => simp at confined

/-- The kinds of signal whose handling can be confined. -/
private def Signal.handledConfined : Signal → Bool
  | .message _ | .aliasMessage .. | .monitor _ | .down .. => true
  | _ => false

/-- Handling a confined kind of signal neither resumes nor ends the process. -/
private theorem State.handle_confined (state : State) (processId : PID) (waiting : Option Wait) (entry : Entry)
    (kind : entry.signal.handledConfined = true) :
    (state.handle processId waiting entry).2 = (none, none) := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp [Signal.handledConfined] at kind <;> simp only [State.handle] <;> (try split) <;> rfl

/-- Handling a confined kind of signal reads the same and has the same effect at
a state agreeing on what its frames read. -/
private theorem Task.handle_agree {state other : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task task' : Task α} {frames : List Frame}
    {timers : Bool} (confined : Config.confined (.running state tasks finished false) (.handle processId) = true)
    (found : task.handleFrames state processId = some (frames, timers)) (agree : Agree frames state other) :
    task'.handleView other processId = task.handleView state processId ∧
      task'.handleEffect other processId = task.handleEffect state processId := by
  simp only [Config.confined] at confined
  simp only [Task.handleFrames] at found
  cases queue : (state.process processId).queue with
  | nil => simp [queue] at confined
  | cons entry rest =>
    simp only [queue] at confined found
    have kind : entry.signal.handledConfined = true := by
      obtain ⟨source, signal⟩ := entry; cases signal <;> simp_all [Signal.handledConfined]
    -- Every frame of handling reads the head, so the other state handles the same signal.
    have own : ∃ reads writes, frames = [(processId, Field.queueHead ||| reads, Field.queueHead ||| writes)] := by
      obtain ⟨source, signal⟩ := entry
      cases signal <;> simp only [Option.some.injEq, Prod.mk.injEq] at found <;>
        first | exact ⟨_, _, found.1.symm⟩ | simp [Signal.handledConfined] at kind
    obtain ⟨reads, writes, equal⟩ := own
    have inside : (processId, Field.queueHead ||| reads, Field.queueHead ||| writes) ∈ frames := by
      rw [equal]; exact List.mem_cons_self
    have head := agree.head inside (by rw [Nat.testBit_or]; exact Bool.or_eq_true_iff.mpr (.inl (by decide)))
    rw [queue] at head
    obtain ⟨rest', queue'⟩ : ∃ rest', (other.process processId).queue = entry :: rest' := by
      cases equal' : (other.process processId).queue with
      | nil => rw [equal'] at head; simp at head
      | cons first rest' => rw [equal'] at head; simp at head; exact ⟨rest', by rw [head]⟩
    have continues : ∀ (state : State) waiting, (state.handle processId waiting entry).2.2 = none := fun state waiting => by
      rw [State.handle_confined state processId waiting entry kind]
    refine ⟨?_, ?_⟩
    · simp only [Task.handleView, queue, queue']
      have kept := fun (state : State) waiting => State.handle_confined state processId waiting entry kind
      simp only [kept]
    · rw [Task.handleEffect_of_continues queue (continues _ _), Task.handleEffect_of_continues queue' (continues _ _)]
      congr 1
      have set : ∀ (state : State) (process : ProcessState), (state.set processId process).process processId = process :=
        fun state process => by simp [State.process, State.record_set]
      obtain ⟨source, signal⟩ := entry
      cases signal with
      | message message => rfl
      | monitor reference => rfl
      | aliasMessage alias message =>
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        have mem : (processId, Field.queueHead ||| Field.aliases, Field.queueHead ||| Field.mailbox) ∈ frames := by
          rw [← found.1]; exact List.mem_cons_self
        have aliases := agree.get mem .aliases (by dsimp only [Part.bit]; decide)
        simp only [ProcessState.get] at aliases
        simp only [State.handleEffect, set, aliases]
      | down reference reason =>
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        cases normal : isNormal reason
        · simp only [normal, Bool.false_eq_true, ↓reduceIte, Nat.or_zero] at found
          have mem : (processId, Field.queueHead ||| (Field.monitoring ||| Field.aliases),
              Field.queueHead ||| (Field.monitoring ||| Field.aliases ||| Field.mailbox)) ∈ frames := by
            rw [← found.1]; exact List.mem_cons_self
          have monitoring := agree.get mem .monitoring (by dsimp only [Part.bit]; decide)
          simp only [ProcessState.get] at monitoring
          simp only [State.handleEffect, set, monitoring, normal, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        · simp only [normal, ↓reduceIte] at found
          have mem : (processId, Field.queueHead ||| (Field.monitoring ||| Field.aliases ||| Field.eagerExits),
              Field.queueHead ||| (Field.monitoring ||| Field.aliases ||| Field.eagerExits ||| Field.mailbox)) ∈ frames := by
            rw [← found.1]; exact List.mem_cons_self
          have monitoring := agree.get mem .monitoring (by dsimp only [Part.bit]; decide)
          have eager := agree.get mem .eagerExits (by dsimp only [Part.bit]; decide)
          simp only [ProcessState.get] at monitoring eager
          simp only [State.handleEffect, set, monitoring, eager, normal]
      | _ => simp [Signal.handledConfined] at kind

/-- The next phase of a process that ended is enabled alike and has the same
effect at a state agreeing on what its frames read. -/
private theorem State.phase_agree {state other : State} {processId : PID} {frames : List Frame} {timers : Bool}
    (found : state.phaseFrames processId = some (frames, timers)) (agree : Agree frames state other) :
    (other.phase processId).isSome = (state.phase processId).isSome ∧
      other.phaseEffect processId = state.phaseEffect processId := by
  unfold State.phaseFrames at found
  cases record : state.record processId with
  | none => simp [record] at found
  | some process =>
    simp only [record] at found
    cases exits : process.exiting with
    | none => simp [exits] at found
    | some exiting =>
      simp only [exits] at found
      have same : state.process processId = process := by simp [State.process, record]
      -- The record exists alike, as every frame of a phase reads some of it.
      have own : ∀ {entry : Frame} {rest : List Frame}, frames = entry :: rest → entry.1 = processId →
          entry.2.1.testBit 15 = true →
          other.record processId = some { other.process processId with } ∧
            (other.process processId).exiting = some exiting := by
        intro entry rest equal pid set
        have inside : entry ∈ frames := by rw [equal]; exact List.mem_cons_self
        obtain ⟨exists', -⟩ := agree processId ⟨15, by decide, pid ▸ readsOf_of_mem inside set⟩
        have exiting' := agree.get inside .exiting set
        rw [pid] at exiting'
        simp only [ProcessState.get, same, exits] at exiting'
        refine ⟨?_, exiting'⟩
        cases found' : other.record processId with
        | none => rw [found', record] at exists'; simp at exists'
        | some process' => simp [State.process, found']
      have recordOf : ∀ (state : State) (process : ProcessState), state.record processId = some process →
          state.process processId = process := fun state process found => by simp [State.process, found]
      -- Sending from the process reads its parked monitor signal and whether the target is alive.
      have sends : ∀ {signal : Signal} {target : PID} (change : ProcessState → ProcessState),
          (∀ process, (change process).parked = process.parked) →
          (∀ process, (change process).exiting.isSome = process.exiting.isSome) →
          (∀ entry ∈ state.sendFrames processId target signal, entry ∈ frames) →
          (other.modify processId change).sendEffect processId target signal =
            (state.modify processId change).sendEffect processId target signal := by
        intro signal target change keepsParked live sub
        obtain ⟨⟨parkedEntry, parkedMem, parkedSame, parkedRead⟩, ⟨liveEntry, liveMem, liveSame, liveRead⟩⟩ :=
          sendFrames_reads state processId target signal
        have parked := agree.get (sub _ parkedMem) .parked parkedRead
        have alive := agree.alive (sub _ liveMem) liveRead
        rw [parkedSame] at parked; rw [liveSame] at alive
        refine State.sendEffect_congr _ ?_ ?_
        · exact (State.process_modify_keeps (get := (·.parked)) keepsParked).trans
            (parked.trans (State.process_modify_keeps (get := (·.parked)) keepsParked).symm)
        · exact (State.alive_modify _ _ _ _ live).trans (alive.trans (State.alive_modify _ _ _ _ live).symm)
      cases downs : exiting.downs with
      | cons down rest =>
        obtain ⟨reference, watcher⟩ := down
        simp only [downs, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨record', exiting'⟩ := own found.1.symm (by split <;> rfl) (by split <;> (dsimp only; decide))
        refine ⟨by cases links : exiting.links <;> simp [State.phase, record, record', exits, exiting', links, downs], ?_⟩
        simp only [State.phaseEffect, same, exits, exiting', downs]
        rw [sends (setDowns rest) (fun _ => rfl) (fun process => by simp only [setDowns]; cases process.exiting <;> rfl)
          fun entry mem => found.1 ▸ List.mem_cons_of_mem _ mem]
      | nil =>
        cases queue : process.queue with
        | nil =>
          simp only [downs, queue, Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨record', exiting'⟩ := own found.1.symm (by split <;> rfl) (by split <;> (dsimp only; decide))
          have inside : (processId, Field.all, Field.all) ∈ frames := by rw [← found.1]; exact List.mem_cons_self
          have queue' := agree.queue inside (by dsimp only; decide)
          rw [same, queue] at queue'
          refine ⟨by cases links : exiting.links <;>
            simp [State.phase, record, record', exits, exiting', links, downs, queue, queue'], ?_⟩
          simp only [State.phaseEffect, same, exits, exiting', downs, queue, queue']
        | cons entry rest =>
          simp only [downs, queue, Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨record', exiting'⟩ := own found.1.symm (by split <;> rfl) (by split <;> (dsimp only; decide))
          have inside : (if rest.isEmpty then (processId, Field.all, Field.all)
              else (processId, Field.exiting ||| Field.queueHead, Field.queueHead)) ∈ frames := by
            rw [← found.1]; exact List.mem_cons_self
          have head := agree.head inside (by split <;> (dsimp only; decide))
          rw [show (if rest.isEmpty then (processId, Field.all, Field.all)
              else (processId, Field.exiting ||| Field.queueHead, Field.queueHead)).1 = processId by split <;> rfl,
            same, queue] at head
          obtain ⟨rest', queue'⟩ : ∃ rest', (other.process processId).queue = entry :: rest' := by
            cases equal' : (other.process processId).queue with
            | nil => rw [equal'] at head; simp at head
            | cons first rest' => rw [equal'] at head; simp at head; exact ⟨rest', by rw [head]⟩
          refine ⟨by cases links : exiting.links <;>
            simp [State.phase, record, record', exits, exiting', links, downs, queue, queue'], ?_⟩
          simp only [State.phaseEffect, same, exits, exiting', downs, queue, queue']
          congr 1
          obtain ⟨source, signal⟩ := entry
          have keepsParked : ∀ process : ProcessState, ({ process with queue := process.queue.drop 1 }).parked =
              process.parked := fun _ => rfl
          have live : ∀ process : ProcessState, ({ process with queue := process.queue.drop 1 }).exiting.isSome =
              process.exiting.isSome := fun _ => rfl
          cases signal <;> simp only [State.answerEffect]
          all_goals first
            | rfl
            | exact sends _ keepsParked live fun entry mem => found.1 ▸ List.mem_cons_of_mem _ mem

/-- Sending a parked monitor signal is enabled alike and has the same effect at
a state agreeing on what its frames read. -/
private theorem State.unpark_agree {state other : State} {processId target : PID} {reference : List Nat}
    (parked : (state.process processId).parked = some (target, reference))
    (agree : Agree ((processId, Field.parked, Field.parked) ::
      state.enqueueFrames processId target (.monitor reference)) state other) :
    (other.process processId).parked = (state.process processId).parked ∧
      other.unparkEffect processId = state.unparkEffect processId := by
  have same := agree.get (entry := (processId, Field.parked, Field.parked)) List.mem_cons_self .parked
    (by dsimp only [Part.bit]; decide)
  simp only [ProcessState.get] at same
  refine ⟨same, State.unparkEffect_congr same fun target' reference' found => ?_⟩
  rw [parked] at found; simp only [Option.some.injEq, Prod.mk.injEq] at found
  obtain ⟨rfl, rfl⟩ := found
  obtain ⟨entry, mem, sameTarget, read⟩ := enqueueFrames_live state processId target (.monitor reference)
  have alive := agree.alive (List.mem_cons_of_mem _ mem) read
  rw [sameTarget] at alive
  refine (State.alive_modify _ _ _ _ ?_).trans (alive.trans (State.alive_modify _ _ _ _ ?_).symm) <;>
    intro process <;> rfl

/-- Firing a timer is enabled alike and has the same effect at a state with the
same timers agreeing on what its frames read. -/
private theorem State.fire_agree {state other : State} {timer : Timer}
    (timers : other.timers = state.timers)
    (agree : Agree (state.enqueueFrames clock timer.destination (.message timer.message)) state other) :
    other.firing = state.firing ∧ other.fireEffect timer = state.fireEffect timer := by
  refine ⟨by simp [State.firing, timers], ?_⟩
  obtain ⟨entry, mem, same, read⟩ := enqueueFrames_live state clock timer.destination (.message timer.message)
  have alive := agree.alive mem read
  rw [same] at alive
  simp only [State.fireEffect]
  congr 1
  exact State.enqueueEffect_congr _ alive

/-! ### Normalization after a confined step is local -/

/-- A record normalizing leaves as it is, given which processes are gone. -/
private def Clean (gone : PID → Bool) (processId : PID) (process : ProcessState) : Prop :=
  normRecord gone processId process = process ∧ process.finished = false

/-- Every record of a normalized state is clean. -/
private theorem Clean.of_normalized {state : State} (sorted : state.Sorted) (normalized : state.normalize = state)
    {processId : PID} {process : ProcessState} (found : state.record processId = some process) :
    Clean state.gone processId process := by
  have equal := congrArg (·.record processId) normalized
  simp only [State.record_normalize sorted, found, Option.map_some, Option.filter] at equal
  split at equal
  · rename_i kept
    simp only [Option.some.injEq] at equal
    refine ⟨by rw [← State.normalizeRecord_eq found]; exact equal, ?_⟩
    rw [← equal]; simpa using kept
  · simp at equal

/-- Normalizing leaves clean records as they are. -/
private theorem State.record_normalize_clean {state : State} (sorted : state.Sorted) {processId : PID}
    (clean : ∀ process, state.record processId = some process → Clean state.gone processId process) :
    state.normalize.record processId = state.record processId := by
  rw [State.record_normalize sorted]
  cases found : state.record processId with
  | none => rfl
  | some process =>
    obtain ⟨same, kept⟩ := clean process found
    simp [Option.filter, State.normalizeRecord_eq found, same, kept]

/-- A live record is clean when none of its queued signals is inert and none
of the links it is removing is to a process that is gone. -/
private theorem Clean.live {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (live : process.exiting = none)
    (queue : ∀ entry ∈ process.queue, inert gone processId process entry = false)
    (links : ∀ link ∈ process.links, link.2.isSome = true → gone link.1 = false) :
    Clean gone processId process := by
  refine ⟨?_, by simp [ProcessState.finished, live]⟩
  unfold normRecord
  rw [live]
  simp only [Kernel.filter_eq]
  rw [List.filter_eq_self.mpr fun entry mem => by simp [queue entry mem],
    List.filter_eq_self.mpr fun link mem => by
      cases some : link.2.isSome <;> simp [some, links link mem]]
  cases process; simp_all

/-- What a clean live record satisfies. -/
private theorem Clean.live_facts {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (clean : Clean gone processId process) (live : process.exiting = none) :
    (∀ entry ∈ process.queue, inert gone processId process entry = false) ∧
      ∀ link ∈ process.links, link.2.isSome = true → gone link.1 = false := by
  have equal := clean.1
  unfold normRecord at equal
  rw [live] at equal
  simp only [Kernel.filter_eq] at equal
  have queue := congrArg ProcessState.queue equal
  have links := congrArg ProcessState.links equal
  simp only at queue links
  refine ⟨fun entry mem => ?_, fun link mem some => ?_⟩
  · have := List.filter_eq_self.mp queue entry mem; simpa using this
  · have := List.filter_eq_self.mp links link mem; simp [some] at this; exact this

/-- A live record stays clean through a change that keeps or removes its queued
signals and the links it is removing, making none of them inert or gone, and
appends signals that are not inert. -/
private theorem Clean.preserve {gone gone' : PID → Bool} {processId : PID} {process process' : ProcessState}
    (clean : Clean gone processId process) (live : process.exiting = none) (live' : process'.exiting = none)
    (queue : ∀ entry ∈ process'.queue, (entry ∈ process.queue ∧
      (inert gone' processId process' entry = true → inert gone processId process entry = true)) ∨
      inert gone' processId process' entry = false)
    (links : ∀ link ∈ process'.links, link.2.isSome = true → link ∈ process.links ∧ (gone' link.1 = true → gone link.1 = true)) :
    Clean gone' processId process' := by
  obtain ⟨queueFacts, linkFacts⟩ := clean.live_facts live
  refine Clean.live live' (fun entry mem => ?_) (fun link mem some => ?_)
  · rcases queue entry mem with ⟨old, more⟩ | fresh
    · cases inside : inert gone' processId process' entry
      · rfl
      · exact absurd (more inside) (by simp [queueFacts entry old])
    · exact fresh
  · obtain ⟨old, more⟩ := links link mem some
    cases going : gone' link.1
    · rfl
    · exact absurd (more going) (by simp [linkFacts link old some])

/-- Whether a signal is inert reads only whether its sender is gone, and the
receiver's references, monitors, aliases and links. -/
private theorem inert_congr {gone gone' : PID → Bool} {processId : PID} {process process' : ProcessState}
    {entry : Entry} (source : gone' entry.source = gone entry.source)
    (refCounter : process'.refCounter = process.refCounter) (monitoring : process'.monitoring = process.monitoring)
    (aliases : process'.aliases = process.aliases) (links : process'.links = process.links) :
    inert gone' processId process' entry = inert gone processId process entry := by
  simp only [inert, source, refCounter, monitoring, aliases, links]

/-- An effect within frames that do not mention a record leaves it as it is. -/
private theorem Effect.InFrames.untouched {effect : Effect} {frames : List Frame} {state : State} {processId : PID}
    (framed : effect.InFrames frames state)
    (absent : ∀ bit, readsOf frames processId bit = false ∧ writesOf frames processId bit = false) :
    effect.record processId = id := by
  rcases framed processId with same | all | ⟨_, _, ⟨bit, _, used⟩, _⟩
  · exact same
  · have := all 0 (by decide); rw [(absent 0).2] at this; simp at this
  · rcases used with read | written
    · rw [(absent bit).1] at read; simp at read
    · rw [(absent bit).2] at written; simp at written

/-- Whether a record refers to a process in what normalizing reads of whether
it is gone, as `State.leavesOthers` checks. -/
private def Refers (process : ProcessState) (other : PID) : Bool :=
  match process.exiting with
  | some exiting =>
      Kernel.any process.queue (·.source == other) ||
        Kernel.contains exiting.links other || Kernel.any exiting.downs (·.2 == other)
  | none =>
      Kernel.any process.queue (fun entry => entry.source == other && match entry.signal with
          | .isAlive | .monitor _ | .unlinkAck _ => true
          | _ => false) ||
        Kernel.any process.links (fun link => link.1 == other && link.2.isSome)

/-- A clean record stays clean when the processes that become gone are none it refers to. -/
private theorem Clean.gone {gone gone' : PID → Bool} {processId : PID} {process : ProcessState}
    (clean : Clean gone processId process)
    (differ : ∀ other, gone' other ≠ gone other → Refers process other = false) :
    Clean gone' processId process := by
  cases exiting : process.exiting with
  | none =>
    obtain ⟨queue, links⟩ := clean.live_facts exiting
    refine Clean.live exiting (fun entry mem => ?_) (fun link mem some => ?_)
    · rw [← queue entry mem]
      obtain ⟨source, signal⟩ := entry
      by_cases same : gone' source = gone source
      · cases signal <;> simp [inert, same]
      · have := differ source same
        simp only [Refers, exiting, Bool.or_eq_false_iff, Kernel.any_eq, List.any_eq_false] at this
        have := this.1 _ mem
        cases signal <;> simp_all [inert]
    · rw [← links link mem some]
      by_cases same : gone' link.1 = gone link.1
      · exact same
      · have := differ link.1 same
        simp only [Refers, exiting, Bool.or_eq_false_iff, Kernel.any_eq, List.any_eq_false] at this
        have := this.2 _ mem
        simp_all
  | some exiting' =>
    obtain ⟨same, kept⟩ := clean
    refine ⟨?_, kept⟩
    have refers : ∀ other, Refers process other = true → gone' other = gone other := fun other refers => by
      by_cases equal : gone' other = gone other
      · exact equal
      · rw [differ other equal] at refers; simp at refers
    have queue : ∀ entry ∈ process.queue, gone' entry.source = gone entry.source := fun entry mem =>
      refers _ (by simp only [Refers, exiting, Kernel.any_eq, Kernel.contains_eq, Bool.or_eq_true, List.any_eq_true,
        beq_iff_eq]; exact .inl (.inl ⟨entry, mem, rfl⟩))
    have links : ∀ target ∈ exiting'.links, gone' target = gone target := fun target mem =>
      refers _ (by simp only [Refers, exiting, Kernel.any_eq, Kernel.contains_eq, Bool.or_eq_true, List.elem_eq_true_of_mem mem,
        true_or, or_true])
    have downs : ∀ down ∈ exiting'.downs, gone' down.2 = gone down.2 := fun down mem =>
      refers _ (by simp only [Refers, exiting, Kernel.any_eq, Kernel.contains_eq, Bool.or_eq_true, List.any_eq_true,
        beq_iff_eq]; exact .inr ⟨down, mem, rfl⟩)
    have congruent : normRecord gone' processId process = normRecord gone processId process := by
      unfold normRecord
      rw [exiting]
      simp only [Kernel.filter_eq]
      rw [List.filter_congr (l := process.queue) fun entry mem => by rw [queue entry mem],
        List.filter_congr (l := exiting'.links) fun target mem => by rw [links target mem],
        List.filter_congr (l := exiting'.downs) fun down mem => by rw [downs down mem]]
    rw [congruent, same]

/-- An effect that leaves every process alive or gone as it was. -/
private def Effect.KeepsAlive (effect : Effect) : Prop :=
  ∀ processId record, liveOf (effect.record processId record) = liveOf record

private theorem Effect.KeepsAlive.empty : ({} : Effect).KeepsAlive := fun _ _ => rfl

private theorem Effect.KeepsAlive.andThen {first second : Effect} (one : first.KeepsAlive) (two : second.KeepsAlive) :
    (first.andThen second).KeepsAlive := fun processId record => by
  rw [Effect.record_andThen]; exact (two _ _).trans (one _ _)

private theorem Effect.KeepsAlive.modify {processId : PID} {change : ProcessState → ProcessState}
    (live : ∀ process, (change process).exiting.isSome = process.exiting.isSome) :
    (Effect.modify processId change).KeepsAlive := fun other record => by
  rw [Effect.record_modify]
  split
  · cases record with
    | none => rfl
    | some process =>
      simp only [Option.map_some, liveOf]
      have := live process
      cases equal : process.exiting <;> cases equal' : (change process).exiting <;> simp_all
  · rfl

private theorem Effect.KeepsAlive.retime (change : List Timer → List Timer) : (Effect.retime change).KeepsAlive :=
  fun _ _ => rfl

private theorem Effect.KeepsAlive.gone {effect : Effect} (keeps : effect.KeepsAlive) (state : State) :
    (effect.apply state).gone = state.gone := by
  funext processId
  simp only [State.gone, State.alive, Effect.record_apply]
  have := keeps processId (state.record processId)
  cases found : state.record processId <;> cases found' : effect.record processId (state.record processId) <;>
    simp_all [liveOf]
  rename_i process process'
  cases equal : process.exiting <;> cases equal' : process'.exiting <;> simp_all

private theorem State.enqueueEffect_keepsAlive (state : State) (source target : PID) (signal : Signal) :
    (state.enqueueEffect source target signal).KeepsAlive := by
  unfold State.enqueueEffect State.fallbackEffect
  repeat' split
  all_goals first
    | exact Effect.KeepsAlive.empty
    | (refine Effect.KeepsAlive.modify ?_; intro process; rfl)

private theorem State.unparkEffect_keepsAlive (state : State) (processId : PID) :
    (state.unparkEffect processId).KeepsAlive := by
  unfold State.unparkEffect
  split
  · refine (Effect.KeepsAlive.modify ?_).andThen (State.enqueueEffect_keepsAlive _ _ _ _)
    intro process; rfl
  · exact Effect.KeepsAlive.empty

private theorem State.sendEffect_keepsAlive (state : State) (source target : PID) (signal : Signal) :
    (state.sendEffect source target signal).KeepsAlive := by
  unfold State.sendEffect
  repeat' split
  all_goals first
    | exact (State.unparkEffect_keepsAlive _ _).andThen (State.enqueueEffect_keepsAlive _ _ _ _)
    | exact State.enqueueEffect_keepsAlive _ _ _ _

/-- A record an effect leaves as it is stays clean, when the effect leaves every
process alive or gone as it was. -/
private theorem Clean.unchanged {state : State} (sorted : state.Sorted) (normalized : state.normalize = state)
    {effect : Effect} (keeps : effect.KeepsAlive) {processId : PID}
    (same : effect.record processId (state.record processId) = state.record processId) :
    ∀ process, (effect.apply state).record processId = some process →
      Clean (effect.apply state).gone processId process := by
  intro process found
  rw [Effect.record_apply, same] at found
  rw [keeps.gone]
  exact Clean.of_normalized sorted normalized found

/-- A record an effect appends a signal to that is not inert stays clean, when
the effect leaves every process alive or gone as it was. -/
private theorem Clean.appended {state : State} (sorted : state.Sorted) (normalized : state.normalize = state)
    {effect : Effect} (keeps : effect.KeepsAlive) {processId source : PID} {signal : Signal}
    (appended : effect.record processId (state.record processId) =
      (state.record processId).map (queueAt source signal))
    (live : ∀ process, state.record processId = some process → process.exiting = none)
    (fresh : ∀ process, state.record processId = some process →
      inert state.gone processId (queueAt source signal process) { source, signal } = false) :
    ∀ process, (effect.apply state).record processId = some process →
      Clean (effect.apply state).gone processId process := by
  intro process found
  rw [Effect.record_apply, appended] at found
  rw [keeps.gone]
  cases record : state.record processId with
  | none => rw [record] at found; simp at found
  | some original =>
    rw [record] at found; simp only [Option.map_some, Option.some.injEq] at found; subst found
    have clean := Clean.of_normalized sorted normalized record
    have exiting := live original record
    refine clean.preserve exiting exiting (fun entry mem => ?_) (fun link mem _ => ⟨mem, id⟩)
    simp only [queueAt, Kernel.append_eq, List.mem_append, List.mem_singleton] at mem
    rcases mem with old | rfl
    · exact .inl ⟨old, fun inside => by
        rw [inert_congr rfl rfl rfl rfl rfl] at inside; exact inside⟩
    · exact .inr (fresh original record)

private theorem Effect.apply_empty (state : State) : ({} : Effect).apply state = state := by
  cases state; rfl

/-- Every record of a state is clean, but those of some processes. -/
private def CleanOutside (state : State) (except : PID → Prop) : Prop :=
  ∀ processId, ¬ except processId → ∀ process, state.record processId = some process →
    Clean state.gone processId process

private theorem Effect.apply_andThen_record (first second : Effect) (state : State) (processId : PID) :
    ((first.andThen second).apply state).record processId = (second.apply (first.apply state)).record processId := by
  simp only [Effect.record_apply, Effect.record_andThen, Function.comp]

private theorem Effect.apply_andThen_gone (first second : Effect) (state : State) :
    ((first.andThen second).apply state).gone = (second.apply (first.apply state)).gone := by
  funext processId
  simp only [State.gone, State.alive, Effect.apply_andThen_record]

private theorem CleanOutside.andThen {first second : Effect} {state : State} {except : PID → Prop}
    (clean : CleanOutside (second.apply (first.apply state)) except) :
    CleanOutside ((first.andThen second).apply state) except := by
  intro processId outside process found
  rw [Effect.apply_andThen_record] at found
  rw [Effect.apply_andThen_gone]
  exact clean processId outside process found

/-- Changing one record, keeping every process alive or gone, keeps the others
clean, and that one when the change is clean. -/
private theorem CleanOutside.modify {state : State} {except : PID → Prop} {processId : PID}
    {change : ProcessState → ProcessState}
    (live : ∀ process, (change process).exiting.isSome = process.exiting.isSome)
    (clean : CleanOutside state except)
    (here : ¬ except processId → ∀ process, state.record processId = some process →
      Clean state.gone processId (change process)) :
    CleanOutside ((Effect.modify processId change).apply state) except := by
  intro other outside process found
  rw [(Effect.KeepsAlive.modify live).gone]
  rw [Effect.record_apply, Effect.record_modify] at found
  split at found
  · rename_i same; subst same
    cases record : state.record other with
    | none => rw [record] at found; simp at found
    | some original =>
      rw [record] at found; simp only [Option.map_some, Option.some.injEq] at found; subst found
      exact here outside original record
  · exact clean other outside process found

/-- Appending a signal that is not inert to a clean live record keeps it clean. -/
private theorem Clean.queued {gone : PID → Bool} {processId source : PID} {signal : Signal} {process : ProcessState}
    (clean : Clean gone processId process) (live : process.exiting = none)
    (fresh : inert gone processId (queueAt source signal process) { source, signal } = false) :
    Clean gone processId (queueAt source signal process) := by
  refine clean.preserve live live (fun entry mem => ?_) (fun link mem _ => ⟨mem, id⟩)
  have mem' : entry ∈ process.queue ∨ entry = { source, signal } := by
    simpa [queueAt, Kernel.append_eq] using mem
  rcases mem' with old | rfl
  · exact .inl ⟨old, fun inside => by rw [inert_congr rfl rfl rfl rfl rfl] at inside; exact inside⟩
  · exact .inr fresh

/-- Queueing a signal keeps a state clean, when the signal is not inert at a
live target, and, when the target is gone, the sender falling back is live and
the `DOWN` it queues for a monitor is not inert. -/
private theorem CleanOutside.enqueue {state : State} {except : PID → Prop} {source target : PID} {signal : Signal}
    (clean : CleanOutside state except)
    (fresh : ∀ process, state.record target = some process → process.exiting = none →
      inert state.gone target (queueAt source signal process) { source, signal } = false)
    (fallback : state.alive target = false → (signal matches .link | .monitor _ | .isAlive | .unlink _) →
      ¬ except source ∧ ∀ process, state.record source = some process → process.exiting = none)
    (notUnlink : ∀ id, signal ≠ .unlink id)
    (down : state.alive target = false → ∀ reference, signal = .monitor reference →
      ∀ process, state.record source = some process →
        inert state.gone source (queueAt target (.down reference (.atom "noproc")) process)
          { source := target, signal := .down reference (.atom "noproc") } = false) :
    CleanOutside ((state.enqueueEffect source target signal).apply state) except := by
  have viaFallback : state.alive target = false →
      CleanOutside ((state.fallbackEffect source target signal).apply state) except := by
    intro dead
    cases signal with
    | link =>
      obtain ⟨outside, live⟩ := fallback dead rfl
      refine CleanOutside.modify (fun _ => rfl) clean fun _ process found =>
        (clean source outside process found).queued (live process found) ?_
      simp [inert]
    | monitor reference =>
      obtain ⟨outside, live⟩ := fallback dead rfl
      exact CleanOutside.modify (fun _ => rfl) clean fun _ process found =>
        (clean source outside process found).queued (live process found) (down dead reference rfl process found)
    | isAlive =>
      obtain ⟨outside, live⟩ := fallback dead rfl
      refine CleanOutside.modify (fun _ => rfl) clean fun _ process found =>
        (clean source outside process found).queued (live process found) ?_
      simp [inert]
    | unlink id => exact absurd rfl (notUnlink id)
    | _ => simpa [State.fallbackEffect, Effect.apply_empty] using clean
  unfold State.enqueueEffect
  cases found : state.record target with
  | none => exact viaFallback (by simp [State.alive, found])
  | some process =>
    simp only
    split
    · rename_i live
      refine CleanOutside.modify (fun _ => rfl) clean fun outside _ found' => ?_
      rw [found] at found'; cases found'
      have exiting : process.exiting = none := by simpa using live
      exact (clean target outside process found).queued exiting (fresh process found exiting)
    · rename_i exiting
      exact viaFallback (by
        simp only [State.alive, found]; cases equal : process.exiting <;> simp_all)

/-- `State.inertEntry` is `inert` with the process's own record. -/
private theorem State.inertEntry_eq (state : State) (processId : PID) (entry : Entry) :
    state.inertEntry processId entry = inert state.gone processId (state.process processId) entry := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> rfl

/-- Sending a parked monitor signal keeps a state clean, from a live process
that still monitors it. -/
private theorem CleanOutside.unpark {state : State} {except : PID → Prop} {processId : PID}
    (clean : CleanOutside state except) (outside : ¬ except processId) (alive : state.alive processId = true)
    (monitored : state.parkedMonitored processId = true) :
    CleanOutside ((state.unparkEffect processId).apply state) except := by
  have found : ∃ process, state.record processId = some process ∧ process.exiting = none := by
    simp only [State.alive] at alive
    cases record : state.record processId with
    | none => rw [record] at alive; simp at alive
    | some process => rw [record] at alive; exact ⟨process, rfl, by simpa using alive⟩
  obtain ⟨process, record, live⟩ := found
  have same : state.process processId = process := by simp [State.process, record]
  unfold State.unparkEffect
  cases parked : (state.process processId).parked with
  | none => simpa [Effect.apply_empty] using clean
  | some found' =>
    obtain ⟨target, reference⟩ := found'
    simp only
    let unparked := fun process : ProcessState => { process with parked := none }
    have cleaned := CleanOutside.modify (change := unparked) (fun _ => rfl) clean fun _ process' found' =>
      (clean processId outside process' found').preserve (by rw [record] at found'; cases found'; exact live)
        (by rw [record] at found'; cases found'; exact live) (fun entry mem => .inl ⟨mem, fun inside => by
          rw [inert_congr rfl rfl rfl rfl rfl] at inside; exact inside⟩) (fun link mem _ => ⟨mem, id⟩)
    refine CleanOutside.andThen ?_
    have recordOf : ((Effect.modify processId unparked).apply state).record processId = some (unparked process) := by
      rw [Effect.record_apply, Effect.record_modify, record]; simp
    have goneOf := (Effect.KeepsAlive.modify (change := unparked) (processId := processId) fun _ => rfl).gone state
    have aliveOf : ∀ pid, ((Effect.modify processId unparked).apply state).alive pid = state.alive pid := fun pid => by
      have := congrFun goneOf pid; simpa [State.gone] using this
    rw [State.enqueueEffect_congr (state := (Effect.modify processId unparked).apply state) _
      (by rw [aliveOf]; exact State.alive_modify _ _ _ _ fun _ => rfl)]
    refine CleanOutside.enqueue cleaned (fun process' _ _ => ?_) (fun _ _ => ⟨outside, fun process' found' => ?_⟩)
      (fun id => by simp) (fun _ reference' equal process' found' => ?_)
    · simp [inert, State.gone, aliveOf, alive]
    · rw [recordOf] at found'; cases found'; exact live
    · simp only [Signal.monitor.injEq] at equal; subst equal
      rw [recordOf] at found'; cases found'
      have parked' : process.parked = some (target, reference) := same ▸ parked
      simp only [State.parkedMonitored, same, parked', Kernel.any_eq, List.any_eq_true, beq_iff_eq] at monitored
      obtain ⟨⟨reference', watched⟩, mem, equal'⟩ := monitored
      simp only at equal'; subst equal'
      simp only [inert, queueAt, unparked, Kernel.any_eq, Bool.and_eq_false_iff, Bool.not_eq_false',
        List.any_eq_true, beq_iff_eq]
      exact .inr ⟨_, mem, rfl⟩

private theorem State.alive_eq_of_gone {state other : State} (gone : state.gone = other.gone) (processId : PID) :
    state.alive processId = other.alive processId := by
  have := congrFun gone processId
  simp only [State.gone] at this
  cases equal : state.alive processId <;> cases equal' : other.alive processId <;> simp_all

/-- An effect that changes none of what inertness reads of any record, nor whether it ended. -/
private def Effect.KeepsInert (effect : Effect) : Prop :=
  ∀ processId record process', effect.record processId record = some process' → ∃ process, record = some process ∧
    process'.refCounter = process.refCounter ∧ process'.monitoring = process.monitoring ∧
    process'.aliases = process.aliases ∧ process'.links = process.links ∧ process.exiting = process'.exiting

private theorem Effect.KeepsInert.empty : ({} : Effect).KeepsInert := fun _ record process' found =>
  ⟨process', found, rfl, rfl, rfl, rfl, rfl⟩

private theorem Effect.KeepsInert.modify {processId : PID} {change : ProcessState → ProcessState}
    (keeps : ∀ process, (change process).refCounter = process.refCounter ∧
      (change process).monitoring = process.monitoring ∧ (change process).aliases = process.aliases ∧
      (change process).links = process.links ∧ process.exiting = (change process).exiting) :
    (Effect.modify processId change).KeepsInert := fun other record process' found => by
  rw [Effect.record_modify] at found
  split at found
  · cases record with
    | none => simp at found
    | some process =>
      simp only [Option.map_some, Option.some.injEq] at found; subst found
      exact ⟨process, rfl, keeps process⟩
  · exact ⟨process', found, rfl, rfl, rfl, rfl, rfl⟩

private theorem Effect.KeepsInert.andThen {first second : Effect} (one : first.KeepsInert) (two : second.KeepsInert) :
    (first.andThen second).KeepsInert := fun processId record process'' found => by
  rw [Effect.record_andThen] at found
  obtain ⟨process', middle, a, b, c, d, e⟩ := two processId _ process'' found
  obtain ⟨process, start, a', b', c', d', e'⟩ := one processId record process' middle
  exact ⟨process, start, a.trans a', b.trans b', c.trans c', d.trans d', e'.trans e⟩

private theorem State.enqueueEffect_keepsInert (state : State) (source target : PID) (signal : Signal)
    (notUnlink : ∀ id, signal ≠ .unlink id) : (state.enqueueEffect source target signal).KeepsInert := by
  unfold State.enqueueEffect State.fallbackEffect
  repeat' split
  all_goals first
    | exact Effect.KeepsInert.empty
    | exact absurd rfl (notUnlink _)
    | (refine Effect.KeepsInert.modify ?_; intro process; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

private theorem State.unparkEffect_keepsInert (state : State) (processId : PID) :
    (state.unparkEffect processId).KeepsInert := by
  unfold State.unparkEffect
  split
  · refine (Effect.KeepsInert.modify ?_).andThen (State.enqueueEffect_keepsInert _ _ _ _ fun _ => by simp)
    intro process; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Effect.KeepsInert.empty

/-- Sending a signal from a live process that still monitors its parked monitor
signal keeps a state clean, when the signal is not inert at a live target, and
is not a link removal or a monitor signal, which only unparking sends. -/
private theorem CleanOutside.send {state : State} {except : PID → Prop} {source target : PID} {signal : Signal}
    (clean : CleanOutside state except) (outside : ¬ except source) (alive : state.alive source = true)
    (monitored : state.parkedMonitored source = true)
    (fresh : ∀ process, state.record target = some process → process.exiting = none →
      inert state.gone target (queueAt source signal process) { source, signal } = false)
    (notUnlink : ∀ id, signal ≠ .unlink id) (notMonitor : ∀ reference, signal ≠ .monitor reference) :
    CleanOutside ((state.sendEffect source target signal).apply state) except := by
  have live : ∀ (state' : State), state'.alive source = true → ∀ process, state'.record source = some process →
      process.exiting = none := fun state' alive' process found => by
    simp only [State.alive, found] at alive'; simpa using alive'
  -- Queueing the signal at a state reached from this one by changes that keep
  -- every process alive or gone and the fields inertness reads.
  have queue : ∀ (state' : State), CleanOutside state' except → state'.gone = state.gone →
      (∀ process', state'.record target = some process' → ∃ process, state.record target = some process ∧
        process'.refCounter = process.refCounter ∧ process'.monitoring = process.monitoring ∧
        process'.aliases = process.aliases ∧ process'.links = process.links ∧ process.exiting = process'.exiting) →
      CleanOutside ((state'.enqueueEffect source target signal).apply state') except := by
    intro state' clean' gone' fields
    refine CleanOutside.enqueue clean' (fun process' found' exiting' => ?_) (fun _ kind => ⟨outside, ?_⟩) notUnlink
      (fun _ reference equal => absurd equal (notMonitor reference))
    · obtain ⟨process, found, refCounter, monitoring, aliases, links, exiting⟩ := fields process' found'
      rw [gone', inert_congr (process' := queueAt source signal process') (process := queueAt source signal process)
        rfl refCounter monitoring aliases links]
      exact fresh process found (exiting.trans exiting')
    · have aliveOf : state'.alive source = true := by
        have := congrFun gone' source; simp only [State.gone] at this
        cases equal : state'.alive source <;> simp_all
      exact live state' aliveOf
  unfold State.sendEffect
  split
  · rename_i parkedTarget reference parked
    split
    · refine CleanOutside.andThen ?_
      have goneOf := (State.unparkEffect_keepsAlive state source).gone state
      have unparked := CleanOutside.unpark clean outside alive monitored
      rw [State.enqueueEffect_congr (state := (state.unparkEffect source).apply state) _
        (by rw [State.alive_unpark, State.alive_eq_of_gone goneOf])]
      exact queue _ unparked goneOf fun process' found' => by
        rw [Effect.record_apply] at found'
        exact State.unparkEffect_keepsInert state source target _ process' found'
    · exact queue state clean rfl fun process found => ⟨process, found, rfl, rfl, rfl, rfl, rfl⟩
  · exact queue state clean rfl fun process found => ⟨process, found, rfl, rfl, rfl, rfl, rfl⟩

/-- A change keeping a live record's queue and what inertness reads keeps it clean. -/
private theorem Clean.neutral {gone : PID → Bool} {processId : PID} {process process' : ProcessState}
    (clean : Clean gone processId process) (live : process.exiting = none) (live' : process'.exiting = none)
    (queue : process'.queue = process.queue) (refCounter : process'.refCounter = process.refCounter)
    (monitoring : process'.monitoring = process.monitoring) (aliases : process'.aliases = process.aliases)
    (links : process'.links = process.links) : Clean gone processId process' :=
  clean.preserve live live' (fun entry mem => .inl ⟨queue ▸ mem, fun inside => by
    rwa [inert_congr rfl refCounter monitoring aliases links] at inside⟩)
    (fun link mem _ => ⟨links ▸ mem, id⟩)

/-- Removing the oldest signal of a clean live record keeps it clean. -/
private theorem Clean.pop {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (clean : Clean gone processId process) (live : process.exiting = none) :
    Clean gone processId { process with queue := process.queue.drop 1 } :=
  clean.preserve live live (fun entry mem => .inl ⟨List.mem_of_mem_drop mem, id⟩) (fun link mem _ => ⟨mem, id⟩)

/-- A change that adds monitors and aliases, keeping the queue and the rest of
what inertness reads, keeps a live record clean. -/
private theorem Clean.grow {gone : PID → Bool} {processId : PID} {process process' : ProcessState}
    (clean : Clean gone processId process) (live : process.exiting = none) (live' : process'.exiting = none)
    (queue : process'.queue = process.queue) (refCounter : process'.refCounter = process.refCounter)
    (monitoring : ∀ entry ∈ process.monitoring, entry ∈ process'.monitoring)
    (aliases : ∀ alias ∈ process.aliases, alias ∈ process'.aliases) (links : process'.links = process.links) :
    Clean gone processId process' := by
  refine clean.preserve live live' (fun entry mem => .inl ⟨queue ▸ mem, fun inside => ?_⟩)
    (fun link mem _ => ⟨links ▸ mem, id⟩)
  have anyMono : ∀ {test : List Nat × PID → Bool},
      Kernel.any process'.monitoring test = false → Kernel.any process.monitoring test = false := by
    intro test none
    simp only [Kernel.any_eq, List.any_eq_false] at none ⊢
    exact fun entry mem => none entry (monitoring entry mem)
  have containsMono : ∀ {alias : List Nat},
      Kernel.contains process'.aliases alias = false → Kernel.contains process.aliases alias = false := by
    intro alias none
    cases inside : Kernel.contains process.aliases alias
    · rfl
    · simp only [Kernel.contains_eq, List.contains_iff_mem] at inside none
      exact absurd (aliases _ inside) (by simpa using none)
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | down reference reason =>
    simp only [inert, refCounter, Bool.and_eq_true, Bool.not_eq_true'] at inside ⊢
    exact ⟨inside.1, anyMono inside.2⟩
  | aliasMessage alias message =>
    simp only [inert, refCounter, Bool.and_eq_true, Bool.not_eq_true'] at inside ⊢
    exact ⟨⟨inside.1.1, containsMono inside.1.2⟩, anyMono inside.2⟩
  | _ => simpa only [inert, links] using inside

private theorem reference_eq_of_allocated {reference owner : List Nat} {count : Nat}
    (owned : reference.dropLast = owner) (last : reference.getLast? = some count) :
    reference = owner ++ [count] := by
  obtain ⟨prefix', rfl⟩ := List.getLast?_eq_some_iff.mp last
  rw [List.dropLast_concat] at owned; rw [owned]

/-- Allocating a reference keeps a live record clean when no queued signal carries it. -/
private theorem Clean.allocate {gone : PID → Bool} {processId : PID} {process : ProcessState}
    (clean : Clean gone processId process) (live : process.exiting = none)
    (fresh : ∀ entry ∈ process.queue, entry.carries (Kernel.append processId [process.refCounter + 1]) = false) :
    Clean gone processId { process with refCounter := process.refCounter + 1 } := by
  refine clean.preserve live live (fun entry mem => .inl ⟨mem, fun inside => ?_⟩) (fun link mem _ => ⟨mem, id⟩)
  have carries := fresh entry mem
  obtain ⟨source, signal⟩ := entry
  have allocated : ∀ (reference : List Nat), reference ≠ Kernel.append processId [process.refCounter + 1] →
      (reference.dropLast == processId && match reference.getLast? with
        | some count => 1 ≤ count && count ≤ process.refCounter + 1
        | none => false) = true →
      (reference.dropLast == processId && match reference.getLast? with
        | some count => 1 ≤ count && count ≤ process.refCounter
        | none => false) = true := by
    intro reference differ owned
    simp only [Bool.and_eq_true, beq_iff_eq] at owned ⊢
    refine ⟨owned.1, ?_⟩
    cases last : reference.getLast? with
    | none => rw [last] at owned; simp at owned
    | some count =>
      rw [last] at owned; simp only [Bool.and_eq_true, decide_eq_true_eq] at owned ⊢
      refine ⟨owned.2.1, ?_⟩
      rcases Nat.lt_or_ge count (process.refCounter + 1) with lower | upper
      · omega
      · exact absurd (by rw [reference_eq_of_allocated owned.1 last, Kernel.append_eq]; congr; omega) differ
  cases signal with
  | down reference reason =>
    simp only [Entry.carries, beq_eq_false_iff_ne] at carries
    simp only [inert] at inside ⊢
    obtain ⟨own, rest⟩ := Bool.and_eq_true_iff.mp inside
    exact Bool.and_eq_true_iff.mpr ⟨allocated reference carries own, rest⟩
  | aliasMessage alias message =>
    simp only [Entry.carries, beq_eq_false_iff_ne] at carries
    simp only [inert] at inside ⊢
    obtain ⟨⟨own, held⟩, rest⟩ := And.imp_left Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp inside)
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨allocated alias carries own, held⟩, rest⟩
  | _ => simpa only [inert] using inside

/-- Removing a monitor and alias keeps a live record clean when no queued signal carries its reference. -/
private theorem Clean.demonitor {gone : PID → Bool} {processId : PID} {process process' : ProcessState}
    {reference : List Nat} (clean : Clean gone processId process) (live : process.exiting = none)
    (live' : process'.exiting = none) (queue : process'.queue = process.queue)
    (refCounter : process'.refCounter = process.refCounter) (links : process'.links = process.links)
    (monitoring : process'.monitoring = Kernel.filter (·.1 != reference) process.monitoring)
    (aliases : process'.aliases = Kernel.erase process.aliases reference)
    (fresh : ∀ entry ∈ process.queue, entry.carries reference = false) :
    Clean gone processId process' := by
  refine clean.preserve live live' (fun entry mem => .inl ⟨queue ▸ mem, fun inside => ?_⟩)
    (fun link mem _ => ⟨links ▸ mem, id⟩)
  have carries := fresh entry (queue ▸ mem)
  obtain ⟨source, signal⟩ := entry
  have anyKept : ∀ (other : List Nat), other ≠ reference →
      Kernel.any process'.monitoring (·.1 == other) = Kernel.any process.monitoring (·.1 == other) := by
    intro other differ
    rw [monitoring]
    simp only [Kernel.any_eq, Kernel.filter_eq, List.any_filter]
    congr 1; funext entry
    by_cases same : entry.1 = other
    · subst same; simp [differ]
    · simp [same]
  have containsKept : ∀ (other : List Nat), other ≠ reference →
      Kernel.contains process'.aliases other = Kernel.contains process.aliases other := by
    intro other differ
    rw [aliases]
    simp only [Kernel.contains_eq, Kernel.erase_eq]
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_erase_of_ne differ]
  cases signal with
  | down reference' reason =>
    simp only [Entry.carries, beq_eq_false_iff_ne] at carries
    simp only [inert, refCounter] at inside ⊢
    rwa [anyKept reference' carries] at inside
  | aliasMessage alias message =>
    simp only [Entry.carries, beq_eq_false_iff_ne] at carries
    simp only [inert, refCounter] at inside ⊢
    rwa [anyKept alias carries, containsKept alias carries] at inside
  | _ => simpa only [inert, links] using inside

private theorem CleanOutside.retime {state : State} {except : PID → Prop} (change : List Timer → List Timer)
    (clean : CleanOutside state except) : CleanOutside ((Effect.retime change).apply state) except := by
  intro processId outside process found
  rw [(Effect.KeepsAlive.retime change).gone]
  rw [Effect.record_apply, Effect.record_retime] at found
  exact clean processId outside process found

/-- Changing a record by an effect or by `State.modify` gives the same records. -/
private theorem Effect.apply_modify_record (state : State) (processId other : PID) (change : ProcessState → ProcessState) :
    ((Effect.modify processId change).apply state).record other = (state.modify processId change).record other :=
  ((Realizes.modify state processId change).records other).symm

private theorem Effect.apply_modify_alive (state : State) (processId other : PID) (change : ProcessState → ProcessState) :
    ((Effect.modify processId change).apply state).alive other = (state.modify processId change).alive other := by
  simp only [State.alive, Effect.apply_modify_record]

private theorem Effect.apply_modify_process (state : State) (processId other : PID) (change : ProcessState → ProcessState) :
    ((Effect.modify processId change).apply state).process other = (state.modify processId change).process other := by
  simp only [State.process, Effect.apply_modify_record]

private theorem Effect.apply_modify_parkedMonitored (state : State) (processId other : PID)
    (change : ProcessState → ProcessState) :
    ((Effect.modify processId change).apply state).parkedMonitored other =
      (state.modify processId change).parkedMonitored other := by
  simp only [State.parkedMonitored, Effect.apply_modify_process]

private theorem State.record_modify_of_records {state other : State} {processId target : PID}
    {change : ProcessState → ProcessState}
    (records : ∀ processId, other.record processId = state.record processId) :
    (other.modify processId change).record target = (state.modify processId change).record target := by
  unfold State.modify
  rw [records]
  split
  · simp only [State.record_set, records]
  · exact records target

/-- Unparking decides alike at states with the same records. -/
private theorem State.unparkEffect_records {state other : State} (processId : PID)
    (records : ∀ processId, other.record processId = state.record processId) :
    other.unparkEffect processId = state.unparkEffect processId := by
  have process : ∀ processId, other.process processId = state.process processId := fun processId => by
    simp [State.process, records]
  refine State.unparkEffect_congr (by rw [process]) fun target _ _ => ?_
  simp only [State.alive]
  rw [State.record_modify_of_records records]

private theorem CleanOutside.retimeIf {state : State} {except : PID → Prop} (condition : Prop) [Decidable condition]
    (change : List Timer → List Timer) (clean : CleanOutside state except) :
    CleanOutside ((if condition then Effect.retime change else {}).apply state) except := by
  split
  · exact CleanOutside.retime change clean
  · simpa [Effect.apply_empty] using clean

private theorem State.parkedMonitored_modify (state : State) (changed processId : PID)
    (change : ProcessState → ProcessState) (parked : ∀ process, (change process).parked = process.parked)
    (monitoring : ∀ process, (change process).monitoring = process.monitoring) :
    (state.modify changed change).parkedMonitored processId = state.parkedMonitored processId := by
  have parked' := State.process_modify_keeps (state := state) (processId := changed) (other := processId)
    (get := (·.parked)) parked
  have monitoring' := State.process_modify_keeps (state := state) (processId := changed) (other := processId)
    (get := (·.monitoring)) monitoring
  simp only [State.parkedMonitored]
  rw [parked', monitoring']

private theorem Effect.KeepsAlive.live_of_record {effect : Effect} (keeps : effect.KeepsAlive) {state : State}
    {processId : PID} {process : ProcessState} (found : (effect.apply state).record processId = some process)
    (alive : state.alive processId = true) : process.exiting = none := by
  have := keeps processId (state.record processId)
  rw [← Effect.record_apply, found] at this
  simp only [State.alive] at alive
  cases record : state.record processId with
  | none => rw [record] at alive; simp at alive
  | some original =>
    rw [record] at alive this
    simp only [liveOf] at this alive
    rw [alive] at this; simpa using this

/-- Normalizing after a confined own step that does not end the process changes no record. -/
private theorem Task.ownEffect_clean {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {task : Task α}
    (sorted : state.Sorted) (normalized : state.normalize = state)
    (confined : Config.confined (.running state tasks finished false) (.own processId) = true)
    (lookup : Kernel.lookup processId tasks = some task)
    (continues : ∀ value, task.computation ≠ .ok value) (raises : ∀ exception, task.computation ≠ .error exception) :
    CleanOutside ((task.ownEffect state processId).apply state) (fun _ => False) := by
  have clean : CleanOutside state (fun _ => False) := fun _ _ _ found => Clean.of_normalized sorted normalized found
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simpa [Task.ownEffect, Effect.apply_empty] using clean
  | none =>
  simp only [Config.confined, lookup, Bool.and_eq_true] at confined
  obtain ⟨⟨alive, monitored⟩, confined⟩ := confined
  have record : ∃ process, state.record processId = some process ∧ process.exiting = none := by
    simp only [State.alive] at alive
    cases found : state.record processId with
    | none => rw [found] at alive; simp at alive
    | some process => rw [found] at alive; exact ⟨process, rfl, by simpa using alive⟩
  obtain ⟨process, found, live⟩ := record
  have same : state.process processId = process := by simp [State.process, found]
  have notGone : state.gone processId = false := by simp [State.gone, alive]
  cases computation with
  | ok value => exact absurd rfl (continues value)
  | error exception => exact absurd rfl (raises exception)
  | get | set | schedule => simp at confined
  | send destination message =>
    exact CleanOutside.send clean (by simp) alive monitored (fun _ _ _ => by simp [inert]) (by simp) (by simp)
  | receive timeout select next =>
    simp only at confined
    simp only [Task.ownEffect]
    rw [show selectMessage (select (state.view processId)) (state.process processId).mailbox = none by simpa using confined]
    simpa [Effect.apply_empty] using clean
  | request query next =>
    cases query with
    | demonitor reference flush =>
      simp only [Kernel.any_eq, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true] at confined
      simp only [Task.ownEffect, State.requestEffect]
      refine CleanOutside.modify (fun _ => rfl) clean fun _ process' found' => ?_
      rw [found] at found'; cases found'
      exact (clean processId (by simp) process found).demonitor (reference := reference) live live rfl rfl rfl rfl rfl
        fun entry mem => by have := confined entry (same ▸ mem); simpa using this
    | cancelTimer reference =>
      simp only [Task.ownEffect, State.requestEffect]
      split
      · refine CleanOutside.andThen (CleanOutside.modify (fun _ => rfl) (CleanOutside.retime _ clean)
          fun _ process' found' => ?_)
        rw [Effect.record_apply, Effect.record_retime, found] at found'; cases found'
        rw [(Effect.KeepsAlive.retime _).gone]
        exact (clean processId (by simp) process found).neutral live live rfl rfl rfl rfl rfl
      · simpa [Effect.apply_empty] using clean
    | alive target =>
      simp only [Task.ownEffect, State.requestEffect]
      split
      · simpa [Effect.apply_empty] using clean
      · split
        · exact CleanOutside.send clean (by simp) alive monitored (fun _ _ _ => by simp [inert, notGone])
            (by simp) (by simp)
        · refine CleanOutside.enqueue clean (fun _ _ _ => by simp [inert]) (fun dead => ?_) (by simp)
            (fun _ _ equal => by simp at equal)
          rw [alive] at dead; simp at dead
    | sendAlias alias message =>
      simp only [Task.ownEffect, State.requestEffect]
      refine CleanOutside.send clean (by simp) alive monitored (fun process' found' live' => ?_) (by simp) (by simp)
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at confined
      have alive' : state.alive alias.dropLast = true := by simp [State.alive, found', live']
      rcases confined with dead | notInert
      · rw [alive'] at dead; simp at dead
      · rw [State.inertEntry_eq] at notInert
        have : state.process alias.dropLast = process' := by simp [State.process, found']
        rw [this] at notInert
        rwa [inert_congr (process' := queueAt _ _ process') (process := process') rfl rfl rfl rfl rfl]
    | monitor target alias =>
      simp only [Kernel.any_eq, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true] at confined
      let allocate := fun process : ProcessState => { process with refCounter := process.refCounter + 1 }
      have allocated : CleanOutside ((allocateEffect processId).apply state) (fun _ => False) :=
        CleanOutside.modify (change := allocate) (fun _ => rfl) clean fun _ process' found' => by
          rw [found] at found'; cases found'
          exact (clean processId (by simp) process found).allocate live fun entry mem => by
            have := confined entry (same ▸ mem); simpa [same] using this
      simp only [Task.ownEffect, State.requestEffect, State.allocate]
      refine CleanOutside.andThen ?_
      split
      · simpa [Effect.apply_empty] using allocated
      · refine CleanOutside.andThen ?_
        have records := Effect.apply_modify_record state processId (change := allocate)
        rw [← State.unparkEffect_records processId records]
        have aliveAllocated : ((allocateEffect processId).apply state).alive processId = true := by
          unfold allocateEffect
          rw [Effect.apply_modify_alive]
          exact (State.alive_modify _ _ _ allocate fun _ => rfl).trans alive
        have monitoredAllocated : ((allocateEffect processId).apply state).parkedMonitored processId = true := by
          unfold allocateEffect
          rw [Effect.apply_modify_parkedMonitored]
          refine (State.parkedMonitored_modify state processId processId _ ?_ ?_).trans monitored <;>
            intro process <;> rfl
        have unparked := CleanOutside.unpark allocated (by simp) aliveAllocated monitoredAllocated
        refine CleanOutside.modify (fun _ => rfl) unparked fun _ process' found' => ?_
        have live' : process'.exiting = none :=
          Effect.KeepsAlive.live_of_record (State.unparkEffect_keepsAlive _ _) found' (by
            first
              | exact aliveAllocated
              | (rw [Effect.apply_modify_alive]; exact (State.alive_modify _ _ _ _ fun _ => rfl).trans alive))
        refine (unparked processId (by simp) process' found').grow live' live' rfl rfl
          (fun entry mem => by simp [Kernel.append_eq, mem]) (fun alias' mem => ?_) rfl
        split <;> simp [Kernel.append_eq, mem]
    | startTimer destination message duration =>
      simp only [Kernel.any_eq, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true] at confined
      let allocate := fun process : ProcessState => { process with refCounter := process.refCounter + 1 }
      have allocated : CleanOutside ((allocateEffect processId).apply state) (fun _ => False) :=
        CleanOutside.modify (change := allocate) (fun _ => rfl) clean fun _ process' found' => by
          rw [found] at found'; cases found'
          exact (clean processId (by simp) process found).allocate live fun entry mem => by
            have := confined entry (same ▸ mem); simpa [same] using this
      simp only [Task.ownEffect, State.requestEffect, State.allocate]
      refine CleanOutside.andThen ?_
      exact CleanOutside.retimeIf _ _ allocated
    | _ => simp at confined

/-- A confined own step of a live process is within its frames. -/
private theorem Effect.InFrames.own {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {processId : PID} {task : Task α} {frames : List Frame} {timers : Bool}
    (alive : state.alive processId = true) (lookup : Kernel.lookup processId tasks = some task)
    (confined : Config.confined (.running state tasks finished false) (.own processId) = true)
    (found : task.ownFrames state processId = some (frames, timers)) :
    (task.ownEffect state processId).InFrames frames state := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp only [Task.ownEffect]; exact Effect.InFrames.empty _ _
  | none =>
    simp only [Config.confined, lookup] at confined
    cases computation with
    | ok =>
      simp only [Task.ownEffect, Task.ownFrames, Option.some.injEq] at found ⊢
      have := congrArg Prod.fst found; simp only at this; rw [← this]
      exact Effect.InFrames.terminateStep state processId _ alive
    | error exception =>
      cases exception with
      | exhausted => simp at confined
      | _ =>
        simp only [Task.ownEffect, Task.ownFrames, Option.some.injEq] at found ⊢
        have := congrArg Prod.fst found; simp only at this; rw [← this]
        exact Effect.InFrames.terminateStep state processId _ alive
    | get | set => simp at confined
    | schedule => simp at confined
    | send destination message =>
      simp only [Task.ownEffect, Task.ownFrames, Option.some.injEq, Prod.mk.injEq] at found ⊢
      rw [← found.1]
      exact Effect.InFrames.send state processId destination _
    | receive timeout select =>
      simp only [Task.ownEffect, Task.ownFrames] at found ⊢
      split at found
      · rename_i selected
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        rw [← found.1]
        simp only [selected]
        exact Effect.InFrames.receiveStep state processId _ _ (by decide) (by decide)
      · rename_i none
        simp only [none]
        exact Effect.InFrames.empty _ _
    | request query =>
      cases query with
      | demonitor reference flush =>
        simp only [Task.ownEffect, State.requestEffect, Task.ownFrames, State.requestFrames,
          Option.some.injEq, Prod.mk.injEq] at found ⊢
        rw [← found.1]
        exact Effect.InFrames.demonitorStep state processId reference
      | monitor target alias =>
        simp only [Task.ownEffect, Task.ownFrames, State.requestFrames] at found ⊢
        by_cases self : target = processId
        · subst self
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
          rw [← found.1]
          have first : (allocateEffect target).InFrames [(target, Field.refCounter, Field.refCounter)] state :=
            Effect.InFrames.single (fun _ => by framed_update) ⟨4, by decide, .inl (by decide)⟩ (by decide)
          refine first.of_record fun other => ?_
          simp only [State.requestEffect, ↓reduceIte, Effect.record_andThen]; rfl
        · have : (target == processId) = false := by simpa using self
          simp only [this, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
          rw [← found.1]
          exact Effect.InFrames.monitorStep state processId target alias self
      | startTimer destination message duration =>
        simp only [Task.ownEffect, State.requestEffect, Task.ownFrames, State.requestFrames,
          Option.some.injEq, Prod.mk.injEq] at found ⊢
        rw [← found.1]
        exact Effect.InFrames.startTimerStep state processId destination _ fun _ => by split <;> rfl
      | cancelTimer reference =>
        simp only [Task.ownEffect, State.requestEffect, Task.ownFrames, State.requestFrames,
          Option.some.injEq, Prod.mk.injEq] at found ⊢
        rw [← found.1]
        split
        · exact Effect.InFrames.cancelTimerStep state processId _
        · exact Effect.InFrames.empty _ _
      | alive target =>
        simp only [Task.ownEffect, State.requestEffect, Task.ownFrames, State.requestFrames] at found ⊢
        by_cases self : target = processId
        · simp only [self, ↓reduceIte]; exact Effect.InFrames.empty _ _
        · have : (target == processId) = false := by simpa using self
          simp only [this, self, Bool.false_eq_true, ↓reduceIte] at found ⊢
          split at found
          · rename_i targetAlive
            simp only [targetAlive, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found ⊢
            rw [← found.1]
            exact Effect.InFrames.send state processId target _
          · rename_i targetDead
            simp only [targetDead, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found ⊢
            rw [← found.1]
            exact Effect.InFrames.flushStep state processId target alive
      | sendAlias alias message =>
        simp only [Task.ownEffect, State.requestEffect, Task.ownFrames, State.requestFrames,
          Option.some.injEq, Prod.mk.injEq] at found ⊢
        rw [← found.1]
        exact Effect.InFrames.send state processId _ _
      | _ => simp at confined

end Lynx.Concurrent
