module

public import Lynx.Concurrent.Diamond
import all Lynx.Concurrent.Diamond

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

private theorem Effect.timers_apply (effect : Effect) (state : State) :
    (effect.apply state).timers = (effect.timers.getD id) state.timers := by
  simp only [Effect.apply]
  generalize (effect.records.map (·.1)) = processes
  have : ∀ (start : State), (processes.foldl (fun changed other =>
      changed.put other (effect.record other (state.record other))) start).timers = start.timers := by
    induction processes with
    | nil => intro; rfl
    | cons head rest ih =>
      intro start
      simp only [List.foldl_cons]
      rw [ih]
      cases effect.record head (state.record head) <;> rfl
  rw [this]

private theorem Effect.elapsed_apply (effect : Effect) (state : State) :
    (effect.apply state).elapsed = state.elapsed := by
  simp only [Effect.apply]
  generalize (effect.records.map (·.1)) = processes
  have : ∀ (start : State), (processes.foldl (fun changed other =>
      changed.put other (effect.record other (state.record other))) start).elapsed = start.elapsed := by
    induction processes with
    | nil => intro; rfl
    | cons head rest ih =>
      intro start
      simp only [List.foldl_cons]
      rw [ih]
      cases effect.record head (state.record head) <;> rfl
  rw [this]

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

private theorem ProcessState.Same.trans {mask : Mask} {first second third : ProcessState}
    (one : first.Same mask second) (two : second.Same mask third) : first.Same mask third :=
  ⟨fun x => (one.1 x).trans (two.1 x), fun x => (one.2.1 x).trans (two.2.1 x),
    fun part x => (one.2.2 part x).trans (two.2.2 part x)⟩

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
  (reads headBit → base.queue ≠ []) ∧
  (writes headBit → base.queue ≠ []) ∧
  (writes liveBit = false → ∀ process, process.Same reads base →
    (change process).exiting.isSome = process.exiting.isSome)

/-- A change within its frame keeps what a frame it writes nothing of reads. -/
private theorem Framed.keeps {reads writes reads' : Mask} {base : ProcessState} {change : ProcessState → ProcessState}
    (framed : Framed reads writes base change) (apart : ∀ bit, writes bit → reads' bit → False)
    (nonempty : reads' headBit → base.queue ≠ []) (tail : reads' tailBit → reads' headBit) :
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
      cases equal : base.queue with
      | nil => exact absurd equal (nonempty inside)
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

/-- Two records, or their absence, agree on a mask: alike live, when it reads
liveness, and agreeing on its fields when both exist. -/
private def RecordSame (mask : Mask) (record record' : Option ProcessState) : Prop :=
  (mask liveBit → record.map (·.exiting.isSome) = record'.map (·.exiting.isSome)) ∧
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
      readsOf frames' processId headBit → process.queue ≠ [])
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
      · simp only [Option.map_some, Option.some.injEq]
        cases written : writesOf frames processId liveBit
        · exact ((framed process found).2.2.2.2.2.2 written process (ProcessState.Same.refl _ _)).symm
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
      | (split
         · exact Realizes.modify _ _ _
         · exact Realizes.refl _)

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
        refCounter := process.refCounter, children := process.children, parked := process.parked
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
    let unparked := match (state.process processId).parked with
      | some (parked, _) => if parked == target then state.unpark processId else state
      | none => state
    let unpark : Effect := match (state.process processId).parked with
      | some (parked, _) => if parked == target then state.unparkEffect processId else {}
      | none => {}
    unpark.andThen (Effect.modify target fun process => { process with
      links := Kernel.filter (·.1 != processId) process.links
      eagerExits := insertPid processId process.eagerExits })
  else state.sendEffect processId target (.exit reason true false)

private theorem Realizes.linkExit (state : State) (processId target : PID) (reason : Term) :
    Realizes (state.linkExitEffect processId target reason) state (state.linkExit processId target reason) := by
  unfold State.linkExitEffect State.linkExit
  split
  · simp only
    cases parked : (state.process processId).parked with
    | none => simpa [Effect.andThen, Effect.record, changeOf] using Realizes.modify state target _
    | some found =>
      obtain ⟨other, reference⟩ := found
      simp only
      split
      · exact (Realizes.unpark _ _).andThen (Realizes.modify _ _ _)
      · simpa [Effect.andThen, Effect.record, changeOf] using Realizes.modify state target _
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
    mailbox := [], queue, exiting := some { reason, links, downs := process.monitors } }
  let exit (state : State) (target : PID) : State := if state.eagerLink processId target reason then
      (state.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
        { exiting with links := Kernel.filter (· != target) exiting.links } }).linkExit processId target reason
    else state
  let exitEffect (state : State) (target : PID) : Effect := if state.eagerLink processId target reason then
      (Effect.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
        { exiting with links := Kernel.filter (· != target) exiting.links } }).andThen
        ((state.modify processId fun process => { process with exiting := process.exiting.map fun exiting =>
          { exiting with links := Kernel.filter (· != target) exiting.links } }).linkExitEffect processId target reason)
    else {}
  ((Effect.retime (Kernel.filter (·.destination != processId))).andThen (Effect.put processId { process with
    mailbox := [], queue, exiting := some { reason, links, downs := process.monitors } })).andThen
    (chainEffect exit exitEffect ended links)

private theorem Realizes.terminate (state : State) (processId : PID) (reason : Term) :
    Realizes (state.terminateEffect processId reason) state (state.terminate processId reason) := by
  unfold State.terminateEffect State.terminate
  simp only [Kernel.foldl_eq]
  refine ((Realizes.retime _ _).andThen (Realizes.put _ _ _)).andThen (Realizes.foldl (fun state target => ?_) _ _)
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
          aliases := Kernel.erase process.aliases reference }
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

/-- Remove a link a process that ended has left to signal. -/
private def unlinkExiting (target : PID) (process : ProcessState) : ProcessState :=
  { process with exiting := process.exiting.map fun exiting =>
      { exiting with links := Kernel.filter (· != target) exiting.links } }

/-- The effect of `State.linkPhase`. -/
private def State.linkPhaseEffect (state : State) (processId target : PID) (reason : Term) : Effect :=
  (Effect.modify processId (unlinkExiting target)).andThen
    ((state.modify processId (unlinkExiting target)).linkExitEffect processId target reason)

private theorem Realizes.linkPhase {state next : State} {processId target : PID}
    (phase : state.linkPhase processId target = some next) :
    ∃ reason, Realizes (state.linkPhaseEffect processId target reason) state next := by
  unfold State.linkPhase at phase
  split at phase
  · rename_i process found
    split at phase
    · rename_i exiting exits
      split at phase
      · simp only [Option.some.injEq] at phase; subst phase
        refine ⟨exiting.reason, ?_⟩
        have set := Realizes.set found (unlinkExiting target)
        have equal : unlinkExiting target process = { process with exiting := some { exiting with
            links := Kernel.filter (· != target) exiting.links } } := by simp [unlinkExiting, exits]
        rw [equal] at set
        have modified : state.modify processId (unlinkExiting target) = state.set processId { process with
            exiting := some { exiting with links := Kernel.filter (· != target) exiting.links } } := by
          simp [State.modify, found, equal]
        unfold State.linkPhaseEffect
        rw [modified]
        exact set.andThen (Realizes.linkExit _ _ _ _)
      · simp at phase
    · simp at phase
  · simp at phase

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
      · split at phase
        · simp at phase
        · rename_i links downs _
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
    (covered : ∀ bit, reads' bit → writes bit → reads bit)
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
    · exact depends _ _ mine self part written (same.2.2 part (by simp [Mask.union, covered _ read written]))

/-- Two changes within frames, one after the other, are within the union of
their frames, when the second reads of what the first writes only what the
first reads too, they do not both remove a queue's head, and what the second
reads of a queue is there before the first. -/
private theorem Framed.comp {reads writes reads' writes' : Mask} {base : ProcessState}
    {change change' : ProcessState → ProcessState}
    (framed : Framed reads writes base change) (framed' : Framed reads' writes' (change base) change')
    (covered : ∀ bit, reads' bit → writes bit → reads bit)
    (popped : reads' headBit → writes headBit → reads tailBit)
    (once : writes headBit → writes' headBit → False)
    (appended : writes tailBit → writes' headBit → False)
    (nonempty : reads' headBit ∨ writes' headBit → base.queue ≠ []) :
    Framed (reads.union reads') (writes.union writes') base (change' ∘ change) := by
  have through : ∀ process, process.Same (reads.union reads') base →
      (change process).Same reads' (change base) := fun process same => framed.same same covered popped
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
  · simp only [Mask.union, Bool.or_eq_true] at read
    rcases read with read | read
    · exact head read
    · exact nonempty (.inl read)
  · simp only [Mask.union, Bool.or_eq_true] at written
    rcases written with written | written
    · exact pops written
    · exact nonempty (.inr written)
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
    (tail : reads' tailBit → reads' headBit) (nonempty : reads' headBit → base.queue ≠ [])
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

end Lynx.Concurrent
