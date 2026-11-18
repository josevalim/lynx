module

public import Lynx.Concurrent.Diamond

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

/-- How a change may change a queue, given which ends its frame writes: not at
all, by removing the oldest signal, by appending signals, or as its reads and
the queue decide. -/
private def QueueChange (head tail : Bool) (reads : Mask) (base : ProcessState)
    (change : ProcessState → ProcessState) : Prop :=
  match head, tail with
  | false, false => ∀ process, process.Same reads base → (change process).queue = process.queue
  | true, false => ∀ process, process.Same reads base → (change process).queue = process.queue.tail
  | false, true => ∃ added, ∀ process, process.Same reads base → (change process).queue = process.queue ++ added
  | true, true => ∀ process process', process.Same reads base → process'.Same reads base →
      process.queue = process'.queue → (change process).queue = (change process').queue

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
  (writes headBit → reads headBit) ∧
  (writes liveBit = false → ∀ process, process.Same reads base →
    (change process).exiting.isSome = process.exiting.isSome)

/-- A change within its frame keeps what a frame it writes nothing of reads. -/
private theorem Framed.keeps {reads writes reads' : Mask} {base : ProcessState} {change : ProcessState → ProcessState}
    (framed : Framed reads writes base change) (apart : ∀ bit, writes bit → reads' bit → False)
    (nonempty : reads' headBit → base.queue ≠ []) (tail : reads' tailBit → reads' headBit) :
    (change base).Same reads' base := by
  obtain ⟨keeps, -, queue, -, -, -, -⟩ := framed
  have self := ProcessState.Same.refl reads base
  refine ⟨fun inside => ?_, fun inside => ?_, fun part inside => ?_⟩
  · have head := tail inside
    cases written : writes headBit
    · cases written' : writes tailBit
      · simp only [QueueChange, written, written'] at queue; exact queue base self
      · exact (apart _ written' inside).elim
    · exact (apart _ written head).elim
  · cases written : writes headBit
    · cases written' : writes tailBit
      · simp only [QueueChange, written, written'] at queue; rw [queue base self]
      · simp only [QueueChange, written, written'] at queue
        obtain ⟨added, queue⟩ := queue
        rw [queue base self]
        cases equal : base.queue with
        | nil => exact absurd equal (nonempty inside)
        | cons _ _ => rfl
    · exact (apart _ written inside).elim
  · cases written : writes part.bit
    · exact keeps base self part written
    · exact (apart _ written inside).elim

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
  obtain ⟨keeps, depends, queue, -, nonempty, pops, -⟩ := framed
  obtain ⟨keeps', depends', queue', -, nonempty', pops', -⟩ := framed'
  refine ProcessState.ext_get ?_ fun part => ?_
  · cases head : writes headBit <;> cases tail : writes tailBit <;>
      cases head' : writes' headBit <;> cases tail' : writes' tailBit <;>
      simp only [QueueChange, head, tail, head', tail'] at queue queue' <;>
      first
        | exact (disjoint _ head head').elim
        | exact (disjoint _ tail tail').elim
        | skip
    · rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
    · obtain ⟨added', queue'⟩ := queue'
      rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
    · rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
    · rw [queue _ same, queue' _ _ same' self' (queue _ self)]
    · obtain ⟨added, queue⟩ := queue
      rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
    · obtain ⟨added, queue⟩ := queue
      rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
      exact (List.tail_append_of_ne_nil (nonempty' (pops' head'))).symm
    · rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
    · obtain ⟨added', queue'⟩ := queue'
      rw [queue _ same, queue' _ self', queue' _ same', queue _ self]
      exact List.tail_append_of_ne_nil (nonempty (pops head))
    · rw [queue _ _ same self (queue' _ self'), queue' _ same']
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
  obtain ⟨keeps, -, queue, -⟩ := framed
  have same : process.Same reads base :=
    ⟨fun read => by simp [(unused tailBit (by decide)).1] at read,
      fun read => by simp [(unused headBit (by decide)).1] at read,
      fun part read => by simp [(unused part.bit part.bit_lt).1] at read⟩
  simp only [QueueChange, (unused headBit (by decide)).2, (unused tailBit (by decide)).2] at queue
  exact ProcessState.ext_get (queue process same) fun part => keeps process same part (unused _ part.bit_lt).2

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

end Lynx.Concurrent
