module

public import Lynx.Concurrent.Commute

/-! Foundations for proving that steps `checkSleep` takes as commuting reach
the same configuration in either order. States keep their records sorted by
PID, so two states are equal when they have the same record for every process
and the same timers (`State.ext_record`). -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-! ### PID order -/

theorem pidBefore_irrefl : ∀ processId : PID, pidBefore processId processId = false
  | [] => rfl
  | head :: rest => by simp [pidBefore, pidBefore_irrefl rest]

theorem pidBefore_trans : ∀ {first second third : PID}, pidBefore first second = true →
    pidBefore second third = true → pidBefore first third = true
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, one, two => by
      simp only [pidBefore, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at one two ⊢
      rcases one with lt | ⟨rfl, one⟩ <;> rcases two with lt' | ⟨rfl, two⟩
      · exact .inl (Nat.lt_trans lt lt')
      · exact .inl lt
      · exact .inl lt'
      · exact .inr ⟨rfl, pidBefore_trans one two⟩
  | [], [], _, one, _ => by simp [pidBefore] at one
  | _ :: _, [], _, one, _ => by simp [pidBefore] at one
  | _, _ :: _, [], _, two => by simp [pidBefore] at two

theorem pidBefore_asymm {first second : PID} (before : pidBefore first second = true) :
    pidBefore second first = false := by
  cases after : pidBefore second first
  · rfl
  · have := pidBefore_trans before after
    rw [pidBefore_irrefl] at this
    exact absurd this (by simp)

theorem pidBefore_total : ∀ {first second : PID}, first ≠ second →
    pidBefore first second = true ∨ pidBefore second first = true
  | [], [], differ => absurd rfl differ
  | [], _ :: _, _ => .inl rfl
  | _ :: _, [], _ => .inr rfl
  | head :: rest, head' :: rest', differ => by
      simp only [pidBefore, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
      rcases Nat.lt_trichotomy head head' with lt | rfl | gt
      · exact .inl (.inl lt)
      · have : rest ≠ rest' := fun same => differ (by rw [same])
        rcases pidBefore_total this with before | before
        · exact .inl (.inr ⟨rfl, before⟩)
        · exact .inr (.inr ⟨rfl, before⟩)
      · exact .inr (.inl gt)

/-! ### Sorted records -/

/-- Records in strictly increasing PID order, hence with distinct PIDs. -/
def Sorted (records : List (PID × ProcessState)) : Prop :=
  records.Pairwise fun first second => pidBefore first.1 second.1 = true

theorem lookup_eq_none_of_before {processId : PID} {records : List (PID × ProcessState)}
    (sorted : Sorted records) (before : ∀ record ∈ records, pidBefore processId record.1 = true) :
    records.lookup processId = none := by
  induction records with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    have differ : (processId == key) = false := by
      have := before (key, value) (by simp)
      cases equal : processId == key
      · rfl
      · rw [eq_of_beq equal, pidBefore_irrefl] at this; exact absurd this (by simp)
    simp only [List.lookup_cons, differ]
    exact ih (List.Pairwise.of_cons sorted) fun record mem => before record (by simp [mem])

/-- Sorted records with the same record for every process are the same. -/
theorem Sorted.ext {first second : List (PID × ProcessState)} (sorted : Sorted first)
    (sorted' : Sorted second) (same : ∀ processId, first.lookup processId = second.lookup processId) :
    first = second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons head rest => obtain ⟨key, _⟩ := head; have := same key; simp at this
  | cons head rest ih =>
    cases second with
    | nil => obtain ⟨key, _⟩ := head; have := same key; simp at this
    | cons head' rest' =>
      obtain ⟨key, value⟩ := head
      obtain ⟨key', value'⟩ := head'
      have above := List.pairwise_cons.mp sorted
      have above' := List.pairwise_cons.mp sorted'
      -- The first keys are the least of each list, so they are the same.
      have keys : key = key' := by
        refine Classical.byContradiction fun differ => ?_
        rcases pidBefore_total differ with before | before
        · have missing : ((key', value') :: rest').lookup key = none :=
            lookup_eq_none_of_before sorted' fun record mem => by
              simp only [List.mem_cons] at mem
              rcases mem with rfl | mem
              · exact before
              · exact pidBefore_trans before (above'.1 record mem)
          have := same key
          simp [missing] at this
        · have missing : ((key, value) :: rest).lookup key' = none :=
            lookup_eq_none_of_before sorted fun record mem => by
              simp only [List.mem_cons] at mem
              rcases mem with rfl | mem
              · exact before
              · exact pidBefore_trans before (above.1 record mem)
          have := same key'
          simp [missing] at this
      subst keys
      have values : value = value' := by have := same key; simpa using this
      subst values
      have rests : rest = rest' := ih above.2 above'.2 fun processId => by
        by_cases equal : processId = key
        · subst equal
          rw [lookup_eq_none_of_before above.2 above.1, lookup_eq_none_of_before above'.2 above'.1]
        · have := same processId
          have differ : (processId == key) = false := by simp [equal]
          simpa [List.lookup_cons, differ] using this
      rw [rests]

/-! ### Records of a state -/

theorem lookup_insertSorted (processId : PID) (process : ProcessState) :
    ∀ (records : List (PID × ProcessState)) (other : PID), (records.lookup processId = none) →
      (insertSorted processId process records).lookup other =
        if other = processId then some process else records.lookup other
  | [], other, _ => by by_cases equal : other = processId <;> simp [insertSorted, equal]
  | (key, value) :: rest, other, missing => by
      have differ : processId ≠ key := by
        intro same; subst same; simp at missing
      have missing' : rest.lookup processId = none := by
        have differ' : (processId == key) = false := by simp [differ]
        simpa [List.lookup_cons, differ'] using missing
      simp only [insertSorted]
      split
      · by_cases equal : other = processId
        · simp [equal]
        · have differ' : (other == processId) = false := by simp [equal]
          simp [List.lookup_cons, differ', equal]
      · have ih := lookup_insertSorted processId process rest other missing'
        by_cases equal : other = processId
        · subst equal
          have differ' : (other == key) = false := by simp [differ]
          simp [List.lookup_cons, differ', ih]
        · by_cases equal' : other = key
          · subst equal'; simp [equal]
          · have differ' : (other == key) = false := by simp [equal']
            simp [List.lookup_cons, differ', ih, equal]

theorem lookup_filter_ne (processId other : PID) (records : List (PID × ProcessState)) :
    (records.filter (·.1 != processId)).lookup other =
      if other = processId then none else records.lookup other := by
  induction records with
  | nil => by_cases equal : other = processId <;> simp [equal]
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    by_cases same : key = processId
    · subst same
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih]
      by_cases equal : other = key
      · simp [equal]
      · have differ : (other == key) = false := by simp [equal]
        simp [equal, List.lookup_cons, differ]
    · have keep : (key != processId) = true := by simp [same]
      simp only [List.filter_cons, keep, ↓reduceIte, List.lookup_cons, ih]
      by_cases equal : other = key
      · subst equal; simp [same]
      · have differ : (other == key) = false := by simp [equal]
        simp [differ]

/-- The record of a process after another's is replaced. -/
theorem State.record_set (state : State) (processId other : PID) (process : ProcessState) :
    (state.set processId process).record other =
      if other = processId then some process else state.record other := by
  simp only [State.set, State.record, insertRecord, Kernel.lookup_eq, Kernel.filter_eq]
  rw [lookup_insertSorted _ _ _ _ (by rw [lookup_filter_ne]; simp), lookup_filter_ne]
  by_cases equal : other = processId <;> simp [equal]

/-- The record of a process after another's is removed. -/
theorem State.record_remove (state : State) (processId other : PID) :
    (state.remove processId).record other = if other = processId then none else state.record other := by
  simp only [State.remove, State.record, Kernel.lookup_eq, Kernel.filter_eq, lookup_filter_ne]

theorem Sorted.filter {records : List (PID × ProcessState)} (sorted : Sorted records)
    (keep : PID × ProcessState → Bool) : Sorted (records.filter keep) :=
  List.Pairwise.filter keep sorted

theorem mem_insertSorted {processId : PID} {process : ProcessState} {record : PID × ProcessState} :
    ∀ {records : List (PID × ProcessState)}, record ∈ insertSorted processId process records →
      record = (processId, process) ∨ record ∈ records
  | [], mem => by simpa [insertSorted] using mem
  | head :: rest, mem => by
      simp only [insertSorted] at mem
      split at mem
      · simpa using mem
      · simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · exact .inr (by simp)
        · rcases mem_insertSorted mem with rfl | mem
          · exact .inl rfl
          · exact .inr (by simp [mem])

theorem Sorted.insertSorted {records : List (PID × ProcessState)} (sorted : Sorted records)
    (processId : PID) (process : ProcessState) (missing : ∀ record ∈ records, record.1 ≠ processId) :
    Sorted (insertSorted processId process records) := by
  induction records with
  | nil => simp [Sorted, Lynx.Concurrent.insertSorted]
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    have above := List.pairwise_cons.mp sorted
    have differ : key ≠ processId := missing (key, value) (by simp)
    simp only [Lynx.Concurrent.insertSorted]
    split
    · rename_i before
      refine List.pairwise_cons.mpr ⟨fun record mem => ?_, sorted⟩
      simp only [List.mem_cons] at mem
      rcases mem with rfl | mem
      · exact before
      · exact pidBefore_trans before (above.1 record mem)
    · rename_i after
      have before : pidBefore key processId = true := by
        rcases pidBefore_total differ with before | before
        · exact before
        · simp [before] at after
      refine List.pairwise_cons.mpr ⟨fun record mem => ?_, ih above.2 fun record mem => missing record (by simp [mem])⟩
      have := fun record => mem_insertSorted (record := record) (processId := processId) (process := process) (records := rest)
      rcases this record mem with rfl | mem
      · exact before
      · exact above.1 record mem

theorem Sorted.insertRecord {records : List (PID × ProcessState)} (sorted : Sorted records)
    (processId : PID) (process : ProcessState) : Sorted (insertRecord processId process records) := by
  simp only [Lynx.Concurrent.insertRecord, Kernel.filter_eq]
  exact (sorted.filter _).insertSorted _ _ fun record mem => by
    have := (List.mem_filter.mp mem).2
    simpa using this

/-- Normalization keeps the records sorted. -/
theorem Sorted.normalize {state : State} (sorted : Sorted state.processes) : Sorted state.normalize.processes := by
  simp only [State.normalize, Kernel.map_eq, Kernel.filter_eq]
  refine List.Pairwise.filter _ ?_
  exact List.pairwise_map.mpr (sorted.imp id)

/-! ### Every step keeps the records sorted -/

/-- A state whose records are sorted. -/
def State.Sorted (state : State) : Prop := Lynx.Concurrent.Sorted state.processes

theorem State.Sorted.set {state : State} (sorted : state.Sorted) (processId : PID) (process : ProcessState) :
    (state.set processId process).Sorted :=
  Lynx.Concurrent.Sorted.insertRecord sorted processId process

theorem State.Sorted.remove {state : State} (sorted : state.Sorted) (processId : PID) :
    (state.remove processId).Sorted := by
  simp only [State.Sorted, State.remove, Kernel.filter_eq]; exact Lynx.Concurrent.Sorted.filter sorted _

theorem State.Sorted.modify {state : State} (sorted : state.Sorted) (processId : PID)
    (change : ProcessState → ProcessState) : (state.modify processId change).Sorted := by
  unfold State.modify; split
  · exact sorted.set _ _
  · exact sorted

theorem State.Sorted.normalize {state : State} (sorted : state.Sorted) : state.normalize.Sorted :=
  Lynx.Concurrent.Sorted.normalize sorted

theorem State.Sorted.settle {state : State} (sorted : state.Sorted) (event : Event) :
    (state.settle event).Sorted := by
  unfold State.settle; split
  · exact sorted.normalize
  · exact sorted

theorem State.Sorted.timers {state : State} (sorted : state.Sorted) (timers : List Timer) :
    ({ state with timers } : State).Sorted := sorted

/-- Prove that an operation built from replacing, changing and removing
records keeps them sorted. -/
syntax "sorted_step" : tactic
macro_rules
  | `(tactic| sorted_step) => `(tactic| first
      | with_reducible assumption
      | with_reducible apply State.Sorted.set | with_reducible apply State.Sorted.remove
      | with_reducible apply State.Sorted.modify | with_reducible apply State.Sorted.normalize
      | with_reducible apply State.Sorted.settle | with_reducible apply State.Sorted.allocate
      | refine State.Sorted.allocate ?_ _
      | split)

theorem State.Sorted.allocate {state : State} (sorted : state.Sorted) (processId : PID) :
    (state.allocate processId).2.Sorted := sorted.modify _ _

theorem State.Sorted.append {state : State} (sorted : state.Sorted) (processId : PID) (message : Term) :
    (state.append processId message).Sorted := sorted.modify _ _

theorem State.Sorted.store {state : State} (sorted : state.Sorted) (processId : PID) (env : Environment) :
    (state.store processId env).Sorted := sorted.modify _ _

theorem State.Sorted.fallback {state : State} (sorted : state.Sorted) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).Sorted := by
  unfold State.fallback; repeat sorted_step

theorem State.Sorted.enqueue {state : State} (sorted : state.Sorted) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).Sorted := by
  unfold State.enqueue
  split
  · split
    · exact sorted.set _ _
    · exact sorted.fallback _ _ _
  · exact sorted.fallback _ _ _

theorem State.Sorted.unpark {state : State} (sorted : state.Sorted) (processId : PID) :
    (state.unpark processId).Sorted := by
  unfold State.unpark; split
  · exact (sorted.modify _ _).enqueue _ _ _
  · exact sorted

theorem State.Sorted.send {state : State} (sorted : state.Sorted) (source target : PID) (signal : Signal) :
    (state.send source target signal).Sorted := by
  unfold State.send
  apply State.Sorted.enqueue
  split
  · split
    · exact sorted.unpark _
    · exact sorted
  · exact sorted

theorem State.Sorted.linkExit {state : State} (sorted : state.Sorted) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).Sorted := by
  unfold State.linkExit
  split
  · apply State.Sorted.modify
    split
    · split
      · exact sorted.unpark _
      · exact sorted
    · exact sorted
  · exact sorted.send _ _ _

theorem State.Sorted.terminate {state : State} (sorted : state.Sorted) (processId : PID) (reason : Term) :
    (state.terminate processId reason).Sorted := by
  unfold State.terminate
  dsimp only
  generalize (Kernel.foldl _ [] _ : List PID) = links
  generalize hstate : State.set _ _ _ = start
  have : start.Sorted := hstate ▸ (sorted.timers _).set _ _
  clear hstate
  simp only [Kernel.foldl_eq]
  induction links generalizing start with
  | nil => exact this
  | cons target rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact (this.modify _ _).linkExit _ _ _
    · exact this

theorem State.Sorted.answer {state : State} (sorted : state.Sorted) (processId : PID) (entry : Entry) :
    (state.answer processId entry).Sorted := by
  unfold State.answer; split <;> first | exact sorted.send _ _ _ | exact sorted

theorem State.Sorted.linkPhase {state next : State} (sorted : state.Sorted) {processId target : PID}
    (phase : state.linkPhase processId target = some next) : next.Sorted := by
  unfold State.linkPhase at phase
  repeat' split at phase
  all_goals first
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).linkExit _ _ _)
    | simp at phase

theorem State.Sorted.phase {state next : State} (sorted : state.Sorted) {processId : PID}
    (phase : state.phase processId = some next) : next.Sorted := by
  unfold State.phase at phase
  repeat' split at phase
  all_goals first
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).send _ _ _)
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).answer _ _)
    | simp at phase

theorem State.Sorted.phases {state next : State} (sorted : state.Sorted) {processId : PID}
    (mem : next ∈ state.phases processId) : next.Sorted := by
  simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at mem
  rcases mem with ⟨_, -, phase⟩ | mem
  · exact sorted.linkPhase phase
  · split at mem
    · rename_i found
      simp only [List.mem_singleton] at mem; subst mem
      exact sorted.phase found
    · simp at mem

theorem State.Sorted.fire {state : State} (sorted : state.Sorted) (timer : Timer) : (state.fire timer).Sorted :=
  (sorted.timers _).enqueue _ _ _

theorem State.Sorted.spawnWith {state : State} (sorted : state.Sorted) (processId : PID) (options : SpawnOptions) :
    (state.spawnWith processId options).2.Sorted := by
  unfold State.spawnWith
  dsimp only
  split
  · apply State.Sorted.modify
    apply State.Sorted.modify
    refine State.Sorted.allocate ?_ _
    split
    · exact ((((sorted.set _ _).set _ _).modify _ _).modify _ _)
    · exact ((sorted.set _ _).set _ _)
  · split
    · exact ((((sorted.set _ _).set _ _).modify _ _).modify _ _)
    · exact ((sorted.set _ _).set _ _)


/-- Close a goal that an operation keeps the records sorted with one of the
shapes the operations of `State.request` and `State.handle` take. -/
syntax "sorted_exact" : tactic
macro_rules
  | `(tactic| sorted_exact) => `(tactic| first
      | assumption
      | exact State.Sorted.modify ‹_› _ _
      | exact State.Sorted.send ‹_› _ _ _
      | exact State.Sorted.enqueue ‹_› _ _ _
      | exact State.Sorted.append ‹_› _ _
      | exact (State.Sorted.modify ‹_› _ _).send _ _ _
      | exact (State.Sorted.modify ‹_› _ _).append _ _
      | exact State.Sorted.allocate ‹_› _
      | exact ((State.Sorted.allocate ‹_› _).unpark _).modify _ _
      | exact (State.Sorted.allocate ‹_› _).timers _
      | exact (State.Sorted.timers ‹_› _).modify _ _)

/-- The state an answer leaves. -/
def Answer.state : Answer β → State
  | .reply _ state | .wait _ state | .continue _ state => state

theorem State.Sorted.request {state : State} (sorted : state.Sorted) (processId : PID)
    (next : Term → Result β) (query : Request) : (state.request processId next query).state.Sorted := by
  cases query <;> simp only [State.request] <;> (repeat' split) <;> simp only [Answer.state] <;> sorted_exact

theorem State.Sorted.exitSignal {state : State} (sorted : state.Sorted) (target source : PID) (reason : Term)
    (linked normalKills : Bool) : (state.exitSignal target source reason linked normalKills).1.Sorted := by
  unfold State.exitSignal; dsimp only; (repeat' split) <;> sorted_exact

theorem State.Sorted.handle {state : State} (sorted : state.Sorted) (processId : PID) (waiting : Option Wait)
    (entry : Entry) : (state.handle processId waiting entry).1.Sorted := by
  unfold State.handle
  split
  · exact sorted.append _ _
  · dsimp only; split <;> sorted_exact
  · exact sorted.exitSignal _ _ _ _ _
  · dsimp only; split <;> sorted_exact
  · dsimp only; split <;> sorted_exact
  · dsimp only; split <;> sorted_exact
  · exact sorted.modify _ _
  · rename_i reference reason _
    dsimp only
    have cleared : (if isNormal reason && Kernel.contains (state.process processId).eagerExits entry.source then
        state.modify processId fun process => { process with
          eagerExits := Kernel.filter (· != entry.source) process.eagerExits } else state).Sorted := by
      split <;> sorted_exact
    generalize (if isNormal reason && _ then _ else state) = cleared' at cleared
    split <;> sorted_exact
  · exact sorted.send _ _ _
  · dsimp only; split <;> sorted_exact
  · dsimp only; split <;> sorted_exact

theorem State.Sorted.ended {state : State} (sorted : state.Sorted) {γ : Type}
    (finish : Except Exception γ → Option (Except Exception α)) (event : Event) (processId : PID)
    (reason : Term) (result : Except Exception γ) :
    (Task.ended finish event state processId reason result).state.Sorted := sorted.terminate _ _

theorem State.Sorted.own {state : State} (sorted : state.Sorted) {processId : PID} {task : Task α}
    {transition : Transition α} (mem : transition ∈ task.own state processId) : transition.state.Sorted := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    cases computation with
    | ok =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem; exact sorted.ended _ _ _ _ _
    | error exception =>
      cases exception <;> simp only [Task.own, List.mem_singleton] at mem <;> subst mem <;>
        first | exact sorted.remove _ | exact sorted.ended _ _ _ _ _
    | get | send =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      first | exact sorted | exact sorted.send _ _ _
    | set => simp only [Task.own, List.mem_singleton] at mem; subst mem; exact sorted.store _ _
    | schedule => simp only [Task.own, List.mem_singleton] at mem; subst mem; exact sorted.spawnWith _ _
    | receive =>
      simp only [Task.own] at mem
      split at mem
      · simp only [List.mem_singleton] at mem; subst mem; exact sorted.modify _ _
      · split at mem
        · simp at mem
        · split at mem
          · simp at mem
          · simp only [List.mem_singleton] at mem; subst mem; exact sorted
    | request query next =>
      have := sorted.request processId next query
      simp only [Task.own] at mem
      split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;>
        rename_i found <;> simpa [found, Answer.state] using this

theorem State.Sorted.handleStep {state : State} (sorted : state.Sorted) {processId : PID} {task : Task α}
    {transition : Transition α} (mem : transition ∈ task.handle state processId) : transition.state.Sorted := by
  simp only [Task.handle] at mem
  split at mem
  · simp at mem
  · rename_i entry rest _
    have handled := (sorted.set processId { state.process processId with queue := rest }).handle processId
      (task.wait.map (·.1)) entry
    generalize (State.set _ _ _).handle _ _ _ = result at mem handled
    obtain ⟨state', resumed, exits⟩ := result
    dsimp only at mem handled
    split at mem
    · simp only [List.mem_singleton] at mem; subst mem; exact handled.ended _ _ _ _ _
    · split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> exact handled

/-- A configuration whose records are sorted. -/
def Config.Sorted : Config α → Prop
  | .start .. => True
  | .running state .. => state.Sorted

theorem State.Sorted.initial (env : Environment) (elapsed : PID → Nat → Nat) :
    (State.initial env elapsed).Sorted := by
  simp [State.Sorted, State.initial, Lynx.Concurrent.Sorted]

/-- Every step keeps the records sorted. -/
theorem Config.Sorted.step {config next : Config α} {event : Event} (sorted : config.Sorted)
    (step : Step config event next) : next.Sorted := by
  cases config with
  | start env computation elapsed =>
    simp only [Step, Config.successors] at step
    split at step
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · split at step
      · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step
        exact State.Sorted.initial _ _
      · simp at step
  | running state tasks finished exhausted =>
    have sorted : state.Sorted := sorted
    cases exhausted
    case true => simp [Step, Config.successors] at step
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with ((⟨before, processId, task, after, -, transition, possible, same⟩ |
      ⟨processId, process, -, phased⟩) | ⟨processId, process, -, unparked⟩) | ⟨timer, -, fired⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      have : transition.state.Sorted := by
        simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
        rcases possible with possible | possible
        · exact sorted.own possible
        · exact sorted.handleStep possible
      unfold Transition.apply
      split
      · exact this
      · exact this.settle _
    · obtain ⟨next', phase, same⟩ := phased
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      exact (sorted.phases phase).normalize
    · cases parked : (state.process processId).parked with
      | none => simp [parked] at unparked
      | some _ =>
        simp only [parked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at unparked
        obtain ⟨-, rfl⟩ := unparked
        exact (sorted.unpark _).normalize
    · simp only [Prod.mk.injEq] at fired
      obtain ⟨-, rfl⟩ := fired
      exact sorted.fire _

/-- Every configuration a run reaches has sorted records. -/
theorem Config.Sorted.run {config last : Config α} {events : List Event} (sorted : config.Sorted)
    (run : Run config events last) : last.Sorted :=
  Run.invariant (fun _ _ _ sorted step => sorted.step step) run sorted

/-! ### Comparisons -/

theorem Signal.eq_of_identical {first second : Signal} (same : first.identical second = true) :
    first = second := by
  cases first <;> cases second <;>
    simp only [Signal.identical, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same <;>
    first
      | rfl
      | rw [Term.eq_of_identical same]
      | rw [same]
      | (obtain ⟨rfl, same⟩ := same; rw [Term.eq_of_identical same])
      | (obtain ⟨same, rfl⟩ := same; rw [Term.eq_of_identical same])
      | (obtain ⟨⟨same, rfl⟩, rfl⟩ := same; rw [Term.eq_of_identical same])

theorem eq_of_identicalLists {same : γ → γ → Bool}
    (sound : ∀ {first second}, same first second = true → first = second) :
    ∀ {first second : List γ}, identicalLists same first second = true → first = second
  | [], [], _ => rfl
  | head :: rest, head' :: rest', equal => by
    simp only [identicalLists, Bool.and_eq_true] at equal
    rw [sound equal.1, eq_of_identicalLists sound equal.2]
  | [], _ :: _, equal | _ :: _, [], equal => by simp [identicalLists] at equal

theorem eq_of_optionIdentical {same : γ → γ → Bool}
    (sound : ∀ {first second}, same first second = true → first = second) :
    ∀ {first second : Option γ}, optionIdentical same first second = true → first = second
  | some _, some _, equal => by rw [sound equal]
  | none, none, _ => rfl
  | some _, none, equal | none, some _, equal => by simp [optionIdentical] at equal

theorem Entry.eq_of_identical {first second : Entry} (same : first.identical second = true) :
    first = second := by
  obtain ⟨source, signal⟩ := first
  obtain ⟨source', signal'⟩ := second
  simp only [Entry.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨rfl, same⟩ := same
  rw [Signal.eq_of_identical same]

theorem Exiting.eq_of_identical {first second : Exiting} (same : first.identical second = true) :
    first = second := by
  obtain ⟨reason, links, downs⟩ := first
  obtain ⟨reason', links', downs'⟩ := second
  simp only [Exiting.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨same, rfl⟩, rfl⟩ := same
  rw [Term.eq_of_identical same]

theorem ProcessState.eq_of_identical {first second : ProcessState} (same : first.identical second = true) :
    first = second := by
  cases first; cases second
  simp only [ProcessState.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨queue, mailbox⟩, pdict⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩, exiting⟩ := same
  rw [eq_of_identicalLists Entry.eq_of_identical queue, Term.eq_of_identicalList mailbox,
    Term.eq_of_identicalEntries pdict, eq_of_optionIdentical Exiting.eq_of_identical exiting]

theorem Timer.eq_of_identical {first second : Timer} (same : first.identical second = true) :
    first = second := by
  obtain ⟨reference, destination, message, duration⟩ := first
  obtain ⟨reference', destination', message', duration'⟩ := second
  simp only [Timer.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨⟨rfl, rfl⟩, same⟩, rfl⟩ := same
  rw [Term.eq_of_identical same]

end Lynx.Concurrent
