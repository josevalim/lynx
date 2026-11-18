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

/-! ### Every step keeps the records sorted and the time elapsed -/

/-- A state whose records are sorted. -/
def State.Sorted (state : State) : Prop := Lynx.Concurrent.Sorted state.processes

variable {elapsed : PID → Nat → Nat}

/-- A state whose records are sorted, with the time elapsed when timers are
canceled, which no step changes. -/
def State.Within (elapsed : PID → Nat → Nat) (state : State) : Prop :=
  state.Sorted ∧ state.elapsed = elapsed

theorem State.Within.set {state : State} (sorted : state.Within elapsed) (processId : PID) (process : ProcessState) :
    (state.set processId process).Within elapsed :=
  ⟨Lynx.Concurrent.Sorted.insertRecord sorted.1 processId process, sorted.2⟩

theorem State.Within.remove {state : State} (sorted : state.Within elapsed) (processId : PID) :
    (state.remove processId).Within elapsed := by
  simp only [State.Within, State.remove, Kernel.filter_eq]; exact ⟨Lynx.Concurrent.Sorted.filter sorted.1 _, sorted.2⟩

theorem State.Within.modify {state : State} (sorted : state.Within elapsed) (processId : PID)
    (change : ProcessState → ProcessState) : (state.modify processId change).Within elapsed := by
  unfold State.modify; split
  · exact sorted.set _ _
  · exact sorted

theorem State.Within.normalize {state : State} (sorted : state.Within elapsed) : state.normalize.Within elapsed :=
  ⟨Lynx.Concurrent.Sorted.normalize sorted.1, sorted.2⟩

theorem State.Within.timers {state : State} (sorted : state.Within elapsed) (timers : List Timer) :
    ({ state with timers } : State).Within elapsed := sorted

/-- Prove that an operation built from replacing, changing and removing
records keeps them sorted. -/
syntax "sorted_step" : tactic
macro_rules
  | `(tactic| sorted_step) => `(tactic| first
      | with_reducible assumption
      | with_reducible apply State.Within.set | with_reducible apply State.Within.remove
      | with_reducible apply State.Within.modify | with_reducible apply State.Within.normalize
      | with_reducible apply State.Within.allocate
      | refine State.Within.allocate ?_ _
      | split)

theorem State.Within.allocate {state : State} (sorted : state.Within elapsed) (processId : PID) :
    (state.allocate processId).2.Within elapsed := sorted.modify _ _

theorem State.Within.append {state : State} (sorted : state.Within elapsed) (processId : PID) (message : Term) :
    (state.append processId message).Within elapsed := sorted.modify _ _

theorem State.Within.store {state : State} (sorted : state.Within elapsed) (processId : PID) (env : Environment) :
    (state.store processId env).Within elapsed := sorted.modify _ _

theorem State.Within.fallback {state : State} (sorted : state.Within elapsed) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).Within elapsed := by
  unfold State.fallback; repeat sorted_step

theorem State.Within.enqueue {state : State} (sorted : state.Within elapsed) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).Within elapsed := by
  unfold State.enqueue
  split
  · split
    · exact sorted.set _ _
    · exact sorted.fallback _ _ _
  · exact sorted.fallback _ _ _

theorem State.Within.unpark {state : State} (sorted : state.Within elapsed) (processId : PID) :
    (state.unpark processId).Within elapsed := by
  unfold State.unpark; split
  · exact (sorted.modify _ _).enqueue _ _ _
  · exact sorted

theorem State.Within.send {state : State} (sorted : state.Within elapsed) (source target : PID) (signal : Signal) :
    (state.send source target signal).Within elapsed := by
  unfold State.send
  apply State.Within.enqueue
  split
  · split
    · exact sorted.unpark _
    · exact sorted
  · exact sorted

theorem State.Within.linkExit {state : State} (sorted : state.Within elapsed) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).Within elapsed := by
  unfold State.linkExit
  split
  · apply State.Within.modify
    split
    · split
      · exact sorted.unpark _
      · exact sorted
    · exact sorted
  · exact sorted.send _ _ _

theorem State.Within.terminate {state : State} (sorted : state.Within elapsed) (processId : PID) (reason : Term) :
    (state.terminate processId reason).Within elapsed := by
  unfold State.terminate
  dsimp only
  generalize (Kernel.foldl _ [] _ : List PID) = links
  generalize hstate : State.set _ _ _ = start
  have : start.Within elapsed := hstate ▸ (sorted.timers _).set _ _
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

theorem State.Within.answer {state : State} (sorted : state.Within elapsed) (processId : PID) (entry : Entry) :
    (state.answer processId entry).Within elapsed := by
  unfold State.answer; split <;> first | exact sorted.send _ _ _ | exact sorted

theorem State.Within.linkPhase {state next : State} (sorted : state.Within elapsed) {processId target : PID}
    (phase : state.linkPhase processId target = some next) : next.Within elapsed := by
  unfold State.linkPhase at phase
  repeat' split at phase
  all_goals first
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).linkExit _ _ _)
    | simp at phase

theorem State.Within.phase {state next : State} (sorted : state.Within elapsed) {processId : PID}
    (phase : state.phase processId = some next) : next.Within elapsed := by
  unfold State.phase at phase
  repeat' split at phase
  all_goals first
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).send _ _ _)
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).answer _ _)
    | simp at phase

theorem State.Within.phases {state next : State} (sorted : state.Within elapsed) {processId : PID}
    (mem : next ∈ state.phases processId) : next.Within elapsed := by
  simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at mem
  rcases mem with ⟨_, -, phase⟩ | mem
  · exact sorted.linkPhase phase
  · split at mem
    · rename_i found
      simp only [List.mem_singleton] at mem; subst mem
      exact sorted.phase found
    · simp at mem

theorem State.Within.fire {state : State} (sorted : state.Within elapsed) (timer : Timer) : (state.fire timer).Within elapsed :=
  (sorted.timers _).enqueue _ _ _

theorem State.Within.spawnWith {state : State} (sorted : state.Within elapsed) (processId : PID) (options : SpawnOptions) :
    (state.spawnWith processId options).2.Within elapsed := by
  unfold State.spawnWith
  dsimp only
  split
  · apply State.Within.modify
    apply State.Within.modify
    refine State.Within.allocate ?_ _
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
      | exact State.Within.modify ‹_› _ _
      | exact State.Within.send ‹_› _ _ _
      | exact State.Within.enqueue ‹_› _ _ _
      | exact State.Within.append ‹_› _ _
      | exact (State.Within.modify ‹_› _ _).send _ _ _
      | exact (State.Within.modify ‹_› _ _).append _ _
      | exact State.Within.allocate ‹_› _
      | exact ((State.Within.allocate ‹_› _).unpark _).modify _ _
      | exact (State.Within.allocate ‹_› _).timers _
      | exact (State.Within.timers ‹_› _).modify _ _)

/-- The state an answer leaves. -/
def Answer.state : Answer β → State
  | .reply _ state | .wait _ state | .continue _ state => state

theorem State.Within.request {state : State} (sorted : state.Within elapsed) (processId : PID)
    (next : Term → Result β) (query : Request) : (state.request processId next query).state.Within elapsed := by
  cases query <;> simp only [State.request] <;> (repeat' split) <;> simp only [Answer.state] <;> sorted_exact

theorem State.Within.exitSignal {state : State} (sorted : state.Within elapsed) (target source : PID) (reason : Term)
    (linked normalKills : Bool) : (state.exitSignal target source reason linked normalKills).1.Within elapsed := by
  unfold State.exitSignal; dsimp only; (repeat' split) <;> sorted_exact

theorem State.Within.handle {state : State} (sorted : state.Within elapsed) (processId : PID) (waiting : Option Wait)
    (entry : Entry) : (state.handle processId waiting entry).1.Within elapsed := by
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
          eagerExits := Kernel.filter (· != entry.source) process.eagerExits } else state).Within elapsed := by
      split <;> sorted_exact
    generalize (if isNormal reason && _ then _ else state) = cleared' at cleared
    split <;> sorted_exact
  · exact sorted.send _ _ _
  · dsimp only; split <;> sorted_exact
  · dsimp only; split <;> sorted_exact

theorem State.Within.ended {state : State} (sorted : state.Within elapsed) {γ : Type}
    (finish : Except Exception γ → Option (Except Exception α)) (event : Event) (processId : PID)
    (reason : Term) (result : Except Exception γ) :
    (Task.ended finish event state processId reason result).state.Within elapsed := sorted.terminate _ _

theorem State.Within.own {state : State} (sorted : state.Within elapsed) {processId : PID} {task : Task α}
    {transition : Transition α} (mem : transition ∈ task.own state processId) : transition.state.Within elapsed := by
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

theorem State.Within.handleStep {state : State} (sorted : state.Within elapsed) {processId : PID} {task : Task α}
    {transition : Transition α} (mem : transition ∈ task.handle state processId) : transition.state.Within elapsed := by
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
def Config.Within (elapsed : PID → Nat → Nat) : Config α → Prop
  | .start _ _ elapsed' => elapsed' = elapsed
  | .running state .. => state.Within elapsed

theorem State.Within.initial (env : Environment) (elapsed : PID → Nat → Nat) :
    (State.initial env elapsed).Within elapsed :=
  ⟨by simp [State.Sorted, State.initial, Lynx.Concurrent.Sorted], rfl⟩

/-- Every step keeps the records sorted. -/
theorem Config.Within.step {config next : Config α} {event : Event} (sorted : config.Within elapsed)
    (step : Step config event next) : next.Within elapsed := by
  cases config with
  | start env computation elapsed' =>
    simp only [Step, Config.successors] at step
    split at step
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; exact sorted
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; exact sorted
    · split at step
      · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step
        have same : elapsed' = elapsed := sorted
        subst same
        exact State.Within.initial _ _
      · simp at step
  | running state tasks finished exhausted =>
    have sorted : state.Within elapsed := sorted
    cases exhausted
    case true => simp [Step, Config.successors] at step
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with ((⟨before, processId, task, after, -, transition, possible, same⟩ |
      ⟨processId, process, -, phased⟩) | ⟨processId, process, -, unparked⟩) | ⟨timer, -, fired⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      have : transition.state.Within elapsed := by
        simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
        rcases possible with possible | possible
        · exact sorted.own possible
        · exact sorted.handleStep possible
      unfold Transition.apply
      split
      · exact this
      · exact this.normalize
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
      exact (sorted.fire _).normalize

/-- Every configuration a run reaches has sorted records. -/
theorem Config.Within.run {config last : Config α} {events : List Event} (sorted : config.Within elapsed)
    (run : Run config events last) : last.Within elapsed :=
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

/-! ### Normalizing twice -/

theorem lookup_map_snd (change : PID → ProcessState → ProcessState) (processId : PID) :
    ∀ records : List (PID × ProcessState),
      (records.map fun record => (record.1, change record.1 record.2)).lookup processId =
        (records.lookup processId).map (change processId)
  | [] => rfl
  | (key, value) :: rest => by
      by_cases equal : processId = key
      · subst equal; simp
      · have differ : (processId == key) = false := by simp [equal]
        simp [List.lookup_cons, differ, lookup_map_snd change processId rest]

theorem Sorted.lookup_filter {records : List (PID × ProcessState)} (sorted : Sorted records)
    (keep : PID × ProcessState → Bool) (processId : PID) :
    (records.filter keep).lookup processId =
      (records.lookup processId).filter fun process => keep (processId, process) := by
  induction records with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    have above := List.pairwise_cons.mp sorted
    by_cases equal : processId = key
    · subst equal
      have missing : rest.lookup processId = none := lookup_eq_none_of_before above.2 above.1
      have missing' : (rest.filter keep).lookup processId = none := by rw [ih above.2, missing]; rfl
      simp only [List.filter_cons]
      split <;> simp_all [Option.filter] <;> assumption
    · have differ : (processId == key) = false := by simp [equal]
      simp only [List.filter_cons]
      split <;> simp [List.lookup_cons, differ, ih above.2]

theorem Sorted.lookup_of_mem {records : List (PID × ProcessState)} (sorted : Sorted records)
    {processId : PID} {process : ProcessState} (mem : (processId, process) ∈ records) :
    records.lookup processId = some process := by
  induction records with
  | nil => simp at mem
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    have above := List.pairwise_cons.mp sorted
    simp only [List.mem_cons, Prod.mk.injEq] at mem
    rcases mem with ⟨rfl, rfl⟩ | mem
    · simp
    · have differ : processId ≠ key := by
        intro same; subst same
        have := above.1 _ mem
        rw [pidBefore_irrefl] at this; exact absurd this (by simp)
      have differ' : (processId == key) = false := by simp [differ]
      simp [List.lookup_cons, differ', ih above.2 mem]

/-- The record of a process after normalizing. -/
theorem State.record_normalize {state : State} (sorted : state.Sorted) (processId : PID) :
    state.normalize.record processId =
      ((state.record processId).map (state.normalizeRecord processId)).filter (!·.finished) := by
  simp only [State.normalize, State.record, Kernel.map_eq, Kernel.filter_eq, Kernel.lookup_eq]
  have mapped : Lynx.Concurrent.Sorted (state.processes.map fun record =>
      (record.1, state.normalizeRecord record.1 record.2)) := List.pairwise_map.mpr (sorted.imp id)
  rw [mapped.lookup_filter, lookup_map_snd]

theorem State.normalizeRecord_exiting (state : State) (processId : PID) (process : ProcessState) :
    (state.normalizeRecord processId process).exiting.isSome = process.exiting.isSome := by
  unfold State.normalizeRecord; split <;> simp_all

theorem ProcessState.finished_exiting {process : ProcessState} (finished : process.finished = true) :
    process.exiting.isSome = true := by
  unfold ProcessState.finished at finished; split at finished <;> simp_all

/-- Normalizing leaves the same processes alive. -/
theorem State.alive_normalize {state : State} (sorted : state.Sorted) (processId : PID) :
    state.normalize.alive processId = state.alive processId := by
  simp only [State.alive, State.record_normalize sorted]
  cases found : state.record processId with
  | none => rfl
  | some process =>
    simp only [Option.map_some, Option.filter]
    have := state.normalizeRecord_exiting processId process
    split
    · cases exiting : process.exiting <;> simp_all
    · rename_i finished
      have := ProcessState.finished_exiting (by simpa using finished)
      cases exiting : process.exiting <;> simp_all

theorem State.gone_normalize {state : State} (sorted : state.Sorted) (processId : PID) :
    state.normalize.gone processId = state.gone processId := by
  simp [State.gone, State.alive_normalize sorted]

theorem lookup_filter_of_key {β : Type} {key : PID} {keep : PID × β → Bool} :
    ∀ {entries : List (PID × β)}, (∀ value, (key, value) ∈ entries → keep (key, value) = true) →
      (entries.filter keep).lookup key = entries.lookup key
  | [], _ => rfl
  | (key', value) :: rest, kept => by
      have rest' := lookup_filter_of_key (keep := keep) (entries := rest) fun value mem => kept value (by simp [mem])
      by_cases equal : key = key'
      · subst equal
        have := kept value (by simp)
        simp [List.filter_cons, this]
      · have differ : (key == key') = false := by simp [equal]
        simp only [List.filter_cons]
        split <;> simp [List.lookup_cons, differ, rest']

theorem State.answersEntry_congr {state other : State} (gone : ∀ processId, other.gone processId = state.gone processId) :
    other.answersEntry = state.answersEntry := by
  funext entry; simp [State.answersEntry, gone]

/-- A normalized record stays the same when normalized again. -/
theorem State.normalizeRecord_normalize {state : State} (sorted : state.Sorted) {processId : PID}
    {process : ProcessState} (mem : (processId, process) ∈ state.processes)
    (kept : (state.normalizeRecord processId process).finished = false) :
    state.normalize.normalizeRecord processId (state.normalizeRecord processId process) =
      state.normalizeRecord processId process := by
  have gone := State.gone_normalize sorted
  have found : state.process processId = process := by
    simp [State.process, State.record, Kernel.lookup_eq, Lynx.Concurrent.Sorted.lookup_of_mem sorted mem]
  have found' : state.normalize.process processId = state.normalizeRecord processId process := by
    simp only [State.process, State.record_normalize sorted]
    simp [State.record, Kernel.lookup_eq, Lynx.Concurrent.Sorted.lookup_of_mem sorted mem, Option.filter, kept]
  generalize normalized : state.normalize = next at gone found'
  unfold State.normalizeRecord
  cases exiting : process.exiting with
  | some exiting' =>
    simp only [Kernel.filter_eq, State.answersEntry_congr gone, List.filter_filter, Bool.and_self, gone]
  | none =>
    simp only [Kernel.filter_eq]
    congr 1
    · refine List.filter_eq_self.mpr fun entry mem => ?_
      have keep := (List.mem_filter.mp mem).2
      simp only [State.keepEntry, State.inertEntry, State.allocated, found, found', exiting,
        Option.isSome_none, Bool.false_and, Bool.or_false, Bool.not_eq_eq_eq_not, Bool.not_true] at keep ⊢
      simp only [State.normalizeRecord, exiting, gone, Kernel.filter_eq, Kernel.lookup_eq] at keep ⊢
      split <;> simp_all
      rw [lookup_filter_of_key fun value _ => by simp_all]
      simp_all
    · simp only [gone, List.filter_filter, Bool.and_self]

/-- Normalizing twice is normalizing once. -/
theorem State.normalize_normalize {state : State} (sorted : state.Sorted) :
    state.normalize.normalize = state.normalize := by
  have records : ∀ record ∈ state.normalize.processes,
      (record.1, state.normalize.normalizeRecord record.1 record.2) = record ∧ record.2.finished = false := by
    intro record mem
    have mem' := mem
    simp only [State.normalize, Kernel.map_eq, Kernel.filter_eq, List.mem_filter, List.mem_map] at mem'
    obtain ⟨⟨original, inside, rfl⟩, kept⟩ := mem'
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at kept
    exact ⟨by rw [State.normalizeRecord_normalize sorted inside kept], kept⟩
  generalize state.normalize = next at records ⊢
  cases next with
  | mk processes timers elapsed =>
    simp only [State.normalize, Kernel.map_eq, Kernel.filter_eq, State.mk.injEq, and_true]
    rw [List.map_congr_left fun record mem => (records record mem).1, List.map_id']
    exact List.filter_eq_self.mpr fun record mem => by simp [(records record mem).2]

/-! ### Every configuration is normalized -/

/-- A running configuration whose state normalizing leaves as it is. A run that
a process did not return from has no steps, and its state is not normalized. -/
def Config.Normalized : Config α → Prop
  | .running state _ _ false => state.normalize = state
  | _ => True

theorem State.normalize_initial (env : Environment) (elapsed : PID → Nat → Nat) :
    (State.initial env elapsed).normalize = State.initial env elapsed := by
  simp [State.initial, State.normalize, State.normalizeRecord, ProcessState.finished, Kernel.map_eq,
    Kernel.filter_eq]

/-- Every step leads to a normalized configuration. -/
theorem Config.Normalized.step {config next : Config α} {event : Event} (sorted : config.Within elapsed)
    (step : Step config event next) : next.Normalized := by
  cases config with
  | start env computation elapsed =>
    simp only [Step, Config.successors] at step
    split at step
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · split at step
      · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step
        exact State.normalize_initial _ _
      · simp at step
  | running state tasks finished exhausted =>
    have sorted : state.Within elapsed := sorted
    cases exhausted
    case true => simp [Step, Config.successors] at step
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with ((⟨before, processId, task, after, -, transition, possible, same⟩ |
      ⟨processId, process, -, phased⟩) | ⟨processId, process, -, unparked⟩) | ⟨timer, -, fired⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      have : transition.state.Within elapsed := by
        simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
        rcases possible with possible | possible
        · exact sorted.own possible
        · exact sorted.handleStep possible
      unfold Transition.apply
      split
      · trivial
      · exact State.normalize_normalize this.1
    · obtain ⟨next', phase, same⟩ := phased
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      exact State.normalize_normalize (sorted.phases phase).1
    · cases parked : (state.process processId).parked with
      | none => simp [parked] at unparked
      | some _ =>
        simp only [parked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at unparked
        obtain ⟨-, rfl⟩ := unparked
        exact State.normalize_normalize (sorted.unpark _).1
    · simp only [Prod.mk.injEq] at fired
      obtain ⟨-, rfl⟩ := fired
      exact State.normalize_normalize (sorted.fire _).1

/-! ### What a step continues with -/

/-- Two transitions that leave the same processes and outcome, whatever their states. -/
def Transition.Shape (transition transition' : Transition α) : Prop :=
  transition.tasks = transition'.tasks ∧ transition.finished = transition'.finished ∧
    transition.exhausted = transition'.exhausted

/-- Two lists of transitions, pairwise of the same shape. -/
def Transition.Shapes : List (Transition α) → List (Transition α) → Prop
  | [], [] => True
  | transition :: rest, transition' :: rest' => transition.Shape transition' ∧ Transition.Shapes rest rest'
  | _, _ => False

theorem Transition.Shape.refl_of {transition transition' : Transition α} (tasks : transition.tasks = transition'.tasks)
    (finished : transition.finished = transition'.finished) (exhausted : transition.exhausted = transition'.exhausted) :
    transition.Shape transition' := ⟨tasks, finished, exhausted⟩

theorem Environment.eq_of_identical {first second : Environment}
    (same : environmentIdentical first second = true) : first = second := by
  obtain ⟨pid, counter, pdict⟩ := first
  obtain ⟨pid', counter', pdict'⟩ := second
  simp only [environmentIdentical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨rfl, rfl⟩, same⟩ := same
  rw [Term.eq_of_identicalEntries same]

theorem selectMessage_value {select : Term → Option β} :
    ∀ {mailbox : List Term} {message : Term} {value : β} {rest : List Term},
      selectMessage select mailbox = some (message, value, rest) → select message = some value
  | [], _, _, _, found => by simp [selectMessage] at found
  | head :: tail, message, value, rest, found => by
      simp only [selectMessage] at found
      split at found
      · rename_i value' selected
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, -⟩ := found
        exact selected
      · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at found
        obtain ⟨_, _, _, found, rfl, rfl, -⟩ := found
        exact selectMessage_value found

theorem State.spawnWith_child (state : State) (processId : PID) (options : SpawnOptions) :
    (state.spawnWith processId options).1 = Kernel.append processId [(state.process processId).children + 1] := by
  unfold State.spawnWith; dsimp only

/-- A request that continues with a computation continues with the same one in every state. -/
theorem State.request_continue {state state' answered answered' : State} {processId : PID}
    {next : Term → Result β} {query : Request} {computation computation' : Result β}
    (continued : state.request processId next query = .continue computation answered)
    (continued' : state'.request processId next query = .continue computation' answered') :
    computation = computation' := by
  cases query <;> simp only [State.request] at continued continued' <;>
    (repeat' split at continued) <;> (repeat' split at continued') <;>
    simp_all

theorem Wait.eq_of_identical {first second : Wait} (same : first.identical second = true) : first = second := by
  cases first <;> cases second <;> simp only [Wait.identical, beq_iff_eq, Bool.false_eq_true] at same <;>
    first | rfl | rw [Term.eq_of_identical same] | rw [same]

/-- A process's own step leaves the same processes and outcome in two states
where it reads the same. -/
theorem Task.own_shape {state state' : State} {processId : PID} {task : Task α}
    (view : (task.ownView state processId).identical (task.ownView state' processId) = true)
    (elapsed : state.elapsed = state'.elapsed) :
    Transition.Shapes (task.own state processId) (task.own state' processId) := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own, Transition.Shapes]
  | none =>
    cases computation with
    | ok => simp [Task.own, Task.ended, Transition.Shape, Transition.Shapes]
    | error exception => cases exception <;> simp [Task.own, Task.ended, Transition.Shape, Transition.Shapes]
    | get next =>
      simp only [Task.ownView, OwnView.identical] at view
      simp [Task.own, Transition.Shape, Transition.Shapes, Environment.eq_of_identical view]
    | set => simp [Task.own, Transition.Shape, Transition.Shapes]
    | send => simp [Task.own, Transition.Shape, Transition.Shapes]
    | schedule options child next =>
      simp only [Task.ownView, OwnView.identical, beq_iff_eq] at view
      simp only [Task.own, Transition.Shapes, and_true, Transition.Shape, State.spawnWith_child, view]
    | receive timeout select next =>
      simp only [Task.ownView, OwnView.identical, Bool.and_eq_true] at view
      obtain ⟨⟨environment, message⟩, timesOut⟩ := view
      have environment := Environment.eq_of_identical environment
      have message := eq_of_optionIdentical Term.eq_of_identical message
      simp only [Task.own]
      rw [← environment] at message ⊢
      cases found : selectMessage (select (state.view processId)) (state.process processId).mailbox with
      | some result =>
        obtain ⟨selected, value, _⟩ := result
        rw [found] at message
        cases found' : selectMessage (select (state.view processId)) (state'.process processId).mailbox with
        | none => rw [found'] at message; simp at message
        | some result' =>
          obtain ⟨selected', value', _⟩ := result'
          rw [found'] at message
          simp only [Option.map_some, Option.some.injEq] at message
          subst message
          have := (selectMessage_value found).symm.trans (selectMessage_value found')
          simp only [Option.some.injEq] at this
          subst this
          simp [Transition.Shape, Transition.Shapes]
      | none =>
        rw [found] at message
        cases found' : selectMessage (select (state.view processId)) (state'.process processId).mailbox with
        | some _ => rw [found'] at message; simp at message
        | none =>
          simp only [found']
          cases timeout with
          | infinity => simp [Transition.Shapes]
          | immediate | finite =>
            have equal : Kernel.any (state.process processId).queue (state.awaitedEntry processId) =
                Kernel.any (state'.process processId).queue (state'.awaitedEntry processId) := by
              simpa using timesOut
            simp only [equal]
            split <;> simp [Transition.Shape, Transition.Shapes]
    | request query next =>
      cases query
      case cancelTimer reference =>
        simp only [Task.ownView, OwnView.identical, Bool.and_eq_true, beq_iff_eq] at view
        obtain ⟨duration, cancels⟩ := view
        simp only [Task.own, State.request, elapsed]
        cases found : Kernel.find? (·.reference == reference) state.timers <;>
          cases found' : Kernel.find? (·.reference == reference) state'.timers <;>
          rw [found, found'] at duration <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
            Option.some.injEq] at duration <;>
          simp [Transition.Shape, Transition.Shapes, duration, cancels]
      all_goals
        simp only [Task.ownView, OwnView.identical] at view
        simp only [Task.own]
        generalize found : state.request processId next _ = answer at view ⊢
        generalize found' : state'.request processId next _ = answer' at view ⊢
        cases answer <;> cases answer' <;>
          simp only [Answer.shape, Answer.Shape.identical, Bool.false_eq_true] at view <;>
          first
            | simp [Transition.Shape, Transition.Shapes, Term.eq_of_identical view]
            | simp [Transition.Shape, Transition.Shapes, Wait.eq_of_identical view]
            | simp [Transition.Shape, Transition.Shapes, State.request_continue found found']

/-- Handling a signal leaves the same processes and outcome in two states
where it reads the same. -/
theorem Task.handle_shape {state state' : State} {processId : PID} {task : Task α}
    (view : handleViewIdentical (task.handleView state processId) (task.handleView state' processId) = true) :
    Transition.Shapes (task.handle state processId) (task.handle state' processId) := by
  simp only [Task.handleView, Task.handle] at view ⊢
  cases queue : (state.process processId).queue <;> cases queue' : (state'.process processId).queue <;>
    simp only [queue, queue', handleViewIdentical, Bool.false_eq_true] at view ⊢
  · trivial
  · rename_i entry rest entry' rest'
    generalize (State.set state processId _).handle processId _ entry = result at view ⊢
    generalize (State.set state' processId _).handle processId _ entry' = result' at view ⊢
    obtain ⟨handled, resumed, exits⟩ := result
    obtain ⟨handled', resumed', exits'⟩ := result'
    simp only [Bool.and_eq_true] at view
    have exits := eq_of_optionIdentical Term.eq_of_identical view.1
    have resumed := eq_of_optionIdentical Term.eq_of_identical view.2
    subst exits; subst resumed
    dsimp only
    split
    · simp [Task.ended, Transition.Shape, Transition.Shapes]
    · split <;> simp [Transition.Shape, Transition.Shapes]

/-! ### Steps on the list of processes -/

/-- Replace the first task of a process by what a function of it gives. -/
def rewriteTask (processId : PID) (change : Task α → List (PID × Task α)) :
    List (PID × Task α) → List (PID × Task α)
  | [] => []
  | (other, task) :: rest =>
      if other = processId then change task ++ rest else (other, task) :: rewriteTask processId change rest

theorem rewriteTask_of_splitAt {processId : PID} {change : Task α → List (PID × Task α)} :
    ∀ {tasks before after : List (PID × Task α)} {task : Task α},
      splitAt processId tasks = some (before, task, after) →
        rewriteTask processId change tasks = before ++ change task ++ after
  | [], _, _, _, found => by simp [splitAt] at found
  | (other, task') :: rest, before, after, task, found => by
      simp only [splitAt] at found
      by_cases same : other = processId
      · subst same
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        simp [rewriteTask]
      · have differ : (other == processId) = false := by simp [same]
        simp only [differ, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff, Prod.exists,
          Prod.mk.injEq] at found
        obtain ⟨before', _, _, found, rfl, rfl, rfl⟩ := found
        simp [rewriteTask, same, rewriteTask_of_splitAt found]

theorem rewriteTask_append {processId : PID} {change : Task α → List (PID × Task α)}
    {front rest : List (PID × Task α)} (missing : ∀ entry ∈ front, entry.1 ≠ processId) :
    rewriteTask processId change (front ++ rest) = front ++ rewriteTask processId change rest := by
  induction front with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨other, task⟩ := head
    have differ : other ≠ processId := missing (other, task) (by simp)
    simp [rewriteTask, differ, ih fun entry mem => missing entry (by simp [mem])]

/-- Steps of two different processes rewrite the list of processes in either order alike. -/
theorem rewriteTask_comm {processId other : PID} (differ : processId ≠ other)
    {change change' : Task α → List (PID × Task α)}
    (missing : ∀ task, ∀ entry ∈ change task, entry.1 ≠ other)
    (missing' : ∀ task, ∀ entry ∈ change' task, entry.1 ≠ processId) :
    ∀ tasks : List (PID × Task α),
      rewriteTask other change' (rewriteTask processId change tasks) =
        rewriteTask processId change (rewriteTask other change' tasks)
  | [] => rfl
  | (key, task) :: rest => by
      by_cases first : key = processId
      · subst first
        simp only [rewriteTask, ↓reduceIte, differ, rewriteTask_append (missing task)]
      · by_cases second : key = other
        · subst second
          simp only [rewriteTask, ↓reduceIte, first, rewriteTask_append (missing' task)]
        · simp [rewriteTask, first, second, rewriteTask_comm differ missing missing' rest]

/-! ### Steps by key are steps -/

theorem splitAt_eq {processId : PID} : ∀ {tasks before after : List (PID × Task α)} {task : Task α},
    splitAt processId tasks = some (before, task, after) → tasks = before ++ (processId, task) :: after
  | [], _, _, _, found => by simp [splitAt] at found
  | (other, task') :: rest, before, after, task, found => by
      simp only [splitAt] at found
      split at found
      · rename_i same
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        simp [eq_of_beq same]
      · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at found
        obtain ⟨before', _, _, found, rfl, rfl, rfl⟩ := found
        simp [splitAt_eq found]

theorem State.mem_processes_of_record {state : State} {processId : PID} {process : ProcessState}
    (found : state.record processId = some process) : ∃ record, (processId, record) ∈ state.processes := by
  simp only [State.record, Kernel.lookup_eq] at found
  generalize state.processes = records at found ⊢
  induction records with
  | nil => simp at found
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    by_cases same : processId = key
    · subst same; exact ⟨value, by simp⟩
    · have differ : (processId == key) = false := by simp [same]
      simp only [List.lookup_cons, differ] at found
      obtain ⟨record, mem⟩ := ih found
      exact ⟨record, by simp [mem]⟩

theorem State.record_of_linkPhase {state next : State} {processId target : PID}
    (phase : state.linkPhase processId target = some next) :
    ∃ process, state.record processId = some process ∧ target ∈ state.exitLinks processId := by
  unfold State.linkPhase at phase
  split at phase
  · rename_i process found
    split at phase
    · rename_i exiting exits
      split at phase
      · rename_i mem
        refine ⟨process, found, ?_⟩
        simp only [State.exitLinks, State.process, found, Option.getD_some, exits]
        simpa [Kernel.contains_eq] using mem
      · simp at phase
    · simp at phase
  · simp at phase

theorem State.record_of_phase {state next : State} {processId : PID}
    (phase : state.phase processId = some next) : ∃ process, state.record processId = some process := by
  unfold State.phase at phase
  split at phase
  · rename_i process found; exact ⟨process, found⟩
  · simp at phase

/-- The step with a key is a step. -/
theorem Config.step_of_stepOf {config next : Config α} {key : Key} {event : Event}
    (found : config.stepOf key = some (event, next)) : Step config event next := by
  match config, key with
  | .start .., _ => simp [Config.stepOf] at found
  | .running _ _ _ true, _ => simp [Config.stepOf] at found
  | .running state tasks finished false, .own processId =>
    simp only [Config.stepOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨⟨before, task, after⟩, split, transition, head, rfl, rfl⟩ := found
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, List.mem_append,
      List.mem_flatMap, List.mem_map]
    refine .inl (.inl (.inl ⟨(before, (processId, task), after), by rw [splitAt_eq split]; exact mem_splits,
      transition, ?_, rfl⟩))
    simp only [Task.transitions, Kernel.append_eq, List.mem_append]
    exact .inl (List.mem_of_head? head)
  | .running state tasks finished false, .handle processId =>
    simp only [Config.stepOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨⟨before, task, after⟩, split, transition, head, rfl, rfl⟩ := found
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, List.mem_append,
      List.mem_flatMap, List.mem_map]
    refine .inl (.inl (.inl ⟨(before, (processId, task), after), by rw [splitAt_eq split]; exact mem_splits,
      transition, ?_, rfl⟩))
    simp only [Task.transitions, Kernel.append_eq, List.mem_append]
    exact .inr (List.mem_of_head? head)
  | .running state tasks finished false, .link processId target =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨next', phase, rfl, rfl⟩ := found
    obtain ⟨process, record, linked⟩ := State.record_of_linkPhase phase
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, List.mem_append,
      List.mem_flatMap, List.mem_map]
    refine .inl (.inl (.inr ⟨(processId, record'), mem, next', ?_, rfl⟩))
    simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap]
    exact .inl ⟨target, linked, phase⟩
  | .running state tasks finished false, .phase processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨next', phase, rfl, rfl⟩ := found
    obtain ⟨process, record⟩ := State.record_of_phase phase
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, List.mem_append,
      List.mem_flatMap, List.mem_map]
    refine .inl (.inl (.inr ⟨(processId, record'), mem, next', ?_, rfl⟩))
    simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap]
    exact .inr (by simp [phase])
  | .running state tasks finished false, .unpark processId =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨parked, found, rfl, rfl⟩ := found
    have record : ∃ process, state.record processId = some process := by
      cases record : state.record processId with
      | none => simp [State.process, record] at found
      | some process => exact ⟨process, rfl⟩
    obtain ⟨process, record⟩ := record
    obtain ⟨record', mem⟩ := State.mem_processes_of_record record
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_filterMap]
    exact .inl (.inr ⟨(processId, record'), mem, by simp [found]⟩)
  | .running state tasks finished false, .fire reference =>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
    obtain ⟨timer, found, rfl, rfl⟩ := found
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.map_eq, List.mem_append, List.mem_map]
    have equal := List.find?_some (by simpa [Kernel.find?_eq] using found)
    have mem := List.mem_of_find?_eq_some (by simpa [Kernel.find?_eq] using found)
    simp only [beq_iff_eq] at equal
    exact .inr ⟨timer, mem, by rw [equal]⟩

end Lynx.Concurrent
