module

public import Lynx.Concurrent.Commute

/-! Foundations for proving that steps `checkSleep` takes as commuting reach
the same configuration in either order. States keep their records sorted by
PID, so two states are equal when they have the same record for every process
and the same timers (`Sorted.ext`). -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-! ### PID order -/

private theorem pidBefore_irrefl : ∀ processId : PID, pidBefore processId processId = false
  | [] => rfl
  | head :: rest => by simp [pidBefore, pidBefore_irrefl rest]

private theorem pidBefore_trans : ∀ {first second third : PID}, pidBefore first second = true →
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


private theorem pidBefore_total : ∀ {first second : PID}, first ≠ second →
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
private def Sorted (records : List (PID × ProcessState)) : Prop :=
  records.Pairwise fun first second => pidBefore first.1 second.1 = true

private theorem lookup_eq_none_of_before {processId : PID} {records : List (PID × ProcessState)}
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
private theorem Sorted.ext {first second : List (PID × ProcessState)} (sorted : Sorted first)
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

private theorem lookup_insertSorted (processId : PID) (process : ProcessState) :
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

private theorem lookup_filter_ne (processId other : PID) (records : List (PID × ProcessState)) :
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
private theorem State.record_set (state : State) (processId other : PID) (process : ProcessState) :
    (state.set processId process).record other =
      if other = processId then some process else state.record other := by
  simp only [State.set, State.record, insertRecord, Kernel.lookup_eq, Kernel.filter_eq]
  rw [lookup_insertSorted _ _ _ _ (by rw [lookup_filter_ne]; simp), lookup_filter_ne]
  by_cases equal : other = processId <;> simp [equal]

/-- The record of a process after another's is removed. -/
private theorem State.record_remove (state : State) (processId other : PID) :
    (state.remove processId).record other = if other = processId then none else state.record other := by
  simp only [State.remove, State.record, Kernel.lookup_eq, Kernel.filter_eq, lookup_filter_ne]

private theorem Sorted.filter {records : List (PID × ProcessState)} (sorted : Sorted records)
    (keep : PID × ProcessState → Bool) : Sorted (records.filter keep) :=
  List.Pairwise.filter keep sorted

private theorem mem_insertSorted {processId : PID} {process : ProcessState} {record : PID × ProcessState} :
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

private theorem Sorted.insertSorted {records : List (PID × ProcessState)} (sorted : Sorted records)
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

private theorem Sorted.insertRecord {records : List (PID × ProcessState)} (sorted : Sorted records)
    (processId : PID) (process : ProcessState) : Sorted (insertRecord processId process records) := by
  simp only [Lynx.Concurrent.insertRecord, Kernel.filter_eq]
  exact (sorted.filter _).insertSorted _ _ fun record mem => by
    have := (List.mem_filter.mp mem).2
    simpa using this

/-- Normalization keeps the records sorted. -/
private theorem Sorted.normalize {state : State} (sorted : Sorted state.processes) : Sorted state.normalize.processes := by
  simp only [State.normalize, Kernel.map_eq, Kernel.filter_eq]
  refine List.Pairwise.filter _ ?_
  exact List.pairwise_map.mpr (sorted.imp id)

/-! ### Every step keeps the records sorted and the time elapsed -/

/-- A state whose records are sorted. -/
private def State.Sorted (state : State) : Prop := Lynx.Concurrent.Sorted state.processes

variable {elapsed : PID → Nat → Nat}

/-- A state whose records are sorted, with the time elapsed when timers are
canceled, which no step changes. -/
private def State.Within (elapsed : PID → Nat → Nat) (state : State) : Prop :=
  state.Sorted ∧ state.elapsed = elapsed

private theorem State.Within.set {state : State} (sorted : state.Within elapsed) (processId : PID) (process : ProcessState) :
    (state.set processId process).Within elapsed :=
  ⟨Lynx.Concurrent.Sorted.insertRecord sorted.1 processId process, sorted.2⟩

private theorem State.Within.remove {state : State} (sorted : state.Within elapsed) (processId : PID) :
    (state.remove processId).Within elapsed := by
  simp only [State.Within, State.remove, Kernel.filter_eq]; exact ⟨Lynx.Concurrent.Sorted.filter sorted.1 _, sorted.2⟩

private theorem State.Within.modify {state : State} (sorted : state.Within elapsed) (processId : PID)
    (change : ProcessState → ProcessState) : (state.modify processId change).Within elapsed := by
  unfold State.modify; split
  · exact sorted.set _ _
  · exact sorted

private theorem State.Within.normalize {state : State} (sorted : state.Within elapsed) : state.normalize.Within elapsed :=
  ⟨Lynx.Concurrent.Sorted.normalize sorted.1, sorted.2⟩

private theorem State.Within.timers {state : State} (sorted : state.Within elapsed) (timers : List Timer) :
    ({ state with timers } : State).Within elapsed := sorted

/-- Prove that an operation built from replacing, changing and removing
records keeps them sorted. -/
local syntax "sorted_step" : tactic
macro_rules
  | `(tactic| sorted_step) => `(tactic| first
      | with_reducible assumption
      | with_reducible apply State.Within.set | with_reducible apply State.Within.remove
      | with_reducible apply State.Within.modify | with_reducible apply State.Within.normalize
      | with_reducible apply State.Within.allocate
      | refine State.Within.allocate ?_ _
      | split)

private theorem State.Within.allocate {state : State} (sorted : state.Within elapsed) (processId : PID) :
    (state.allocate processId).2.Within elapsed := sorted.modify _ _

private theorem State.Within.append {state : State} (sorted : state.Within elapsed) (processId : PID) (message : Term) :
    (state.append processId message).Within elapsed := sorted.modify _ _

private theorem State.Within.store {state : State} (sorted : state.Within elapsed) (processId : PID) (env : Environment) :
    (state.store processId env).Within elapsed := sorted.modify _ _

private theorem State.Within.fallback {state : State} (sorted : state.Within elapsed) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).Within elapsed := by
  unfold State.fallback; repeat sorted_step

private theorem State.Within.enqueue {state : State} (sorted : state.Within elapsed) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).Within elapsed := by
  unfold State.enqueue
  split
  · split
    · exact sorted.set _ _
    · exact sorted.fallback _ _ _
  · exact sorted.fallback _ _ _

private theorem State.Within.unpark {state : State} (sorted : state.Within elapsed) (processId : PID) :
    (state.unpark processId).Within elapsed := by
  unfold State.unpark; split
  · exact (sorted.modify _ _).enqueue _ _ _
  · exact sorted

private theorem State.Within.send {state : State} (sorted : state.Within elapsed) (source target : PID) (signal : Signal) :
    (state.send source target signal).Within elapsed := by
  unfold State.send
  apply State.Within.enqueue
  split
  · split
    · exact sorted.unpark _
    · exact sorted
  · exact sorted

private theorem State.Within.linkExit {state : State} (sorted : state.Within elapsed) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).Within elapsed := by
  unfold State.linkExit
  split
  · exact State.Within.modify sorted _ _
  · exact sorted.send _ _ _

private theorem State.Within.terminate {state : State} (sorted : state.Within elapsed) (processId : PID) (reason : Term) :
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

private theorem State.Within.answer {state : State} (sorted : state.Within elapsed) (processId : PID) (entry : Entry) :
    (state.answer processId entry).Within elapsed := by
  unfold State.answer; split <;> first | exact sorted.send _ _ _ | exact sorted

private theorem State.Within.linkPhase {state next : State} (sorted : state.Within elapsed) {processId target : PID}
    (phase : state.linkPhase processId target = some next) : next.Within elapsed := by
  unfold State.linkPhase at phase
  repeat' split at phase
  all_goals first
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).linkExit _ _ _)
    | simp at phase

private theorem State.Within.phase {state next : State} (sorted : state.Within elapsed) {processId : PID}
    (phase : state.phase processId = some next) : next.Within elapsed := by
  unfold State.phase at phase
  repeat' split at phase
  all_goals first
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).send _ _ _)
    | (simp only [Option.some.injEq] at phase; subst phase; exact (sorted.set _ _).answer _ _)
    | simp at phase

private theorem State.Within.phases {state next : State} (sorted : state.Within elapsed) {processId : PID}
    (mem : next ∈ state.phases processId) : next.Within elapsed := by
  simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at mem
  rcases mem with ⟨_, -, phase⟩ | mem
  · exact sorted.linkPhase phase
  · split at mem
    · rename_i found
      simp only [List.mem_singleton] at mem; subst mem
      exact sorted.phase found
    · simp at mem

private theorem State.Within.fire {state : State} (sorted : state.Within elapsed) (timer : Timer) : (state.fire timer).Within elapsed :=
  (sorted.timers _).enqueue _ _ _

private theorem State.Within.spawnWith {state : State} (sorted : state.Within elapsed) (processId : PID) (options : SpawnOptions) :
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
local syntax "sorted_exact" : tactic
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
private def Answer.state : Answer β → State
  | .reply _ state | .wait _ state | .continue _ state => state

private theorem State.Within.request {state : State} (sorted : state.Within elapsed) (processId : PID)
    (next : Term → Result β) (query : Request) : (state.request processId next query).state.Within elapsed := by
  cases query <;> simp only [State.request] <;> (repeat' split) <;> simp only [Answer.state] <;> sorted_exact

private theorem State.Within.exitSignal {state : State} (sorted : state.Within elapsed) (target source : PID) (reason : Term)
    (linked normalKills : Bool) : (state.exitSignal target source reason linked normalKills).1.Within elapsed := by
  unfold State.exitSignal; dsimp only; (repeat' split) <;> sorted_exact

private theorem State.Within.handle {state : State} (sorted : state.Within elapsed) (processId : PID) (waiting : Option Wait)
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

private theorem State.Within.ended {state : State} (sorted : state.Within elapsed) {γ : Type}
    (finish : Except Exception γ → Option (Except Exception α)) (event : Event) (processId : PID)
    (reason : Term) (result : Except Exception γ) :
    (Task.ended finish event state processId reason result).state.Within elapsed := sorted.terminate _ _

private theorem State.Within.own {state : State} (sorted : state.Within elapsed) {processId : PID} {task : Task α}
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

private theorem State.Within.handleStep {state : State} (sorted : state.Within elapsed) {processId : PID} {task : Task α}
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
private def Config.Within (elapsed : PID → Nat → Nat) : Config α → Prop
  | .start _ _ elapsed' => elapsed' = elapsed
  | .running state .. => state.Within elapsed

private theorem State.Within.initial (env : Environment) (elapsed : PID → Nat → Nat) :
    (State.initial env elapsed).Within elapsed :=
  ⟨by simp [State.Sorted, State.initial, Lynx.Concurrent.Sorted], rfl⟩

/-- Every step keeps the records sorted. -/
private theorem Config.Within.step {config next : Config α} {event : Event} (sorted : config.Within elapsed)
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
private theorem Config.Within.run {config last : Config α} {events : List Event} (sorted : config.Within elapsed)
    (run : Run config events last) : last.Within elapsed :=
  Run.invariant (fun _ _ _ sorted step => sorted.step step) run sorted

/-! ### Comparisons -/

private theorem Signal.eq_of_identical {first second : Signal} (same : first.identical second = true) :
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

private theorem eq_of_identicalLists {same : γ → γ → Bool}
    (sound : ∀ {first second}, same first second = true → first = second) :
    ∀ {first second : List γ}, identicalLists same first second = true → first = second
  | [], [], _ => rfl
  | head :: rest, head' :: rest', equal => by
    simp only [identicalLists, Bool.and_eq_true] at equal
    rw [sound equal.1, eq_of_identicalLists sound equal.2]
  | [], _ :: _, equal | _ :: _, [], equal => by simp [identicalLists] at equal

private theorem eq_of_optionIdentical {same : γ → γ → Bool}
    (sound : ∀ {first second}, same first second = true → first = second) :
    ∀ {first second : Option γ}, optionIdentical same first second = true → first = second
  | some _, some _, equal => by rw [sound equal]
  | none, none, _ => rfl
  | some _, none, equal | none, some _, equal => by simp [optionIdentical] at equal

private theorem Entry.eq_of_identical {first second : Entry} (same : first.identical second = true) :
    first = second := by
  obtain ⟨source, signal⟩ := first
  obtain ⟨source', signal'⟩ := second
  simp only [Entry.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨rfl, same⟩ := same
  rw [Signal.eq_of_identical same]

private theorem Exiting.eq_of_identical {first second : Exiting} (same : first.identical second = true) :
    first = second := by
  obtain ⟨reason, links, downs⟩ := first
  obtain ⟨reason', links', downs'⟩ := second
  simp only [Exiting.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨same, rfl⟩, rfl⟩ := same
  rw [Term.eq_of_identical same]

private theorem ProcessState.eq_of_identical {first second : ProcessState} (same : first.identical second = true) :
    first = second := by
  cases first; cases second
  simp only [ProcessState.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨queue, mailbox⟩, pdict⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩, exiting⟩ := same
  rw [eq_of_identicalLists Entry.eq_of_identical queue, Term.eq_of_identicalList mailbox,
    Term.eq_of_identicalEntries pdict, eq_of_optionIdentical Exiting.eq_of_identical exiting]

private theorem Timer.eq_of_identical {first second : Timer} (same : first.identical second = true) :
    first = second := by
  obtain ⟨reference, destination, message, duration⟩ := first
  obtain ⟨reference', destination', message', duration'⟩ := second
  simp only [Timer.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨⟨rfl, rfl⟩, same⟩, rfl⟩ := same
  rw [Term.eq_of_identical same]

/-! ### Normalizing twice -/

private theorem lookup_map_snd (change : PID → ProcessState → ProcessState) (processId : PID) :
    ∀ records : List (PID × ProcessState),
      (records.map fun record => (record.1, change record.1 record.2)).lookup processId =
        (records.lookup processId).map (change processId)
  | [] => rfl
  | (key, value) :: rest => by
      by_cases equal : processId = key
      · subst equal; simp
      · have differ : (processId == key) = false := by simp [equal]
        simp [List.lookup_cons, differ, lookup_map_snd change processId rest]

private theorem Sorted.lookup_filter {records : List (PID × ProcessState)} (sorted : Sorted records)
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

private theorem Sorted.lookup_of_mem {records : List (PID × ProcessState)} (sorted : Sorted records)
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
private theorem State.record_normalize {state : State} (sorted : state.Sorted) (processId : PID) :
    state.normalize.record processId =
      ((state.record processId).map (state.normalizeRecord processId)).filter (!·.finished) := by
  simp only [State.normalize, State.record, Kernel.map_eq, Kernel.filter_eq, Kernel.lookup_eq]
  have mapped : Lynx.Concurrent.Sorted (state.processes.map fun record =>
      (record.1, state.normalizeRecord record.1 record.2)) := List.pairwise_map.mpr (sorted.imp id)
  rw [mapped.lookup_filter, lookup_map_snd]

private theorem State.normalizeRecord_exiting (state : State) (processId : PID) (process : ProcessState) :
    (state.normalizeRecord processId process).exiting.isSome = process.exiting.isSome := by
  unfold State.normalizeRecord; split <;> simp_all

private theorem ProcessState.finished_exiting {process : ProcessState} (finished : process.finished = true) :
    process.exiting.isSome = true := by
  unfold ProcessState.finished at finished; split at finished <;> simp_all

/-- Normalizing leaves the same processes alive. -/
private theorem State.alive_normalize {state : State} (sorted : state.Sorted) (processId : PID) :
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

private theorem State.gone_normalize {state : State} (sorted : state.Sorted) (processId : PID) :
    state.normalize.gone processId = state.gone processId := by
  simp [State.gone, State.alive_normalize sorted]

private theorem lookup_filter_of_key {β : Type} {key : PID} {keep : PID × β → Bool} :
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

private theorem State.answersEntry_congr {state other : State} (gone : ∀ processId, other.gone processId = state.gone processId) :
    other.answersEntry = state.answersEntry := by
  funext entry; simp [State.answersEntry, gone]

/-- A normalized record stays the same when normalized again. -/
private theorem State.normalizeRecord_normalize {state : State} (sorted : state.Sorted) {processId : PID}
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
private theorem State.normalize_normalize {state : State} (sorted : state.Sorted) :
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
private def Config.Normalized : Config α → Prop
  | .running state _ _ false => state.normalize = state
  | _ => True

private theorem State.normalize_initial (env : Environment) (elapsed : PID → Nat → Nat) :
    (State.initial env elapsed).normalize = State.initial env elapsed := by
  simp [State.initial, State.normalize, State.normalizeRecord, ProcessState.finished, Kernel.map_eq,
    Kernel.filter_eq]

/-- Every step leads to a normalized configuration. -/
private theorem Config.Normalized.step {config next : Config α} {event : Event} (sorted : config.Within elapsed)
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
private def Transition.Shape (transition transition' : Transition α) : Prop :=
  transition.tasks = transition'.tasks ∧ transition.finished = transition'.finished ∧
    transition.exhausted = transition'.exhausted

/-- Two lists of transitions, pairwise of the same shape. -/
private def Transition.Shapes : List (Transition α) → List (Transition α) → Prop
  | [], [] => True
  | transition :: rest, transition' :: rest' => transition.Shape transition' ∧ Transition.Shapes rest rest'
  | _, _ => False


private theorem Environment.eq_of_identical {first second : Environment}
    (same : environmentIdentical first second = true) : first = second := by
  obtain ⟨pid, counter, pdict⟩ := first
  obtain ⟨pid', counter', pdict'⟩ := second
  simp only [environmentIdentical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨rfl, rfl⟩, same⟩ := same
  rw [Term.eq_of_identicalEntries same]

private theorem selectMessage_value {select : Term → Option β} :
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

private theorem State.spawnWith_child (state : State) (processId : PID) (options : SpawnOptions) :
    (state.spawnWith processId options).1 = Kernel.append processId [(state.process processId).children + 1] := by
  unfold State.spawnWith; dsimp only

/-- A request that continues with a computation continues with the same one in every state. -/
private theorem State.request_continue {state state' answered answered' : State} {processId : PID}
    {next : Term → Result β} {query : Request} {computation computation' : Result β}
    (continued : state.request processId next query = .continue computation answered)
    (continued' : state'.request processId next query = .continue computation' answered') :
    computation = computation' := by
  cases query <;> simp only [State.request] at continued continued' <;>
    (repeat' split at continued) <;> (repeat' split at continued') <;>
    simp_all

private theorem Wait.eq_of_identical {first second : Wait} (same : first.identical second = true) : first = second := by
  cases first <;> cases second <;> simp only [Wait.identical, beq_iff_eq, Bool.false_eq_true] at same <;>
    first | rfl | rw [Term.eq_of_identical same] | rw [same]

/-- A process's own step leaves the same processes and outcome in two states
where it reads the same. -/
private theorem Task.own_shape {state state' : State} {processId : PID} {task : Task α}
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


/-! ### Steps on the list of processes -/

/-- Replace the first task of a process by what a function of it gives. -/
private def rewriteTask (processId : PID) (change : Task α → List (PID × Task α)) :
    List (PID × Task α) → List (PID × Task α)
  | [] => []
  | (other, task) :: rest =>
      if other = processId then change task ++ rest else (other, task) :: rewriteTask processId change rest

private theorem rewriteTask_of_splitAt {processId : PID} {change : Task α → List (PID × Task α)} :
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

private theorem rewriteTask_append {processId : PID} {change : Task α → List (PID × Task α)}
    {front rest : List (PID × Task α)} (missing : ∀ entry ∈ front, entry.1 ≠ processId) :
    rewriteTask processId change (front ++ rest) = front ++ rewriteTask processId change rest := by
  induction front with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨other, task⟩ := head
    have differ : other ≠ processId := missing (other, task) (by simp)
    simp [rewriteTask, differ, ih fun entry mem => missing entry (by simp [mem])]

/-- Steps of two different processes rewrite the list of processes in either order alike. -/
private theorem rewriteTask_comm {processId other : PID} (differ : processId ≠ other)
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

private theorem splitAt_eq {processId : PID} : ∀ {tasks before after : List (PID × Task α)} {task : Task α},
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

private theorem State.mem_processes_of_record {state : State} {processId : PID} {process : ProcessState}
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

private theorem State.record_of_linkPhase {state next : State} {processId target : PID}
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

private theorem State.record_of_phase {state next : State} {processId : PID}
    (phase : state.phase processId = some next) : ∃ process, state.record processId = some process := by
  unfold State.phase at phase
  split at phase
  · rename_i process found; exact ⟨process, found⟩
  · simp at phase

/-- The step with a key is a step. -/
private theorem Config.step_of_stepOf {config next : Config α} {key : Key} {event : Event}
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

/-! ### At most one process finishes the run -/

/-- Whether a process's result can reach the run's outcome. -/
private def Task.Finishes (task : Task α) : Prop := ∃ result, (task.finish result).isSome = true

/-- At most one process can finish the run: the root. -/
private def Config.FinishesOnce : Config α → Prop
  | .start .. => True
  | .running _ tasks _ _ => ∀ entry ∈ tasks, ∀ entry' ∈ tasks, entry.2.Finishes → entry'.2.Finishes →
      entry.1 = entry'.1

/-- What a transition leaves of a process that can finish the run is that process. -/
private def Transition.Keeps (processId : PID) (task : Task α) (transition : Transition α) : Prop :=
  ∀ entry ∈ transition.tasks, entry.2.Finishes → entry.1 = processId ∧ task.Finishes

private theorem Task.own_keeps {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.own state processId) : transition.Keeps processId task := by
  obtain ⟨computation, finish, wait⟩ := task
  intro entry inside finishes
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    cases computation with
    | ok => simp [Task.own, Task.ended] at mem; subst mem; simp at inside
    | error exception =>
      cases exception <;> simp [Task.own, Task.ended] at mem <;> subst mem <;> simp at inside
    | get | set | send =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      simp only [List.mem_singleton] at inside; subst inside
      exact ⟨rfl, finishes⟩
    | schedule =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact ⟨rfl, finishes⟩
      · obtain ⟨_, finishes⟩ := finishes; simp [Task.child] at finishes
    | receive =>
      simp only [Task.own] at mem
      (repeat' split at mem) <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;>
        simp only [List.mem_singleton] at inside <;> subst inside <;> exact ⟨rfl, finishes⟩
    | request =>
      simp only [Task.own] at mem
      split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;>
        simp only [List.mem_singleton] at inside <;> subst inside <;> exact ⟨rfl, finishes⟩

private theorem Task.handle_keeps {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.handle state processId) : transition.Keeps processId task := by
  intro entry inside finishes
  simp only [Task.handle] at mem
  split at mem
  · simp at mem
  · generalize (State.set _ _ _).handle _ _ _ = result at mem
    obtain ⟨_, resumed, exits⟩ := result
    dsimp only at mem
    split at mem
    · simp only [List.mem_singleton] at mem; subst mem; simp [Task.ended] at inside
    · split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;>
        simp only [List.mem_singleton] at inside <;> subst inside
      · exact ⟨rfl, finishes⟩
      · exact ⟨rfl, finishes⟩

/-- Every step keeps at most one process able to finish the run. -/
private theorem Config.FinishesOnce.step {config next : Config α} {event : Event} (once : config.FinishesOnce)
    (step : Step config event next) : next.FinishesOnce := by
  cases config with
  | start env computation elapsed =>
    simp only [Step, Config.successors] at step
    split at step
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step; trivial
    · split at step
      · simp only [List.mem_singleton, Prod.mk.injEq] at step; obtain ⟨-, rfl⟩ := step
        intro entry inside entry' inside' _ _
        simp only [List.mem_singleton] at inside inside'
        rw [inside, inside']
      · simp at step
  | running state tasks finished exhausted =>
    cases exhausted
    case true => simp [Step, Config.successors] at step
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with ((⟨before, processId, task, after, split, transition, possible, same⟩ |
      ⟨processId, process, -, phased⟩) | ⟨processId, process, -, unparked⟩) | ⟨timer, -, fired⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      have keeps : transition.Keeps processId task := by
        simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
        rcases possible with possible | possible
        · exact Task.own_keeps possible
        · exact Task.handle_keeps possible
      have split := eq_of_mem_splits split
      unfold Transition.apply
      split
      · intro _ inside; simp at inside
      · -- Every entry is one of the old ones, or the process's own, which could finish before.
        have origin : ∀ entry ∈ Kernel.append (Kernel.append before transition.tasks) after, entry.2.Finishes →
            ∃ old ∈ tasks, old.1 = entry.1 ∧ old.2.Finishes := by
          intro entry inside finishes
          simp only [Kernel.append_eq, List.mem_append] at inside
          rcases inside with (inside | inside) | inside
          · exact ⟨entry, by rw [split]; simp [inside], rfl, finishes⟩
          · obtain ⟨same, finishes'⟩ := keeps entry inside finishes
            exact ⟨(processId, task), by rw [split]; simp, same.symm, finishes'⟩
          · exact ⟨entry, by rw [split]; simp [inside], rfl, finishes⟩
        intro entry inside entry' inside' finishes finishes'
        obtain ⟨old, mem, same, finishes⟩ := origin entry inside finishes
        obtain ⟨old', mem', same', finishes'⟩ := origin entry' inside' finishes'
        rw [← same, ← same']
        exact once old mem old' mem' finishes finishes'
    · obtain ⟨_, _, same⟩ := phased
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      exact once
    · cases parked : (state.process processId).parked with
      | none => simp [parked] at unparked
      | some _ =>
        simp only [parked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at unparked
        obtain ⟨-, rfl⟩ := unparked
        exact once
    · simp only [Prod.mk.injEq] at fired
      obtain ⟨-, rfl⟩ := fired
      exact once

/-! ### What a step by key does to the processes -/

private theorem lookup_of_splitAt {processId : PID} : ∀ {tasks before after : List (PID × Task α)} {task : Task α},
    splitAt processId tasks = some (before, task, after) → Kernel.lookup processId tasks = some task
  | [], _, _, _, found => by simp [splitAt] at found
  | (other, task') :: rest, before, after, task, found => by
      simp only [splitAt] at found
      split at found
      · rename_i same
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        have : other = processId := eq_of_beq same
        subst this
        simp [Kernel.lookup_eq]
      · rename_i differ
        simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at found
        obtain ⟨_, _, _, found, -, rfl, -⟩ := found
        have := lookup_of_splitAt found
        have differ' : (processId == other) = false := by
          cases equal : processId == other
          · rfl
          · exact absurd (by rw [eq_of_beq equal]; exact beq_self_eq_true other) differ
        simpa [Kernel.lookup_eq, List.lookup_cons, differ'] using this

/-- What a process's own step does, by key. -/
private theorem Config.stepOf_own {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {processId : PID} {event : Event} {next : Config α}
    (found : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next)) :
    ∃ task transition, Kernel.lookup processId tasks = some task ∧
      (task.own state processId).head? = some transition ∧
      next = if transition.exhausted then .running transition.state [] finished true
        else .running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
          (transition.finished.orElse fun _ => finished) false := by
  simp only [Config.stepOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
  obtain ⟨⟨before, task, after⟩, split, transition, head, -, rfl⟩ := found
  refine ⟨task, transition, lookup_of_splitAt split, head, ?_⟩
  simp only [Transition.apply, Kernel.append_eq, rewriteTask_of_splitAt split, List.append_assoc]

/-- What handling a signal does, by key. -/
private theorem Config.stepOf_handle {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {processId : PID} {event : Event} {next : Config α}
    (found : (Config.running state tasks finished false).stepOf (.handle processId) = some (event, next)) :
    ∃ task transition, Kernel.lookup processId tasks = some task ∧
      (task.handle state processId).head? = some transition ∧
      next = if transition.exhausted then .running transition.state [] finished true
        else .running transition.state.normalize (rewriteTask processId (fun _ => transition.tasks) tasks)
          (transition.finished.orElse fun _ => finished) false := by
  simp only [Config.stepOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
  obtain ⟨⟨before, task, after⟩, split, transition, head, -, rfl⟩ := found
  refine ⟨task, transition, lookup_of_splitAt split, head, ?_⟩
  simp only [Transition.apply, Kernel.append_eq, rewriteTask_of_splitAt split, List.append_assoc]

/-- A step that is no process's own nor handling leaves the processes as they are. -/
private theorem Config.stepOf_keeps {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {key : Key} {event : Event} {next : Config α} (owner : key.owner = none)
    (found : (Config.running state tasks finished false).stepOf key = some (event, next)) :
    ∃ state', next = .running state' tasks finished false := by
  cases key <;> simp only [Key.owner, reduceCtorEq] at owner <;>
    simp only [Config.stepOf, Option.map_eq_some_iff, Prod.mk.injEq] at found <;>
    obtain ⟨_, _, -, rfl⟩ := found <;> exact ⟨_, rfl⟩

/-- How handling a signal changes its process, given what it reads and the process's task. -/
private def handleChange (processId : PID) (view : Option Term × Option Term) (task : Task α) : List (PID × Task α) :=
  match view.1 with
  | some _ => []
  | none =>
    match view.2, task with
    | some value, ⟨_, finish, some (_, next)⟩ => [(processId, ⟨next value, finish, none⟩)]
    | _, _ => [(processId, task)]

/-- The run's result handling a signal leaves, given what it reads and the process's task. -/
private def handleFinished (view : Option Term × Option Term) (task : Task α) : Option (Except Exception α) :=
  match view.1 with
  | some reason => task.finish (.error (.exit reason))
  | none => none

private theorem Task.handle_change {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.handle state processId) :
    ∃ view, task.handleView state processId = some view ∧
      transition.tasks = handleChange processId view task ∧
      transition.finished = handleFinished view task ∧ transition.exhausted = false := by
  simp only [Task.handle, Task.handleView] at mem ⊢
  cases queue : (state.process processId).queue with
  | nil => simp [queue] at mem
  | cons entry rest =>
    simp only [queue] at mem ⊢
    generalize (State.set _ _ _).handle _ _ _ = result at mem ⊢
    obtain ⟨_, resumed, exits⟩ := result
    dsimp only at mem ⊢
    refine ⟨(exits, resumed), rfl, ?_⟩
    obtain ⟨computation, finish, wait⟩ := task
    cases exits with
    | some reason =>
      simp only [List.mem_singleton] at mem; subst mem
      simp [Task.ended, handleChange, handleFinished]
    | none =>
      cases resumed <;> cases wait <;> simp only [List.mem_singleton] at mem <;> subst mem <;>
        simp [handleChange, handleFinished]

private theorem lookup_append_of_missing {β : Type _} {key : PID} {front rest : List (PID × β)}
    (missing : ∀ entry ∈ front, entry.1 ≠ key) : (front ++ rest).lookup key = rest.lookup key := by
  induction front with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨key', value⟩ := head
    have differ : (key == key') = false := by
      have := missing (key', value) (by simp); simp [Ne.symm this]
    simp [List.lookup_cons, differ, ih fun entry mem => missing entry (by simp [mem])]

private theorem lookup_rewriteTask {processId other : PID} {change : Task α → List (PID × Task α)}
    (differ : other ≠ processId) (missing : ∀ task, ∀ entry ∈ change task, entry.1 ≠ other) :
    ∀ tasks : List (PID × Task α),
      Kernel.lookup other (rewriteTask processId change tasks) = Kernel.lookup other tasks
  | [] => rfl
  | (key, task) :: rest => by
      have ih := lookup_rewriteTask differ missing rest
      simp only [Kernel.lookup_eq] at ih ⊢
      by_cases same : key = processId
      · subst same
        have differ' : (other == key) = false := by simp [differ]
        simp only [rewriteTask, ↓reduceIte, List.lookup_cons, differ', lookup_append_of_missing (missing task)]
      · simp only [rewriteTask, same, ↓reduceIte, List.lookup_cons]
        split <;> simp_all

/-- Rewriting a process's task by itself leaves the list as it is. -/
private theorem rewriteTask_keep (processId : PID) :
    ∀ tasks : List (PID × Task α), rewriteTask processId (fun task => [(processId, task)]) tasks = tasks
  | [] => rfl
  | (key, task) :: rest => by
      by_cases same : key = processId
      · subst same; simp [rewriteTask]
      · simp [rewriteTask, same, rewriteTask_keep processId rest]

private theorem handleChange_pids {processId : PID} {view : Option Term × Option Term} {task : Task α} :
    ∀ entry ∈ handleChange processId view task, entry.1 = processId := by
  intro entry mem
  unfold handleChange at mem
  split at mem
  · simp at mem
  · split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> rfl

private theorem handleFinished_some {view : Option Term × Option Term} {task : Task α}
    (finished : (handleFinished view task).isSome = true) :
    handleChange processId view task = [] ∧ task.Finishes := by
  unfold handleFinished at finished
  unfold handleChange
  split at finished
  · rename_i reason found
    exact ⟨by simp [found], ⟨_, finished⟩⟩
  · simp at finished

/-- A process's own step leaves itself, and the child it spawns. -/
private theorem Task.own_pids {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.own state processId) :
    ∀ entry ∈ transition.tasks, entry.1 = processId ∨
      entry.1 = Kernel.append processId [(state.process processId).children + 1] ∧
        ∃ options child next, task.computation = .schedule options child next := by
  obtain ⟨computation, finish, wait⟩ := task
  intro entry inside
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    cases computation with
    | ok => simp [Task.own, Task.ended] at mem; subst mem; simp at inside
    | error exception =>
      cases exception <;> simp [Task.own, Task.ended] at mem <;> subst mem <;> simp at inside
    | get | set | send =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      simp only [List.mem_singleton] at inside; subst inside; exact .inl rfl
    | schedule options child next =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact .inl rfl
      · exact .inr ⟨State.spawnWith_child state processId options, options, child, next, rfl⟩
    | receive =>
      simp only [Task.own] at mem
      (repeat' split at mem) <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;>
        simp only [List.mem_singleton] at inside <;> subst inside <;> exact .inl rfl
    | request =>
      simp only [Task.own] at mem
      split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;>
        simp only [List.mem_singleton] at inside <;> subst inside <;> exact .inl rfl

/-- A process's own step that finishes the run ends the process. -/
private theorem Task.own_finished {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (mem : transition ∈ task.own state processId) (finished : transition.finished.isSome = true) :
    transition.tasks = [] ∧ task.Finishes := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at mem
  | none =>
    cases computation with
    | ok => simp [Task.own, Task.ended] at mem; subst mem; exact ⟨rfl, _, finished⟩
    | error exception =>
      cases exception <;> simp [Task.own, Task.ended] at mem <;> subst mem <;>
        first | exact ⟨rfl, _, finished⟩ | simp at finished
    | get | set | send | schedule =>
      simp only [Task.own, List.mem_singleton] at mem; subst mem; simp at finished
    | receive =>
      simp only [Task.own] at mem
      (repeat' split at mem) <;> simp only [List.mem_singleton, List.not_mem_nil] at mem <;> subst mem <;>
        simp at finished
    | request =>
      simp only [Task.own] at mem
      split at mem <;> simp only [List.mem_singleton] at mem <;> subst mem <;> simp at finished

/-! ### Steps as changes of the processes -/

/-- What a step does to the processes: it rewrites its process's task, and
sets the run's result from it. -/
private structure TaskChange (α : Type) : Type 1 where
  processId : PID
  change : Task α → List (PID × Task α)
  finish : Task α → Option (Except Exception α)

/-- The configuration a step leads to, by what it does to the processes: for a
step of no process, it leaves them as they are. -/
private def Config.Changes (config : Config α) (change : Option (TaskChange α)) (next : Config α) : Prop :=
  match config with
  | .running _ tasks finished false => ∃ state', match change with
    | none => next = .running state' tasks finished false
    | some change => ∃ task, Kernel.lookup change.processId tasks = some task ∧
        next = .running state' (rewriteTask change.processId change.change tasks)
          ((change.finish task).orElse fun _ => finished) false
  | _ => False

/-- What a process's own step does, given its transition. -/
private def Transition.change (processId : PID) (transition : Transition α) : TaskChange α :=
  ⟨processId, fun _ => transition.tasks, fun _ => transition.finished⟩

/-- What handling a signal does, given what it reads. -/
private def handleTaskChange (processId : PID) (view : Option Term × Option Term) : TaskChange α :=
  ⟨processId, handleChange processId view, handleFinished view⟩

private theorem Config.changes_own {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {processId : PID} {event : Event} {next : Config α} {task : Task α} {transition : Transition α}
    (found : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next))
    (lookup : Kernel.lookup processId tasks = some task) (head : (task.own state processId).head? = some transition)
    (exhausted : transition.exhausted = false) :
    (Config.running state tasks finished false).Changes (some (transition.change processId)) next := by
  obtain ⟨task', transition', lookup', head', rfl⟩ := Config.stepOf_own found
  rw [lookup] at lookup'; simp only [Option.some.injEq] at lookup'; subst lookup'
  rw [head] at head'; simp only [Option.some.injEq] at head'; subst head'
  exact ⟨transition.state.normalize, task, lookup, by simp [exhausted, Transition.change]⟩

private theorem rewriteTask_of_lookup {processId : PID} {change : Task α → List (PID × Task α)} {task : Task α} :
    ∀ {tasks : List (PID × Task α)}, Kernel.lookup processId tasks = some task →
      rewriteTask processId change tasks = rewriteTask processId (fun _ => change task) tasks
  | [], found => by simp [Kernel.lookup_eq] at found
  | (key, task') :: rest, found => by
      by_cases same : key = processId
      · subst same
        simp only [Kernel.lookup_eq, List.lookup_cons, beq_self_eq_true, Option.some.injEq] at found
        subst found
        simp [rewriteTask]
      · have differ : (processId == key) = false := by simp [Ne.symm same]
        simp only [Kernel.lookup_eq, List.lookup_cons, differ] at found
        simp [rewriteTask, same, rewriteTask_of_lookup (by simpa [Kernel.lookup_eq] using found)]

private theorem Config.changes_handle {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {processId : PID} {event : Event} {next : Config α}
    (found : (Config.running state tasks finished false).stepOf (.handle processId) = some (event, next)) :
    ∃ task view, Kernel.lookup processId tasks = some task ∧ task.handleView state processId = some view ∧
      (Config.running state tasks finished false).Changes (some (handleTaskChange processId view)) next := by
  obtain ⟨task, transition, lookup, head, rfl⟩ := Config.stepOf_handle found
  obtain ⟨view, read, tasks', finished', exhausted⟩ := Task.handle_change (List.mem_of_head? head)
  refine ⟨task, view, lookup, read, transition.state.normalize, task, lookup, ?_⟩
  simp [exhausted, tasks', finished', handleTaskChange, rewriteTask_of_lookup (change := handleChange processId view) lookup]

private theorem Config.changes_keeps {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {key : Key} {event : Event} {next : Config α} (owner : key.owner = none)
    (found : (Config.running state tasks finished false).stepOf key = some (event, next)) :
    (Config.running state tasks finished false).Changes none next := by
  obtain ⟨state', rfl⟩ := Config.stepOf_keeps owner found
  exact ⟨state', rfl⟩

private theorem Transition.Shapes.head {transitions transitions' : List (Transition α)}
    (shapes : Transition.Shapes transitions transitions') {transition : Transition α}
    (head : transitions.head? = some transition) :
    ∃ transition', transitions'.head? = some transition' ∧ transition.Shape transition' := by
  cases transitions with
  | nil => simp at head
  | cons first rest =>
    cases transitions' with
    | nil => simp [Transition.Shapes] at shapes
    | cons first' rest' =>
      simp only [List.head?_cons, Option.some.injEq] at head; subst head
      exact ⟨first', rfl, shapes.1⟩

/-- A process's own step makes the same change in two configurations where its
process has the same task and reads the same. -/
private theorem Config.changes_own_transfer {state state' : State} {tasks tasks' : List (PID × Task α)}
    {finished finished' : Option (Except Exception α)} {processId : PID} {event event' : Event}
    {next next' : Config α} {task : Task α}
    (found : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next))
    (found' : (Config.running state' tasks' finished' false).stepOf (.own processId) = some (event', next'))
    (lookup : Kernel.lookup processId tasks = some task) (lookup' : Kernel.lookup processId tasks' = some task)
    (view : (task.ownView state processId).identical (task.ownView state' processId) = true)
    (elapsed : state.elapsed = state'.elapsed) :
    ∃ transition, (task.own state processId).head? = some transition ∧
      (transition.exhausted = false →
        (Config.running state tasks finished false).Changes (some (transition.change processId)) next ∧
        (Config.running state' tasks' finished' false).Changes (some (transition.change processId)) next') ∧
      (transition.exhausted = true → next = .running transition.state [] finished true) := by
  obtain ⟨task₁, transition, lookup₁, head, equal⟩ := Config.stepOf_own found
  rw [lookup] at lookup₁; simp only [Option.some.injEq] at lookup₁; subst lookup₁
  obtain ⟨task₂, transition', lookup₂, head', equal'⟩ := Config.stepOf_own found'
  rw [lookup'] at lookup₂; simp only [Option.some.injEq] at lookup₂; subst lookup₂
  obtain ⟨transition'', head'', shape⟩ := (Task.own_shape view elapsed).head head
  rw [head'] at head''; simp only [Option.some.injEq] at head''; subst head''
  obtain ⟨tasksEqual, finishedEqual, exhaustedEqual⟩ := shape
  refine ⟨transition, head, fun exhausted => ⟨?_, ?_⟩, fun exhausted => by simp [equal, exhausted]⟩
  · exact Config.changes_own found lookup head exhausted
  · have : transition.change processId = transition'.change processId := by
      simp [Transition.change, tasksEqual, finishedEqual]
    rw [this]
    exact Config.changes_own found' lookup' head' (exhaustedEqual ▸ exhausted)

/-- Handling a signal makes the same change in two configurations where it reads the same. -/
private theorem Config.changes_handle_transfer {state state' : State} {tasks tasks' : List (PID × Task α)}
    {finished finished' : Option (Except Exception α)} {processId : PID} {event event' : Event}
    {next next' : Config α}
    (found : (Config.running state tasks finished false).stepOf (.handle processId) = some (event, next))
    (found' : (Config.running state' tasks' finished' false).stepOf (.handle processId) = some (event', next'))
    (view : (Config.running state tasks finished false).sameView (.running state' tasks' finished' false)
      (.handle processId) = true) :
    ∃ task view, Kernel.lookup processId tasks = some task ∧ task.handleView state processId = some view ∧
      (Config.running state tasks finished false).Changes (some (handleTaskChange processId view)) next ∧
      (Config.running state' tasks' finished' false).Changes (some (handleTaskChange processId view)) next' := by
  obtain ⟨task, read, lookup, reads, changes⟩ := Config.changes_handle found
  obtain ⟨task', read', lookup', reads', changes'⟩ := Config.changes_handle found'
  simp only [Config.sameView, lookup, lookup', reads, reads', handleViewIdentical] at view
  obtain ⟨exits, resumed⟩ := read
  obtain ⟨exits', resumed'⟩ := read'
  simp only [Bool.and_eq_true] at view
  have exitsEqual := eq_of_optionIdentical Term.eq_of_identical view.1
  have resumedEqual := eq_of_optionIdentical Term.eq_of_identical view.2
  subst exitsEqual; subst resumedEqual
  exact ⟨task, _, lookup, reads, changes, changes'⟩

private theorem orElse_comm_of_not_both {first second : Option γ} {rest : Option γ}
    (notBoth : first.isSome = true → second.isSome = true → False) :
    (second.orElse fun _ => first.orElse fun _ => rest) = (first.orElse fun _ => second.orElse fun _ => rest) := by
  cases first <;> cases second <;> simp_all

/-- Two steps of different processes, in either order, leave the same
processes and result, when at most one of them sets the result. -/
private theorem Config.changes_comm {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {change change' : TaskChange α} {next next' last last' : Config α}
    (first : (Config.running state tasks finished false).Changes (some change) next)
    (second : (Config.running state tasks finished false).Changes (some change') next')
    (after : next.Changes (some change') last) (after' : next'.Changes (some change) last')
    (differ : change.processId ≠ change'.processId)
    (missing : ∀ task, ∀ entry ∈ change.change task, entry.1 ≠ change'.processId)
    (missing' : ∀ task, ∀ entry ∈ change'.change task, entry.1 ≠ change.processId)
    (once : ∀ task task', Kernel.lookup change.processId tasks = some task →
      Kernel.lookup change'.processId tasks = some task' →
      (change.finish task).isSome = true → (change'.finish task').isSome = true → False) :
    ∃ tasks' finished' state₁ state₂, last = .running state₁ tasks' finished' false ∧
      last' = .running state₂ tasks' finished' false := by
  obtain ⟨state₁, task, lookup, rfl⟩ := first
  obtain ⟨state₂, task', lookup', rfl⟩ := second
  obtain ⟨state₃, task₃, lookup₃, rfl⟩ := after
  obtain ⟨state₄, task₄, lookup₄, rfl⟩ := after'
  rw [lookup_rewriteTask (Ne.symm differ) missing, lookup'] at lookup₃
  simp only [Option.some.injEq] at lookup₃; subst lookup₃
  rw [lookup_rewriteTask differ missing', lookup] at lookup₄
  simp only [Option.some.injEq] at lookup₄; subst lookup₄
  refine ⟨_, _, state₃, state₄, rfl, ?_⟩
  rw [rewriteTask_comm differ missing missing', orElse_comm_of_not_both (once task task' lookup lookup')]

/-- A step of no process and a step of a process, in either order, leave the
same processes and result. -/
private theorem Config.changes_comm_keeps {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {change : TaskChange α} {next next' last last' : Config α}
    (first : (Config.running state tasks finished false).Changes (some change) next)
    (second : (Config.running state tasks finished false).Changes none next')
    (after : next.Changes none last) (after' : next'.Changes (some change) last') :
    ∃ tasks' finished' state₁ state₂, last = .running state₁ tasks' finished' false ∧
      last' = .running state₂ tasks' finished' false := by
  obtain ⟨state₁, task, lookup, rfl⟩ := first
  obtain ⟨state₂, rfl⟩ := second
  obtain ⟨state₃, rfl⟩ := after
  obtain ⟨state₄, task₄, lookup₄, rfl⟩ := after'
  rw [lookup] at lookup₄; simp only [Option.some.injEq] at lookup₄; subst lookup₄
  exact ⟨_, _, state₃, state₄, rfl, rfl⟩

/-- Two steps of no process, in either order, leave the processes and result. -/
private theorem Config.changes_comm_none {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {next next' last last' : Config α}
    (first : (Config.running state tasks finished false).Changes none next)
    (second : (Config.running state tasks finished false).Changes none next')
    (after : next.Changes none last) (after' : next'.Changes none last') :
    ∃ tasks' finished' state₁ state₂, last = .running state₁ tasks' finished' false ∧
      last' = .running state₂ tasks' finished' false := by
  obtain ⟨_, rfl⟩ := first
  obtain ⟨_, rfl⟩ := second
  obtain ⟨state₃, rfl⟩ := after
  obtain ⟨state₄, rfl⟩ := after'
  exact ⟨_, _, state₃, state₄, rfl, rfl⟩

/-! ### Facts the commutation proof uses -/

private theorem Config.stepOf_exhausted {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} (key : Key) :
    (Config.running state tasks finished true).stepOf key = none := by
  cases key <;> rfl

private theorem Config.running_of_stepOf {config : Config α} {key : Key} {step : Event × Config α}
    (found : config.stepOf key = some step) :
    ∃ state tasks finished, config = .running state tasks finished false := by
  match config with
  | .start .. => simp [Config.stepOf] at found
  | .running _ _ _ true => simp [Config.stepOf_exhausted] at found
  | .running state tasks finished false => exact ⟨state, tasks, finished, rfl⟩

private theorem State.handle_not_waiting (state : State) (processId : PID) (entry : Entry) :
    (state.handle processId none entry).2.1 = none := by
  obtain ⟨source, signal⟩ := entry
  cases signal <;> simp only [State.handle] <;> (try split) <;> rfl

private theorem Task.handleView_not_waiting {state : State} {processId : PID} {task : Task α}
    {view : Option Term × Option Term} (waiting : task.wait = none)
    (read : task.handleView state processId = some view) : view.2 = none := by
  simp only [Task.handleView, waiting, Option.map_none] at read
  split at read
  · simp at read
  · simp only [Option.some.injEq] at read
    rw [← read]
    exact State.handle_not_waiting _ _ _

private theorem handleChange_keep {processId : PID} {exits : Option Term} :
    exits = none → handleChange (α := α) processId (exits, none) = fun task => [(processId, task)] := by
  intro none'; subst none'
  funext task
  obtain ⟨_, _, wait⟩ := task
  cases wait <;> rfl

private theorem mem_of_lookup {β : Type _} {processId : PID} {value : β} :
    ∀ {entries : List (PID × β)}, Kernel.lookup processId entries = some value → (processId, value) ∈ entries
  | [], found => by simp [Kernel.lookup_eq] at found
  | (key, value') :: rest, found => by
      by_cases same : processId = key
      · subst same
        simp only [Kernel.lookup_eq, List.lookup_cons, beq_self_eq_true, Option.some.injEq] at found
        subst found; simp
      · have differ : (processId == key) = false := by simp [same]
        simp only [Kernel.lookup_eq, List.lookup_cons, differ] at found
        exact List.mem_cons_of_mem _ (mem_of_lookup (by simpa [Kernel.lookup_eq] using found))

private theorem lookup_eq_none_of_missing {β : Type _} {key : PID} :
    ∀ {entries : List (PID × β)}, (∀ entry ∈ entries, entry.1 ≠ key) → entries.lookup key = none
  | [], _ => rfl
  | (key', value) :: rest, missing => by
      have differ : (key == key') = false := by
        have := missing (key', value) (by simp); simp [Ne.symm this]
      have rest' : ∀ entry ∈ rest, entry.1 ≠ key := fun entry mem => missing entry (List.mem_cons_of_mem _ mem)
      simp only [List.lookup_cons, differ]
      exact lookup_eq_none_of_missing rest'

/-- No process has two tasks, as `Config.distinctTasks` checks. -/
private theorem distinct_of_distinctTasks {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (distinct : (Config.running state tasks finished exhausted).distinctTasks = true) :
    tasks.Pairwise fun entry entry' => entry.1 ≠ entry'.1 := by
  simp only [Config.distinctTasks, Kernel.all_eq, List.all_eq_true, Kernel.any_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.any_eq_false, beq_iff_eq, Prod.forall] at distinct
  induction tasks with
  | nil => exact .nil
  | cons head rest ih =>
    refine List.pairwise_cons.mpr ⟨fun entry mem same => ?_, ih fun before key task after mem' => ?_⟩
    · obtain ⟨before, after, rfl⟩ := List.append_of_mem mem
      have := distinct (head :: before) entry.1 entry.2 after (by
        have := mem_splits (before := head :: before) (item := entry) (after := after)
        simpa using this) head.1 head.2 (by simp)
      exact this same
    · intro other task' inside
      refine distinct (head :: before) key task after ?_ other task' (List.mem_cons_of_mem _ inside)
      simp only [splits, Kernel.map_eq, List.mem_cons, List.mem_map]
      exact .inr ⟨(before, (key, task), after), mem', rfl⟩

/-- In a list where no process has two tasks, a process whose task is removed has none. -/
private theorem lookup_rewriteTask_remove {processId : PID} :
    ∀ {tasks : List (PID × Task α)}, tasks.Pairwise (fun entry entry' => entry.1 ≠ entry'.1) →
      Kernel.lookup processId (rewriteTask processId (fun _ => []) tasks) = none
  | [], _ => rfl
  | (key, task) :: rest, distinct => by
      have above := List.pairwise_cons.mp distinct
      by_cases same : key = processId
      · subst same
        simp only [rewriteTask, ↓reduceIte, List.nil_append, Kernel.lookup_eq]
        exact lookup_eq_none_of_missing fun entry mem => (above.1 entry mem).symm
      · simp only [rewriteTask, same, ↓reduceIte, Kernel.lookup_eq, List.lookup_cons]
        have differ : (processId == key) = false := by simp [Ne.symm same]
        simpa [differ, Kernel.lookup_eq] using lookup_rewriteTask_remove above.2

/-! ### Own steps for the commutation proof -/

/-- A process's own step that another step can follow does not stop the run. -/
private theorem Config.own_step {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {processId : PID} {event : Event} {next : Config α} {key : Key} {step : Event × Config α}
    (found : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next))
    (more : next.stepOf key = some step) :
    ∃ task transition, Kernel.lookup processId tasks = some task ∧ task.wait = none ∧
      (task.own state processId).head? = some transition ∧ transition.exhausted = false ∧
      (Config.running state tasks finished false).Changes (some (transition.change processId)) next := by
  obtain ⟨task, transition, lookup, head, equal⟩ := Config.stepOf_own found
  have waiting : task.wait = none := by
    obtain ⟨_, _, wait⟩ := task
    cases wait
    · rfl
    · simp [Task.own] at head
  have exhausted : transition.exhausted = false := by
    cases exhausted : transition.exhausted
    · rfl
    · simp only [exhausted, ↓reduceIte] at equal; subst equal
      simp [Config.stepOf_exhausted] at more
  exact ⟨task, transition, lookup, waiting, head, exhausted, Config.changes_own found lookup head exhausted⟩

/-- A process's own step makes the change it makes at a configuration in
another where its process has the same task and it reads the same. -/
private theorem Config.own_transfer {state state' : State} {tasks tasks' : List (PID × Task α)}
    {finished finished' : Option (Except Exception α)} {processId : PID} {event event' : Event}
    {next next' : Config α} {task : Task α} {transition : Transition α}
    (found : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next))
    (found' : (Config.running state' tasks' finished' false).stepOf (.own processId) = some (event', next'))
    (lookup : Kernel.lookup processId tasks = some task) (lookup' : Kernel.lookup processId tasks' = some task)
    (head : (task.own state processId).head? = some transition) (exhausted : transition.exhausted = false)
    (view : (Config.running state tasks finished false).sameView (.running state' tasks' finished' false)
      (.own processId) = true)
    (elapsed : state.elapsed = state'.elapsed) :
    (Config.running state' tasks' finished' false).Changes (some (transition.change processId)) next' := by
  simp only [Config.sameView, lookup, lookup'] at view
  obtain ⟨transition', head', changes, -⟩ := Config.changes_own_transfer found found' lookup lookup' view elapsed
  rw [head] at head'; simp only [Option.some.injEq] at head'; subst head'
  exact (changes exhausted).2

/-- The tasks a process's own step leaves are its own and a child no process has yet. -/
private theorem Config.own_missing {state : State} {tasks : List (PID × Task α)} {finished : Option (Except Exception α)}
    {processId other : PID} {task task' : Task α} {transition : Transition α}
    (fresh : (Config.running state tasks finished false).spawnsFresh (.own processId) = true)
    (lookup : Kernel.lookup processId tasks = some task) (waiting : task.wait = none)
    (head : (task.own state processId).head? = some transition)
    (differ : processId ≠ other) (present : Kernel.lookup other tasks = some task') :
    ∀ entry ∈ transition.tasks, entry.1 ≠ other := by
  intro entry mem same
  rcases Task.own_pids (List.mem_of_head? head) entry mem with mine | ⟨child, options, spawned, next, schedule⟩
  · exact differ (mine.symm.trans same)
  · obtain ⟨computation, finish, wait⟩ := task
    simp only at waiting schedule
    rw [waiting, schedule] at lookup
    simp only [Config.spawnsFresh, lookup, Kernel.any_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.any_eq_false, beq_iff_eq] at fresh
    exact fresh (other, task') (mem_of_lookup present) (by rw [← same, child])

private theorem Config.own_finishes {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (head : (task.own state processId).head? = some transition)
    (finished : ((transition.change processId).finish task).isSome = true) : task.Finishes :=
  (Task.own_finished (List.mem_of_head? head) finished).2

private theorem handleFinishes {processId : PID} {view : Option Term × Option Term} {task : Task α}
    (finished : ((handleTaskChange processId view).finish task).isSome = true) : task.Finishes :=
  (handleFinished_some (processId := processId) finished).2

private theorem State.eq_of_identical {first second : State} (same : first.identical second = true)
    (elapsed : first.elapsed = second.elapsed) : first = second := by
  obtain ⟨processes, timers, elapsed₁⟩ := first
  obtain ⟨processes', timers', elapsed₂⟩ := second
  simp only [State.identical, Bool.and_eq_true] at same elapsed
  have records := eq_of_identicalLists (same := fun record record' : PID × ProcessState =>
      record.1 == record'.1 && record.2.identical record'.2) (fun {record record'} equal => by
    obtain ⟨key, value⟩ := record
    obtain ⟨key', value'⟩ := record'
    simp only [Bool.and_eq_true, beq_iff_eq] at equal
    rw [equal.1, ProcessState.eq_of_identical equal.2]) same.1
  rw [records, eq_of_identicalLists Timer.eq_of_identical same.2, elapsed]

/-- The owners of two keys that `Config.commutesAfter` lets commute. -/
private theorem Key.owners_differ {processId other : PID}
    (owners : (!((some processId).isSome && some processId == some other && true)) = true) : processId ≠ other := by
  intro same; subst same; simp at owners

/-- A process's own step and another step that `Config.commutesAfter` compares
in both orders leave the same processes and result. -/
private theorem Config.processes_own {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {processId : PID} {other : Key} {event event' event₃ event₄ : Event}
    {next next' last last' : Config α}
    (within : state.Within elapsed) (once : (Config.running state tasks finished false).FinishesOnce)
    (owners : (!((some processId).isSome && some processId == other.owner && true == other.isOwn)) = true)
    (fresh : (Config.running state tasks finished false).spawnsFresh (.own processId) = true)
    (fresh' : (Config.running state tasks finished false).spawnsFresh other = true)
    (distinct : (Config.running state tasks finished false).distinctTasks = true)
    (step : (Config.running state tasks finished false).stepOf (.own processId) = some (event, next))
    (step' : (Config.running state tasks finished false).stepOf other = some (event', next'))
    (after : next.stepOf other = some (event₃, last)) (after' : next'.stepOf (.own processId) = some (event₄, last'))
    (view : (Config.running state tasks finished false).sameView next' (.own processId) = true)
    (view' : (Config.running state tasks finished false).sameView next other = true) :
    ∃ tasks' finished' state₁ state₂, last = .running state₁ tasks' finished' false ∧
      last' = .running state₂ tasks' finished' false := by
  obtain ⟨task, transition, lookup, waiting, head, exhausted, changes⟩ := Config.own_step step after
  obtain ⟨state₁, tasks₁, finished₁, rfl⟩ := Config.running_of_stepOf after
  obtain ⟨state₂, tasks₂, finished₂, rfl⟩ := Config.running_of_stepOf after'
  have within₂ : state₂.Within elapsed :=
    Config.Within.step (config := .running state tasks finished false) within (Config.step_of_stepOf step')
  have elapsed₂ : state.elapsed = state₂.elapsed := within.2.trans within₂.2.symm
  have within₁ : state₁.Within elapsed :=
    Config.Within.step (config := .running state tasks finished false) within (Config.step_of_stepOf step)
  have elapsed₁ : state.elapsed = state₁.elapsed := within.2.trans within₁.2.symm
  have pairwise := distinct_of_distinctTasks distinct
  cases other with
  | own other =>
    have differ : processId ≠ other := Key.owners_differ owners
    obtain ⟨task', transition', lookup', waiting', head', exhausted', changes'⟩ := Config.own_step step' after'
    have missing := Config.own_missing fresh lookup waiting head differ lookup'
    have missing' := Config.own_missing fresh' lookup' waiting' head' (Ne.symm differ) lookup
    have changes₂ := changes'
    obtain ⟨_, _, _, equal₂⟩ := changes₂
    simp only [Config.running.injEq] at equal₂
    obtain ⟨-, rfl, -, -⟩ := equal₂
    have changes₁ := changes
    obtain ⟨_, _, _, equal₁⟩ := changes₁
    simp only [Config.running.injEq] at equal₁
    obtain ⟨-, rfl, -, -⟩ := equal₁
    have stays : Kernel.lookup processId (rewriteTask other (fun _ => transition'.tasks) tasks) = some task := by
      rw [lookup_rewriteTask differ fun _ => missing', lookup]
    have stays' : Kernel.lookup other (rewriteTask processId (fun _ => transition.tasks) tasks) = some task' := by
      rw [lookup_rewriteTask (Ne.symm differ) fun _ => missing, lookup']
    exact Config.changes_comm changes changes'
      (Config.own_transfer step' after lookup' stays' head' exhausted' view' elapsed₁)
      (Config.own_transfer step after' lookup stays head exhausted view elapsed₂)
      differ (fun _ => missing) (fun _ => missing')
      (fun task task' found found' finishes finishes' => by
        simp only [Transition.change] at found found' finishes finishes'
        rw [lookup] at found; rw [lookup'] at found'
        simp only [Option.some.injEq] at found found'; subst found; subst found'
        exact differ (once _ (mem_of_lookup lookup) _ (mem_of_lookup lookup')
          (Config.own_finishes head finishes) (Config.own_finishes head' finishes')))
  | handle other =>
    obtain ⟨task', read, lookup', reads, changes', changes₁'⟩ :=
      Config.changes_handle_transfer step' after view'
    by_cases same : other = processId
    · subst same
      rw [lookup] at lookup'; simp only [Option.some.injEq] at lookup'; subst lookup'
      obtain ⟨exits, resumed⟩ := read
      have resumedNone : resumed = none := Task.handleView_not_waiting waiting reads
      subst resumedNone
      have changes₂ := changes'
      obtain ⟨_, _, _, equal₂⟩ := changes₂
      simp only [Config.running.injEq] at equal₂
      obtain ⟨-, rfl, rfl, -⟩ := equal₂
      have keep : ∀ exits : Option Term, exits = none →
          handleChange (α := α) other (exits, none) = fun task => [(other, task)] := fun _ => handleChange_keep
      cases exits with
      | some reason =>
        exfalso
        obtain ⟨_, _, found, -, -⟩ := Config.stepOf_own after'
        simp only [handleTaskChange] at found
        rw [rewriteTask_of_lookup lookup] at found
        simp only [handleChange] at found
        rw [lookup_rewriteTask_remove pairwise] at found
        simp at found
      | none =>
        have stays : Kernel.lookup other (rewriteTask (handleTaskChange (α := α) other (none, none)).processId
            (handleTaskChange other (none, none)).change tasks) = some task := by
          simp only [handleTaskChange, keep none rfl, rewriteTask_keep, lookup]
        have changes₂ := Config.own_transfer step after' lookup stays head exhausted view elapsed₂
        obtain ⟨_, _, _, equal₁⟩ := changes
        simp only [Config.running.injEq] at equal₁
        obtain ⟨rfl, rfl, rfl, -⟩ := equal₁
        obtain ⟨state₃, task₃, -, rfl⟩ := changes₁'
        obtain ⟨state₄, task₄, -, rfl⟩ := changes₂
        refine ⟨rewriteTask other (fun _ => transition.tasks) tasks,
          transition.finished.orElse fun _ => finished, state₃, state₄, ?_, ?_⟩
        · simp [handleTaskChange, keep none rfl, rewriteTask_keep, handleFinished, Transition.change]
        · simp [handleTaskChange, keep none rfl, rewriteTask_keep, handleFinished, Transition.change]
    · have differ : processId ≠ other := Ne.symm same
      have missing := Config.own_missing fresh lookup waiting head differ lookup'
      have missing' : ∀ task, ∀ entry ∈ (handleTaskChange (α := α) other read).change task, entry.1 ≠ processId :=
        fun _ entry mem => by
          rw [handleChange_pids entry mem]; exact same
      have stays : Kernel.lookup processId (rewriteTask other (handleTaskChange other read).change tasks) =
          some task := by rw [lookup_rewriteTask differ missing', lookup]
      have changes₂ := changes'
      obtain ⟨_, _, _, equal₂⟩ := changes₂
      simp only [Config.running.injEq] at equal₂
      obtain ⟨-, rfl, -, -⟩ := equal₂
      exact Config.changes_comm changes changes' changes₁'
        (Config.own_transfer step after' lookup stays head exhausted view elapsed₂)
        differ (fun _ => missing) missing'
        (fun task task' found found' finishes finishes' => by
          simp only [Transition.change, handleTaskChange] at found found' finishes
          rw [lookup] at found; rw [lookup'] at found'
          simp only [Option.some.injEq] at found found'; subst found; subst found'
          exact differ (once _ (mem_of_lookup lookup) _ (mem_of_lookup lookup')
            (Config.own_finishes head finishes) (handleFinishes finishes')))
  | link _ _ | phase _ | unpark _ | fire _ =>
    have keeps' := Config.changes_keeps rfl step'
    have keeps₁ := Config.changes_keeps rfl after
    have keeps₂ := keeps'
    obtain ⟨_, equal₂⟩ := keeps₂
    simp only [Config.running.injEq] at equal₂
    obtain ⟨-, rfl, rfl, -⟩ := equal₂
    exact Config.changes_comm_keeps changes keeps' keeps₁
      (Config.own_transfer step after' lookup lookup head exhausted view elapsed₂)

/-- Two steps that `Config.commutesAfter` compares in both orders leave the
same processes and result. -/
private theorem Config.processes_of_fallback {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key other : Key} {event event' event₃ event₄ : Event}
    {next next' last last' : Config α}
    (within : state.Within elapsed) (once : (Config.running state tasks finished false).FinishesOnce)
    (owners : (!(key.owner.isSome && key.owner == other.owner && key.isOwn == other.isOwn)) = true)
    (fresh : (Config.running state tasks finished false).spawnsFresh key = true)
    (fresh' : (Config.running state tasks finished false).spawnsFresh other = true)
    (distinct : (Config.running state tasks finished false).distinctTasks = true)
    (step : (Config.running state tasks finished false).stepOf key = some (event, next))
    (step' : (Config.running state tasks finished false).stepOf other = some (event', next'))
    (after : next.stepOf other = some (event₃, last)) (after' : next'.stepOf key = some (event₄, last'))
    (view : (Config.running state tasks finished false).sameView next' key = true)
    (view' : (Config.running state tasks finished false).sameView next other = true) :
    ∃ tasks' finished' state₁ state₂, last = .running state₁ tasks' finished' false ∧
      last' = .running state₂ tasks' finished' false := by
  have swap : ∀ {tasks' : List (PID × Task α)} {finished' : Option (Except Exception α)},
      (∃ state₁ state₂, last' = .running state₁ tasks' finished' false ∧
        last = .running state₂ tasks' finished' false) →
      ∃ tasks' finished' state₁ state₂, last = .running state₁ tasks' finished' false ∧
        last' = .running state₂ tasks' finished' false := fun ⟨state₁, state₂, first, second⟩ =>
    ⟨_, _, state₂, state₁, second, first⟩
  have swapped : (∃ tasks' finished' state₁ state₂, last' = .running state₁ tasks' finished' false ∧
      last = .running state₂ tasks' finished' false) → _ := fun ⟨_, _, state₁, state₂, first, second⟩ =>
    swap ⟨state₁, state₂, first, second⟩
  cases key with
  | own processId =>
    exact Config.processes_own within once owners fresh fresh' distinct step step' after after' view view'
  | handle processId =>
    cases other with
    | own other =>
      exact swapped (Config.processes_own within once (by simp [Key.owner, Key.isOwn]) fresh' fresh distinct
        step' step after' after view' view)
    | handle other =>
      have differ : processId ≠ other := by
        intro same; subst same; simp [Key.owner, Key.isOwn] at owners
      obtain ⟨_, _, _, rfl⟩ := Config.running_of_stepOf after'
      obtain ⟨_, _, _, rfl⟩ := Config.running_of_stepOf after
      obtain ⟨task, read, lookup, -, changes, changes₂⟩ := Config.changes_handle_transfer step after' view
      obtain ⟨task', read', lookup', -, changes', changes₁⟩ := Config.changes_handle_transfer step' after view'
      exact Config.changes_comm changes changes' changes₁ changes₂ differ
        (fun _ entry mem => by rw [handleChange_pids entry mem]; exact differ)
        (fun _ entry mem => by rw [handleChange_pids entry mem]; exact Ne.symm differ)
        (fun task task' found found' finishes finishes' => by
          simp only [handleTaskChange] at found found'
          rw [lookup] at found; rw [lookup'] at found'
          simp only [Option.some.injEq] at found found'; subst found; subst found'
          exact differ (once _ (mem_of_lookup lookup) _ (mem_of_lookup lookup')
            (handleFinishes finishes) (handleFinishes finishes')))
    | link _ _ | phase _ | unpark _ | fire _ =>
      have keeps' := Config.changes_keeps rfl step'
      obtain ⟨_, _, _, rfl⟩ := Config.running_of_stepOf after
      have keeps₁ := Config.changes_keeps rfl after
      have keeps₂ := keeps'
      obtain ⟨_, equal₂⟩ := keeps₂
      simp only [Config.running.injEq] at equal₂
      obtain ⟨rfl, rfl, rfl, -⟩ := equal₂
      obtain ⟨task, read, lookup, -, changes, changes₂⟩ := Config.changes_handle_transfer step after' view
      exact Config.changes_comm_keeps changes keeps' keeps₁ changes₂
  | link _ _ | phase _ | unpark _ | fire _ =>
    have keeps := Config.changes_keeps rfl step
    obtain ⟨_, _, _, rfl⟩ := Config.running_of_stepOf after'
    have keeps₂ := Config.changes_keeps rfl after'
    have keeps₁ := keeps
    obtain ⟨_, equal₁⟩ := keeps₁
    simp only [Config.running.injEq] at equal₁
    obtain ⟨rfl, rfl, rfl, -⟩ := equal₁
    cases other with
    | own other =>
      exact swapped (Config.processes_own within once (by simp [Key.owner]) fresh' fresh distinct
        step' step after' after view' view)
    | handle other =>
      obtain ⟨task, read, lookup, -, changes', changes₁⟩ := Config.changes_handle_transfer step' after view'
      exact swapped (Config.changes_comm_keeps changes' keeps keeps₂ changes₁)
    | link _ _ | phase _ | unpark _ | fire _ =>
      have keeps' := Config.changes_keeps rfl step'
      have keeps₁ := Config.changes_keeps rfl after
      exact Config.changes_comm_none keeps keeps' keeps₁ keeps₂

/-- Two steps that the evaluated comparison of `Config.commutesAfter` accepts
reach the same configuration in either order. -/
private theorem Config.commutes_of_fallback {state : State} {tasks : List (PID × Task α)}
    {finished : Option (Except Exception α)} {key other : Key} {event event' event₃ event₄ : Event}
    {next next' last last' : Config α}
    (within : state.Within elapsed) (once : (Config.running state tasks finished false).FinishesOnce)
    (owners : (!(key.owner.isSome && key.owner == other.owner && key.isOwn == other.isOwn)) = true)
    (fresh : (Config.running state tasks finished false).spawnsFresh key = true)
    (fresh' : (Config.running state tasks finished false).spawnsFresh other = true)
    (distinct : (Config.running state tasks finished false).distinctTasks = true)
    (step : (Config.running state tasks finished false).stepOf key = some (event, next))
    (step' : (Config.running state tasks finished false).stepOf other = some (event', next'))
    (after : next.stepOf other = some (event₃, last)) (after' : next'.stepOf key = some (event₄, last'))
    (view : (Config.running state tasks finished false).sameView next' key = true)
    (view' : (Config.running state tasks finished false).sameView next other = true)
    (same : last.sameAfter last' = true) : last = last' := by
  obtain ⟨tasks', finished', state₁, state₂, rfl, rfl⟩ :=
    Config.processes_of_fallback within once owners fresh fresh' distinct step step' after after' view view'
  have within₁ : state₁.Within elapsed := Config.Within.step (Config.Within.step (config :=
    .running state tasks finished false) within (Config.step_of_stepOf step)) (Config.step_of_stepOf after)
  have within₂ : state₂.Within elapsed := Config.Within.step (Config.Within.step (config :=
    .running state tasks finished false) within (Config.step_of_stepOf step')) (Config.step_of_stepOf after')
  simp only [Config.sameAfter, Bool.and_eq_true] at same
  rw [State.eq_of_identical same.2 (within₁.2.trans within₂.2.symm)]

end Lynx.Concurrent
