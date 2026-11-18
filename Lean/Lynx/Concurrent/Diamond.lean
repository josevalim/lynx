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

end Lynx.Concurrent
