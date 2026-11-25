module

public import Lynx.Concurrent

/-! Every run ends. Each step of a process replaces its computation by what
follows it, possibly with a spawned child, starts waiting inside a request, or
ends the process. Every other step lowers the weight of the state: handling a
signal sends at most a lighter one, a phase of a process that ended sends at
most one signal, sending a parked monitor signal and firing a timer queue one
signal, and normalization only removes. So statements about the runs that can
no longer step cover every run. -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-- The steps a signal has left: requests are answered with one more signal. -/
@[expose] def Signal.weight : Signal → Nat
  | .link | .monitor _ | .isAlive | .unlink _ => 2
  | _ => 1

/-- The steps a record has left outside its process's own steps: its queued
signals, its parked monitor signal, and the phases of a process that ended. -/
@[expose] def ProcessState.weight (process : ProcessState) : Nat :=
  (process.queue.map (·.signal.weight)).sum + (if process.parked.isSome then 3 else 0) +
    match process.exiting with
    | some exiting => 2 * (exiting.links.length + exiting.downs.length) + 1
    | none => 0

/-- The weight of a list of records. -/
@[expose] def recordsWeight (records : List (PID × ProcessState)) : Nat := (records.map (·.2.weight)).sum

/-- The steps the records, the timers and the staged persistent term update
have left: a timer fires and its message is then handled, and an update
becomes visible. -/
@[expose] def State.weight (state : State) : Nat :=
  recordsWeight state.processes + 2 * state.timers.length + (if state.persistent.staged.isSome then 1 else 0)

/-! ### Records -/

theorem recordsWeight_cons (record : PID × ProcessState) (rest : List (PID × ProcessState)) :
    recordsWeight (record :: rest) = record.2.weight + recordsWeight rest := by
  simp [recordsWeight]

theorem recordsWeight_insertSorted (processId : PID) (process : ProcessState)
    (records : List (PID × ProcessState)) :
    recordsWeight (insertSorted processId process records) = process.weight + recordsWeight records := by
  induction records with
  | nil => simp [insertSorted, recordsWeight]
  | cons head rest ih =>
    simp only [insertSorted]
    split <;> simp only [recordsWeight_cons, ih] <;> omega

/-- Removing the records of a process removes at least the weight of the one it finds. -/
theorem recordsWeight_filter (processId : PID) (records : List (PID × ProcessState)) :
    recordsWeight (records.filter (·.1 != processId)) +
      ((records.lookup processId).map ProcessState.weight).getD 0 ≤ recordsWeight records := by
  induction records with
  | nil => simp [recordsWeight]
  | cons head rest ih =>
    obtain ⟨other, record⟩ := head
    by_cases same : other = processId
    · subst same
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.lookup_cons,
        beq_self_eq_true, Option.map_some, Option.getD_some, recordsWeight_cons]
      have : recordsWeight (rest.filter (·.1 != other)) ≤ recordsWeight rest := by
        have := ih; omega
      omega
    · have differ : (other != processId) = true := by simp [same]
      have differ' : (processId == other) = false := by simp [Ne.symm same]
      simp only [List.filter_cons, differ, ↓reduceIte, List.lookup_cons, differ', recordsWeight_cons]
      omega

/-- Replacing a record changes the weight by at most the difference of the two records. -/
theorem State.weight_set (state : State) (processId : PID) (process : ProcessState) :
    (state.set processId process).weight + (state.process processId).weight ≤
      state.weight + process.weight := by
  have filtered := recordsWeight_filter processId state.processes
  simp only [State.weight, State.set, insertRecord, Kernel.insertSorted_eq, recordsWeight_insertSorted, Kernel.filter_eq]
  simp only [State.process, State.record, Kernel.lookup_eq]
  cases found : state.processes.lookup processId with
  | none => simp only [found, Option.map_none, Option.getD_none] at filtered; simp [ProcessState.weight]; omega
  | some record => simp only [found, Option.map_some, Option.getD_some] at filtered; simp; omega


/-- A change that adds at most `extra` to a record adds at most that to the state. -/
theorem State.weight_modify (state : State) (processId : PID) (change : ProcessState → ProcessState)
    (lighter : ∀ process, (change process).weight ≤ process.weight + extra) :
    (state.modify processId change).weight ≤ state.weight + extra := by
  unfold State.modify
  split
  · rename_i process found
    have set := state.weight_set processId (change process)
    rw [show state.process processId = process by simp [State.process, found]] at set
    have := lighter process
    omega
  · omega

/-- A change that keeps a record's queue, parked signal and phases keeps the weight. -/
theorem State.weight_modify_same (state : State) (processId : PID) (change : ProcessState → ProcessState)
    (same : ∀ process, (change process).queue = process.queue ∧ (change process).parked = process.parked ∧
      (change process).exiting = process.exiting) :
    (state.modify processId change).weight ≤ state.weight := by
  have := state.weight_modify (extra := 0) processId change fun process => by
    obtain ⟨queue, parked, exiting⟩ := same process
    simp [ProcessState.weight, queue, parked, exiting]
  simpa using this

theorem State.weight_append (state : State) (processId : PID) (message : Term) :
    (state.append processId message).weight ≤ state.weight :=
  state.weight_modify_same processId _ fun _ => ⟨rfl, rfl, rfl⟩

/-- The weight of a queue. -/
@[expose] def queueWeight (queue : List Entry) : Nat := (queue.map (·.signal.weight)).sum

theorem ProcessState.weight_eq (process : ProcessState) :
    process.weight = queueWeight process.queue + (if process.parked.isSome then 3 else 0) +
      match process.exiting with
      | some exiting => 2 * (exiting.links.length + exiting.downs.length) + 1
      | none => 0 := rfl

/-- Adding a signal to a record's queue adds its weight. -/
theorem State.weight_push (state : State) (processId : PID) (entry : Entry) :
    (state.modify processId fun process => { process with queue := Kernel.append process.queue [entry] }).weight ≤
      state.weight + entry.signal.weight :=
  state.weight_modify processId _ fun process => by
    simp [ProcessState.weight_eq, queueWeight, Kernel.append_eq]; omega

/-- Queueing a signal adds at most its weight, as does falling back. -/
theorem State.weight_fallback (state : State) (source target : PID) (signal : Signal) :
    (state.fallback source target signal).weight ≤ state.weight + signal.weight := by
  unfold State.fallback
  split
  · refine Nat.le_trans (state.weight_push source _) ?_; simp [Signal.weight]
  · refine Nat.le_trans (state.weight_push source _) ?_; simp [Signal.weight]
  · have := state.weight_modify_same source
      (fun process => { process with links := Kernel.filter (·.1 != target) process.links })
      fun _ => ⟨rfl, rfl, rfl⟩
    omega
  · refine Nat.le_trans (state.weight_push source _) ?_; simp [Signal.weight]
  · omega

theorem State.weight_enqueue (state : State) (source target : PID) (signal : Signal) :
    (state.enqueue source target signal).weight ≤ state.weight + signal.weight := by
  unfold State.enqueue
  split
  · rename_i process found
    split
    · have set := state.weight_set target { process with queue := Kernel.append process.queue [{ source, signal }] }
      rw [show state.process target = process by simp [State.process, found]] at set
      have heavier : ({ process with queue := Kernel.append process.queue [{ source, signal }] } : ProcessState).weight =
          process.weight + signal.weight := by
        simp only [ProcessState.weight_eq, queueWeight, Kernel.append_eq, List.map_append, List.map_cons,
          List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
        omega
      omega
    · exact state.weight_fallback source target signal
  · exact state.weight_fallback source target signal

theorem State.weight_unpark (state : State) (processId : PID) :
    (state.unpark processId).weight + (if (state.process processId).parked.isSome then 1 else 0) ≤
      state.weight := by
  cases parked : (state.process processId).parked with
  | none => simp [State.unpark, parked]
  | some found =>
    obtain ⟨target, reference⟩ := found
    simp only [State.unpark, parked, Option.isSome_some, ↓reduceIte]
    have modified : (state.modify processId fun process => { process with parked := none }).weight + 3 ≤
        state.weight := by
      unfold State.modify
      split
      · rename_i process found
        have set := state.weight_set processId { process with parked := none }
        have equal : state.process processId = process := by simp [State.process, found]
        rw [equal] at set parked
        have lighter : ({ process with parked := none } : ProcessState).weight + 3 = process.weight := by
          simp only [ProcessState.weight_eq, parked, Option.isSome_some, ↓reduceIte, Option.isSome_none,
            Bool.false_eq_true]
          omega
        dsimp only
        omega
      · rename_i none
        simp only [State.record, Kernel.lookup_eq] at none
        simp [State.process, State.record, Kernel.lookup_eq, none] at parked
    have queued := (state.modify processId fun process => { process with parked := none }).weight_enqueue
      processId target (.monitor reference)
    simp only [Signal.weight] at queued
    omega

theorem State.weight_send (state : State) (source target : PID) (signal : Signal) :
    (state.send source target signal).weight ≤ state.weight + signal.weight := by
  have unparked := state.weight_unpark source
  have queued := state.weight_enqueue source target signal
  have queued' := (state.unpark source).weight_enqueue source target signal
  cases parked : (state.process source).parked with
  | none => simpa [State.send, parked] using queued
  | some found =>
    obtain ⟨other, reference⟩ := found
    by_cases same : other = target
    · simp only [State.send, parked, same, beq_self_eq_true, ↓reduceIte]; omega
    · have differ : (other == target) = false := by simp [same]
      simp only [State.send, parked, differ, Bool.false_eq_true, ↓reduceIte]; omega

/-! ### Normalization -/

theorem sum_filter_le (weight : γ → Nat) (keep : γ → Bool) (items : List γ) :
    ((items.filter keep).map weight).sum ≤ (items.map weight).sum := by
  induction items with
  | nil => simp
  | cons head rest ih => simp only [List.filter_cons]; split <;> simp <;> omega

theorem sum_map_le {first second : γ → Nat} (items : List γ) (le : ∀ item ∈ items, first item ≤ second item) :
    (items.map first).sum ≤ (items.map second).sum := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have := le head (by simp)
    have := ih fun item mem => le item (by simp [mem])
    omega

theorem ProcessState.weight_normalizeRecord (state : State) (processId : PID) (process : ProcessState) :
    (state.normalizeRecord processId process).weight ≤ process.weight := by
  have queue := sum_filter_le (·.signal.weight) (state.keepEntry processId process) process.queue
  have answers := sum_filter_le (·.signal.weight) state.answersEntry process.queue
  unfold State.normalizeRecord
  simp only [Kernel.filter_eq]
  split
  · rename_i exiting found
    have := List.length_filter_le (fun target => !state.gone target) exiting.links
    have := List.length_filter_le (fun down : List Nat × PID => !state.gone down.2) exiting.downs
    simp only [ProcessState.weight_eq, queueWeight, found]
    split <;> simp_all <;> omega
  · rename_i none
    simp only [ProcessState.weight_eq, queueWeight, none]
    omega

theorem State.weight_normalize (state : State) : state.normalize.weight ≤ state.weight := by
  simp only [State.normalize_eq, State.weight, recordsWeight, Kernel.map_eq, Kernel.filter_eq]
  have filtered := sum_filter_le (·.2.weight) (fun record : PID × ProcessState => !record.2.finished)
    (state.processes.map fun record => (record.1, state.normalizeRecord record.1 record.2))
  have mapped : ((state.processes.map fun record => (record.1, state.normalizeRecord record.1 record.2)).map
      (·.2.weight)).sum ≤ (state.processes.map (·.2.weight)).sum := by
    simp only [List.map_map]
    exact sum_map_le _ fun record _ => ProcessState.weight_normalizeRecord state record.1 record.2
  omega

/-! ### Steps -/

theorem State.weight_exitSignal (state : State) (target source : PID) (reason : Term) (linked normalKills : Bool) :
    (state.exitSignal target source reason linked normalKills).1.weight ≤ state.weight := by
  have links := state.weight_modify_same target
    (fun process => { process with links := Kernel.filter (·.1 != source) process.links }) fun _ => ⟨rfl, rfl, rfl⟩
  have appended := State.weight_append (state.modify target fun process =>
    { process with links := Kernel.filter (·.1 != source) process.links }) target
    (.tuple #[.atom "EXIT", .pid source, reason])
  have appended' := State.weight_append state target (.tuple #[.atom "EXIT", .pid source, reason])
  unfold State.exitSignal
  dsimp only
  repeat' split
  all_goals (dsimp only; omega)

/-- Handling a signal sends at most a lighter one. -/
theorem State.weight_handle (state : State) (processId : PID) (waiting : Option Wait) (entry : Entry) :
    (state.handle processId waiting entry).1.weight + 1 ≤ state.weight + entry.signal.weight := by
  obtain ⟨source, signal⟩ := entry
  have same := fun (change : ProcessState → ProcessState) (keeps : ∀ process, (change process).queue = process.queue ∧
      (change process).parked = process.parked ∧ (change process).exiting = process.exiting) =>
    state.weight_modify_same processId change keeps
  cases signal with
  | message message => have := state.weight_append processId message; simp [State.handle, Signal.weight]; omega
  | aliasMessage alias message =>
    have := state.weight_append processId message
    simp only [State.handle, Signal.weight]; split <;> (try dsimp only) <;> omega
  | exit reason linked normalKills =>
    have := state.weight_exitSignal processId source reason linked normalKills
    simp only [State.handle, Signal.weight]; omega
  | link =>
    have := same (fun process => { process with links := Kernel.append process.links [(source, none)] })
      fun _ => ⟨rfl, rfl, rfl⟩
    simp only [State.handle, Signal.weight]; split <;> (try dsimp only) <;> omega
  | unlink id =>
    have removed := same (fun process => { process with links := Kernel.filter (·.1 != source) process.links })
      fun _ => ⟨rfl, rfl, rfl⟩
    have sent := state.weight_send processId source (.unlinkAck id)
    have sent' := (state.modify processId fun process =>
      { process with links := Kernel.filter (·.1 != source) process.links }).weight_send processId source (.unlinkAck id)
    simp only [State.handle, Signal.weight] at *; split <;> (try dsimp only) <;> omega
  | unlinkAck id =>
    have := same (fun process => { process with links := Kernel.filter (fun link => !(link.1 == source && link.2 == some id)) process.links })
      fun _ => ⟨rfl, rfl, rfl⟩
    simp only [State.handle, Signal.weight]; split <;> (try dsimp only) <;> omega
  | monitor reference =>
    have := same (fun process => { process with monitors := Kernel.append process.monitors [(reference, source)] })
      fun _ => ⟨rfl, rfl, rfl⟩
    simp only [State.handle, Signal.weight]; omega
  | down reference reason =>
    have cleared := same (fun process => { process with eagerExits := Kernel.filter (· != source) process.eagerExits })
      fun _ => ⟨rfl, rfl, rfl⟩
    have removed := fun (base : State) => base.weight_modify_same processId (fun process => { process with
        monitoring := Kernel.filter (·.1 != reference) process.monitoring
        aliases := Kernel.erase process.aliases reference }) fun _ => ⟨rfl, rfl, rfl⟩
    have appended := fun (base : State) => State.weight_append (base.modify processId fun process => { process with
        monitoring := Kernel.filter (·.1 != reference) process.monitoring
        aliases := Kernel.erase process.aliases reference }) processId
      (.tuple #[.atom "DOWN", .reference reference, .atom "process", .pid source, reason])
    have := removed state
    have := appended state
    have := removed (state.modify processId fun process =>
      { process with eagerExits := Kernel.filter (· != source) process.eagerExits })
    have := appended (state.modify processId fun process =>
      { process with eagerExits := Kernel.filter (· != source) process.eagerExits })
    simp only [State.handle, Signal.weight]; (repeat' split) <;> (try dsimp only) <;> omega
  | isAlive =>
    have := state.weight_send processId source (.reply (.atom "true"))
    simp only [State.handle, Signal.weight] at *; omega
  | reply value => simp only [State.handle, Signal.weight]; split <;> (try dsimp only) <;> omega
  | flush => simp only [State.handle, Signal.weight]; split <;> (try dsimp only) <;> omega

theorem State.weight_answer (state : State) (processId : PID) (entry : Entry) :
    (state.answer processId entry).weight + 1 ≤ state.weight + entry.signal.weight := by
  obtain ⟨source, signal⟩ := entry
  cases signal with
  | link => have := state.weight_send processId source (.exit (.atom "noproc") true false)
            simp only [State.answer, Signal.weight] at *; omega
  | monitor reference => have := state.weight_send processId source (.down reference (.atom "noproc"))
                         simp only [State.answer, Signal.weight] at *; omega
  | isAlive => have := state.weight_send processId source (.reply (.atom "false"))
               simp only [State.answer, Signal.weight] at *; omega
  | _ => simp [State.answer, Signal.weight]

/-- A link exit sends at most one light signal. -/
theorem State.weight_linkExit (state : State) (processId target : PID) (reason : Term) :
    (state.linkExit processId target reason).weight ≤ state.weight + 1 := by
  have eager := fun (base : State) => base.weight_modify_same target
    (fun other => { other with
      links := Kernel.filter (·.1 != processId) other.links
      eagerExits := insertPid processId other.eagerExits })
    fun _ => ⟨rfl, rfl, rfl⟩
  have sent := state.weight_send processId target (.exit reason true false)
  simp only [Signal.weight] at sent
  unfold State.linkExit
  split
  · have := eager state; omega
  · omega

/-- A phase signaling a link lowers the weight. -/
theorem State.weight_linkPhase {state next : State} {processId target : PID}
    (phase : state.linkPhase processId target = some next) : next.weight < state.weight := by
  unfold State.linkPhase at phase
  split at phase
  · rename_i process found
    have equal : state.process processId = process := by simp [State.process, found]
    split at phase
    · rename_i exiting exits
      split at phase
      · rename_i mem
        simp only [Option.some.injEq] at phase; subst phase
        simp only [Kernel.contains_eq, List.elem_eq_mem, decide_eq_true_eq] at mem
        have shorter : (exiting.links.filter (· != target)).length < exiting.links.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨target, mem, by simp⟩
        have set := state.weight_set processId
          { process with exiting := some { exiting with links := Kernel.filter (· != target) exiting.links } }
        rw [equal] at set
        have lighter : ({ process with exiting := some { exiting with
            links := Kernel.filter (· != target) exiting.links } } : ProcessState).weight + 2 ≤ process.weight := by
          simp only [ProcessState.weight_eq, exits, Kernel.filter_eq]; omega
        have sent := (state.set processId { process with exiting := some { exiting with
          links := Kernel.filter (· != target) exiting.links } }).weight_linkExit processId target exiting.reason
        omega
      · simp at phase
    · simp at phase
  · simp at phase

/-- A phase sending a `DOWN` or answering a request lowers the weight. -/
theorem State.weight_phase {state next : State} {processId : PID} (phase : state.phase processId = some next) :
    next.weight < state.weight := by
  unfold State.phase at phase
  split at phase
  · rename_i process found
    have equal : state.process processId = process := by simp [State.process, found]
    split at phase
    · rename_i exiting exits
      have weight : process.weight = queueWeight process.queue + (if process.parked.isSome then 3 else 0) +
          (2 * (exiting.links.length + exiting.downs.length) + 1) := by
        simp [ProcessState.weight_eq, exits]
      split at phase
      · simp at phase
      · rename_i reference watcher rest links downs
        simp only [Option.some.injEq] at phase; subst phase
        have set := state.weight_set processId { process with exiting := some { exiting with downs := rest } }
        rw [equal] at set
        have lighter : ({ process with exiting := some { exiting with downs := rest } } : ProcessState).weight + 2 =
            process.weight := by
          simp [ProcessState.weight_eq, links, downs] at weight ⊢; omega
        have sent := (state.set processId { process with exiting := some { exiting with downs := rest } }).weight_send
          processId watcher (.down reference exiting.reason)
        simp only [Signal.weight] at sent; omega
      · split at phase
        · rename_i entry rest queue
          simp only [Option.some.injEq] at phase; subst phase
          have set := state.weight_set processId { process with queue := rest }
          rw [equal] at set
          have lighter : ({ process with queue := rest } : ProcessState).weight + entry.signal.weight =
              process.weight := by
            simp only [ProcessState.weight_eq, queueWeight, queue, List.map_cons, List.sum_cons]; omega
          have answered := (state.set processId { process with queue := rest }).weight_answer processId entry
          omega
        · simp at phase
    · simp at phase
  · simp at phase

/-- Every phase of a process that ended lowers the weight. -/
theorem State.weight_phases {state next : State} {processId : PID} (mem : next ∈ state.phases processId) :
    next.weight < state.weight := by
  simp only [State.phases, Kernel.append_eq, Kernel.filterMap_eq, List.mem_append, List.mem_filterMap] at mem
  rcases mem with ⟨target, -, phase⟩ | mem
  · exact state.weight_linkPhase phase
  · split at mem
    · rename_i found
      simp only [List.mem_singleton] at mem; subst mem
      exact state.weight_phase found
    · simp at mem

theorem mem_firstOfEach {seen : List (List Nat)} {timers : List Timer} {timer : Timer}
    (mem : timer ∈ firstOfEach seen timers) : timer ∈ timers := by
  induction timers generalizing seen with
  | nil => simp [firstOfEach] at mem
  | cons head rest ih =>
    simp only [firstOfEach, Kernel.contains_eq] at mem
    split at mem
    · exact List.mem_cons_of_mem _ (ih mem)
    · simp only [List.mem_cons] at mem
      rcases mem with rfl | mem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih mem)

/-- A timer firing lowers the weight. -/
theorem State.weight_fire {state : State} {timer : Timer} (mem : timer ∈ state.timers) :
    (state.fire timer).weight < state.weight := by
  have shorter : (state.timers.filter (·.reference != timer.reference)).length <
      state.timers.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨timer, mem, by simp⟩
  have queued := ({ state with timers := Kernel.filter (·.reference != timer.reference) state.timers } : State).weight_enqueue
    clock timer.destination (.message timer.message)
  simp only [State.fire, State.weight, Kernel.filter_eq, Signal.weight] at queued ⊢
  omega

/-- A staged persistent term update becoming visible lowers the weight. -/
theorem State.weight_commit {state : State} {update : Update} (staged : state.persistent.staged = some update) :
    state.commit.weight < state.weight := by
  simp only [State.commit, staged, State.weight, Option.isSome_some, Option.isSome_none, ↓reduceIte,
    Bool.false_eq_true]
  omega

/-! ### Processes -/

/-- A computation and what follows it: the continuation of its request, or a
child it spawns. A request may also continue with a receive that then
continues with it, or with an error. -/
private inductive Follows : (Σ β, Result β) → (Σ β, Result β) → Prop where
  | get : Follows ⟨β, next env⟩ ⟨β, .get next⟩
  | set : Follows ⟨β, next⟩ ⟨β, .set env next⟩
  | spawned : Follows ⟨β, next child⟩ ⟨β, Result.schedule options computation next⟩
  | child : Follows ⟨Term, computation⟩ ⟨β, Result.schedule options computation next⟩
  | send : Follows ⟨β, next⟩ ⟨β, .send destination message next⟩
  | receive : Follows ⟨β, next value⟩ ⟨β, .receive timeout select next⟩
  | request : Follows ⟨β, next reply⟩ ⟨β, .request query next⟩
  | requestReceive {γ : Type} {select : Environment → Term → Option γ} :
      Follows ⟨β, .receive timeout select fun _ => next reply⟩ ⟨β, .request query next⟩
  | requestError : Follows ⟨β, .error exception⟩ ⟨β, .request query next⟩
  /-- A persistent term update continues by waiting for it to become visible. -/
  | requestAwait (staging : query ≠ .persistentAwait) :
      Follows ⟨β, .request .persistentAwait fun _ => next reply⟩ ⟨β, .request query next⟩

/-- What follows a request does not depend on the request. -/
private theorem Follows.request_any {item : Σ β, Result β} {query query' : Request} {next : Term → Result β}
    (staging : query ≠ .persistentAwait) (follows : Follows item ⟨β, .request query' next⟩) :
    Follows item ⟨β, .request query next⟩ := by
  cases follows with
  | request => exact .request
  | requestReceive => exact .requestReceive
  | requestError => exact .requestError
  | requestAwait => exact .requestAwait staging

private theorem follows_acc {β : Type} (computation : Result β) :
    Acc Follows ⟨β, computation⟩ := by
  induction computation with
  | ok | error => exact ⟨_, fun _ follows => by cases follows⟩
  | get next ih => exact ⟨_, fun _ follows => by cases follows; exact ih _⟩
  | set env next ih => exact ⟨_, fun _ follows => by cases follows; exact ih⟩
  | schedule options child next childIh nextIh =>
    exact ⟨_, fun _ follows => by cases follows <;> first | exact nextIh _ | exact childIh⟩
  | send destination message next ih => exact ⟨_, fun _ follows => by cases follows; exact ih⟩
  | receive timeout select next ih => exact ⟨_, fun _ follows => by cases follows; exact ih _⟩
  | request query next ih =>
    refine ⟨_, fun _ follows => ?_⟩
    cases follows with
    | request => exact ih _
    | requestReceive => exact ⟨_, fun _ follows => by cases follows; exact ih _⟩
    | requestError => exact ⟨_, fun _ follows => by cases follows⟩
    | requestAwait =>
      refine ⟨_, fun _ follows => ?_⟩
      cases follows with
      | request => exact ih _
      | requestReceive => exact ⟨_, fun _ follows => by cases follows; exact ih _⟩
      | requestError => exact ⟨_, fun _ follows => by cases follows⟩
      | requestAwait staging => exact absurd rfl staging

/-- A process's computation, and whether it waits inside a request. A waiting
process continues with its request's continuation. -/
private inductive Below : (Σ β, Result β × Bool) → (Σ β, Result β × Bool) → Prop where
  | step {β β' : Type} {next : Result β'} {current : Result β} {waiting : Bool}
      (follows : Follows ⟨β', next⟩ ⟨β, current⟩) : Below ⟨β', (next, false)⟩ ⟨β, (current, waiting)⟩
  | waits {β : Type} {query query' : Request} {next : Term → Result β} {current : Result β}
      (request : current = .request query next) (staging : query ≠ .persistentAwait) :
      Below ⟨β, (.request query' next, true)⟩ ⟨β, (current, false)⟩

private theorem below_acc : ∀ (β : Type) (computation : Result β), Acc Follows ⟨β, computation⟩ →
    ∀ waiting, Acc Below ⟨β, (computation, waiting)⟩ := by
  intro β computation accessible
  generalize equal : (⟨β, computation⟩ : Σ β, Result β) = item at accessible
  induction accessible generalizing β computation with
  | intro item _ ih =>
    subst equal
    have below : ∀ {γ : Type} {next : Result γ}, Follows ⟨γ, next⟩ ⟨β, computation⟩ →
        ∀ waiting, Acc Below ⟨γ, (next, waiting)⟩ :=
      fun follows waiting => ih _ follows _ _ rfl waiting
    have waitingAcc : Acc Below ⟨β, (computation, true)⟩ := ⟨_, fun other below' => by
      cases below' with
      | step follows => exact below follows false⟩
    intro waiting
    cases waiting
    · refine ⟨_, fun other below' => ?_⟩
      cases below' with
      | step follows => exact below follows false
      | @waits _ query query' next _ request staging =>
        subst request
        exact ⟨_, fun other below' => by
          cases below' with
          | step follows => exact below (Follows.request_any (query := query) staging follows) false⟩
    · exact waitingAcc

/-- A process's computation, and whether it waits. -/
private def entry (item : PID × Task α) : Σ β, Result β × Bool :=
  ⟨item.2.β, match item.2.wait with
    | none => (item.2.computation, false)
    | some (_, next) => (.request (.alive []) next, true)⟩

/-- A request continuing with a computation continues with what follows it. -/
private theorem request_continue {state answered : State} {processId : PID} {next : Term → Result β}
    {query : Request} {computation : Result β}
    (continued : state.request processId next query = .continue computation answered) :
    Follows ⟨β, computation⟩ ⟨β, .request query next⟩ := by
  cases query <;> simp only [State.request, State.stage] at continued <;> (repeat' split at continued) <;>
    first
      | (simp only [Answer.continue.injEq] at continued; obtain ⟨rfl, -⟩ := continued
         first | exact .requestReceive | exact .requestError | exact .requestAwait (by simp))
      | simp at continued

/-- What a step of a process itself leaves follows it. -/
private theorem own_below {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (possible : transition ∈ task.own state processId) :
    ∀ item ∈ transition.tasks, Below (entry item) (entry (processId, task)) := by
  obtain ⟨computation, finish, wait⟩ := task
  cases wait with
  | some => simp [Task.own] at possible
  | none =>
    cases computation with
    | ok | error =>
      intro item mem
      simp only [Task.own] at possible
      (try split at possible) <;> simp_all [Task.ended]
    | get | set | send =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      simp only [List.mem_singleton, forall_eq, entry]; exact .step (by constructor)
    | schedule options child next =>
      simp only [Task.own, List.mem_singleton] at possible; subst possible
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, entry, Task.child]
      exact ⟨.step .spawned, .step .child⟩
    | receive timeout select next =>
      simp only [Task.own] at possible
      split at possible
      · simp only [List.mem_singleton] at possible; subst possible
        simp only [List.mem_singleton, forall_eq, entry]; exact .step .receive
      · split at possible <;> (try split at possible) <;> simp only [List.mem_singleton, List.not_mem_nil] at possible <;>
          subst possible <;> simp only [List.mem_singleton, forall_eq, entry] <;> exact .step .receive
    | request query next =>
      simp only [Task.own] at possible
      split at possible
      · simp only [List.mem_singleton] at possible; subst possible
        simp only [List.mem_singleton, forall_eq, entry]; exact .step .request
      · rename_i computation answered continued
        simp only [List.mem_singleton] at possible; subst possible
        simp only [List.mem_singleton, forall_eq, entry]; exact .step (request_continue continued)
      · rename_i waiting answered waited
        simp only [List.mem_singleton] at possible; subst possible
        simp only [List.mem_singleton, forall_eq, entry]
        refine .waits rfl ?_
        rintro rfl
        simp only [State.request] at waited
        repeat' split at waited
        all_goals simp at waited
      · simp at possible

/-- Handling a signal leaves the process as it is, resumes it, or ends it. -/
private theorem handle_tasks {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (possible : transition ∈ task.handle state processId) :
    (transition.tasks = [(processId, task)] ∧ transition.state.weight < state.weight) ∨
      (∀ item ∈ transition.tasks, Below (entry item) (entry (processId, task))) := by
  simp only [Task.handle] at possible
  split at possible
  · simp at possible
  · rename_i entry' rest queue
    have set := state.weight_set processId { state.process processId with queue := rest }
    have weighed := (state.set processId { state.process processId with queue := rest }).weight_handle
      processId (Option.map (·.1) task.wait) entry'
    have lighter : ({ state.process processId with queue := rest } : ProcessState).weight + entry'.signal.weight =
        (state.process processId).weight := by
      simp only [ProcessState.weight_eq, queueWeight, queue, List.map_cons, List.sum_cons]; omega
    generalize handled : (state.set processId { state.process processId with queue := rest }).handle processId
      (Option.map (·.1) task.wait) entry' = result at possible weighed
    obtain ⟨handledState, resumed, exits⟩ := result
    dsimp only at weighed set lighter
    split at possible
    · simp only [List.mem_singleton] at possible; subst possible
      exact .inr (by simp [Task.ended])
    · split at possible
      · rename_i value _ finish wait next
        simp only [List.mem_singleton] at possible; subst possible
        exact .inr (by simp only [List.mem_singleton, forall_eq, entry]; exact .step .request)
      · simp only [List.mem_singleton] at possible; subst possible
        refine .inl ⟨rfl, ?_⟩
        dsimp only
        omega

/-! ### Runs -/

/-- One item of a list replaced by any number of items below it. -/
private def Replaces (below : γ → γ → Prop) (next current : List γ) : Prop :=
  ∃ before item after replacement, current = before ++ item :: after ∧
    next = before ++ replacement ++ after ∧ ∀ new ∈ replacement, below new item

private theorem replaces_cons {below : γ → γ → Prop} {next rest : List γ} {head : γ}
    (replaces : Replaces below next (head :: rest)) :
    (∃ replacement, next = replacement ++ rest ∧ ∀ new ∈ replacement, below new head) ∨
      ∃ next', next = head :: next' ∧ Replaces below next' rest := by
  obtain ⟨before, item, after, replacement, current, rfl, smaller⟩ := replaces
  cases before with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at current
    obtain ⟨rfl, rfl⟩ := current
    exact .inl ⟨replacement, by simp, smaller⟩
  | cons first before =>
    simp only [List.cons_append, List.cons.injEq] at current
    obtain ⟨rfl, rfl⟩ := current
    exact .inr ⟨before ++ replacement ++ after, by simp, before, item, after, replacement, rfl, rfl,
      smaller⟩

/-- Replacing items by items below them, where nothing descends forever, ends. -/
private theorem replaces_acc {below : γ → γ → Prop} :
    ∀ items : List γ, (∀ item ∈ items, Acc below item) → Acc (Replaces below) items := by
  intro items
  induction items with
  | nil =>
    intro _
    refine ⟨_, fun next replaces => ?_⟩
    obtain ⟨before, item, after, -, current, -⟩ := replaces
    simp at current
  | cons head rest ih =>
    intro accessible
    have restAcc := ih fun item mem => accessible item (by simp [mem])
    suffices prepend : ∀ head, Acc below head → ∀ rest, Acc (Replaces below) rest →
        Acc (Replaces below) (head :: rest) from
      prepend head (accessible head (by simp)) rest restAcc
    intro head headAcc
    induction headAcc with
    | intro head _ headIh =>
      intro rest restAcc
      induction restAcc with
      | intro rest restSmaller restIh =>
        refine ⟨_, fun next replaces => ?_⟩
        rcases replaces_cons replaces with ⟨replacement, rfl, smaller⟩ | ⟨next', rfl, replaces'⟩
        · have : ∀ replacement : List γ, (∀ new ∈ replacement, below new head) →
              Acc (Replaces below) (replacement ++ rest) := by
            intro replacement smaller
            induction replacement with
            | nil => exact ⟨_, restSmaller⟩
            | cons new others ih =>
              exact headIh new (smaller new (by simp)) _
                (ih fun item mem => smaller item (by simp [mem]))
          exact this replacement smaller
        · exact restIh next' replaces'

/-- The processes' computations, and the weight of the state. -/
private def measure (state : State) (tasks : List (PID × Task α)) :
    List (Σ β, Result β × Bool) × Nat :=
  (tasks.map entry, state.weight)

private abbrev Lower : List (Σ β, Result β × Bool) × Nat → List (Σ β, Result β × Bool) × Nat → Prop :=
  Prod.Lex (Replaces Below) (· < ·)

/-- A step of a process replaces it by what follows it, or keeps it and lowers the weight. -/
private theorem process_step {state : State} {tasks before after : List (PID × Task α)}
    {processId : PID} {task : Task α} (split : tasks = before ++ (processId, task) :: after)
    {transition : Transition α} (possible : transition ∈ task.transitions state processId) :
    Lower (measure transition.state.normalize (Kernel.append (Kernel.append before transition.tasks) after))
      (measure state tasks) := by
  simp only [Task.transitions, Kernel.append_eq, List.mem_append] at possible
  have normalized := transition.state.weight_normalize
  rcases possible with possible | possible
  · exact .left _ _ ⟨before.map entry, entry (processId, task), after.map entry,
      transition.tasks.map entry, by simp [split], by simp, fun new mem => by
        simp only [List.mem_map] at mem
        obtain ⟨item, mem, rfl⟩ := mem
        exact own_below possible item mem⟩
  · rcases handle_tasks possible with ⟨same, lighter⟩ | below
    · have : (Kernel.append (Kernel.append before transition.tasks) after).map entry = tasks.map entry := by
        simp [split, same]
      simp only [measure, this]
      exact .right _ (by omega)
    · exact .left _ _ ⟨before.map entry, entry (processId, task), after.map entry,
        transition.tasks.map entry, by simp [split], by simp, fun new mem => by
          simp only [List.mem_map] at mem
          obtain ⟨item, mem, rfl⟩ := mem
          exact below item mem⟩

private theorem exhausted_acc (state : State) (tasks : List (PID × Task α)) (finished : Option (Except Exception α)) :
    Acc (fun next first => ∃ event, Step first event next) (Config.running state tasks finished true) :=
  ⟨_, fun _ ⟨_, step⟩ => by simp [Step, Config.successors] at step⟩

private theorem running_acc :
    ∀ (state : State) (tasks : List (PID × Task α)) (finished : Option (Except Exception α)) (exhausted : Bool),
      Acc (fun next first => ∃ event, Step first event next) (Config.running state tasks finished exhausted) := by
  intro state tasks finished exhausted
  cases exhausted
  case true => exact exhausted_acc state tasks finished
  have accessible : Acc Lower (measure state tasks) :=
    Prod.lexAccessible (replaces_acc _ fun (item : Σ β, Result β × Bool) _ =>
        below_acc item.1 item.2.1 (follows_acc _) item.2.2)
      (fun _ => Nat.lt_wfRel.wf.apply _) _
  generalize equal : measure state tasks = current at accessible
  induction accessible generalizing state tasks finished with
  | intro current _ ih =>
    refine ⟨_, fun next ⟨event, step⟩ => ?_⟩
    simp only [Step, Config.successors, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq,
      List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Prod.exists] at step
    rcases step with (((⟨before, processId, task, after, split, transition, possible, same⟩ |
      ⟨processId, process, mem, phased⟩) | ⟨processId, process, mem, unparked⟩) | ⟨timer, mem, fired⟩) |
      ⟨update, staged, committed⟩
    · simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      unfold Transition.apply
      split
      · exact exhausted_acc _ _ _
      · exact ih _ (equal ▸ process_step (eq_of_mem_splits split) possible) _ _ _ rfl
    · obtain ⟨next', phase, same⟩ := phased
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      have := state.weight_phases phase
      have := next'.weight_normalize
      exact ih _ (equal ▸ .right _ (by omega)) _ _ _ rfl
    · cases parked : (state.process processId).parked with
      | none => simp [parked] at unparked
      | some _ =>
        simp only [parked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at unparked
        obtain ⟨-, rfl⟩ := unparked
        have unparks := state.weight_unpark processId
        have := (state.unpark processId).weight_normalize
        simp only [parked, Option.isSome_some, ↓reduceIte] at unparks
        exact ih _ (equal ▸ .right _ (by omega)) _ _ _ rfl
    · simp only [Prod.mk.injEq] at fired
      obtain ⟨-, rfl⟩ := fired
      have := State.weight_fire (mem_firstOfEach mem)
      have := (state.fire timer).weight_normalize
      exact ih _ (equal ▸ .right _ (by omega)) _ _ _ rfl
    · simp only [Prod.mk.injEq] at committed
      obtain ⟨-, rfl⟩ := committed
      have := State.weight_commit (Option.mem_toList.mp staged)
      have := state.commit.weight_normalize
      exact ih _ (equal ▸ .right _ (by omega)) _ _ _ rfl

/-- No run goes on forever: steps are well-founded. -/
theorem Config.terminates :
    WellFounded (fun next first : Config α => ∃ event, Step first event next) := by
  refine ⟨fun config => ?_⟩
  cases config with
  | running state tasks finished exhausted => exact running_acc state tasks finished exhausted
  | start env computation =>
    have accessible := follows_acc computation
    generalize equal : (⟨α, computation⟩ : Σ β, Result β) = current at accessible
    induction accessible generalizing env computation with
    | intro current _ ih =>
      refine ⟨_, fun next ⟨event, step⟩ => ?_⟩
      simp only [Step, Config.successors] at step
      cases computation with
      | get next =>
        simp only [List.mem_singleton, Prod.mk.injEq] at step
        obtain ⟨-, rfl⟩ := step
        exact ih _ (equal ▸ .get) _ _ rfl
      | set env' next =>
        simp only [List.mem_singleton, Prod.mk.injEq] at step
        obtain ⟨-, rfl⟩ := step
        exact ih _ (equal ▸ .set) _ _ rfl
      | _ =>
        simp [isRequest] at step <;> obtain ⟨-, rfl⟩ := step <;> exact running_acc _ _ _ _

end Lynx.Concurrent
