module

public import Lynx.Concurrent
public import Lynx.Term.Compare
public import Lynx.Concurrent.Kernel

/-! Footprints of concurrent steps: what a step observes of the state and what
it does to it.

A step observes projections of the records of processes, of the timers, and of
the signals in transit, and changes each record, the timers, and the signals in
transit by a function of their old value. Two steps commute when neither
changes what the other observes and their changes commute. Both are decided by
evaluating the changes at the current state, so a message appended to a mailbox
commutes with a receive that would not take it, without a rule of its own. -/

public section

namespace Lynx.Concurrent

open Lynx

/-- Whether two signals are the same. -/
@[expose] def Signal.identical : Signal → Signal → Bool
  | .message term, .message term' => term.identical term'
  | .aliasMessage alias term, .aliasMessage alias' term' =>
      alias == alias' && term.identical term'
  | .exit reason linked, .exit reason' linked' => reason.identical reason' && linked == linked'
  | .link, .link | .unlink, .unlink => true
  | .monitor reference, .monitor reference' => reference == reference'
  | .down reference reason, .down reference' reason' =>
      reference == reference' && reason.identical reason'
  | _, _ => false

private theorem Signal.eq_of_identical {first second : Signal}
    (same : first.identical second = true) : first = second := by
  cases first <;> cases second <;>
    simp only [Signal.identical, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same <;>
    first
      | rfl
      | rw [Term.eq_of_identical same]
      | (obtain ⟨rfl, same⟩ := same; rw [Term.eq_of_identical same])
      | (obtain ⟨same, rfl⟩ := same; rw [Term.eq_of_identical same])
      | rw [same]

/-- Whether two lists are the same, comparing their elements with `same`. -/
@[expose] def identicalLists (same : γ → γ → Bool) : List γ → List γ → Bool
  | [], [] => true
  | first :: rest, second :: rest' => same first second && identicalLists same rest rest'
  | _, _ => false

private theorem eq_of_identicalLists {same : γ → γ → Bool}
    (sound : ∀ {first second}, same first second = true → first = second) :
    ∀ {first second : List γ}, identicalLists same first second = true → first = second
  | [], [], _ => rfl
  | head :: rest, head' :: rest', equal => by
    simp only [identicalLists, Bool.and_eq_true] at equal
    rw [sound equal.1, eq_of_identicalLists sound equal.2]
  | [], _ :: _, equal | _ :: _, [], equal => by simp [identicalLists] at equal

/-- Whether two envelopes are the same. -/
@[expose] def Envelope.identical (first second : Envelope) : Bool :=
  first.source == second.source && first.target == second.target &&
    first.signal.identical second.signal

private theorem Envelope.eq_of_identical {first second : Envelope}
    (same : first.identical second = true) : first = second := by
  obtain ⟨source, target, signal⟩ := first
  obtain ⟨source', target', signal'⟩ := second
  simp only [Envelope.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨rfl, rfl⟩, same⟩ := same
  rw [Signal.eq_of_identical same]

/-- Whether two timers are the same. -/
@[expose] def Timer.identical (first second : Timer) : Bool :=
  first.reference == second.reference && first.destination == second.destination &&
    first.message.identical second.message && first.duration == second.duration

private theorem Timer.eq_of_identical {first second : Timer}
    (same : first.identical second = true) : first = second := by
  obtain ⟨reference, destination, message, duration⟩ := first
  obtain ⟨reference', destination', message', duration'⟩ := second
  simp only [Timer.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨⟨rfl, rfl⟩, same⟩, rfl⟩ := same
  rw [Term.eq_of_identical same]

/-- Whether two records are the same. -/
@[expose] def ProcessState.identical (first second : ProcessState) : Bool :=
  Term.identicalEntries first.pdict second.pdict &&
    Term.identicalList first.mailbox second.mailbox &&
    first.refCounter == second.refCounter && first.children == second.children &&
    first.links == second.links && first.monitors == second.monitors &&
    first.monitoring == second.monitoring && first.aliases == second.aliases &&
    first.trapExit == second.trapExit && first.cancels == second.cancels

private theorem ProcessState.eq_of_identical {first second : ProcessState}
    (same : first.identical second = true) : first = second := by
  cases first; cases second
  simp only [ProcessState.identical, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨pdict, mailbox⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := same
  rw [Term.eq_of_identicalEntries pdict, Term.eq_of_identicalList mailbox]

/-- Whether two records, or their absence, are the same. -/
@[expose] def recordIdentical : Option ProcessState → Option ProcessState → Bool
  | some first, some second => first.identical second
  | none, none => true
  | _, _ => false

private theorem eq_of_recordIdentical {first second : Option ProcessState}
    (same : recordIdentical first second = true) : first = second := by
  cases first <;> cases second <;> simp only [recordIdentical, Bool.false_eq_true] at same
  · rfl
  · rw [ProcessState.eq_of_identical same]

/-! ### Footprints -/

/-- What a step does: each record it changes, by a function of the old record,
and functions of the old timers and signals in transit, if it changes them. -/
structure Effect where
  records : List (PID × (Option ProcessState → Option ProcessState)) := []
  timers : Option (List Timer → List Timer) := none
  inTransit : Option (List Envelope → List Envelope) := none

/-- How an effect changes the record of a process. -/
@[expose] def Effect.record (effect : Effect) (processId : PID) :
    Option ProcessState → Option ProcessState :=
  match Kernel.find? (·.1 == processId) effect.records with
  | some (_, change) => change
  | none => id

/-- The state after an effect. -/
@[expose] def Effect.apply (effect : Effect) (state : State) : State :=
  { state with
    processes := fun processId => effect.record processId (state.processes processId)
    timers := (effect.timers.getD id) state.timers
    inTransit := (effect.inTransit.getD id) state.inTransit }

/-- What a step observes: projections of records, which also observe whether
the process is live, of the timers, and of the signals in transit. -/
structure Observes where
  records : List (PID × (ProcessState → ProcessState)) := []
  timers : List (List Timer → List Timer) := []
  inTransit : List (List Envelope → List Envelope) := []

/-- Two states agree on what a step observes. The time elapsed when timers are
canceled never changes, so it is always observed. -/
private def Observes.Agree (observes : Observes) (state other : State) : Prop :=
  (∀ entry ∈ observes.records,
    (other.processes entry.1).map entry.2 = (state.processes entry.1).map entry.2) ∧
  (∀ view ∈ observes.timers, view other.timers = view state.timers) ∧
  (∀ view ∈ observes.inTransit, view other.inTransit = view state.inTransit) ∧
  other.elapsed = state.elapsed

/-- What a step observes and does. -/
structure Footprint where
  observes : Observes := {}
  effect : Effect := {}

/-- Whether an effect keeps what a step observes, evaluated at a state. -/
@[expose] def Effect.keeps (effect : Effect) (observes : Observes) (state : State) : Bool :=
  Kernel.all observes.records (fun (processId, view) =>
    match Kernel.find? (·.1 == processId) effect.records with
    | some (_, change) => recordIdentical ((change (state.processes processId)).map view)
        ((state.processes processId).map view)
    | none => true) &&
  (match effect.timers with
    | some change => Kernel.all observes.timers fun view =>
        identicalLists Timer.identical (view (change state.timers)) (view state.timers)
    | none => true) &&
  match effect.inTransit with
  | some change => Kernel.all observes.inTransit fun view =>
      identicalLists Envelope.identical (view (change state.inTransit)) (view state.inTransit)
  | none => true

/-- Whether two effects reach the same state in either order, evaluated at a state. -/
@[expose] def Effect.commutes (first second : Effect) (state : State) : Bool :=
  Kernel.all first.records (fun (processId, change) =>
    match Kernel.find? (·.1 == processId) second.records with
    | some (_, change') =>
        let record := state.processes processId
        recordIdentical (change (change' record)) (change' (change record))
    | none => true) &&
  (match first.timers, second.timers with
    | some change, some change' =>
        identicalLists Timer.identical (change (change' state.timers)) (change' (change state.timers))
    | _, _ => true) &&
  match first.inTransit, second.inTransit with
  | some change, some change' =>
      identicalLists Envelope.identical (change (change' state.inTransit))
        (change' (change state.inTransit))
  | _, _ => true

/-- Whether two steps commute at a state: neither changes what the other
observes, and their effects reach the same state in either order. -/
@[expose] def Footprint.independent (first second : Footprint) (state : State) : Bool :=
  first.effect.keeps second.observes state && second.effect.keeps first.observes state &&
    first.effect.commutes second.effect state

/-! ### Effects of operations -/

/-- One effect after another. -/
@[expose] def Effect.andThen (first second : Effect) : Effect where
  records := Kernel.append
    (Kernel.map (fun (processId, change) => (processId, second.record processId ∘ change))
      first.records)
    second.records
  timers := match first.timers, second.timers with
    | some change, some change' => some (change' ∘ change)
    | some change, none => some change
    | none, change' => change'
  inTransit := match first.inTransit, second.inTransit with
    | some change, some change' => some (change' ∘ change)
    | some change, none => some change
    | none, change' => change'

/-- Change the record of a process, if it is live. -/
@[expose] def Effect.change (processId : PID) (change : ProcessState → ProcessState) : Effect :=
  { records := [(processId, Option.map change)] }

/-- Send a signal. -/
@[expose] def Effect.send (envelope : Envelope) : Effect := { inTransit := some (enqueue envelope) }

/-- Append a message to a mailbox. -/
@[expose] def ProcessState.append (message : Term) (process : ProcessState) : ProcessState :=
  { process with mailbox := Kernel.append process.mailbox [message] }

/-- A process ends with a reason: its record goes, timers sending to it are
canceled, and linked and watching processes get signals. -/
@[expose] def Effect.ending (processId : PID) (process : ProcessState) (reason : Term) : Effect :=
  { records := [(processId, fun _ => none)]
    timers := some (Kernel.filter (·.destination != processId))
    inTransit := some fun inTransit =>
      Kernel.foldl (fun inTransit (reference, watcher) =>
          enqueue ⟨processId, watcher, .down reference reason⟩ inTransit)
        (Kernel.foldl (fun inTransit linked =>
          enqueue ⟨processId, linked, .exit reason true⟩ inTransit) inTransit process.links)
        process.monitors }

/-! ### Views of records -/

/-- Observe only whether a process is live. -/
@[expose] def ProcessState.live (_ : ProcessState) : ProcessState := {}

/-- What a running process observes. -/
@[expose] def ProcessState.env (process : ProcessState) : ProcessState :=
  { pdict := process.pdict, refCounter := process.refCounter }

/-- What a process ending observes: whom it signals. -/
@[expose] def ProcessState.ending (process : ProcessState) : ProcessState :=
  { links := process.links, monitors := process.monitors }

/-- The message a receive selects, if any. -/
@[expose] def selected (select : Term → Option β) (mailbox : List Term) : List Term :=
  match selectMessage select mailbox with
  | some (message, _, _) => [message]
  | none => []

/-- The mailbox once a receive takes the message it selects. -/
@[expose] def remaining (select : Term → Option β) (mailbox : List Term) : List Term :=
  match selectMessage select mailbox with
  | some (_, _, rest) => rest
  | none => mailbox

/-- Whether an envelope goes from one process to another. -/
@[expose] def Envelope.between (source target : PID) (envelope : Envelope) : Bool :=
  envelope.source == source && envelope.target == target

/-- The oldest signal from one process to another. -/
@[expose] def oldest (source target : PID) (inTransit : List Envelope) : List Envelope :=
  (Kernel.find? (Envelope.between source target) inTransit).toList

/-- The signals in transit once the oldest from one process to another arrives. -/
@[expose] def arrive (source target : PID) (inTransit : List Envelope) : List Envelope :=
  Kernel.eraseP (Envelope.between source target) inTransit

/-- The timer with a reference that fires first. -/
@[expose] def firstTimer (reference : List Nat) (timers : List Timer) : List Timer :=
  (Kernel.find? (·.reference == reference) timers).toList

/-! ### Footprints of steps -/

/-- Observe a record. -/
@[expose] def Observes.record (processId : PID) (view : ProcessState → ProcessState) : Observes :=
  { records := [(processId, view)] }

/-- Observe more. -/
@[expose] def Observes.and (first second : Observes) : Observes :=
  { records := Kernel.append first.records second.records
    timers := Kernel.append first.timers second.timers
    inTransit := Kernel.append first.inTransit second.inTransit }

/-- The footprint of a process ending, observing more. -/
@[expose] def Footprint.ending (state : State) (processId : PID) (reason : Term) : Footprint :=
  { observes := .record processId ProcessState.ending
    effect := .ending processId (state.process processId) reason }

/-- The footprint of a spawn. -/
@[expose] def Footprint.spawn (state : State) (processId : PID) (options : SpawnOptions) : Footprint :=
  let process := state.process processId
  let child := Kernel.append processId [process.children + 1]
  let reference := Kernel.append processId [process.refCounter + 1]
  { observes := .record processId fun process =>
      { children := process.children, refCounter := process.refCounter }
    effect := { records := [
      (processId, Option.map fun process =>
        let process := { process with children := process.children + 1 }
        let process := if options.link then { process with links := insertOnce child process.links }
          else process
        if options.monitor then
          { process with refCounter := process.refCounter + 1
                         monitoring := Kernel.append process.monitoring [(reference, child)] }
        else process),
      (child, fun _ => some { links := if options.link then [processId] else []
                              monitors := if options.monitor then [(reference, processId)] else [] })] } }

/-- The footprint of answering a request. -/
@[expose] def requestFootprint (state : State) (processId : PID) : Request → Footprint
  | .monitor target alias =>
      let reference := Kernel.append processId [(state.process processId).refCounter + 1]
      let counted : Observes := .record processId fun process => { refCounter := process.refCounter }
      if target = processId then
        { observes := counted
          effect := .change processId fun process => { process with refCounter := process.refCounter + 1 } }
      else
        { observes := counted.and (.record target ProcessState.live)
          effect := (Effect.change processId fun process =>
            { process with
                refCounter := process.refCounter + 1
                monitoring := Kernel.append process.monitoring [(reference, target)]
                aliases := if alias then Kernel.append process.aliases [reference]
                  else process.aliases }).andThen
            (.send (if state.alive target then ⟨processId, target, .monitor reference⟩
              else ⟨target, processId, .down reference (.atom "noproc")⟩)) }
  | .demonitor reference flush =>
      { observes := .record processId fun process =>
          { monitoring := Kernel.filter (·.1 == reference) process.monitoring }
        effect := .change processId fun process =>
          let active := Kernel.any process.monitoring (·.1 == reference)
          { process with
              monitoring := Kernel.filter (·.1 != reference) process.monitoring
              aliases := Kernel.erase process.aliases reference
              mailbox := if flush && !active then
                  Kernel.eraseP (isMonitorMessage reference) process.mailbox
                else process.mailbox } }
  | .link target =>
      let observes : Observes := (Observes.record processId fun process => { trapExit := process.trapExit }).and
        (.record target ProcessState.live)
      if target = processId then { observes }
      else if !state.alive target && !(state.process processId).trapExit then { observes }
      else
        { observes
          effect := (Effect.change processId fun process =>
            { process with links := insertOnce target process.links }).andThen
            (.send (if state.alive target then ⟨processId, target, .link⟩
              else ⟨target, processId, .exit (.atom "noproc") true⟩)) }
  | .unlink target =>
      { observes := .record processId ProcessState.live
        effect := (Effect.change processId fun process =>
          { process with links := Kernel.erase process.links target }).andThen
          (if target = processId then {} else .send ⟨processId, target, .unlink⟩) }
  | .exit target reason =>
      if target = processId then
        let trapping : Observes := .record processId fun process => { trapExit := process.trapExit }
        if isKill reason || !(state.process processId).trapExit then
          { observes := trapping.and (.record processId ProcessState.ending)
            effect := .ending processId (state.process processId)
              (if isKill reason then .atom "killed" else reason) }
        else
          { observes := trapping
            effect := .change processId
              (ProcessState.append (.tuple #[.atom "EXIT", .pid processId, reason])) }
      else
        { observes := .record processId ProcessState.live
          effect := .send ⟨processId, target, .exit reason false⟩ }
  | .trapExit enabled =>
      { observes := .record processId fun process => { trapExit := process.trapExit }
        effect := .change processId fun process => { process with trapExit := enabled } }
  | .alive target =>
      if target = processId then { observes := .record processId ProcessState.live }
      else
        { observes := { records := [(processId, ProcessState.live), (target, ProcessState.live)]
                        inTransit := [fun inTransit => Kernel.filter (fun envelope =>
                          envelope.between processId target || envelope.between target processId)
                          inTransit] } }
  | .sendAlias alias message =>
      let owner := alias.dropLast
      if owner = processId then
        { observes := .record processId ProcessState.live
          effect := .change processId fun process =>
            if Kernel.contains process.aliases alias then process.append message else process }
      else
        { observes := .record processId ProcessState.live
          effect := .send ⟨processId, owner, .aliasMessage alias message⟩ }
  | .startTimer destination message duration =>
      let reference := Kernel.append processId [(state.process processId).refCounter + 1]
      { observes := (Observes.record processId fun process => { refCounter := process.refCounter }).and
          (.record destination ProcessState.live)
        effect := (Effect.change processId fun process =>
          { process with refCounter := process.refCounter + 1 }).andThen
          (if state.alive destination then
            { timers := some (insertTimer { reference, destination, message, duration }) }
          else {}) }
  | .cancelTimer reference =>
      { observes := { records := [(processId, fun process => { cancels := process.cancels })]
                      timers := [fun timers => Kernel.filter (·.reference == reference) timers] }
        effect := match Kernel.find? (·.reference == reference) state.timers with
          | some _ =>
              { records := [(processId, Option.map fun process =>
                  { process with cancels := process.cancels + 1 })]
                timers := some (Kernel.filter (·.reference != reference)) }
          | none => {} }

/-- The footprint of a process's own step. -/
@[expose] def Task.footprint (state : State) (processId : PID) : Task α → Footprint
  | ⟨computation, _⟩ =>
    match computation with
    | .error .exhausted =>
        { observes := .record processId ProcessState.live
          effect := { records := [(processId, fun _ => none)] } }
    | .ok _ => Footprint.ending state processId (.atom "normal")
    | .error exception => Footprint.ending state processId (exitReason exception)
    | .get _ => { observes := .record processId ProcessState.env }
    | .set updated _ =>
        { observes := .record processId ProcessState.live
          effect := .change processId fun process =>
            { process with pdict := updated.pdict
                           refCounter := max process.refCounter updated.refCounter } }
    | Result.schedule options _ _ => Footprint.spawn state processId options
    | .send destination message _ =>
        { observes := .record processId ProcessState.live
          effect := if destination = processId then .change processId (ProcessState.append message)
            else .send ⟨processId, destination, .message message⟩ }
    | .receive _ select _ =>
        let choose := select (state.view processId)
        { observes := .record processId fun process =>
            { pdict := process.pdict, refCounter := process.refCounter
              mailbox := selected choose process.mailbox }
          effect := match selectMessage choose (state.process processId).mailbox with
            | some _ => .change processId fun process =>
                { process with mailbox := remaining choose process.mailbox }
            | none => {} }
    | .request query _ => requestFootprint state processId query

/-- What a live process does with a signal, without exiting. -/
@[expose] def ProcessState.receive (source : PID) (process : ProcessState) : Signal → ProcessState
  | .message message => process.append message
  | .aliasMessage alias message =>
      if Kernel.contains process.aliases alias then process.append message else process
  | .exit reason linked =>
      if linked && !Kernel.contains process.links source then process else
      let process := if linked then { process with links := Kernel.erase process.links source }
        else process
      if process.trapExit then process.append (.tuple #[.atom "EXIT", .pid source, reason])
      else process
  | .link => { process with links := insertOnce source process.links }
  | .unlink => { process with links := Kernel.erase process.links source }
  | .monitor reference =>
      { process with monitors := Kernel.append process.monitors [(reference, source)] }
  | .down reference reason =>
      if Kernel.any process.monitoring (·.1 == reference) then
        { process with
            monitoring := Kernel.filter (·.1 != reference) process.monitoring
            aliases := Kernel.erase process.aliases reference }.append
          (.tuple #[.atom "DOWN", .reference reference, .atom "process", .pid source, reason])
      else process

/-- The footprint of a signal reaching a live process. -/
@[expose] def Footprint.delivery (state : State) (envelope : Envelope) : Footprint :=
  let target := envelope.target
  let source := envelope.source
  let channel : Observes := { records := [(target, ProcessState.live)], inTransit := [oldest source target] }
  let taken : Effect := { inTransit := some (arrive source target) }
  match envelope.signal with
  | .exit reason linked =>
      match (state.exitSignal target source reason linked).2 with
      | some reason =>
          let process := state.process target
          let process := if linked then { process with links := Kernel.erase process.links source }
            else process
          { observes := channel.and (.record target id)
            effect := taken.andThen (.ending target process reason) }
      | none =>
          { observes := channel.and (.record target fun process =>
              { links := Kernel.filter (· == source) process.links, trapExit := process.trapExit })
            effect := taken.andThen (.change target (·.receive source envelope.signal)) }
  | signal => { observes := channel, effect := taken.andThen (.change target (·.receive source signal)) }

/-- The footprint of a signal reaching a process that is not live. -/
@[expose] def Footprint.bounce (envelope : Envelope) : Footprint :=
  let target := envelope.target
  let source := envelope.source
  { observes := { records := [(target, ProcessState.live)], inTransit := [oldest source target] }
    effect := { inTransit := some fun inTransit =>
      let inTransit := arrive source target inTransit
      match envelope.signal with
      | .link => enqueue ⟨target, source, .exit (.atom "noproc") true⟩ inTransit
      | .monitor reference => enqueue ⟨target, source, .down reference (.atom "noproc")⟩ inTransit
      | _ => inTransit } }

/-- The footprint of a timer firing. -/
@[expose] def Footprint.fire (timer : Timer) : Footprint :=
  { observes := { timers := [firstTimer timer.reference] }
    effect := { timers := some (Kernel.filter (·.reference != timer.reference))
                inTransit := some (enqueue ⟨clock, timer.destination, .message timer.message⟩) } }

/-- `arrive` in proofs: core's `eraseP`. -/
private theorem arrive_eq {source target : PID} {inTransit : List Envelope} :
    arrive source target inTransit = inTransit.eraseP (Envelope.between source target) := by
  simp [arrive]

/-! ### Commuting footprints -/

private theorem State.ext' {first second : State} (processes : first.processes = second.processes)
    (timers : first.timers = second.timers) (inTransit : first.inTransit = second.inTransit)
    (elapsed : first.elapsed = second.elapsed) : first = second := by
  cases first; cases second; simp_all

@[simp] private theorem Effect.processes_apply {effect : Effect} {state : State} {processId : PID} :
    (effect.apply state).processes processId = effect.record processId (state.processes processId) :=
  rfl

@[simp] private theorem Effect.elapsed_apply {effect : Effect} {state : State} :
    (effect.apply state).elapsed = state.elapsed := rfl

/-- An effect keeping what a step observes leaves a state agreeing on it. -/
private theorem Effect.agree_of_keeps {effect : Effect} {observes : Observes} {state : State}
    (keeps : effect.keeps observes state = true) : observes.Agree state (effect.apply state) := by
  simp only [Effect.keeps, Bool.and_eq_true, List.all_eq_true, Kernel.all_eq,
      Kernel.find?_eq] at keeps
  obtain ⟨⟨records, timers⟩, inTransit⟩ := keeps
  refine ⟨fun entry mem => ?_, fun view mem => ?_, fun view mem => ?_, rfl⟩
  · have := records entry mem
    simp only [Effect.processes_apply, Effect.record, Kernel.find?_eq]
    split at this
    · rename_i found
      rw [found]
      exact eq_of_recordIdentical this
    · rename_i found
      rw [found]
      rfl
  · simp only [Effect.apply]
    split at timers
    · rename_i found
      simp only [List.all_eq_true] at timers
      rw [found]
      exact eq_of_identicalLists Timer.eq_of_identical (timers view mem)
    · rename_i found
      rw [found]
      rfl
  · simp only [Effect.apply]
    split at inTransit
    · rename_i found
      simp only [List.all_eq_true] at inTransit
      rw [found]
      exact eq_of_identicalLists Envelope.eq_of_identical (inTransit view mem)
    · rename_i found
      rw [found]
      rfl

/-- Commuting effects reach the same state in either order. -/
private theorem Effect.apply_comm {first second : Effect} {state : State}
    (commutes : first.commutes second state = true) :
    first.apply (second.apply state) = second.apply (first.apply state) := by
  simp only [Effect.commutes, Bool.and_eq_true, List.all_eq_true, Kernel.all_eq,
      Kernel.find?_eq] at commutes
  obtain ⟨⟨records, timers⟩, inTransit⟩ := commutes
  refine State.ext' (funext fun processId => ?_) ?_ ?_ rfl
  · simp only [Effect.processes_apply, Effect.record, Kernel.find?_eq]
    cases found : first.records.find? (·.1 == processId) with
    | none => rfl
    | some entry =>
      obtain ⟨processId', change⟩ := entry
      have same : processId' = processId := by
        have := List.find?_some found; simpa using this
      subst same
      have := records _ (List.mem_of_find?_eq_some found)
      cases found' : second.records.find? (·.1 == processId') with
      | none => rfl
      | some entry' =>
        obtain ⟨_, change'⟩ := entry'
        simp only [found'] at this
        exact eq_of_recordIdentical this
  · simp only [Effect.apply]
    split at timers
    · rename_i change change' found found'
      rw [found, found']
      exact eq_of_identicalLists Timer.eq_of_identical timers
    · rename_i none
      cases found : first.timers <;> cases found' : second.timers <;> simp_all
  · simp only [Effect.apply]
    split at inTransit
    · rename_i change change' found found'
      rw [found, found']
      exact eq_of_identicalLists Envelope.eq_of_identical inTransit
    · rename_i none
      cases found : first.inTransit <;> cases found' : second.inTransit <;> simp_all

end Lynx.Concurrent

namespace Lynx.Concurrent

open Lynx

/-! ### Effects of operations, as functions of the state -/

private theorem Observes.Agree.refl (observes : Observes) (state : State) :
    observes.Agree state state :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

private theorem Observes.Agree.left {first second : Observes} {state other : State}
    (agree : (first.and second).Agree state other) : first.Agree state other :=
  ⟨fun entry mem => agree.1 entry (by simp [Observes.and, mem]),
    fun view mem => agree.2.1 view (by simp [Observes.and, mem]),
    fun view mem => agree.2.2.1 view (by simp [Observes.and, mem]), agree.2.2.2⟩

private theorem Observes.Agree.right {first second : Observes} {state other : State}
    (agree : (first.and second).Agree state other) : second.Agree state other :=
  ⟨fun entry mem => agree.1 entry (by simp [Observes.and, mem]),
    fun view mem => agree.2.1 view (by simp [Observes.and, mem]),
    fun view mem => agree.2.2.1 view (by simp [Observes.and, mem]), agree.2.2.2⟩

/-- What agreeing on a view of a record says about the record. -/
private theorem Observes.Agree.view {observes : Observes} {state other : State} {processId : PID}
    {view : ProcessState → ProcessState} (agree : observes.Agree state other)
    (mem : (processId, view) ∈ observes.records) :
    (other.processes processId).isSome = (state.processes processId).isSome ∧
      view (other.process processId) = view (state.process processId) := by
  have equal := agree.1 _ mem
  simp only [State.process] at equal ⊢
  cases found : other.processes processId <;> cases found' : state.processes processId <;>
    simp_all

private theorem Observes.Agree.record {processId : PID} {view : ProcessState → ProcessState}
    {state other : State} (agree : (Observes.record processId view).Agree state other) :
    (other.processes processId).isSome = (state.processes processId).isSome ∧
      view (other.process processId) = view (state.process processId) :=
  agree.view (by simp [Observes.record])

@[simp] private theorem Effect.apply_empty {state : State} : ({} : Effect).apply state = state := by
  apply State.ext' <;> first | rfl | (funext; rfl)

private theorem Effect.record_andThen {first second : Effect} {processId : PID} :
    (first.andThen second).record processId = second.record processId ∘ first.record processId := by
  have predicate : ((fun (entry : PID × (Option ProcessState → Option ProcessState)) =>
      entry.1 == processId) ∘ fun (entry : PID × (Option ProcessState → Option ProcessState)) =>
        (entry.1, second.record entry.1 ∘ entry.2)) =
      fun (entry : PID × (Option ProcessState → Option ProcessState)) => entry.1 == processId := rfl
  unfold Effect.record Effect.andThen
  simp only [Kernel.find?_eq, Kernel.append_eq, Kernel.map_eq, List.find?_append, List.find?_map,
    predicate]
  cases found : first.records.find? (·.1 == processId) with
  | none => rfl
  | some entry =>
    obtain ⟨processId', change⟩ := entry
    have same : processId' = processId := by simpa using List.find?_some found
    subst same
    simp [Effect.record]

@[simp] private theorem Effect.apply_andThen {first second : Effect} {state : State} :
    (first.andThen second).apply state = second.apply (first.apply state) := by
  apply State.ext'
  · funext processId
    simp only [Effect.processes_apply, Effect.record_andThen, Function.comp_apply]
  · simp only [Effect.apply, Effect.andThen, Kernel.append_eq, Kernel.map_eq]
    cases first.timers <;> cases second.timers <;> rfl
  · simp only [Effect.apply, Effect.andThen, Kernel.append_eq, Kernel.map_eq]
    cases first.inTransit <;> cases second.inTransit <;> rfl
  · rfl

@[simp] private theorem Effect.apply_change {processId : PID} {change : ProcessState → ProcessState}
    {state : State} : (Effect.change processId change).apply state = state.modify processId change := by
  unfold State.modify
  cases found : state.processes processId with
  | none =>
    refine State.ext' (funext fun candidate => ?_) rfl rfl rfl
    simp only [Effect.processes_apply, Effect.record, Effect.change, List.find?_cons,
        List.find?_nil, Kernel.find?_eq]
    by_cases same : processId = candidate
    · subst same; simp [found]
    · have : (processId == candidate) = false := by simpa using same
      simp [this]
  | some process =>
    refine State.ext' (funext fun candidate => ?_) rfl rfl rfl
    simp only [Effect.processes_apply, Effect.record, Effect.change, List.find?_cons, List.find?_nil,
      State.update, Kernel.find?_eq]
    by_cases same : processId = candidate
    · subst same; simp [found]
    · have : (processId == candidate) = false := by simpa using same
      simp [this, Ne.symm same]

@[simp] private theorem Effect.apply_send {envelope : Envelope} {state : State} :
    (Effect.send envelope).apply state = state.emit envelope.source envelope.target envelope.signal := by
  apply State.ext' <;> first | rfl | (funext; rfl)

private theorem State.append_eq {state : State} {processId : PID} {message : Term} :
    state.append processId message = state.modify processId (ProcessState.append message) := rfl

/-- Folding sends over a state sends them over its signals in transit. -/
private theorem foldl_emit {items : List γ} {envelope : γ → Envelope} {state : State} :
    items.foldl (fun state item => state.emit (envelope item).source (envelope item).target
        (envelope item).signal) state =
      { state with
        inTransit := (items.foldl (fun inTransit item => enqueue (envelope item) inTransit)
          state.inTransit) } := by
  induction items generalizing state with
  | nil => rfl
  | cons head rest ih => simp only [List.foldl_cons, ih]; rfl

private theorem Effect.apply_ending {processId : PID} {reason : Term} {state : State} :
    (Effect.ending processId (state.process processId) reason).apply state =
      state.terminate processId reason := by
  unfold State.terminate
  simp only [Kernel.foldl_eq]
  rw [foldl_emit (envelope := fun (entry : List Nat × PID) => ⟨processId, entry.2, .down entry.1 reason⟩),
    foldl_emit (envelope := fun linked => ⟨processId, linked, .exit reason true⟩)]
  apply State.ext'
  · funext candidate
    simp only [Effect.processes_apply, Effect.record, Effect.ending, List.find?_cons, List.find?_nil,
      State.update, Kernel.find?_eq, Kernel.filter_eq, Kernel.foldl_eq]
    by_cases same : processId = candidate
    · subst same; simp
    · have : (processId == candidate) = false := by simpa using same
      simp [this, Ne.symm same]
  · rfl
  · simp [Effect.apply, Effect.ending]; rfl
  · rfl

/-- Ending depends only on whom the process signals. -/
private theorem Effect.ending_congr {processId : PID} {process process' : ProcessState} {reason : Term}
    (same : process'.ending = process.ending) :
    Effect.ending processId process' reason = Effect.ending processId process reason := by
  simp only [ProcessState.ending, ProcessState.mk.injEq] at same
  simp only [Effect.ending, same, Kernel.filter_eq, Kernel.foldl_eq]

private theorem Effect.apply_remove {processId : PID} {state : State} :
    ({ records := [(processId, fun _ => none)] } : Effect).apply state = state.update processId none := by
  apply State.ext'
  · funext candidate
    simp only [Effect.processes_apply, Effect.record, List.find?_cons, List.find?_nil,
        State.update, Kernel.find?_eq]
    by_cases same : processId = candidate
    · subst same; simp
    · have : (processId == candidate) = false := by simpa using same
      simp [this, Ne.symm same]
  · rfl
  · rfl
  · rfl

/-! ### Which signals arrive and which timers fire -/

private theorem between_iff {envelope head : Envelope} :
    Envelope.between envelope.source envelope.target head = true ↔
      (head.source, head.target) = (envelope.source, envelope.target) := by
  simp [Envelope.between]

private theorem mem_deliverableFrom_iff {before : List Envelope} {seen : List (PID × PID)}
    {inTransit : List Envelope} {envelope : Envelope} {rest : List Envelope} :
    (envelope, rest) ∈ deliverableFrom before seen inTransit ↔
      (envelope.source, envelope.target) ∉ seen ∧
      inTransit.find? (Envelope.between envelope.source envelope.target) = some envelope ∧
      rest = before ++ inTransit.eraseP (Envelope.between envelope.source envelope.target) := by
  induction inTransit generalizing before seen with
  | nil => simp [deliverableFrom]
  | cons head tail ih =>
    simp only [deliverableFrom, Kernel.append_eq, Kernel.contains_eq]
    by_cases same : Envelope.between envelope.source envelope.target head = true
    · have pair := between_iff.mp same
      simp only [List.find?_cons, same, List.eraseP_cons_of_pos same, Option.some.injEq]
      split
      · rename_i seenHead
        rw [ih]
        rw [pair, List.elem_iff] at seenHead
        simp [seenHead]
      · rename_i fresh
        rw [pair, List.elem_iff] at fresh
        rw [List.mem_cons, ih]
        constructor
        · rintro (equal | ⟨notSeen, -, -⟩)
          · simp only [Prod.mk.injEq] at equal
            obtain ⟨rfl, rfl⟩ := equal
            exact ⟨fresh, rfl, rfl⟩
          · exact absurd (List.mem_cons_self) (pair ▸ notSeen)
        · rintro ⟨-, rfl, rfl⟩
          exact .inl rfl
    · have notSame : (Envelope.between envelope.source envelope.target head) = false := by simpa using same
      simp only [List.find?_cons, notSame, List.eraseP_cons_of_neg same]
      split
      · rw [ih]; simp
      · rw [List.mem_cons, ih]
        constructor
        · rintro (equal | ⟨notSeen, found, rfl⟩)
          · simp only [Prod.mk.injEq] at equal
            obtain ⟨rfl, rfl⟩ := equal
            simp [Envelope.between] at notSame
          · exact ⟨fun mem => notSeen (List.mem_cons_of_mem _ mem), found, by simp⟩
        · rintro ⟨notSeen, found, rfl⟩
          refine .inr ⟨fun mem => ?_, found, by simp⟩
          rcases List.mem_cons.mp mem with equal | mem
          · exact same (between_iff.mpr equal.symm)
          · exact notSeen mem

/-- A signal arrives when it is the oldest of its pair, leaving the others. -/
private theorem mem_deliverable_iff {inTransit : List Envelope} {envelope : Envelope}
    {rest : List Envelope} :
    (envelope, rest) ∈ deliverable inTransit ↔
      oldest envelope.source envelope.target inTransit = [envelope] ∧
      rest = arrive envelope.source envelope.target inTransit := by
  simp only [deliverable, mem_deliverableFrom_iff, List.not_mem_nil, not_false_eq_true, true_and,
    List.nil_append, oldest, arrive, Kernel.find?_eq, Kernel.eraseP_eq]
  constructor
  · rintro ⟨found, rfl⟩; simp [found]
  · rintro ⟨found, rfl⟩
    refine ⟨?_, rfl⟩
    cases equal : inTransit.find? (Envelope.between envelope.source envelope.target) <;>
      simp_all

private theorem mem_firstOfEach_iff {seen : List (List Nat)} {timers : List Timer} {timer : Timer} :
    timer ∈ firstOfEach seen timers ↔
      timer.reference ∉ seen ∧ timers.find? (·.reference == timer.reference) = some timer := by
  induction timers generalizing seen with
  | nil => simp [firstOfEach]
  | cons head rest ih =>
    simp only [firstOfEach, Kernel.contains_eq]
    by_cases same : head.reference = timer.reference
    · have matched : (head.reference == timer.reference) = true := by simpa using same
      simp only [List.find?_cons, matched, Option.some.injEq]
      split
      · rename_i seenHead
        rw [ih]
        rw [List.elem_iff, same] at seenHead
        simp [seenHead]
      · rename_i fresh
        rw [List.elem_iff, same] at fresh
        rw [List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨notSeen, -⟩)
          · exact ⟨fresh, rfl⟩
          · exact absurd (same ▸ List.mem_cons_self) notSeen
        · rintro ⟨-, rfl⟩; exact .inl rfl
    · have different : (head.reference == timer.reference) = false := by simpa using same
      simp only [List.find?_cons, different]
      split
      · rw [ih]
      · rw [List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨notSeen, found⟩)
          · exact absurd rfl same
          · exact ⟨fun mem => notSeen (List.mem_cons_of_mem _ mem), found⟩
        · rintro ⟨notSeen, found⟩
          refine .inr ⟨fun mem => ?_, found⟩
          rcases List.mem_cons.mp mem with equal | mem
          · exact same equal.symm
          · exact notSeen mem

/-- A timer can fire when it is the first with its reference. -/
private theorem mem_firing_iff {state : State} {timer : Timer} :
    timer ∈ state.firing ↔ firstTimer timer.reference state.timers = [timer] := by
  simp only [State.firing, mem_firstOfEach_iff, List.not_mem_nil, not_false_eq_true, true_and,
    firstTimer, Kernel.find?_eq]
  cases state.timers.find? (·.reference == timer.reference) <;> simp

/-! ### Steps act as their footprints say -/

/-- A step at another state: the same outcome, and the effect applied to it. -/
private def Matches (effect : Effect) (other : State) (transition transition' : Transition α) : Prop :=
  transition'.event = transition.event ∧ transition'.tasks = transition.tasks ∧
    transition'.finished = transition.finished ∧ transition'.exhausted = transition.exhausted ∧
    transition'.state = effect.apply other

@[simp] private theorem Effect.apply_inTransit {change : List Envelope → List Envelope} {state : State} :
    ({ inTransit := some change } : Effect).apply state = { state with inTransit := change state.inTransit } :=
  rfl

/-- The signal that arrives at a state arrives at another with the same oldest signal. -/
private theorem arrives {state other : State} {envelope : Envelope} {rest : List Envelope}
    (mem : (envelope, rest) ∈ deliverable state.inTransit)
    (same : oldest envelope.source envelope.target other.inTransit =
      oldest envelope.source envelope.target state.inTransit) :
    (envelope, arrive envelope.source envelope.target other.inTransit) ∈ deliverable other.inTransit ∧
      rest = arrive envelope.source envelope.target state.inTransit := by
  rw [mem_deliverable_iff] at mem ⊢
  exact ⟨⟨same.trans mem.1, rfl⟩, mem.2⟩

private theorem fire_matches {state other : State} {timer : Timer} (firing : timer ∈ state.firing)
    (agree : (Footprint.fire timer).observes.Agree state other) :
    timer ∈ other.firing ∧ other.fire timer = (Footprint.fire timer).effect.apply other := by
  refine ⟨?_, rfl⟩
  rw [mem_firing_iff] at firing ⊢
  rw [agree.2.1 (firstTimer timer.reference) (by simp [Footprint.fire]), firing]

private theorem bounce_matches {state other : State} {envelope : Envelope} {rest : List Envelope}
    (mem : (envelope, rest) ∈ deliverable state.inTransit)
    (agree : (Footprint.bounce envelope).observes.Agree state other) :
    (other.processes envelope.target).isSome = (state.processes envelope.target).isSome ∧
    (envelope, arrive envelope.source envelope.target other.inTransit) ∈ deliverable other.inTransit ∧
    { other with inTransit := arrive envelope.source envelope.target other.inTransit }.bounce envelope =
      (Footprint.bounce envelope).effect.apply other ∧
    { state with inTransit := rest }.bounce envelope = (Footprint.bounce envelope).effect.apply state := by
  have live := (agree.view (processId := envelope.target) (view := ProcessState.live)
    (by simp [Footprint.bounce])).1
  obtain ⟨mem', rfl⟩ := arrives mem (agree.2.2.1 _ (by simp [Footprint.bounce]))
  obtain ⟨source, target, signal⟩ := envelope
  refine ⟨live, mem', ?_, ?_⟩ <;> cases signal <;> rfl

/-- Whether a live process exits on an exit signal, and with which reason. -/
private def exits (process : ProcessState) (source : PID) (reason : Term) (linked : Bool) : Option Term :=
  if linked && !process.links.contains source then none
  else if !linked && isKill reason then some (.atom "killed")
  else if process.trapExit then none
  else if isNormal reason then none
  else some reason

private theorem State.exitSignal_snd {state : State} {target source : PID} {reason : Term}
    {linked : Bool} :
    (state.exitSignal target source reason linked).2 = exits (state.process target) source reason linked := by
  unfold State.exitSignal exits
  repeat' split
  all_goals simp_all

private theorem State.modify_modify {state : State} {processId : PID}
    {first second : ProcessState → ProcessState} :
    (state.modify processId first).modify processId second = state.modify processId (second ∘ first) := by
  unfold State.modify
  cases found : state.processes processId with
  | none => simp [found]
  | some process =>
    simp only [State.update]
    refine State.ext' (funext fun candidate => ?_) rfl rfl rfl
    by_cases same : candidate = processId <;> simp [same]

private theorem State.update_self {state : State} {processId : PID} {process : ProcessState}
    (found : state.processes processId = some process) : state.update processId (some process) = state := by
  refine State.ext' (funext fun candidate => ?_) rfl rfl rfl
  simp only [State.update]
  split <;> simp_all

private theorem State.modify_of_some {state : State} {processId : PID} {process : ProcessState}
    {change : ProcessState → ProcessState} (found : state.processes processId = some process) :
    state.modify processId change = state.update processId (some (change process)) := by
  simp [State.modify, found]

private theorem State.modify_of_none {state : State} {processId : PID}
    {change : ProcessState → ProcessState} (found : state.processes processId = none) :
    state.modify processId change = state := by
  simp [State.modify, found]

private theorem State.update_update {state : State} {processId : PID} {first second : Option ProcessState} :
    (state.update processId first).update processId second = state.update processId second := by
  refine State.ext' (funext fun candidate => ?_) rfl rfl rfl
  simp only [State.update]
  split <;> rfl

private theorem State.modify_update {state : State} {processId : PID} {process : ProcessState}
    {change : ProcessState → ProcessState} :
    (state.update processId (some process)).modify processId change =
      state.update processId (some (change process)) := by
  rw [State.modify_of_some (process := process) (by simp [State.update]), State.update_update]

/-- An exit signal a process survives changes its record only. -/
private theorem State.exitSignal_fst {state : State} {target source : PID} {reason : Term}
    {linked : Bool} (survives : exits (state.process target) source reason linked = none) :
    (state.exitSignal target source reason linked).1 =
      state.modify target (·.receive source (.exit reason linked)) := by
  unfold State.exitSignal
  unfold exits at survives
  simp only [State.append_eq]
  cases found : state.processes target with
  | none =>
    simp only [State.process, found, Option.getD_none] at survives ⊢
    repeat' split
    all_goals simp_all [State.modify_of_none found, ProcessState.receive]
  | some process =>
    simp only [State.process, found, Option.getD_some] at survives ⊢
    simp only [State.modify_of_some found]
    repeat' split
    all_goals simp_all [ProcessState.receive, ProcessState.append, State.update_self found,
      State.modify_update, State.modify_of_some found]

/-- An exit signal a process does not survive changes its links only. -/
private theorem State.exitSignal_fst_exits {state : State} {target source : PID} {reason exit : Term}
    {linked : Bool} (exiting : exits (state.process target) source reason linked = some exit) :
    (state.exitSignal target source reason linked).1 =
      if linked then state.modify target fun process => { process with links := process.links.erase source }
      else state := by
  unfold State.exitSignal
  unfold exits at exiting
  repeat' split
  all_goals simp_all

/-- Taking a signal other than an exit signal changes the record of the receiver only. -/
private theorem State.receive_eq {state : State} {envelope : Envelope}
    (notExit : ∀ reason linked, envelope.signal ≠ .exit reason linked) :
    state.receive envelope = (state.modify envelope.target (·.receive envelope.source envelope.signal), none) := by
  obtain ⟨source, target, signal⟩ := envelope
  unfold State.receive
  dsimp only
  cases signal with
  | exit reason linked => exact absurd rfl (notExit reason linked)
  | message => rfl
  | link | unlink | monitor => rfl
  | aliasMessage alias message =>
    simp only [ProcessState.receive, State.append_eq, Prod.mk.injEq, and_true, Kernel.contains_eq]
    cases found : state.processes target with
    | none => simp [State.process, found, State.modify_of_none found]
    | some process =>
      simp only [State.process, found, Option.getD_some, State.modify_of_some found]
      split <;> simp [*, State.update_self found]
  | down reference reason =>
    simp only [ProcessState.receive, State.append_eq, State.modify_modify, Kernel.any_eq,
        Kernel.erase_eq, Kernel.filter_eq]
    cases found : state.processes target with
    | none => simp [State.process, found, State.modify_of_none found]
    | some process =>
      simp only [State.process, found, Option.getD_some, State.modify_of_some found]
      split <;> simp [*, State.update_self found]

private theorem contains_of_filter {items items' : List PID} {item : PID}
    (same : items'.filter (· == item) = items.filter (· == item)) :
    items'.contains item = items.contains item := by
  have : ∀ items : List PID, items.contains item = (items.filter (· == item)).contains item := by
    intro items
    rw [Bool.eq_iff_iff]
    simp [List.mem_filter]
  rw [this items', this items, same]

/-- Ending a process does not depend on its record. -/
private theorem Effect.ending_modify {processId : PID} {process : ProcessState} {reason : Term}
    {state : State} {change : ProcessState → ProcessState} :
    (Effect.ending processId process reason).apply (state.modify processId change) =
      (Effect.ending processId process reason).apply state := by
  unfold State.modify
  split
  · refine State.ext' (funext fun candidate => ?_) rfl rfl rfl
    simp only [Effect.processes_apply, Effect.record, Effect.ending, List.find?_cons, List.find?_nil,
      State.update, Kernel.find?_eq, Kernel.filter_eq, Kernel.foldl_eq]
    by_cases same : processId = candidate
    · subst same; simp
    · have : (processId == candidate) = false := by simpa using same
      simp [this, Ne.symm same]
  · rfl

private theorem State.view_eq {state other : State} {processId : PID}
    (same : (other.process processId).env = (state.process processId).env) :
    other.view processId = state.view processId := by
  simp only [ProcessState.env, ProcessState.mk.injEq] at same
  simp [State.view, same]

private theorem delivery_matches {state other : State} {processId : PID} {task : Task α}
    {envelope : Envelope} {rest : List Envelope}
    (mem : (envelope, rest) ∈ deliverable state.inTransit) (target : envelope.target = processId)
    (agree : (Footprint.delivery state envelope).observes.Agree state other) :
    (envelope, arrive envelope.source envelope.target other.inTransit) ∈ deliverable other.inTransit ∧
    Matches (Footprint.delivery state envelope).effect other (task.delivery state processId envelope rest)
      (task.delivery other processId envelope (arrive envelope.source envelope.target other.inTransit)) ∧
    (task.delivery state processId envelope rest).state = (Footprint.delivery state envelope).effect.apply state := by
  subst target
  obtain ⟨source, target, signal⟩ := envelope
  have channel : (Observes.mk [(target, ProcessState.live)] []
      [oldest source target]).Agree state other := by
    unfold Footprint.delivery at agree
    dsimp only at agree
    split at agree
    · split at agree <;> exact agree.left
    · exact agree
  obtain ⟨mem', rfl⟩ := arrives mem (channel.2.2.1 _ (by simp))
  refine ⟨mem', ?_⟩
  cases signal with
  | exit reason linked =>
    have processes : ∀ inTransit : List Envelope,
        ({ other with inTransit } : State).process target = other.process target := fun _ => rfl
    have processes' : ∀ inTransit : List Envelope,
        ({ state with inTransit } : State).process target = state.process target := fun _ => rfl
    simp only [Task.delivery, State.receive]
    rw [State.exitSignal_snd, State.exitSignal_snd, processes, processes']
    unfold Footprint.delivery at agree ⊢
    simp only [State.exitSignal_snd] at agree ⊢
    cases exiting : exits (state.process target) source reason linked with
    | none =>
      simp only [exiting] at agree ⊢
      have view := agree.right.record
      simp only [ProcessState.mk.injEq, true_and, and_true, Kernel.filter_eq] at view
      have same : exits (other.process target) source reason linked = none := by
        rw [← exiting]
        unfold exits
        rw [view.2.2, contains_of_filter view.2.1]
      simp only [same, Matches]
      rw [State.exitSignal_fst (by rw [processes]; exact same),
        State.exitSignal_fst (by rw [processes']; exact exiting)]
      simp only [Effect.apply_andThen, Effect.apply_inTransit, Effect.apply_change]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> trivial
    | some exit =>
      simp only [exiting] at agree ⊢
      have view := agree.right.record
      simp only [id] at view
      have same : exits (other.process target) source reason linked = some exit := by
        rw [view.2]; exact exiting
      simp only [same, Matches, Task.ended]
      rw [State.exitSignal_fst_exits (by rw [processes]; exact same),
        State.exitSignal_fst_exits (by rw [processes']; exact exiting)]
      simp only [Effect.apply_andThen, Effect.apply_inTransit]
      have ending : ∀ current : State, current.process target = state.process target →
          (if linked then current.modify target fun process =>
            { process with links := process.links.erase source } else current).terminate target exit =
          (Effect.ending target (if linked then { state.process target with
            links := Kernel.erase (state.process target).links source } else state.process target)
              exit).apply current := by
        intro current found
        simp only [Kernel.erase_eq]
        split
        · rw [← Effect.apply_ending, Effect.ending_modify]
          congr 2
          cases live : current.processes target with
          | none =>
            simp only [State.process, live, Option.getD_none] at found
            simp [State.process, State.modify_of_none live, ← found, live]
          | some process =>
            simp only [State.process, live, Option.getD_some] at found
            simp [State.process, State.modify_of_some live, State.update, ← found]
        · rw [← Effect.apply_ending, found]
      refine ⟨⟨trivial, trivial, trivial, trivial, ?_⟩, ?_⟩
      · exact ending _ view.2
      · exact ending _ rfl
  | _ =>
    simp only [Task.delivery, Matches]
    rw [State.receive_eq (by simp), State.receive_eq (by simp)]
    simp only [Footprint.delivery, Effect.apply_andThen, Effect.apply_inTransit, Effect.apply_change]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> trivial

/-! ### Own steps -/

private theorem State.processes_modify {state : State} {processId candidate : PID}
    {change : ProcessState → ProcessState} :
    (state.modify processId change).processes candidate =
      if candidate = processId then (state.processes processId).map change
      else state.processes candidate := by
  unfold State.modify
  cases found : state.processes processId with
  | none => split <;> simp_all
  | some process => simp [State.update]

@[simp] private theorem State.timers_modify' {state : State} {processId : PID}
    {change : ProcessState → ProcessState} : (state.modify processId change).timers = state.timers := by
  unfold State.modify; split <;> rfl

@[simp] private theorem State.inTransit_modify' {state : State} {processId : PID}
    {change : ProcessState → ProcessState} :
    (state.modify processId change).inTransit = state.inTransit := by
  unfold State.modify; split <;> rfl

@[simp] private theorem State.elapsed_modify {state : State} {processId : PID}
    {change : ProcessState → ProcessState} : (state.modify processId change).elapsed = state.elapsed := by
  unfold State.modify; split <;> rfl

private theorem State.alive_modify {state : State} {processId candidate : PID}
    {change : ProcessState → ProcessState} :
    (state.modify processId change).alive candidate = state.alive candidate := by
  simp only [State.alive, State.processes_modify]
  split <;> simp_all

/-- A change that applies only under a condition on the record. -/
private theorem State.modify_if {state : State} {processId : PID} {condition : ProcessState → Bool}
    {change : ProcessState → ProcessState} :
    (if condition (state.process processId) then state.modify processId change else state) =
      state.modify processId fun process => if condition process then change process else process := by
  cases found : state.processes processId with
  | none =>
    simp only [State.modify_of_none found]
    split <;> rfl
  | some process =>
    simp only [State.process, found, Option.getD_some, State.modify_of_some found]
    split <;> simp [*, State.update_self found]

private theorem State.modify_congr {state : State} {processId : PID}
    {change change' : ProcessState → ProcessState}
    (same : ∀ process, state.processes processId = some process → change process = change' process) :
    state.modify processId change = state.modify processId change' := by
  cases found : state.processes processId with
  | none => simp only [State.modify_of_none found]
  | some process => simp only [State.modify_of_some found, same process found]

/-- Spawning, as an effect. -/
private theorem State.spawnWith_eq {state : State} {processId : PID} {options : SpawnOptions}
    (live : (state.processes processId).isSome) :
    state.spawnWith processId options =
      (processId ++ [(state.process processId).children + 1],
        (Footprint.spawn state processId options).effect.apply state) := by
  obtain ⟨process, found⟩ := Option.isSome_iff_exists.mp live
  have distinct : processId ++ [process.children + 1] ≠ processId := by
    intro equal; have := congrArg List.length equal; simp at this
  simp only [State.process, found, Option.getD_some, State.spawnWith, State.spawn, State.allocate,
      Kernel.append_eq]
  refine Prod.ext rfl ?_
  dsimp only
  refine State.ext' (funext fun candidate => ?_) ?_ ?_ ?_
  · simp only [Effect.processes_apply, Effect.record, Footprint.spawn, State.process, found,
      Option.getD_some, List.find?_cons, List.find?_nil, Kernel.find?_eq, Kernel.append_eq]
    by_cases parent : processId = candidate
    · subst parent
      have : (processId ++ [process.children + 1] == processId) = false := beq_false_of_ne distinct
      cases options with
      | mk link monitor =>
        cases link <;> cases monitor <;>
          simp [State.processes_modify, State.update, found]
    · by_cases child : processId ++ [process.children + 1] = candidate
      · subst child
        have : (processId == processId ++ [process.children + 1]) = false :=
          beq_false_of_ne (Ne.symm distinct)
        cases options with
        | mk link monitor =>
          cases link <;> cases monitor <;>
            simp [this, State.processes_modify, State.update, distinct]
      · have : (processId == candidate) = false := by simpa using parent
        have this' : (processId ++ [process.children + 1] == candidate) = false := by
          simpa using child
        cases options with
        | mk link monitor =>
          cases link <;> cases monitor <;>
            simp [this, this', State.processes_modify, State.update, Ne.symm parent, Ne.symm child]
  all_goals
    cases options with
    | mk link monitor => cases link <;> cases monitor <;> simp [State.update] <;> rfl

private theorem Footprint.spawn_congr {state other : State} {processId : PID} {options : SpawnOptions}
    (children : (other.process processId).children = (state.process processId).children)
    (counter : (other.process processId).refCounter = (state.process processId).refCounter) :
    Footprint.spawn other processId options = Footprint.spawn state processId options := by
  simp only [Footprint.spawn, children, counter, Kernel.append_eq]

private theorem selectMessage_value {select : Term → Option β} {mailbox : List Term} {message : Term}
    {value : β} {rest : List Term} (selected : selectMessage select mailbox = some (message, value, rest)) :
    select message = some value := by
  induction mailbox generalizing rest with
  | nil => simp [selectMessage] at selected
  | cons head tail ih =>
    simp only [selectMessage] at selected
    split at selected
    · rename_i found
      simp only [Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl, rfl⟩ := selected
      exact found
    · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at selected
      obtain ⟨_, _, rest', found, rfl, rfl, rfl⟩ := selected
      exact ih found

/-- Lists related elementwise. -/
private inductive Related (relation : γ → δ → Prop) : List γ → List δ → Prop
  | nil : Related relation [] []
  | cons {first : γ} {second : δ} {rest : List γ} {rest' : List δ} :
      relation first second → Related relation rest rest' →
        Related relation (first :: rest) (second :: rest')

private theorem related_single {relation : γ → δ → Prop} {first : γ} {second : δ}
    (related : relation first second) : Related relation [first] [second] :=
  .cons related .nil

private theorem ending_matches {state other : State} {processId : PID} {reason : Term}
    {finish : Except Exception γ → Option (Except Exception α)} {event : Event}
    {result : Except Exception γ}
    (same : (other.process processId).ending = (state.process processId).ending) :
    Matches (Effect.ending processId (state.process processId) reason) other
      (Task.ended finish event state processId reason result)
      (Task.ended finish event other processId reason result) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [Task.ended]
  rw [← Effect.apply_ending, Effect.ending_congr same]

/-- Answers to a request at two states agreeing on what it observes: the same
reply and exit, and the effect applied, or the process ends unchanged. -/
private def Answers (effect : Effect) (state other : State) (processId : PID)
    (answer answer' : Term × State × Option Term) : Prop :=
  answer'.1 = answer.1 ∧ answer'.2.2 = answer.2.2 ∧
    match answer.2.2 with
    | none => answer'.2.1 = effect.apply other
    | some reason => answer.2.1 = state ∧ answer'.2.1 = other ∧
        other.terminate processId reason = effect.apply other

private theorem any_eq_filter {items : List γ} {condition : γ → Bool} :
    (!(items.filter condition).isEmpty) = items.any condition := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [List.filter_cons, List.any_cons]; split <;> simp_all

private theorem alive_eq {state other : State} {processId : PID}
    (same : (other.processes processId).isSome = (state.processes processId).isSome) :
    other.alive processId = state.alive processId := same

private theorem request_matches {state other : State} {processId : PID} {query : Request}
    (agree : (requestFootprint state processId query).observes.Agree state other) :
    Option.Rel (Answers (requestFootprint state processId query).effect state other processId)
      (state.request processId query) (other.request processId query) := by
  cases query with
  | monitor target alias =>
    by_cases self : target = processId
    · subst self
      simp only [requestFootprint, ↓reduceIte] at agree ⊢
      have view := agree.record
      simp only [ProcessState.mk.injEq, true_and, and_true] at view
      simp only [State.request, State.allocate, ↓reduceIte, view.2, Kernel.append_eq]
      exact .some ⟨rfl, rfl, by simp⟩
    · simp only [requestFootprint, self, ↓reduceIte, Kernel.append_eq] at agree ⊢
      have counter := agree.left.record
      simp only [ProcessState.mk.injEq, true_and, and_true] at counter
      have target' := alive_eq agree.right.record.1
      simp only [State.request, State.allocate, self, ↓reduceIte, State.alive_modify, counter.2,
          target', Kernel.append_eq]
      refine .some ⟨rfl, rfl, ?_⟩
      simp only [Effect.apply_andThen, Effect.apply_change, Effect.apply_send, State.modify_modify]
      split <;> rfl
  | demonitor reference flush =>
    simp only [requestFootprint, Kernel.any_eq, Kernel.erase_eq, Kernel.eraseP_eq,
        Kernel.filter_eq] at agree ⊢
    have view := agree.record
    simp only [ProcessState.mk.injEq, true_and, and_true] at view
    have active : (other.process processId).monitoring.any (·.1 == reference) =
        (state.process processId).monitoring.any (·.1 == reference) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨entry, mem, found⟩
        have : entry ∈ (other.process processId).monitoring.filter (·.1 == reference) :=
          List.mem_filter.mpr ⟨mem, found⟩
        rw [view.2] at this
        exact ⟨entry, (List.mem_filter.mp this).1, found⟩
      · rintro ⟨entry, mem, found⟩
        have : entry ∈ (state.process processId).monitoring.filter (·.1 == reference) :=
          List.mem_filter.mpr ⟨mem, found⟩
        rw [← view.2] at this
        exact ⟨entry, (List.mem_filter.mp this).1, found⟩
    simp only [State.request, active, Kernel.any_eq, Kernel.erase_eq, Kernel.eraseP_eq,
        Kernel.filter_eq]
    refine .some ⟨rfl, rfl, ?_⟩
    simp only [Effect.apply_change]
    refine State.modify_congr fun process found => ?_
    have : other.process processId = process := by simp [State.process, found]
    rw [← this, active]
  | link target =>
    simp only [requestFootprint] at agree ⊢
    have agree' : ((Observes.record processId fun process => { trapExit := process.trapExit }).and
        (.record target ProcessState.live)).Agree state other := by
      split at agree
      · exact agree
      · split at agree <;> exact agree
    have trapping := agree'.left.record
    simp only [ProcessState.mk.injEq, true_and, and_true] at trapping
    have target' := alive_eq agree'.right.record.1
    by_cases self : target = processId
    · simp only [self, ↓reduceIte, State.request]
      exact .some ⟨rfl, rfl, by simp⟩
    · simp only [self, ↓reduceIte, State.request, target', trapping.2]
      split
      · exact .some ⟨rfl, rfl, by simp⟩
      · refine .some ⟨rfl, rfl, ?_⟩
        simp only [Effect.apply_andThen, Effect.apply_change, Effect.apply_send, State.alive_modify,
          target']
        split <;> rfl
  | unlink target =>
    simp only [requestFootprint, State.request, Kernel.erase_eq]
    refine .some ⟨rfl, rfl, ?_⟩
    simp only [Effect.apply_andThen, Effect.apply_change]
    split <;> simp
  | exit target reason =>
    by_cases self : target = processId
    · subst self
      simp only [requestFootprint, ↓reduceIte] at agree ⊢
      have trapping := agree.view (processId := target)
        (view := fun process => { trapExit := process.trapExit })
        (by split <;> simp [Observes.and, Observes.record])
      simp only [ProcessState.mk.injEq, true_and, and_true] at trapping
      have ends : ∀ exit, (isKill reason || !(state.process target).trapExit) = true →
          other.terminate target exit = (Effect.ending target (state.process target) exit).apply other := by
        intro exit condition
        rw [ite_eq_left condition] at agree
        have ending := (agree.right : (Observes.record target ProcessState.ending).Agree state other).record
        rw [← Effect.apply_ending, Effect.ending_congr ending.2]
      simp only [State.request, ↓reduceIte, trapping.2, State.exitSignal, Bool.false_and,
        Bool.false_eq_true, Bool.not_false, Bool.true_and, Kernel.contains_eq]
      cases kill : isKill reason
      · cases trap : (state.process target).trapExit
        · have condition : (isKill reason || !(state.process target).trapExit) = true := by
            simp [kill, trap]
          have ending := ends reason condition
          simp only [↓reduceIte, Bool.false_eq_true, Bool.not_false, Bool.and_true]
          cases normal : isNormal reason <;> exact .some ⟨rfl, rfl, rfl, rfl, ending⟩
        · have condition : (isKill reason || !(state.process target).trapExit) = false := by
            simp [kill, trap]
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.and_false]
          exact .some ⟨rfl, rfl, by simp [State.append_eq]⟩
      · have condition : (isKill reason || !(state.process target).trapExit) = true := by simp [kill]
        have ending := ends (.atom "killed") condition
        have normal : isNormal reason = false := by
          unfold isKill at kill; unfold isNormal; split <;> simp_all
        simp only [↓reduceIte, normal, Bool.false_and, Bool.false_eq_true]
        exact .some ⟨rfl, rfl, rfl, rfl, ending⟩
    · simp only [requestFootprint, State.request, self, ↓reduceIte]
      exact .some ⟨rfl, rfl, by simp⟩
  | trapExit enabled =>
    simp only [requestFootprint] at agree ⊢
    have view := agree.record
    simp only [ProcessState.mk.injEq, true_and, and_true] at view
    simp only [State.request, view.2]
    exact .some ⟨rfl, rfl, by simp⟩
  | alive target =>
    by_cases self : target = processId
    · simp only [requestFootprint, State.request, self, ↓reduceIte]
      exact .some ⟨rfl, rfl, by simp⟩
    · simp only [requestFootprint, self, ↓reduceIte, Kernel.filter_eq] at agree ⊢
      have target' := alive_eq (agree.view (processId := target) (view := ProcessState.live)
        (by simp)).1
      have between := agree.2.2.1 _ (List.mem_singleton_self _)
      have pending : ∀ current : State, (current.inTransit.any fun envelope =>
          (envelope.source == processId && envelope.target == target) ||
            (envelope.source == target && envelope.target == processId)) =
          !(current.inTransit.filter fun envelope =>
            envelope.between processId target || envelope.between target processId).isEmpty := by
        intro current
        rw [← any_eq_filter]
        rfl
      simp only [State.request, self, ↓reduceIte, pending, between, target', Kernel.any_eq]
      split
      · exact .none
      · exact .some ⟨rfl, rfl, by simp⟩
  | sendAlias alias message =>
    simp only [requestFootprint, State.request, Kernel.contains_eq]
    split
    · refine .some ⟨rfl, rfl, ?_⟩
      simp only [Effect.apply_change, State.append_eq]
      exact State.modify_if (condition := fun process => process.aliases.contains alias)
        (change := ProcessState.append message)
    · exact .some ⟨rfl, rfl, by simp⟩
  | startTimer destination message duration =>
    simp only [requestFootprint, Kernel.append_eq] at agree ⊢
    have counter := agree.left.record
    simp only [ProcessState.mk.injEq, true_and, and_true] at counter
    have destination' := alive_eq agree.right.record.1
    simp only [State.request, State.allocate, State.alive_modify, counter.2, destination',
        Kernel.append_eq]
    refine .some ⟨rfl, rfl, ?_⟩
    simp only [Effect.apply_andThen, Effect.apply_change]
    split
    · refine State.ext' ?_ rfl rfl rfl
      rfl
    · simp
  | cancelTimer reference =>
    simp only [requestFootprint, Kernel.filter_eq, Kernel.find?_eq] at agree ⊢
    have cancels := agree.view (processId := processId) (view := fun process => { cancels := process.cancels })
      (by simp)
    simp only [ProcessState.mk.injEq] at cancels
    have timers := agree.2.1 _ (List.mem_singleton_self _)
    have found : other.timers.find? (·.reference == reference) =
        state.timers.find? (·.reference == reference) := by
      rw [← List.head?_filter, ← List.head?_filter, timers]
    simp only [State.request, found, cancels.2, agree.2.2.2, Kernel.filter_eq, Kernel.find?_eq]
    cases found' : state.timers.find? (·.reference == reference) with
    | some timer =>
      refine .some ⟨rfl, rfl, ?_⟩
      refine State.ext' (funext fun candidate => ?_) (by simp [Effect.apply])
        (by simp [Effect.apply]) (by simp [Effect.apply, agree.2.2.2])
      simp only [Effect.processes_apply, Effect.record, List.find?_cons, List.find?_nil,
        State.processes_modify, Kernel.find?_eq]
      by_cases same : processId = candidate
      · subst same; simp
      · have : (processId == candidate) = false := by simpa using same
        simp [this, Ne.symm same]
    | none =>
      exact .some ⟨rfl, rfl, by simp⟩

private theorem own_matches {state other : State} {processId : PID} {task : Task α}
    (live : (state.processes processId).isSome)
    (agree : (task.footprint state processId).observes.Agree state other) :
    Related (Matches (task.footprint state processId).effect other) (task.own state processId)
      (task.own other processId) := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | ok value =>
    have := (agree : (Footprint.ending state processId _).observes.Agree state other).record
    exact related_single (ending_matches this.2)
  | error exception =>
    cases exception with
    | exhausted =>
      refine related_single ⟨rfl, rfl, rfl, rfl, ?_⟩
      exact Effect.apply_remove.symm
    | _ =>
      have := (agree : (Footprint.ending state processId _).observes.Agree state other).record
      exact related_single (ending_matches this.2)
  | get next =>
    have view := (agree : (Observes.record processId ProcessState.env).Agree state other).record
    refine related_single ⟨rfl, ?_, rfl, rfl, Effect.apply_empty.symm⟩
    simp [State.view_eq view.2]
  | set updated next =>
    refine related_single ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [Task.footprint, Effect.apply_change]
    rfl
  | schedule options child next =>
    have view := (agree : (Footprint.spawn state processId options).observes.Agree state other).record
    simp only [ProcessState.mk.injEq, true_and, and_true] at view
    have live' : (other.processes processId).isSome := view.1.trans live
    simp only [Task.own, Task.footprint, State.spawnWith_eq live, State.spawnWith_eq live',
      Footprint.spawn_congr view.2.2 view.2.1]
    exact related_single ⟨by rw [view.2.2], by rw [view.2.2], rfl, rfl, rfl⟩
  | send destination message next =>
    refine related_single ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [Task.footprint]
    split <;> simp [State.append_eq]
  | receive timeout select next =>
    have view := (agree : (Observes.record processId fun process =>
      { pdict := process.pdict, refCounter := process.refCounter
        mailbox := selected (select (state.view processId)) process.mailbox }).Agree state other).record
    simp only [ProcessState.mk.injEq, and_true] at view
    have env : other.view processId = state.view processId :=
      State.view_eq (by simp [ProcessState.env, view.2.1, view.2.2.2])
    have chosen := view.2.2.1
    simp only [Task.own, Task.footprint, env]
    generalize select (state.view processId) = choose at chosen ⊢
    cases found : selectMessage choose (state.process processId).mailbox with
    | some selection =>
      obtain ⟨message, value, rest⟩ := selection
      obtain ⟨value', rest', found'⟩ : ∃ value' rest',
          selectMessage choose (other.process processId).mailbox = some (message, value', rest') := by
        simp only [selected, found] at chosen
        split at chosen
        · rename_i message' value' rest' found'
          simp only [List.cons.injEq, and_true] at chosen
          exact ⟨value', rest', chosen ▸ found'⟩
        · simp at chosen
      have same : value' = value := by
        have := (selectMessage_value found').symm.trans (selectMessage_value found)
        simpa using this
      subst same
      simp only [found']
      refine related_single ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp only [Effect.apply_change]
      refine State.modify_congr fun process live' => ?_
      have : (other.process processId).mailbox = process.mailbox := by simp [State.process, live']
      simp [remaining, ← this, found']
    | none =>
      have found' : selectMessage choose (other.process processId).mailbox = none := by
        simp only [selected, found] at chosen
        split at chosen
        · simp at chosen
        · assumption
      simp only [found']
      cases timeout
      · exact .nil
      all_goals exact related_single ⟨rfl, rfl, rfl, rfl, Effect.apply_empty.symm⟩
  | request query next =>
    have answers := request_matches (state := state) (other := other) (processId := processId)
      (query := query) agree
    simp only [Task.own, Task.footprint]
    revert answers
    generalize state.request processId query = answer
    generalize other.request processId query = answer'
    intro answers
    cases answers with
    | none => exact .nil
    | some answers =>
      rename_i answer answer'
      obtain ⟨reply, answered, exit⟩ := answer
      obtain ⟨reply', answered', exit'⟩ := answer'
      obtain ⟨replied, exited, settled⟩ := answers
      simp only at replied exited settled
      subst replied exited
      cases exit' with
      | none => exact related_single ⟨rfl, rfl, rfl, rfl, settled⟩
      | some reason =>
        obtain ⟨rfl, rfl, ending⟩ := settled
        exact related_single ⟨rfl, rfl, rfl, rfl, ending⟩

/-- A process's own step observes the process. -/
private theorem Task.footprint_observes {state : State} {processId : PID} {task : Task α} :
    ∃ view, (processId, view) ∈ (task.footprint state processId).observes.records := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | error exception =>
    cases exception <;> simp only [Task.footprint, Footprint.ending, Observes.record] <;>
      exact ⟨_, List.mem_cons_self⟩
  | request query next =>
    cases query <;> simp only [Task.footprint, requestFootprint, Kernel.any_eq, Kernel.append_eq,
        Kernel.contains_eq, Kernel.erase_eq, Kernel.eraseP_eq, Kernel.filter_eq,
        Kernel.find?_eq] <;> (repeat' split) <;>
      (try simp only [Observes.record, Observes.and, List.cons_append, List.nil_append,
          Kernel.append_eq]) <;>
      exact ⟨_, List.mem_cons_self⟩
  | _ =>
    simp only [Task.footprint, Footprint.ending, Footprint.spawn, Observes.record,
        Kernel.append_eq] <;>
      exact ⟨_, List.mem_cons_self⟩

/-- Own steps are at most one. -/
private theorem Task.own_length {state : State} {processId : PID} {task : Task α} :
    (task.own state processId).length ≤ 1 := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | receive timeout select next =>
    simp only [Task.own]
    split
    · simp
    · cases timeout <;> simp
  | request query next =>
    simp only [Task.own]
    split <;> simp
  | error exception => cases exception <;> simp [Task.own]
  | _ => simp [Task.own]

/-- Related lists relate their elements at each index. -/
private theorem Related.get {relation : γ → δ → Prop} {first : List γ} {second : List δ}
    (related : Related relation first second) {index : Nat} {item : γ}
    (found : first[index]? = some item) : ∃ item', second[index]? = some item' ∧ relation item item' := by
  induction related generalizing index with
  | nil => simp at found
  | cons head _ ih =>
    cases index with
    | zero => simp at found; subst found; exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

/-- A step of a process changes the state as its footprint says. -/
private theorem own_state {state : State} {processId : PID} {task : Task α} {transition : Transition α}
    (live : (state.processes processId).isSome) (mem : transition ∈ task.own state processId) :
    transition.state = (task.footprint state processId).effect.apply state := by
  have related := own_matches (task := task) live (Observes.Agree.refl _ state)
  obtain ⟨index, bound, rfl⟩ := List.getElem_of_mem mem
  obtain ⟨transition', found, matched⟩ := related.get (index := index)
    (List.getElem?_eq_getElem bound)
  simp only [List.getElem?_eq_getElem bound, Option.some.injEq] at found
  subst found
  exact matched.2.2.2.2

end Lynx.Concurrent

namespace Lynx.Concurrent

open Lynx

/-! ### What steps observe and change of other processes -/

/-- A process's own step observes other processes only through whether they are live. -/
private theorem Task.footprint_observes_others {state : State} {processId : PID} {task : Task α} :
    ∀ entry ∈ (task.footprint state processId).observes.records,
      entry.1 = processId ∨ entry.2 = ProcessState.live := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | error exception =>
    cases exception <;> simp [Task.footprint, Footprint.ending, Observes.record]
  | request query next =>
    cases query <;> simp only [Task.footprint, requestFootprint, Kernel.any_eq, Kernel.append_eq,
        Kernel.contains_eq, Kernel.erase_eq, Kernel.eraseP_eq, Kernel.filter_eq,
        Kernel.find?_eq] <;> (repeat' split) <;>
      simp [Observes.record, Observes.and]
  | _ => simp [Task.footprint, Footprint.ending, Footprint.spawn, Observes.record]

/-- A process's own step changes its own record, and the record of a child it spawns. -/
private theorem Task.footprint_changes {state : State} {processId : PID} {task : Task α} :
    ∀ entry ∈ (task.footprint state processId).effect.records,
      entry.1 = processId ∨ entry.1 = processId ++ [(state.process processId).children + 1] := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | error exception =>
    cases exception <;> simp [Task.footprint, Footprint.ending, Effect.ending]
  | request query next =>
    cases query <;> simp only [Task.footprint, requestFootprint, Kernel.any_eq, Kernel.append_eq,
        Kernel.contains_eq, Kernel.erase_eq, Kernel.eraseP_eq, Kernel.filter_eq,
        Kernel.find?_eq] <;> (repeat' split) <;>
      simp [Effect.andThen, Effect.change, Effect.send, Effect.ending]
  | receive timeout select next =>
    simp only [Task.footprint]
    split <;> simp [Effect.change]
  | send destination message next =>
    simp only [Task.footprint]
    split <;> simp [Effect.change, Effect.send]
  | _ => simp [Task.footprint, Footprint.ending, Footprint.spawn, Effect.change, Effect.ending]

/-- A signal arriving changes the receiver's record only. -/
private theorem Footprint.delivery_changes {state : State} {envelope : Envelope} :
    ∀ entry ∈ (Footprint.delivery state envelope).effect.records, entry.1 = envelope.target := by
  obtain ⟨source, target, signal⟩ := envelope
  unfold Footprint.delivery
  cases signal <;> simp only <;> (try split) <;>
    simp [Effect.andThen, Effect.change, Effect.ending]

/-- A signal arriving observes the receiver's record only. -/
private theorem Footprint.delivery_observes_target {state : State} {envelope : Envelope} :
    ∀ entry ∈ (Footprint.delivery state envelope).observes.records, entry.1 = envelope.target := by
  obtain ⟨source, target, signal⟩ := envelope
  unfold Footprint.delivery
  cases signal <;> simp only <;> (try split) <;> simp [Observes.and, Observes.record]

end Lynx.Concurrent

namespace Lynx.Concurrent

open Lynx

/-! ### Steps that stay in the process's own record -/

/-- Whether a process's next step only reads or replaces its environment, or
receives a message already queued. Its effects stay in its own record. -/
@[expose] def Task.local (state : State) (processId : PID) : Task α → Bool
  | ⟨computation, _⟩ =>
    match computation with
    | .get _ | .set .. => true
    | .receive _ select _ =>
        (selectMessage (select (state.view processId)) (state.process processId).mailbox).isSome
    | _ => false

/-- A signal changes a mailbox only by appending to it, and what it appends
and the rest of the record do not depend on the mailbox or the environment. -/
private theorem ProcessState.receive_split {process : ProcessState} {source : PID} {signal : Signal} :
    let core := ({ process with mailbox := [] } : ProcessState).receive source signal
    process.receive source signal = { core with mailbox := process.mailbox ++ core.mailbox } ∧
      core.pdict = process.pdict ∧ core.refCounter = process.refCounter := by
  cases process
  cases signal <;> simp only [ProcessState.receive, ProcessState.append, Kernel.append_eq,
      Kernel.any_eq, Kernel.contains_eq, Kernel.erase_eq, Kernel.filter_eq] <;> (repeat' split) <;>
    simp_all

private theorem selectMessage_append {select : Term → Option β} {mailbox extra : List Term}
    (matched : (selectMessage select mailbox).isSome) :
    selected select (mailbox ++ extra) = selected select mailbox ∧
      remaining select (mailbox ++ extra) = remaining select mailbox ++ extra ∧
      (selectMessage select (mailbox ++ extra)).isSome := by
  obtain ⟨⟨message, value, rest⟩, found⟩ := Option.isSome_iff_exists.mp matched
  obtain ⟨-, -, -, extend⟩ := selectMessage_index found
  simp [selected, remaining, found, extend]

/-- A local step: what it observes of its process, how it changes the record,
and the records it applies to. -/
private structure LocalShape (view : ProcessState → ProcessState) (change : ProcessState → ProcessState)
    (ready : ProcessState → Prop) : Prop where
  receive : ∀ process source signal, ready process →
    ready (process.receive source signal) ∧ view (process.receive source signal) = view process ∧
      change (process.receive source signal) = (change process).receive source signal
  fields : ∀ process, ∃ pdict refCounter mailbox, change process = { process with pdict, refCounter, mailbox }
  links : ∀ process links, change { process with links } = { change process with links }

private theorem Task.local_shape {state : State} {processId : PID} {task : Task α}
    (isLocal : task.local state processId = true) :
    ∃ view change ready, (task.footprint state processId).observes = .record processId view ∧
      (∀ current : State, (task.footprint state processId).effect.apply current =
        current.modify processId change) ∧
      (∀ entry ∈ (task.footprint state processId).effect.records, entry.1 = processId) ∧
      ready (state.process processId) ∧ LocalShape view change ready ∧
      ∀ current : State, current.view processId = state.view processId →
        ready (current.process processId) → task.local current processId = true := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | get next =>
    refine ⟨ProcessState.env, id, fun _ => True, rfl, fun current => ?_, by simp [Task.footprint],
      trivial, ⟨fun process source signal _ => ?_, fun process => ⟨process.pdict, process.refCounter,
        process.mailbox, rfl⟩, fun _ _ => rfl⟩, fun _ _ _ => rfl⟩
    · simp only [Task.footprint, Effect.apply_empty]
      cases found : current.processes processId with
      | none => rw [State.modify_of_none found]
      | some record => rw [State.modify_of_some found]; exact (State.update_self found).symm
    · obtain ⟨split, pdict, refCounter⟩ := ProcessState.receive_split (process := process)
        (source := source) (signal := signal)
      refine ⟨trivial, ?_, rfl⟩
      rw [split]
      simp [ProcessState.env, pdict, refCounter]
  | set updated next =>
    let change : ProcessState → ProcessState := fun process =>
      { process with pdict := updated.pdict, refCounter := max process.refCounter updated.refCounter }
    refine ⟨ProcessState.live, change, fun _ => True, rfl,
      fun current => by simp only [Task.footprint, Effect.apply_change]; rfl,
      by simp [Task.footprint, Effect.change],
      trivial, ⟨fun process source signal _ => ⟨trivial, rfl, ?_⟩,
        fun process => ⟨_, _, process.mailbox, rfl⟩, fun _ _ => rfl⟩, fun _ _ _ => rfl⟩
    cases process
    cases signal <;> simp only [change, ProcessState.receive, ProcessState.append,
        Kernel.append_eq, Kernel.any_eq, Kernel.contains_eq, Kernel.erase_eq, Kernel.filter_eq] <;>
      (repeat' split) <;> simp_all
  | receive timeout select next =>
    simp only [Task.local] at isLocal
    let choose := select (state.view processId)
    let view : ProcessState → ProcessState := fun process =>
      { pdict := process.pdict, refCounter := process.refCounter, mailbox := selected choose process.mailbox }
    let change : ProcessState → ProcessState := fun process =>
      { process with mailbox := remaining choose process.mailbox }
    refine ⟨view, change, fun process => (selectMessage choose process.mailbox).isSome, rfl,
      fun current => ?_, ?_, isLocal,
      ⟨fun process source signal ready => ?_, fun process => ⟨_, _, _, rfl⟩, fun _ _ => rfl⟩,
      fun current same ready => by simp only [Task.local, same]; exact ready⟩
    · simp only [Task.footprint]
      split
      · simp only [Effect.apply_change]; rfl
      · simp_all
    · simp only [Task.footprint]
      split <;> simp [Effect.change]
    · obtain ⟨split, pdict, refCounter⟩ := ProcessState.receive_split (process := process)
        (source := source) (signal := signal)
      obtain ⟨same, rest, matched⟩ := selectMessage_append (extra := (({ process with mailbox := [] } :
        ProcessState).receive source signal).mailbox) ready
      refine ⟨by rw [split]; exact matched, ?_, ?_⟩
      · rw [split]
        simp only [view, pdict, refCounter, same]
      · obtain ⟨split', -, -⟩ := ProcessState.receive_split
          (process := change process) (source := source) (signal := signal)
        rw [split, split']
        simp only [change, rest]
  | _ => simp [Task.local] at isLocal

end Lynx.Concurrent

namespace Lynx.Concurrent

open Lynx

/-- A local step continues the process, with the same report. -/
private theorem Task.local_own {state : State} {processId : PID} {task : Task α}
    (isLocal : task.local state processId = true) :
    ∃ transition computation, task.own state processId = [transition] ∧
      transition.tasks = [(processId, ⟨computation, task.finish⟩)] ∧ transition.finished = none ∧
      transition.exhausted = false := by
  obtain ⟨computation, finish⟩ := task
  cases computation with
  | get next => exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | set updated next => exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | receive timeout select next =>
    simp only [Task.local] at isLocal
    obtain ⟨⟨message, value, rest⟩, found⟩ := Option.isSome_iff_exists.mp isLocal
    simp only [Task.own, found]
    exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | _ => simp [Task.local] at isLocal

end Lynx.Concurrent

namespace Lynx.Concurrent

open Lynx

/-- A process ends the same way after a change of its record that keeps whom it signals. -/
private theorem State.terminate_modify {state : State} {processId : PID} {reason : Term}
    {change : ProcessState → ProcessState}
    (keeps : ∀ process, (change process).ending = process.ending) :
    (state.modify processId change).terminate processId reason = state.terminate processId reason := by
  rw [← Effect.apply_ending, ← Effect.apply_ending, Effect.ending_modify]
  cases found : state.processes processId with
  | none => simp [State.modify_of_none found]
  | some process =>
    rw [State.modify_of_some found]
    have : ((state.update processId (some (change process))).process processId) = change process := by
      simp [State.process, State.update]
    rw [this, Effect.ending_congr (keeps process)]
    simp [State.process, found]

/-- A signal ending a process does so the same way after a local step, which
keeps whether it traps exits and whom it is linked to. -/
private theorem local_absorbed {state : State} {processId source : PID} {signal : Signal}
    {change : ProcessState → ProcessState}
    (fields : ∀ process, ∃ pdict refCounter mailbox,
      change process = { process with pdict, refCounter, mailbox })
    (linksChange : ∀ process links, change { process with links } = { change process with links })
    (ends : (state.receive ⟨source, processId, signal⟩).2.isSome) :
    ((state.modify processId change).receive ⟨source, processId, signal⟩).2 =
        (state.receive ⟨source, processId, signal⟩).2 ∧
      ((state.modify processId change).receive ⟨source, processId, signal⟩).1.terminate processId
          ((state.receive ⟨source, processId, signal⟩).2.getD .nil) =
        (state.receive ⟨source, processId, signal⟩).1.terminate processId
          ((state.receive ⟨source, processId, signal⟩).2.getD .nil) := by
  cases signal with
  | exit reason linked =>
    simp only [State.receive] at ends ⊢
    have process : ((state.modify processId change).process processId).links =
          (state.process processId).links ∧
        ((state.modify processId change).process processId).trapExit =
          (state.process processId).trapExit := by
      cases found : state.processes processId with
      | none => simp [State.modify_of_none found]
      | some record =>
        obtain ⟨pdict, refCounter, mailbox, changed⟩ := fields record
        simp [State.modify_of_some found, State.process, State.update, found, changed]
    have same : exits ((state.modify processId change).process processId) source reason linked =
        exits (state.process processId) source reason linked := by
      unfold exits; rw [process.1, process.2]
    rw [State.exitSignal_snd] at ends
    obtain ⟨exit, exiting⟩ := Option.isSome_iff_exists.mp ends
    refine ⟨by rw [State.exitSignal_snd, State.exitSignal_snd, same], ?_⟩
    rw [State.exitSignal_fst_exits (by rw [same]; exact exiting), State.exitSignal_fst_exits exiting]
    have keeps : ∀ process, (change process).ending = process.ending := by
      intro process
      obtain ⟨pdict, refCounter, mailbox, changed⟩ := fields process
      simp [changed, ProcessState.ending]
    split
    · rw [State.modify_modify]
      have swapped : ((fun process : ProcessState =>
            { process with links := process.links.erase source }) ∘ change) =
          change ∘ fun process => { process with links := process.links.erase source } := by
        funext process
        obtain ⟨pdict, refCounter, mailbox, changed⟩ := fields process
        have erased := linksChange process (process.links.erase source)
        simp only [Function.comp_apply, erased, changed]
      rw [swapped, ← State.modify_modify, State.terminate_modify keeps]
    · exact State.terminate_modify keeps
  | _ => simp [State.receive_eq] at ends

end Lynx.Concurrent
