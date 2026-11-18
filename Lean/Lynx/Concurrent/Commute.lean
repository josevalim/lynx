module

public import Lynx.Concurrent
public import Lynx.Term.Compare
public import Lynx.Concurrent.Kernel

/-! When two steps commute. Each step has a key, and a configuration has at
most one step per key. Two steps commute when each can follow the other, both
orders reach identical states, and neither changes what the other's process
continues with (`Task.view`). States are compared directly; processes, whose
computations cannot be compared, are compared through the views they were
computed from. -/

public section

namespace Lynx.Concurrent

open Lynx

attribute [local instance high] Kernel.pidBEq

/-! ### Comparing states -/

/-- Whether two lists are the same, comparing their elements with `same`. -/
@[expose] def identicalLists (same : γ → γ → Bool) : List γ → List γ → Bool
  | [], [] => true
  | first :: rest, second :: rest' => same first second && identicalLists same rest rest'
  | _, _ => false

/-- Whether two signals are the same. -/
@[expose] def Signal.identical : Signal → Signal → Bool
  | .message term, .message term' => term.identical term'
  | .aliasMessage alias term, .aliasMessage alias' term' => alias == alias' && term.identical term'
  | .exit reason linked kills, .exit reason' linked' kills' =>
      reason.identical reason' && linked == linked' && kills == kills'
  | .link, .link | .isAlive, .isAlive | .flush, .flush => true
  | .unlink id, .unlink id' | .unlinkAck id, .unlinkAck id' => id == id'
  | .monitor reference, .monitor reference' => reference == reference'
  | .down reference reason, .down reference' reason' => reference == reference' && reason.identical reason'
  | .reply value, .reply value' => value.identical value'
  | _, _ => false

/-- Whether two queued signals are the same. -/
@[expose] def Entry.identical (first second : Entry) : Bool :=
  first.source == second.source && first.signal.identical second.signal

/-- Whether two exit phases are the same. -/
@[expose] def Exiting.identical (first second : Exiting) : Bool :=
  first.reason.identical second.reason && first.links == second.links && first.downs == second.downs

/-- Whether two optional values are the same. -/
@[expose] def optionIdentical (same : γ → γ → Bool) : Option γ → Option γ → Bool
  | some first, some second => same first second
  | none, none => true
  | _, _ => false

/-- Whether two records are the same. -/
@[expose] def ProcessState.identical (first second : ProcessState) : Bool :=
  identicalLists Entry.identical first.queue second.queue &&
    Term.identicalList first.mailbox second.mailbox &&
    Term.identicalEntries first.pdict second.pdict &&
    first.refCounter == second.refCounter && first.children == second.children &&
    first.links == second.links && first.monitors == second.monitors &&
    first.monitoring == second.monitoring && first.aliases == second.aliases &&
    first.trapExit == second.trapExit && first.cancels == second.cancels &&
    first.unlinks == second.unlinks && first.parked == second.parked &&
    first.eagerExits == second.eagerExits && optionIdentical Exiting.identical first.exiting second.exiting

/-- Whether two timers are the same. -/
@[expose] def Timer.identical (first second : Timer) : Bool :=
  first.reference == second.reference && first.destination == second.destination &&
    first.message.identical second.message && first.duration == second.duration

/-- Whether two states are the same, except for the time elapsed, which no step changes. -/
@[expose] def State.identical (first second : State) : Bool :=
  identicalLists (fun record record' => record.1 == record'.1 && record.2.identical record'.2)
    first.processes second.processes &&
  identicalLists Timer.identical first.timers second.timers

/-! ### Keys -/

/-- Which step of a configuration: a process's own step, its handling of the
oldest signal it queued, a phase of a process that ended signaling one of its
links or else its next phase, a parked monitor signal sent, or a timer firing. -/
inductive Key where
  | own (processId : PID)
  | handle (processId : PID)
  | link (processId target : PID)
  | phase (processId : PID)
  | unpark (processId : PID)
  | fire (reference : List Nat)

/-- Compare keys in evaluation. -/
@[expose] def Key.beq : Key → Key → Bool
  | .own processId, .own processId' | .handle processId, .handle processId'
  | .phase processId, .phase processId' | .unpark processId, .unpark processId' => processId == processId'
  | .link processId target, .link processId' target' => processId == processId' && target == target'
  | .fire reference, .fire reference' => reference == reference'
  | _, _ => false

instance : BEq Key := ⟨Key.beq⟩

instance : LawfulBEq Key where
  eq_of_beq {first second} equal := by
    change Key.beq first second = true at equal
    cases first <;> cases second <;> simp_all [Key.beq]
  rfl {key} := by
    change Key.beq key key = true
    cases key <;> simp [Key.beq]

instance : DecidableEq Key := fun first second => decidable_of_iff (first == second) beq_iff_eq

/-- Whether a key is a process's own step. -/
@[expose] def Key.isOwn : Key → Bool
  | .own _ => true
  | _ => false

/-- The process whose computation a step replaces, if any. -/
@[expose] def Key.owner : Key → Option PID
  | .own processId | .handle processId => some processId
  | _ => none

/-! ### Steps by key -/

/-- Whether handling the oldest queued signal commutes with every other step,
now and after any of them: a signal that does nothing, a message from a
process, which the process's own steps cannot race with as a receive only
times out with nothing left to handle, a reply or marker resuming a process
that waits, or an acknowledgement of an unlink. Other signals race with what
the process may do before handling them, such as timing out before a timer's
message, removing a monitor, trapping exits, or ending. -/
@[expose] def Task.forcedHead (state : State) (processId : PID) (task : Task α) (entry : Entry) : Bool :=
  state.inertEntry processId entry || match entry.signal with
    | .message _ => entry.source != clock
    | .unlinkAck _ => true
    | .reply _ | .flush => task.wait.isSome
    | _ => false

/-- Whether a process that ended sends next a `DOWN` its watcher drops. -/
@[expose] def State.dropsDown (state : State) (processId : PID) : Bool :=
  match (state.process processId).exiting with
  | some { reason, links := [], downs := (reference, watcher) :: _ } =>
      !state.keepEntry watcher (state.process watcher) { source := processId, signal := .down reference reason }
  | _ => false

/-- The steps of a running configuration, each with its key and whether every
run can take it first (`Config.forced`): a process reading or replacing its
environment or receiving a message already handled, handling a signal that
`Task.forcedHead` accepts, or sending a `DOWN` its watcher drops. -/
@[expose] def Config.taggedSteps : Config α → List (Key × Event × Config α × Bool)
  | .start .. => []
  | .running _ _ _ true => []
  | .running state tasks finished false =>
      Kernel.append (Kernel.append (Kernel.append
        (Kernel.flatMap (fun (before, (processId, task), after) =>
          Kernel.append
            (Kernel.map (fun transition => (Key.own processId, transition.event,
              transition.apply before after finished false,
              transition.event matches .internal _ | .receive ..)) (task.own state processId))
            (Kernel.map (fun transition => (Key.handle processId, transition.event,
              transition.apply before after finished false,
              match (state.process processId).queue with
              | entry :: _ => task.forcedHead state processId entry
              | [] => false)) (task.handle state processId)))
          (splits tasks))
        (Kernel.flatMap (fun (processId, _) =>
          Kernel.append
            (Kernel.filterMap (fun target => (state.linkPhase processId target).map fun next =>
              (Key.link processId target, Event.phase processId, .running next.normalize tasks finished false, false))
              (state.exitLinks processId))
            (match state.phase processId with
              | some next => [(Key.phase processId, Event.phase processId, .running next.normalize tasks finished false,
                  state.dropsDown processId)]
              | none => []))
          state.processes))
        (Kernel.filterMap (fun (processId, _) =>
          (state.process processId).parked.map fun _ =>
            (Key.unpark processId, Event.unpark processId,
              .running (state.unpark processId).normalize tasks finished false, false))
          state.processes))
        (Kernel.map (fun timer =>
          (Key.fire timer.reference, Event.fire timer.reference,
            .running (state.fire timer).normalize tasks finished false, false)) state.firing)

/-- The steps of a running configuration, each with its key. -/
@[expose] def Config.steps (config : Config α) : List (Key × Event × Config α) :=
  Kernel.map (fun (key, event, next, _) => (key, event, next)) config.taggedSteps

/-- Where a process is in a list of tasks: the tasks before it, its own, and those after. -/
@[expose] def splitAt (processId : PID) : List (PID × Task α) →
    Option (List (PID × Task α) × Task α × List (PID × Task α))
  | [] => none
  | (other, task) :: rest =>
      if other == processId then some ([], task, rest)
      else (splitAt processId rest).map fun (before, found, after) => ((other, task) :: before, found, after)

/-- The step with a key, computed directly. -/
@[expose] def Config.stepOf : Config α → Key → Option (Event × Config α)
  | .start .., _ => none
  | .running _ _ _ true, _ => none
  | .running state tasks finished false, .own processId =>
      (splitAt processId tasks).bind fun (before, task, after) =>
        (task.own state processId).head?.map fun transition =>
          (transition.event, transition.apply before after finished false)
  | .running state tasks finished false, .handle processId =>
      (splitAt processId tasks).bind fun (before, task, after) =>
        (task.handle state processId).head?.map fun transition =>
          (transition.event, transition.apply before after finished false)
  | .running state tasks finished false, .link processId target =>
      (state.linkPhase processId target).map fun next =>
        (Event.phase processId, .running next.normalize tasks finished false)
  | .running state tasks finished false, .phase processId =>
      (state.phase processId).map fun next => (Event.phase processId, .running next.normalize tasks finished false)
  | .running state tasks finished false, .unpark processId =>
      (state.process processId).parked.map fun _ =>
        (Event.unpark processId, .running (state.unpark processId).normalize tasks finished false)
  | .running state tasks finished false, .fire reference =>
      (Kernel.find? (·.reference == reference) state.firing).map fun timer =>
        (Event.fire reference, .running (state.fire timer).normalize tasks finished false)

/-! ### What a process continues with -/

/-- What a request continues with, without the state it leaves. -/
inductive Answer.Shape where
  | reply (value : Term)
  | wait (wait : Wait)
  | continue

@[expose] def Answer.shape : Answer β → Answer.Shape
  | .reply value _ => .reply value
  | .wait waiting _ => .wait waiting
  | .continue .. => .continue

/-- Whether two waits are the same. -/
@[expose] def Wait.identical : Wait → Wait → Bool
  | .flush value, .flush value' => value.identical value'
  | .reply source, .reply source' => source == source'
  | .exit, .exit => true
  | _, _ => false

@[expose] def Answer.Shape.identical : Answer.Shape → Answer.Shape → Bool
  | .reply value, .reply value' => value.identical value'
  | .wait waiting, .wait waiting' => waiting.identical waiting'
  | .continue, .continue => true
  | _, _ => false

/-- What a process's own step reads from the state to continue. -/
inductive OwnView where
  | none
  | env (env : Environment)
  | child (child : PID)
  /-- The message a receive takes, with the environment its guard reads, or
  whether it can time out. -/
  | receive (env : Environment) (message : Option Term) (timesOut : Bool)
  | answer (shape : Answer.Shape)
  /-- What canceling a timer replies from: the timer's duration, if it is yet
  to fire, and how many timers the process canceled before. The reply itself
  depends on the elapsed time, which evaluation leaves unknown. -/
  | cancel (duration : Option Nat) (cancels : Nat)

@[expose] def environmentIdentical (first second : Environment) : Bool :=
  first.currentPid == second.currentPid && first.refCounter == second.refCounter &&
    Term.identicalEntries first.pdict second.pdict

@[expose] def OwnView.identical : OwnView → OwnView → Bool
  | .none, .none => true
  | .env first, .env second => environmentIdentical first second
  | .child first, .child second => first == second
  | .receive first message timesOut, .receive second message' timesOut' =>
      environmentIdentical first second && optionIdentical Term.identical message message' && timesOut == timesOut'
  | .answer shape, .answer shape' => shape.identical shape'
  | .cancel duration cancels, .cancel duration' cancels' => duration == duration' && cancels == cancels'
  | _, _ => false

/-- What a process's own step reads from the state to continue. -/
@[expose] def Task.ownView (state : State) (processId : PID) : Task α → OwnView
  | ⟨_, _, some _⟩ => .none
  | ⟨computation, _, none⟩ =>
    match computation with
    | .get _ => .env (state.view processId)
    | Result.schedule .. => .child (Kernel.append processId [(state.process processId).children + 1])
    | .receive timeout select _ =>
        let process := state.process processId
        let view := state.view processId
        .receive view ((selectMessage (select view) process.mailbox).map (·.1))
          (match timeout with
            | .infinity => false
            | _ => !Kernel.any process.queue (state.awaitedEntry processId))
    | .request (.cancelTimer reference) _ =>
        .cancel ((Kernel.find? (·.reference == reference) state.timers).map (·.duration))
          (state.process processId).cancels
    | .request query next => .answer (state.request processId next query).shape
    | _ => .none

/-- What handling the oldest queued signal reads to continue: the reason the
process exits with, and the value it resumes with. -/
@[expose] def Task.handleView (state : State) (processId : PID) (task : Task α) :
    Option (Option Term × Option Term) :=
  match (state.process processId).queue with
  | [] => none
  | entry :: rest =>
      let (_, resumed, exits) :=
        (state.set processId { state.process processId with queue := rest }).handle processId
          (task.wait.map (·.1)) entry
      some (exits, resumed)

@[expose] def handleViewIdentical : Option (Option Term × Option Term) → Option (Option Term × Option Term) → Bool
  | some (exits, resumed), some (exits', resumed') =>
      optionIdentical Term.identical exits exits' && optionIdentical Term.identical resumed resumed'
  | none, none => true
  | _, _ => false

/-- Whether a step's process continues alike in two configurations. -/
@[expose] def Config.sameView : Config α → Config α → Key → Bool
  | .running state tasks _ _, .running state' tasks' _ _, .own processId =>
      match Kernel.lookup processId tasks, Kernel.lookup processId tasks' with
      | some task, some task' => (task.ownView state processId).identical (task'.ownView state' processId)
      | _, _ => false
  | .running state tasks _ _, .running state' tasks' _ _, .handle processId =>
      -- Handling reads whether the process waits, which a step of its own may change.
      match Kernel.lookup processId tasks, Kernel.lookup processId tasks' with
      | some task, some task' =>
          handleViewIdentical (task.handleView state processId) (task'.handleView state' processId)
      | _, _ => false
  | _, _, _ => true

/-- Whether two configurations reached by the same steps in different orders
are the same: the same processes and flags, and identical states. -/
@[expose] def Config.sameAfter : Config α → Config α → Bool
  | .running state tasks finished exhausted, .running state' tasks' finished' exhausted' =>
      Kernel.map Prod.fst tasks == Kernel.map Prod.fst tasks' &&
        finished.isSome == finished'.isSome && exhausted == exhausted' && state.identical state'
  | _, _ => false

/-! ### Frames

What a step reads and writes of each record, as masks of fields, so that steps
touching records apart commute without being evaluated. A queue has a head,
which handling pops, and a tail, which sending appends to: the two commute, as
a queue being handled is never empty. Reading whether a queue is empty reads both. -/

namespace Field
@[expose] def queueHead : Nat := 1
@[expose] def queueTail : Nat := 2
@[expose] def mailbox : Nat := 4
@[expose] def pdict : Nat := 8
@[expose] def refCounter : Nat := 16
@[expose] def children : Nat := 32
@[expose] def links : Nat := 64
@[expose] def monitors : Nat := 128
@[expose] def monitoring : Nat := 256
@[expose] def aliases : Nat := 512
@[expose] def trapExit : Nat := 1024
@[expose] def cancels : Nat := 2048
@[expose] def unlinks : Nat := 4096
@[expose] def parked : Nat := 8192
@[expose] def eagerExits : Nat := 16384
@[expose] def exiting : Nat := 32768
/-- Whether the process is alive or has a record. -/
@[expose] def live : Nat := 65536
end Field

/-- A write of a field that commutes with itself, as removing different
entries from a list: bits above the fields'. -/
@[expose] def Field.commuting (fields : Nat) : Nat := fields <<< 20

/-- A process, and the fields of its record a step reads and writes. -/
abbrev Frame := PID × Nat × Nat

/-- The frames of appending a signal to a live queue. A `DOWN` or a message to
an alias that normalization drops at once writes nothing: whether it is
dropped reads nothing, as no monitor or alias of an allocated reference comes
back, so a dropped one stays dropped. A link exit from a process that is gone
is always appended: it is dropped while its receiver has no active link, which
linking again restores, so it reads the links. Other signals are kept unless
an acknowledgement no unlink waits for, which reads the links. -/
@[expose] def State.appendFrames (state : State) (source target : PID) (signal : Signal) : List Frame :=
  match signal with
  | .exit _ true _ => [(target, Field.live ||| Field.links, Field.queueTail)]
  | .down .. | .aliasMessage .. =>
      if state.keepEntry target (state.process target) { source, signal } then
        [(target, Field.live, Field.queueTail)]
      else [(target, Field.live, 0)]
  | _ => [(target, Field.live ||| Field.links ||| Field.unlinks, Field.queueTail)]

/-- The frames of queueing a signal, or of its sender's fallback. -/
@[expose] def State.enqueueFrames (state : State) (source target : PID) (signal : Signal) : List Frame :=
  if state.alive target then state.appendFrames source target signal
  else (target, Field.live, 0) :: match signal with
    | .link => state.appendFrames target source (.exit (.atom "noproc") true false)
    | .monitor reference => state.appendFrames target source (.down reference (.atom "noproc"))
    | .unlink _ => [(source, Field.links, Field.links)]
    | .isAlive => state.appendFrames target source (.reply (.atom "false"))
    | _ => []

/-- The frames of sending a signal, after a parked monitor signal to the same target. -/
@[expose] def State.sendFrames (state : State) (source target : PID) (signal : Signal) : List Frame :=
  match (state.process source).parked with
  | some (parked, reference) =>
      if parked == target then
        (source, Field.parked, Field.parked) ::
          Kernel.append (state.enqueueFrames source target (.monitor reference))
            (state.enqueueFrames source target signal)
      else (source, Field.parked, 0) :: state.enqueueFrames source target signal
  | none => (source, Field.parked, 0) :: state.enqueueFrames source target signal

/-- The frames of a request, and whether it uses the timers. -/
@[expose] def State.requestFrames (state : State) (processId : PID) : Request → Option (List Frame × Bool)
  | .monitor target _ =>
      if target == processId then some ([(processId, Field.refCounter, Field.refCounter)], false) else
      let fields := Field.refCounter ||| Field.parked ||| Field.monitoring ||| Field.aliases
      let unpark := match (state.process processId).parked with
        | some (parked, reference) => state.enqueueFrames processId parked (.monitor reference)
        | none => []
      some ((processId, fields, fields) :: unpark, false)
  | .demonitor .. =>
      some ([(processId, Field.monitoring ||| Field.aliases, Field.monitoring ||| Field.aliases)], false)
  | .link target =>
      if target == processId then some ([], false) else
      let process := state.process processId
      let reads : List Frame := [(processId, Field.trapExit ||| Field.links ||| Field.eagerExits, 0), (target, Field.live, 0)]
      if !state.alive target && !process.trapExit then some (reads, false) else
      match Kernel.lookup target process.links with
      | some none => some (reads, false)
      | _ => some ((processId, 0, Field.links) :: Kernel.append reads (state.sendFrames processId target .link), false)
  | .unlink target =>
      if target == processId then some ([], false) else
      let process := state.process processId
      match Kernel.lookup target process.links with
      | some none =>
          some ((processId, Field.links ||| Field.unlinks, Field.links ||| Field.unlinks) ::
            state.sendFrames processId target (.unlink (process.unlinks + 1)), false)
      | _ => some ([(processId, Field.links, 0)], false)
  | .exit target reason _ =>
      some ((processId, Field.trapExit, 0) :: state.sendFrames processId target (.exit reason false false), false)
  | .trapExit _ =>
      some ([(processId, Field.trapExit ||| Field.eagerExits, Field.trapExit)], false)
  | .alive target =>
      if target == processId then some ([], false)
      else if state.alive target then some (state.sendFrames processId target .isAlive, false)
      else some ([(target, Field.live, 0), (processId, 0, Field.queueTail)], false)
  | .sendAlias alias message =>
      some (state.sendFrames processId alias.dropLast (.aliasMessage alias message), false)
  | .startTimer destination _ _ =>
      some ([(processId, Field.refCounter, Field.refCounter), (destination, Field.live, 0)], true)
  | .cancelTimer _ => some ([(processId, Field.cancels, Field.cancels)], true)

/-- Every field. -/
@[expose] def Field.all : Nat := 131071

/-- The frames of a process ending: its own record, and the records of others
that normalization changes once it is gone, and whether it cancels timers. A
live process drops the requests the process queued, which only it can queue,
and the links it was removing; a process that ended drops everything the
process queued and its signals to it. -/
@[expose] def State.endFrames (state : State) (processId : PID) : List Frame × Bool :=
  let others := Kernel.filterMap (fun (other, process) =>
    if other == processId then none else
    let fields := match process.exiting with
      | some exiting =>
          (if Kernel.any process.queue (·.source == processId) then Field.queueHead ||| Field.queueTail else 0) |||
          (if Kernel.contains exiting.links processId || Kernel.any exiting.downs (·.2 == processId)
            then Field.exiting ||| Field.live else 0)
      | none =>
          (if Kernel.any process.queue (fun entry => entry.source == processId && match entry.signal with
              | .isAlive | .monitor _ | .unlinkAck _ => true
              | _ => false) then Field.queueHead ||| Field.queueTail else 0) |||
          (if Kernel.any process.links (fun link => link.1 == processId && link.2.isSome) then Field.links else 0)
    if fields == 0 then none else some (other, fields, fields)) state.processes
  -- It applies the link exits that only remove a link, after a parked monitor
  -- signal to the same target.
  let process := state.process processId
  let eager := Kernel.filterMap (fun (target, unlinking) => if unlinking.isNone then
      some (target, Field.live ||| Field.trapExit ||| Field.queueHead,
        Field.commuting (Field.links ||| Field.eagerExits))
    else none) process.links
  let unpark := match process.parked with
    | some (target, _) => [(target, Field.live, Field.queueTail)]
    | none => []
  ((processId, Field.all, Field.all) :: Kernel.append others (Kernel.append eager unpark),
    Kernel.any state.timers (·.destination == processId))

/-- The frames of a process's own step, `none` when it ends or starts a process. -/
@[expose] def Task.ownFrames (state : State) (processId : PID) : Task α → Option (List Frame × Bool)
  | ⟨_, _, some _⟩ => some ([], false)
  | ⟨computation, _, none⟩ =>
    let view := Field.pdict ||| Field.refCounter
    match computation with
    | .get _ => some ([(processId, view, 0)], false)
    | .set .. => some ([(processId, Field.refCounter, view)], false)
    | .send destination message _ =>
        some (state.sendFrames processId destination (.message message), false)
    | .receive timeout select _ =>
        let reads := view ||| Field.mailbox
        match selectMessage (select (state.view processId)) (state.process processId).mailbox with
        | some _ => some ([(processId, reads, Field.mailbox)], false)
        | none => match timeout with
          | .infinity => some ([(processId, reads, 0)], false)
          | _ => some ([(processId, reads ||| Field.queueHead ||| Field.queueTail, 0)], false)
    | .request query _ => state.requestFrames processId query
    | .ok _ => some (state.endFrames processId)
    | .error .exhausted => none
    | .error _ => some (state.endFrames processId)
    | Result.schedule _ _ _ =>
        let child := Kernel.append processId [(state.process processId).children + 1]
        let fields := Field.children ||| Field.refCounter ||| Field.links ||| Field.monitoring
        some ([(processId, fields, fields), (child, Field.all, Field.all)], false)

/-- The frames of handling the oldest queued signal, `none` when the process ends. -/
@[expose] def Task.handleFrames (state : State) (processId : PID) (task : Task α) : Option (List Frame × Bool) :=
  match (state.process processId).queue with
  | [] => some ([], false)
  | entry :: _ =>
    let own (reads writes : Nat) : Frame := (processId, reads, Field.queueHead ||| writes)
    match entry.signal with
    | .message _ => some ([own 0 Field.mailbox], false)
    | .aliasMessage .. => some ([own Field.aliases Field.mailbox], false)
    | .exit .. =>
        match task.handleView state processId with
        | some (none, _) => some ([own (Field.links ||| Field.trapExit) (Field.links ||| Field.mailbox)], false)
        | _ => some (state.endFrames processId)
    | .link | .unlinkAck _ => some ([own Field.links Field.links], false)
    | .unlink id => some (own Field.links Field.links :: state.sendFrames processId entry.source (.unlinkAck id), false)
    | .monitor _ => some ([own Field.monitors Field.monitors], false)
    | .down _ reason =>
        let eager := if isNormal reason && Kernel.contains (state.process processId).eagerExits entry.source
          then Field.eagerExits else 0
        let fields := Field.monitoring ||| Field.aliases ||| eager
        some ([own fields (fields ||| Field.mailbox)], false)
    | .isAlive => some (own 0 0 :: state.sendFrames processId entry.source (.reply (.atom "true")), false)
    | .reply _ | .flush => some ([own 0 0], false)

/-- The frames of a phase of a process that ended signaling one of its links.
Links are removed in any order, which commutes. -/
@[expose] def State.linkFrames (state : State) (processId target : PID) : Option (List Frame × Bool) :=
  match state.record processId with
  | some process =>
      match process.exiting with
      | some exiting =>
          let own : Frame := (processId, 0, Field.commuting Field.exiting)
          let signal : Signal := .exit exiting.reason true false
          -- Handling a link from this process changes whether the exit is
          -- applied when sent, which reads nothing else of the queue.
          let linking := Kernel.any (state.process target).queue
            (fun entry => entry.source == processId && entry.signal matches .link)
          let queue := if linking then Field.queueHead else 0
          if isNormal exiting.reason && state.alive target && !(state.process target).trapExit && !linking then
            let unpark := match process.parked with
              | some (parked, reference) =>
                  if parked == target then
                    (processId, Field.parked, Field.parked) ::
                      state.enqueueFrames processId target (.monitor reference)
                  else [(processId, Field.parked, 0)]
              | none => [(processId, Field.parked, 0)]
            some (own :: (target, Field.live ||| Field.trapExit,
              Field.commuting (Field.links ||| Field.eagerExits)) :: unpark, false)
          else some (own :: (target, Field.live ||| Field.trapExit ||| queue, 0) ::
            state.sendFrames processId target signal, false)
      | none => none
  | none => none

/-- The frames of the next phase of a process that ended once it signaled its links. -/
@[expose] def State.phaseFrames (state : State) (processId : PID) : Option (List Frame × Bool) :=
  match state.record processId with
  | some process =>
      match process.exiting with
      | some exiting =>
          let own : Frame := (processId, Field.exiting, Field.exiting)
          match exiting.downs, process.queue with
          | (reference, watcher) :: _, _ =>
              some (own :: state.sendFrames processId watcher (.down reference exiting.reason), false)
          | [], entry :: _ =>
              let own : Frame := (processId, Field.exiting ||| Field.parked ||| Field.queueHead,
                Field.queueHead ||| Field.live)
              some (own :: match entry.signal with
                | .link => state.sendFrames processId entry.source (.exit (.atom "noproc") true false)
                | .monitor reference => state.sendFrames processId entry.source (.down reference (.atom "noproc"))
                | .isAlive => state.sendFrames processId entry.source (.reply (.atom "false"))
                | _ => [], false)
          | [], [] => some ([own], false)
      | none => none
  | none => none

/-- The frames of a step, and whether it uses the timers; `none` when unknown,
as for steps that end or start a process, which change what normalization removes. -/
@[expose] def Config.frames : Config α → Key → Option (List Frame × Bool)
  | .running state tasks _ false, .own processId =>
      (Kernel.lookup processId tasks).bind fun task => task.ownFrames state processId
  | .running state tasks _ false, .handle processId =>
      (Kernel.lookup processId tasks).bind fun task => task.handleFrames state processId
  | .running state _ _ false, .link processId target => state.linkFrames processId target
  | .running state _ _ false, .phase processId => state.phaseFrames processId
  | .running state _ _ false, .unpark processId =>
      match (state.process processId).parked with
      | some (target, reference) =>
          some ((processId, Field.parked, Field.parked) :: state.enqueueFrames processId target (.monitor reference), false)
      | none => none
  | .running state _ _ false, .fire reference =>
      match Kernel.find? (·.reference == reference) state.timers with
      | some timer => some (state.enqueueFrames clock timer.destination (.message timer.message), true)
      | none => none
  | _, _ => none

/-- Whether no frame of one step writes what a frame of the other reads or writes. -/
@[expose] def framesApart (frames frames' : List Frame) : Bool :=
  Kernel.all frames fun (processId, reads, writes) => Kernel.all frames' fun (processId', reads', writes') =>
    processId != processId' ||
      let plain := writes &&& 1048575
      let plain' := writes' &&& 1048575
      plain &&& (reads' ||| writes' ||| (writes' >>> 20)) == 0 && (writes >>> 20) &&& (reads' ||| plain') == 0 &&
        plain' &&& reads == 0 && (writes' >>> 20) &&& reads == 0

/-- Whether two steps touch records apart and do not both use the timers. -/
@[expose] def Config.apart (config : Config α) (key other : Key) : Bool :=
  match config.frames key, config.frames other with
  | some (frames, timers), some (frames', timers') => !(timers && timers') && framesApart frames frames'
  | _, _ => false

/-- Whether a step spawns no process, or one whose PID no process has yet,
which the proofs of commuting steps rely on. PIDs are never reused, so this
holds of every step. -/
@[expose] def Config.spawnsFresh : Config α → Key → Bool
  | .running state tasks _ _, .own processId =>
      match Kernel.lookup processId tasks with
      | some ⟨Result.schedule .., _, none⟩ =>
          let child := Kernel.append processId [(state.process processId).children + 1]
          !Kernel.any tasks (·.1 == child)
      | _ => true
  | _, _ => true

/-- Whether no process has two tasks, which the proofs of commuting steps rely
on. Each process has one task, so this holds of every configuration. -/
@[expose] def Config.distinctTasks : Config α → Bool
  | .running _ tasks _ _ =>
      Kernel.all (splits tasks) fun (before, (processId, _), _) => !Kernel.any before (·.1 == processId)
  | _ => true

/-- Whether two steps of different processes commute at a configuration, given
the configurations each leads to: they touch apart, or each can follow the
other, neither changes what the other's process continues with, and both
orders reach the same configuration. -/
@[expose] def Config.commutesAfter (config : Config α) (key : Key) (next : Config α) (other : Key)
    (next' : Config α) : Bool :=
  !(key.owner.isSome && key.owner == other.owner && key.isOwn == other.isOwn) &&
  config.spawnsFresh key && config.spawnsFresh other && config.distinctTasks &&
  (config.apart key other ||
    match next.stepOf other, next'.stepOf key with
    | some (_, last), some (_, last') =>
        config.sameView next' key && config.sameView next other && last.sameAfter last'
    | _, _ => false)

/-- Whether a step leaves every process's computation as it is: it is not a
process's own step, nor handling a signal by a process that waits, which may resume it. -/
@[expose] def Config.keepsTasks : Config α → Key → Bool
  | .running _ tasks _ _, .handle processId =>
      match Kernel.lookup processId tasks with
      | some task => task.wait.isNone
      | none => false
  | _, .own _ => false
  | _, _ => true

/-- Whether a step `other` explored before stays asleep after `key`: they
commute, or `other` absorbs `key`, reaching after it what it reaches alone,
which needs `key` to leave every computation as it is. -/
@[expose] def Config.staysAfter (config : Config α) (steps : List (Key × Event × Config α)) (key : Key)
    (next : Config α) (other : Key) : Bool :=
  match Kernel.find? (·.1 == other) steps with
  | some (_, _, next') =>
      config.commutesAfter key next other next' || config.keepsTasks key &&
      match next.stepOf other with
      | some (_, last) =>
          config.sameView next other && last.sameAfter next'
      | none => false
  | none => false

/-- A step every run can take first: a process reading or replacing its
environment, receiving a message already handled, or handling a queued signal
when neither its own next step nor any other process can tell when, or a
process that ended sending a `DOWN` its watcher drops. -/
@[expose] def Config.forced : Config α → Option Key
  | .running state tasks _ false =>
      Kernel.find? (fun _ => true) (Kernel.filterMap (fun (processId, task) =>
        let process := state.process processId
        let own : Bool := match task.wait, task.computation with
          | none, .get _ | none, .set .. => true
          | none, .receive _ select _ =>
              (selectMessage (select (state.view processId)) process.mailbox).isSome
          | _, _ => false
        if own then some (Key.own processId) else
        match process.queue with
        | entry :: _ => if task.forcedHead state processId entry then some (Key.handle processId) else none
        | [] => none) tasks) |>.orElse fun _ =>
      Kernel.find? (fun _ => true) (Kernel.filterMap (fun (processId, _) =>
        if state.dropsDown processId then some (Key.phase processId) else none) state.processes)
  | _ => none

/-! ### Checking with sleep sets -/

/-- Follow every step not asleep. A step is followed with the steps asleep and
the steps followed before it asleep, keeping only those that stay asleep after it. -/
@[expose] def explore (visit : List Key → Config α → Bool) (stays : Key → Config α → Key → Bool)
    (sleep : List Key) : List Key → List (Key × Event × Config α) → Bool
  | _, [] => true
  | done, (key, _, next) :: rest =>
      if Kernel.contains sleep key then explore visit stays sleep done rest
      else visit (Kernel.filter (stays key next) (Kernel.append sleep done)) next &&
        explore visit stays sleep (Kernel.append done [key]) rest

/-- Whether every run ends in an accepted outcome, following at most `depth`
steps along each run, where runs taking a step asleep first are covered elsewhere. -/
@[expose] def checkSleep (accept : Outcome α → Bool) : Nat → List Key → Config α → Bool
  | 0, _, _ => false
  | depth + 1, sleep, config =>
      match config.taggedSteps with
      | [] =>
          match config.successors with
          | [] => accept config.outcome
          | successors => Kernel.all successors fun (_, next) => checkSleep accept depth [] next
      | tagged =>
          -- The first forced step, as `Config.forced` finds it.
          match Kernel.find? (·.2.2.2) tagged with
          | some (_, _, next, _) => checkSleep accept depth sleep next
          | none =>
              let steps := Kernel.map (fun (key, event, next, _) => (key, event, next)) tagged
              explore (checkSleep accept depth) (config.staysAfter steps) sleep [] steps

end Lynx.Concurrent
