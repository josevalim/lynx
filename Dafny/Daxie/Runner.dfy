include "Process.dfy"

module Runner {
  import opened Terms
  import opened Processes

  // Whole-program typed function table and declared arities. Effectful bodies
  // emit requests; pureApply receives the table only where a pure call is needed.
  datatype FunEntry = Pure(body: (seq<Term>, seq<Term>) -> Reply)
    | Effectful(effectfulBody: (seq<Term>, seq<Term>) -> Result)
  datatype Program = Program(arities: map<nat, nat>, entries: map<nat, FunEntry>)
  datatype Process = Process(pid: nat, computation: Result, frames: seq<Reply -> Result>, mailbox: seq<Term>)
  datatype Completion = Completion(reply: Reply, mailbox: seq<Term>)
  datatype Runtime = Runtime(nextPid: nat, runnable: seq<Process>, finished: map<nat, Completion>)
  datatype Outcome = Completed(state: Runtime) | Exhausted(state: Runtime)
  datatype Transition = Transition(state: Runtime, boundary: bool)

  // Pure entries cannot return Apply or any process request: their type is Reply.
  function Invoke(entry: FunEntry, captures: seq<Term>, args: seq<Term>): Result {
    match entry
    case Pure(body) => Resume(body(captures, args))
    case Effectful(body) => body(captures, args)
  }

  // Same fast path as Lean pureApply; effectful/invalid-arity calls stay requests.
  function pureApply(program: Program, callee: Term, args: seq<Term>): Result {
    match callee
    case Function(id, arity, captures) =>
      if |args| == arity then
        if id in program.entries then
          match program.entries[id]
          case Pure(body) => Resume(body(captures, args))
          case Effectful(_) => apply_2(callee, args)
        else Error(Tuple([Atom("badfun"), callee]))
      else apply_2(callee, args)
    case _ => apply_2(callee, args)
  }

  function Continue(reply: Reply, next: Term -> Result): Result {
    match reply
    case Returned(value) => next(value)
    case Raised(reason) => Error(reason)
  }

  function SetComputation(state: Runtime, computation: Result, frames: seq<Reply -> Result>): Runtime
    requires |state.runnable| > 0
  {
    var current := state.runnable[0];
    state.(runnable := [current.(computation := computation, frames := frames)] + state.runnable[1..])
  }

  function Finish(state: Runtime, reply: Reply): Runtime
    requires |state.runnable| > 0
  {
    var current := state.runnable[0];
    if |current.frames| == 0 then
      state.(runnable := state.runnable[1..],
        finished := state.finished[current.pid := Completion(reply, current.mailbox)])
    else SetComputation(state, current.frames[0](reply), current.frames[1..])
  }

  function Deliver(processes: seq<Process>, destination: nat, message: Term): seq<Process> {
    seq(|processes|, i requires 0 <= i < |processes| =>
      var process := processes[i];
      if process.pid == destination then process.(mailbox := process.mailbox + [message]) else process)
  }

  lemma DeliveryIsLocal(processes: seq<Process>, destination: nat, message: Term, index: nat)
    requires index < |processes|
    ensures |Deliver(processes, destination, message)| == |processes|
    ensures Deliver(processes, destination, message)[index].pid == processes[index].pid
    ensures Deliver(processes, destination, message)[index].mailbox ==
      (if processes[index].pid == destination then processes[index].mailbox + [message]
       else processes[index].mailbox)
  {}

  function Known(program: Program, id: nat, arity: nat): bool {
    id in program.entries && id in program.arities && program.arities[id] == arity
  }

  function Step(program: Program, state: Runtime): Transition
    requires |state.runnable| > 0
  {
    var current := state.runnable[0];
    match current.computation
    case Ok(value) => Transition(Finish(state, Returned(value)), false)
    case Error(reason) => Transition(Finish(state, Raised(reason)), false)
    case Then(source, next) => Transition(SetComputation(state, source,
      [reply => Continue(reply, next)] + current.frames), false)
    case Self(resume) => Transition(SetComputation(state,
      resume(Returned(Pid(current.pid))), current.frames), false)
    case Apply(callee, args, resume) =>
      (match callee
       case Function(id, arity, captures) =>
         if !Known(program, id, arity) then Transition(SetComputation(state,
           resume(Raised(Tuple([Atom("badfun"), callee]))), current.frames), false)
         else if |args| != arity then Transition(SetComputation(state,
           resume(Raised(BadArity(callee, args))), current.frames), false)
         else Transition(SetComputation(state, Invoke(program.entries[id], captures, args),
           [resume] + current.frames), false)
       case _ => Transition(SetComputation(state,
         resume(Raised(Tuple([Atom("badfun"), callee]))), current.frames), false))
    case Spawn(callee, resume) =>
      (match callee
       case Function(id, 0, captures) =>
         if Known(program, id, 0) then
           var pid := state.nextPid;
           var parent := current.(computation := resume(Returned(Pid(pid))));
           var child := Process(pid, Invoke(program.entries[id], captures, []), [], []);
           Transition(Runtime(pid + 1, [parent] + state.runnable[1..] + [child], state.finished), true)
         else Transition(SetComputation(state, resume(Raised(Atom("badarg"))), current.frames), false)
       case _ => Transition(SetComputation(state, resume(Raised(Atom("badarg"))), current.frames), false))
    case Send(destination, message, resume) =>
      (match destination
       case Pid(pid) =>
         var updated := state.(runnable := Deliver(state.runnable, pid, message));
         Transition(SetComputation(updated, resume(Returned(message)), current.frames), true)
       case _ => Transition(SetComputation(state, resume(Raised(Atom("badarg"))), current.frames), false))
  }

  // A missing or finished requested PID leaves the current runnable order alone.
  function Select(processes: seq<Process>, pid: nat): seq<Process>
    ensures |Select(processes, pid)| == |processes|
    decreases |processes|
  {
    if |processes| == 0 then []
    else if processes[0].pid == pid then processes
    else
      var rest := Select(processes[1..], pid);
      if |rest| > 0 && rest[0].pid == pid then [rest[0], processes[0]] + rest[1..]
      else [processes[0]] + rest
  }

  function RunFrom(program: Program, state: Runtime, schedule: seq<nat>, fuel: nat): Outcome
    decreases fuel
  {
    if |state.runnable| == 0 then Completed(state)
    else if fuel == 0 then Exhausted(state)
    else
      var transition := Step(program, state);
      if transition.boundary && |schedule| > 0 then
        RunFrom(program, transition.state.(runnable := Select(transition.state.runnable, schedule[0])),
          schedule[1..], fuel - 1)
      else RunFrom(program, transition.state, schedule, fuel - 1)
  }

  function Run(program: Program, computation: Result, schedule: seq<nat>, fuel: nat): Outcome {
    RunFrom(program, Runtime(2, [Process(1, computation, [], [])], map[]), schedule, fuel)
  }
}
