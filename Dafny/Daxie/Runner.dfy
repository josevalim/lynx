include "Process.dfy"

module Runner {
  import opened Terms
  import opened Processes

  // A generated whole-program dispatcher and its declared arities. Only the
  // runner receives this context; translated functions emit Apply requests.
  datatype Program = Program(arities: map<nat, nat>, dispatch: (nat, seq<Term>, seq<Term>) -> Result)
  datatype Process = Process(pid: nat, computation: Result, frames: seq<Reply -> Result>, mailbox: seq<Term>)
  datatype Completion = Completion(reply: Reply, mailbox: seq<Term>)
  datatype Runtime = Runtime(nextPid: nat, runnable: seq<Process>, finished: map<nat, Completion>)
  datatype Outcome = Completed(state: Runtime) | Exhausted(state: Runtime)
  datatype Transition = Transition(state: Runtime, boundary: bool)

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
    id in program.arities && program.arities[id] == arity
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
         else Transition(SetComputation(state, program.dispatch(id, captures, args),
           [resume] + current.frames), false)
       case _ => Transition(SetComputation(state,
         resume(Raised(Tuple([Atom("badfun"), callee]))), current.frames), false))
    case Spawn(callee, resume) =>
      (match callee
       case Function(id, 0, captures) =>
         if Known(program, id, 0) then
           var pid := state.nextPid;
           var parent := current.(computation := resume(Returned(Pid(pid))));
           var child := Process(pid, program.dispatch(id, captures, []), [], []);
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
  datatype OptionReply = NoReply | HasReply(reply: Reply)

  // Interpret the pure requests used by expectations. Fuel bounds dispatch and
  // sequencing; unsupported process effects are not successful expectations.
  function EvaluatePure(program: Program, computation: Result, fuel: nat): OptionReply
    decreases fuel
  {
    if fuel == 0 then NoReply else
    match computation
    case Ok(value) => HasReply(Returned(value))
    case Error(reason) => HasReply(Raised(reason))
    case Then(source, next) =>
      (match EvaluatePure(program, source, fuel - 1)
       case NoReply => NoReply
       case HasReply(Raised(reason)) => HasReply(Raised(reason))
       case HasReply(Returned(value)) => EvaluatePure(program, next(value), fuel - 1))
    case Apply(callee, arguments, resume) =>
      (match callee
       case Function(id, arity, captures) =>
         if !Known(program, id, arity) then EvaluatePure(program,
           resume(Raised(Tuple([Atom("badfun"), callee]))), fuel - 1)
         else if |arguments| != arity then EvaluatePure(program,
           resume(Raised(BadArity(callee, arguments))), fuel - 1)
         else (match EvaluatePure(program, program.dispatch(id, captures, arguments), fuel - 1)
           case NoReply => NoReply
           case HasReply(reply) => EvaluatePure(program, resume(reply), fuel - 1))
       case _ => EvaluatePure(program,
         resume(Raised(Tuple([Atom("badfun"), callee]))), fuel - 1))
    case _ => NoReply
  }
}
