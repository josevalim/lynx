include "../Daxie/Runner.dfy"
include "../Daxie/Arithmetic.dfy"
include "../Daxie/Compare.dfy"

module ProcessExamples {
  import opened Terms
  import opened Processes
  import opened Runner
  import opened Arithmetic
  import opened Comparison

  // One generated dispatcher covers closures from all source modules.
  // A.make_adder(n) = fn x -> n + x end
  // B.worker(parent) = send(parent, self())
  function Dispatch(id: nat, captures: seq<Term>, args: seq<Term>): Result {
    match id
    case 0 => if |captures| == 1 && |args| == 1 then add_2(captures[0], args[0])
              else Error(Atom("function_clause"))
    case 1 => if |captures| == 1 && |args| == 0 then
                Bind(self_0(), pid => send_2(captures[0], pid))
              else Error(Atom("function_clause"))
    case 2 => if |captures| == 1 && |args| == 1 then
                Bind(apply_2(Function(0, 1, captures), args),
                  value => apply_2(Function(0, 1, captures), [value]))
              else Error(Atom("function_clause"))
    case 3 => apply_2(Function(3, 0, []), [])
    case 4 => Error(Atom("child_error"))
    case _ => Error(Atom("undef"))
  }

  function ProgramContext(): Program {
    Program(map[0 := 1, 1 := 0, 2 := 1, 3 := 0, 4 := 0],
      map[0 := Pure((captures, args) =>
            if |captures| == 1 && |args| == 1 then ToReply(add_2(captures[0], args[0]))
            else Raised(Atom("function_clause"))),
          1 := Effectful((captures, args) => Dispatch(1, captures, args)),
          2 := Effectful((captures, args) => Dispatch(2, captures, args)),
          3 := Effectful((captures, args) => Dispatch(3, captures, args)),
          4 := Pure((captures, args) => Raised(Atom("child_error")))])
  }

  function StartWorker(): Result {
    Bind(self_0(), parent => spawn_1(Function(1, 0, [parent])))
  }

  lemma BindIdentity(value: Term)
    ensures Bind(Ok(value), x => Ok(x)) == Ok(value)
  {}

  lemma SendReturnsMessage(pid: nat, message: Term)
    ensures send_2(Pid(pid), message).Send?
    ensures send_2(Pid(pid), message).resume(Returned(message)) == Ok(message)
  {}

  lemma {:fuel RunFrom, 4, 5} CapturedAdder(offset: int, argument: int)
    ensures Run(ProgramContext(), apply_2(Function(0, 1, [Integer(offset)]), [Integer(argument)]), [], 3).Completed?
    ensures 1 in Run(ProgramContext(), apply_2(Function(0, 1, [Integer(offset)]), [Integer(argument)]), [], 3).state.finished
    ensures Run(ProgramContext(), apply_2(Function(0, 1, [Integer(offset)]), [Integer(argument)]), [], 3).state.finished[1].reply == Returned(Integer(offset + argument))
  {}

  method CheckReply(reply: Reply, expected: Term) {
    match reply {
      case Returned(value) => expect exactCompare(value, expected) == Eq;
      case Raised(_) => expect false, "unexpected error";
    }
  }

  method CheckError(outcome: Outcome, expected: Term) {
    expect outcome.Completed?;
    expect 1 in outcome.state.finished;
    match outcome.state.finished[1].reply {
      case Raised(reason) => expect exactCompare(reason, expected) == Eq;
      case Returned(_) => expect false, "expected error";
    }
  }

  method Tests() {
    var program := ProgramContext();
    var closure := Function(0, 1, [Integer(10)]);
    var called := Run(program, apply_2(closure, [Integer(5)]), [], 20);
    expect called.Completed? && 1 in called.state.finished;
    CheckReply(called.state.finished[1].reply, Integer(15));
    var nested := Run(program, apply_2(Function(2, 1, [Integer(10)]), [Integer(5)]), [], 40);
    expect nested.Completed? && 1 in nested.state.finished;
    CheckReply(nested.state.finished[1].reply, Integer(25));
    CheckError(Run(program, apply_2(Integer(1), []), [], 10), Tuple([Atom("badfun"), Integer(1)]));
    CheckError(Run(program, apply_2(closure, []), [], 10), BadArity(closure, []));
    var unknown := Function(99, 0, []);
    CheckError(Run(program, apply_2(unknown, []), [], 10), Tuple([Atom("badfun"), unknown]));
    CheckError(Run(program, spawn_1(unknown), [], 10), Atom("badarg"));
    CheckError(Run(program, spawn_1(closure), [], 10), Atom("badarg"));
    CheckError(Run(program, send_2(Atom("name"), Nil), [], 10), Atom("badarg"));
    var exhausted := Run(program, apply_2(Function(3, 0, []), []), [], 20);
    expect exhausted.Exhausted?;

    // Run the child at the spawn boundary before the parent terminates.
    var spawned := Run(program, StartWorker(), [2, 1], 40);
    expect spawned.Completed?;
    expect spawned.state.nextPid == 3;
    expect 1 in spawned.state.finished && 2 in spawned.state.finished;
    CheckReply(spawned.state.finished[1].reply, Pid(2));
    CheckReply(spawned.state.finished[2].reply, Pid(2));
    expect |spawned.state.finished[1].mailbox| == 1;
    expect exactCompare(spawned.state.finished[1].mailbox[0], Pid(2)) == Eq;
    expect |spawned.state.finished[2].mailbox| == 0;

    // Default scheduling finishes the parent first: sending to it is a no-op.
    var late := Run(program, StartWorker(), [], 40);
    expect late.Completed? && 1 in late.state.finished && 2 in late.state.finished;
    expect |late.state.finished[1].mailbox| == 0;

    var selfSend := Bind(self_0(), pid =>
      Bind(send_2(pid, Atom("first")), _ => send_2(pid, Atom("second"))));
    var sent := Run(program, selfSend, [], 30);
    expect sent.Completed? && 1 in sent.state.finished;
    CheckReply(sent.state.finished[1].reply, Atom("second"));
    expect |sent.state.finished[1].mailbox| == 2;
    expect exactCompare(sent.state.finished[1].mailbox[0], Atom("first")) == Eq;
    expect exactCompare(sent.state.finished[1].mailbox[1], Atom("second")) == Eq;

    var absent := Run(program, send_2(Pid(999), Integer(7)), [], 10);
    expect absent.Completed? && 1 in absent.state.finished;
    CheckReply(absent.state.finished[1].reply, Integer(7));

    // A child error is independent of the parent; all children still finish.
    var childError := Run(program, spawn_1(Function(4, 0, [])), [2], 20);
    expect childError.Completed? && 1 in childError.state.finished && 2 in childError.state.finished;
    CheckReply(childError.state.finished[1].reply, Pid(2));
    expect childError.state.finished[2].reply.Raised?;
    expect exactCompare(childError.state.finished[2].reply.reason, Atom("child_error")) == Eq;

    // Low-level Apply resumes errors as well as values, so handlers can catch them.
    var caught := Run(program, Apply(Function(4, 0, []), [], (reply: Reply) =>
      match reply case Raised(_) => Ok(Atom("caught")) case Returned(value) => Ok(value)), [], 20);
    expect caught.Completed? && 1 in caught.state.finished;
    CheckReply(caught.state.finished[1].reply, Atom("caught"));
  }
}
