include "Term.dfy"

module Processes {
  import opened Terms

  function ArgumentList(args: seq<Term>): Term
    decreases |args|
  {
    if |args| == 0 then Nil else Cons(args[0], ArgumentList(args[1..]))
  }

  function BadArity(callee: Term, args: seq<Term>): Term {
    Tuple([Atom("badarity"), Tuple([callee, ArgumentList(args)])])
  }

  function apply_2(callee: Term, args: seq<Term>): Result {
    match callee
    case Function(_, arity, _) =>
      if |args| == arity then Apply(callee, args, Resume)
      else Error(BadArity(callee, args))
    case _ => Error(Tuple([Atom("badfun"), callee]))
  }

  function spawn_1(callee: Term): Result {
    match callee
    case Function(_, 0, _) => Spawn(callee, Resume)
    case _ => Error(Atom("badarg"))
  }

  function send_2(destination: Term, message: Term): Result {
    match destination
    case Pid(_) => Send(destination, message, Resume)
    case _ => Error(Atom("badarg"))
  }

  function self_0(): Result { Self(Resume) }
}
