include "List.dfy"

module Terms {
  import opened Lists
  type FiniteFloat = value: fp64 | value.IsFinite witness 0.0

  datatype Term =
    Integer(integer: int)
    | Float(float: FiniteFloat)
    | Atom(atom: string)
    | Function(id: nat, arity: nat, captures: seq<Term>)
    | Pid(pid: nat)
    | Tuple(elements: seq<Term>)
    | Map(entries: List<(Term, Term)>)
    | Nil
    | Cons(head: Term, tail: Term)

  datatype Reply = Returned(value: Term) | Raised(reason: Term)
  datatype Result = Ok(value: Term) | Error(reason: Term)
    | Apply(callee: Term, arguments: seq<Term>, resume: Reply -> Result)
    | Spawn(callee: Term, resume: Reply -> Result)
    | Send(destination: Term, message: Term, resume: Reply -> Result)
    | Self(resume: Reply -> Result)
    | Then(source: Result, next: Term -> Result)

  function Resume(reply: Reply): Result {
    match reply
    case Returned(value) => Ok(value)
    case Raised(reason) => Error(reason)
  }

  function Bind(computation: Result, next: Term -> Result): Result
  {
    match computation
    case Ok(value) => next(value)
    case Error(reason) => Error(reason)
    case _ => Then(computation, next)
  }

  function Boolean(value: bool): Term {
    Atom(if value then "true" else "false")
  }
}
