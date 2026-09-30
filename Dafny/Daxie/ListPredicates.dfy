include "Runner.dfy"
module ListPredicates {
  import opened Terms
  import opened Processes
  import opened Runner

  // Elixir: is_proper_list(xs, fn x -> is_integer(x) end).
  function is_proper_list_2(program: Program, xs: Term, callback: Term): Result
    decreases xs
  {
    match xs
    case Nil => Ok(Boolean(true))
    case Cons(head, tail) => Bind(pureApply(program, callback, [head]), (answer: Term) =>
      match answer
      case Atom("true") => is_proper_list_2(program, tail, callback)
      case _ => Ok(Boolean(false)))
    case _ => Ok(Boolean(false))
  }
  function IntegerBody(captures: seq<Term>, args: seq<Term>): Reply {
    if |args| == 1 then
      Returned(match args[0] case Integer(_) => Boolean(true) case _ => Boolean(false))
    else Raised(Atom("badarg"))
  }
  function IntegerProgram(): Program { Program(map[0 := 1], map[0 := Pure(IntegerBody)]) }
  function IntegerClosure(): Term { Function(0, 1, []) }

  // Verified callback summary keeps table lookup out of repeated SMT unfolding.
  opaque function IntegerCallback(x: Term): (answer: Result)
    ensures answer == Ok(match x case Integer(_) => Boolean(true) case _ => Boolean(false))
  {
    pureApply(IntegerProgram(), IntegerClosure(), [x])
  }

  // Specialize the traversal for the known table, retaining Term application.
  function IntegerExpectation(xs: Term): Result
    decreases xs
  {
    match xs
    case Nil => Ok(Boolean(true))
    case Cons(head, tail) => Bind(IntegerCallback(head), (answer: Term) =>
      match answer
      case Atom("true") => IntegerExpectation(tail)
      case _ => Ok(Boolean(false)))
    case _ => Ok(Boolean(false))
  }
  lemma IntegerCallbackSpecialization(xs: Term)
    ensures is_proper_list_2(IntegerProgram(), xs, IntegerClosure()) == IntegerExpectation(xs)
    decreases xs
  {
    match xs { case Cons(_, tail) => IntegerCallbackSpecialization(tail); case _ => }
  }
}
