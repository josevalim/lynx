include "Runner.dfy"
module ListPredicates {
  import opened Terms
  import opened Processes
  import opened Runner

  // Elixir: is_proper_list(xs, fn x -> is_integer(x) end).
  // The traversal accepts an ordinary Term closure, not a host callback.
  function is_proper_list_2(xs: Term, callback: Term): Result
    decreases xs
  {
    match xs
    case Nil => Ok(Boolean(true))
    case Cons(head, tail) => Bind(apply_2(callback, [head]), (answer: Term) =>
      match answer
      case Atom("true") => is_proper_list_2(tail, callback)
      case _ => Ok(Boolean(false)))
    case _ => Ok(Boolean(false))
  }

  function SpineDepth(xs: Term): nat
    decreases xs
  {
    match xs case Cons(_, tail) => 1 + SpineDepth(tail) case _ => 0
  }
  function is_integer_1(x: Term): Result {
    match x case Integer(_) => Ok(Boolean(true)) case _ => Ok(Boolean(false))
  }
  function IntegerDispatch(id: nat, captures: seq<Term>, args: seq<Term>): Result {
    match id
    case 0 => if |args| == 1 then is_integer_1(args[0]) else Error(Atom("function_clause"))
    case _ => Error(Atom("function_clause"))
  }
  function IntegerProgram(): Program { Program(map[0 := 1], IntegerDispatch) }
  function IntegerClosure(): Term { Function(0, 1, []) }
  opaque function IntegerExpectation(xs: Term): OptionReply {
    EvaluatePure(IntegerProgram(), is_proper_list_2(xs, IntegerClosure()), SpineDepth(xs) + 4)
  }
}
