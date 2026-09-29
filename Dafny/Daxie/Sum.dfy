include "Arithmetic.dfy"

module TermSum {
  import opened Terms
  import opened Arithmetic

  /*
  expects is_proper_list(list, &is_integer/1)
  ensures (result -> is_integer(result))
  property sum(l) + sum(r) == sum(l ++ r)
  def sum([]), do: 0
  def sum([x | xs]), do: x + sum(xs)
  */
  predicate IsProperIntegerList(list: Term)
    decreases list
  {
    match list
    case Nil => true
    case Cons(Integer(_), tail) => IsProperIntegerList(tail)
    case _ => false
  }

  function sum_1(list: Term): Result
    decreases list
  {
    match list
    case Nil => Ok(Integer(0))
    case Cons(head, tail) =>
      Bind(sum_1(tail), subtotal => add_2(head, subtotal))
    case _ => Error(Atom("function_clause"))
  }

  function append_2(left: Term, right: Term): Result
    decreases left
  {
    match left
    case Nil => Ok(right)
    case Cons(head, tail) =>
      Bind(append_2(tail, right), rest => Ok(Cons(head, rest)))
    case _ => Error(Atom("badarg"))
  }

  // Supporting lemma; checked with the project, outside benchmark timings.
  lemma AppendPreservesIntegers(left: Term, right: Term)
    requires IsProperIntegerList(left) && IsProperIntegerList(right)
    ensures append_2(left, right).Ok?
    ensures IsProperIntegerList(append_2(left, right).value)
    decreases left
  {
    match left {
      case Cons(_, tail) => AppendPreservesIntegers(tail, right);
      case _ =>
    }
  }
}
