module NativeSum {
  // The same inductive list and unbounded integers, without Term or Result.
  datatype List = Nil | Cons(head: int, tail: List)

  function sum_1(list: List): int
    decreases list
  {
    match list
    case Nil => 0
    case Cons(head, tail) => head + sum_1(tail)
  }

  function Append(left: List, right: List): List
    decreases left
  {
    match left
    case Nil => right
    case Cons(head, tail) => Cons(head, Append(tail, right))
  }

  lemma SumAppend(left: List, right: List)
    ensures sum_1(left) + sum_1(right) == sum_1(Append(left, right))
    decreases left
  {
    match left {
      case Nil =>
      case Cons(_, tail) => SumAppend(tail, right);
    }
  }
}
