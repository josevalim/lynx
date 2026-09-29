include "../Benchmarks/TermSum.dfy"
include "../Benchmarks/NativeSum.dfy"

module Correspondence {
  import opened Terms
  import T = TermSum
  import N = NativeSum

  function Encode(list: N.List): Term
    decreases list
  {
    match list
    case Nil => Nil
    case Cons(head, tail) => Cons(Integer(head), Encode(tail))
  }

  lemma SumAgrees(list: N.List)
    ensures T.IsProperIntegerList(Encode(list))
    ensures T.sum_1(Encode(list)) == Ok(Integer(N.sum_1(list)))
    decreases list
  {
    match list {
      case Nil =>
      case Cons(_, tail) => SumAgrees(tail);
    }
  }
}
