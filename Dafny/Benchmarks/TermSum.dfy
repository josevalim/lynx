include "../Daxie/Sum.dfy"

module TermBenchmarks {
  import opened Terms
  import opened Arithmetic
  import opened TermSum

  lemma SumContract(list: Term)
    requires IsProperIntegerList(list)
    ensures sum_1(list).Ok? && sum_1(list).value.Integer?
    decreases list
  {
    match list {
      case Cons(_, tail) => SumContract(tail);
      case _ =>
    }
  }

  lemma SumAppend(left: Term, right: Term)
    requires IsProperIntegerList(left) && IsProperIntegerList(right)
    ensures sum_1(left).Ok? && sum_1(right).Ok?
    ensures append_2(left, right).Ok?
    ensures sum_1(append_2(left, right).value) ==
      add_2(sum_1(left).value, sum_1(right).value)
    decreases left
  {
    SumContract(left);
    SumContract(right);
    AppendPreservesIntegers(left, right);
    match left {
      case Cons(head, tail) =>
        SumContract(tail);
        AppendPreservesIntegers(tail, right);
        SumContract(append_2(tail, right).value);
        SumAppend(tail, right);
        assert sum_1(left) == Ok(Integer(head.integer + sum_1(tail).value.integer));
        assert append_2(left, right) == Ok(Cons(head, append_2(tail, right).value));
      case _ =>
    }
  }
}
