include "Compare.dfy"

module Maps {
  import opened Terms
  import opened Lists
  import opened Comparison

  function new_0(): Result { Ok(Map(Empty)) }

  function get_2(key: Term, input: Term): Result {
    match input
    case Map(entries) =>
      (match Find(entries, key)
       case Found(value) => Ok(value)
       case Missing => Error(Tuple([Atom("badkey"), key])))
    case _ => Error(Tuple([Atom("badmap"), input]))
  }

  function put_3(key: Term, value: Term, input: Term): Result {
    match input
    case Map(entries) => Ok(Map(Link((key, value), entries)))
    case _ => Error(Tuple([Atom("badmap"), input]))
  }

  function merge_2(left: Term, right: Term): Result {
    match (left, right)
    case (Map(a), Map(b)) => Ok(Map(Append(b, a)))
    case (Map(_), _) => Error(Tuple([Atom("badmap"), right]))
    case _ => Error(Tuple([Atom("badmap"), left]))
  }

  lemma FindAppend(left: List<(Term, Term)>, right: List<(Term, Term)>, key: Term)
    ensures Find(Append(left, right), key) ==
      (match Find(left, key) case Missing => Find(right, key) case value => value)
    decreases left
  {
    match left {
      case Empty =>
      case Link(_, tail) => FindAppend(tail, right, key);
    }
  }
}
