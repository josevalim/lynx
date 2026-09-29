include "Term.dfy"

module TermHeight {
  import opened Terms
  import opened Lists

  function Max(a: nat, b: nat): nat { if a < b then b else a }

  function Maximum(xs: seq<nat>): nat
    ensures forall i :: 0 <= i < |xs| ==> xs[i] <= Maximum(xs)
    decreases |xs|
  {
    if |xs| == 0 then 0 else Max(xs[0], Maximum(xs[1..]))
  }

  function Height(t: Term): nat
    decreases t
  {
    match t
    case Function(_, _, xs) => 1 + Maximum(seq(|xs|, i requires 0 <= i < |xs| => Height(xs[i])))
    case Tuple(xs) => 1 + Maximum(seq(|xs|, i requires 0 <= i < |xs| => Height(xs[i])))
    case Map(xs) => 1 + EntriesHeight(xs)
    case Cons(head, tail) => 1 + Max(Height(head), Height(tail))
    case _ => 1
  }

  function EntriesHeight(xs: List<(Term, Term)>): nat
    decreases xs
  {
    match xs
    case Empty => 0
    case Link((key, value), tail) => Max(Max(Height(key), Height(value)), EntriesHeight(tail))
  }

  function Heights(xs: seq<Term>): seq<nat> {
    seq(|xs|, i requires 0 <= i < |xs| => Height(xs[i]))
  }

  lemma HeightsTail(xs: seq<Term>)
    requires |xs| > 0
    ensures Maximum(Heights(xs[1..])) <= Maximum(Heights(xs))
  {
    assert Heights(xs[1..]) == Heights(xs)[1..];
  }
}
