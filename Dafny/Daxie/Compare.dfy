include "Height.dfy"

module Comparison {
  import opened Terms
  import opened Lists
  import opened TermHeight

  datatype Lookup = Missing | Found(value: Term)

  datatype Ordering = Lt | Eq | Gt

  function IntCompare(a: int, b: int): Ordering {
    if a < b then Lt else if a == b then Eq else Gt
  }

  function StringCompare(a: string, b: string): Ordering
    decreases |a|
  {
    if |a| == 0 then (if |b| == 0 then Eq else Lt)
    else if |b| == 0 then Gt
    else if a[0] == b[0] then StringCompare(a[1..], b[1..])
    else if a[0] < b[0] then Lt else Gt
  }

  function FloatCompare(a: FiniteFloat, b: FiniteFloat, exact: bool): Ordering {
    if a < b then Lt else if a > b then Gt
    else if exact && a.IsNegative != b.IsNegative then
      (if a.IsNegative then Lt else Gt) else Eq
  }

  function Swap(order: Ordering): Ordering {
    match order
    case Lt => Gt
    case Eq => Eq
    case Gt => Lt
  }

  // Truncating a finite float produces an exactly representable integer.
  // Comparing integers first avoids rounding the arbitrary input integer.
  // The tie case distinguishes a fractional float from its truncation.
  // This also avoids the nightly C# backend's unsupported subnormal-to-real cast.
  function MixedCompare(integer: int, floating: FiniteFloat): Ordering {
    var truncated := fp64.ToInt(floating);
    match IntCompare(integer, truncated)
    case Eq => if fp64.Equal(floating, fp64.FromReal(truncated as real)) then Eq
               else if floating.IsNegative then Gt else Lt
    case order => order
  }

  // Numeric order compares exact mathematical values, including mixed operands.
  // Exact order separates numeric types and signed zero, as in the Lean model.
  function Compare(a: Term, b: Term, exact: bool): Ordering
    decreases Max(Height(a), Height(b)), 5, 0
  {
    match (a, b)
    case (Integer(x), Integer(y)) => IntCompare(x, y)
    case (Integer(x), Float(y)) => if exact then Lt else MixedCompare(x, y)
    case (Float(x), Integer(y)) => if exact then Gt else Swap(MixedCompare(y, x))
    case (Float(x), Float(y)) => FloatCompare(x, y, exact)
    case (Integer(_), _) => Lt
    case (_, Integer(_)) => Gt
    case (Float(_), _) => Lt
    case (_, Float(_)) => Gt
    case (Atom(x), Atom(y)) => StringCompare(x, y)
    case (Atom(_), _) => Lt
    case (_, Atom(_)) => Gt
    case (Function(id, _, xs), Function(other, _, ys)) =>
      (match IntCompare(id, other)
       case Eq => CompareSequence(xs, ys, true)
       case order => order)
    case (Function(_, _, _), _) => Lt
    case (_, Function(_, _, _)) => Gt
    case (Pid(x), Pid(y)) => IntCompare(x, y)
    case (Pid(_), _) => Lt
    case (_, Pid(_)) => Gt
    case (Tuple(x), Tuple(y)) =>
      (match IntCompare(|x|, |y|)
       case Eq => CompareSequence(x, y, exact)
       case order => order)
    case (Tuple(_), _) => Lt
    case (_, Tuple(_)) => Gt
    case (Map(x), Map(y)) =>
      if SameBindings(x, y, exact) then Eq else
        var left := Normalize(x);
        var right := Normalize(y);
        (match IntCompare(Length(left), Length(right))
         case Eq =>
           (match CompareKeys(left, right)
            case Eq => CompareValues(left, right, exact)
            case order => order)
         case order => order)
    case (Map(_), _) => Lt
    case (_, Map(_)) => Gt
    case (Nil, Nil) => Eq
    case (Nil, Cons(_, _)) => Lt
    case (Cons(_, _), Nil) => Gt
    case (Cons(x, xs), Cons(y, ys)) =>
      (match Compare(x, y, exact)
       case Eq => Compare(xs, ys, exact)
       case order => order)
  }

  function CompareSequence(a: seq<Term>, b: seq<Term>, exact: bool): Ordering
    decreases Max(Maximum(Heights(a)), Maximum(Heights(b))) + 1, 4, |a|
  {
    if |a| == 0 then (if |b| == 0 then Eq else Lt)
    else if |b| == 0 then Gt else
      HeightsTail(a); HeightsTail(b);
      match Compare(a[0], b[0], exact)
      case Eq => CompareSequence(a[1..], b[1..], exact)
      case order => order
  }

  function Find(xs: List<(Term, Term)>, key: Term): (result: Lookup)
    ensures result.Found? ==> Height(result.value) <= EntriesHeight(xs)
    decreases Max(EntriesHeight(xs), Height(key)) + 1, 2, Length(xs)
  {
    match xs
    case Empty => Missing
    case Link((stored, value), tail) =>
      (match Compare(key, stored, true)
       case Eq => Found(value)
       case _ => Find(tail, key))
  }

  function MatchesKeys(keys: List<(Term, Term)>, a: List<(Term, Term)>, b: List<(Term, Term)>, exact: bool): bool
    requires EntriesHeight(keys) <= Max(EntriesHeight(a), EntriesHeight(b))
    decreases Max(EntriesHeight(a), EntriesHeight(b)) + 1, 3, Length(keys)
  {
    match keys
    case Empty => true
    case Link((key, _), tail) =>
      (match (Find(a, key), Find(b, key))
       case (Found(x), Found(y)) => Compare(x, y, exact) == Eq && MatchesKeys(tail, a, b, exact)
       case (Missing, Missing) => MatchesKeys(tail, a, b, exact)
       case _ => false)
  }

  function SameBindings(a: List<(Term, Term)>, b: List<(Term, Term)>, exact: bool): bool
    decreases Max(EntriesHeight(a), EntriesHeight(b)) + 1, 4, 0
  {
    MatchesKeys(a, a, b, exact) && MatchesKeys(b, a, b, exact)
  }

  function Insert(entry: (Term, Term), xs: List<(Term, Term)>): (result: List<(Term, Term)>)
    ensures EntriesHeight(result) <= Max(Max(Height(entry.0), Height(entry.1)), EntriesHeight(xs))
    decreases Max(Max(Height(entry.0), Height(entry.1)), EntriesHeight(xs)) + 1, 3, Length(xs)
  {
    match xs
    case Empty => Link(entry, Empty)
    case Link(head, tail) =>
      (match Compare(entry.0, head.0, true)
       case Lt => Link(entry, xs)
       case Eq => Link(entry, tail)
       case Gt => Link(head, Insert(entry, tail)))
  }

  function Normalize(xs: List<(Term, Term)>): (result: List<(Term, Term)>)
    ensures EntriesHeight(result) <= EntriesHeight(xs)
    decreases EntriesHeight(xs) + 1, 4, Length(xs)
  {
    match xs
    case Empty => Empty
    case Link(head, tail) => Insert(head, Normalize(tail))
  }

  function CompareKeys(a: List<(Term, Term)>, b: List<(Term, Term)>): Ordering
    decreases Max(EntriesHeight(a), EntriesHeight(b)) + 1, 4, Length(a)
  {
    match (a, b)
    case (Empty, Empty) => Eq
    case (Empty, _) => Lt
    case (_, Empty) => Gt
    case (Link((key, _), tail), Link((other, _), rest)) =>
      (match Compare(key, other, true)
       case Eq => CompareKeys(tail, rest)
       case order => order)
  }

  function CompareValues(a: List<(Term, Term)>, b: List<(Term, Term)>, exact: bool): Ordering
    decreases Max(EntriesHeight(a), EntriesHeight(b)) + 1, 4, Length(a)
  {
    match (a, b)
    case (Empty, Empty) => Eq
    case (Empty, _) => Lt
    case (_, Empty) => Gt
    case (Link((_, value), tail), Link((_, other), rest)) =>
      (match Compare(value, other, exact)
       case Eq => CompareValues(tail, rest, exact)
       case order => order)
  }

  function compare(a: Term, b: Term): Ordering { Compare(a, b, false) }
  function exactCompare(a: Term, b: Term): Ordering { Compare(a, b, true) }

  function eq_2(a: Term, b: Term): Result { Ok(Boolean(compare(a, b) == Eq)) }
  function neq_2(a: Term, b: Term): Result { Ok(Boolean(compare(a, b) != Eq)) }
  function exact_eq_2(a: Term, b: Term): Result { Ok(Boolean(exactCompare(a, b) == Eq)) }
  function exact_neq_2(a: Term, b: Term): Result { Ok(Boolean(exactCompare(a, b) != Eq)) }
  function lt_2(a: Term, b: Term): Result { Ok(Boolean(compare(a, b) == Lt)) }
  function le_2(a: Term, b: Term): Result { Ok(Boolean(compare(a, b) != Gt)) }
  function gt_2(a: Term, b: Term): Result { Ok(Boolean(compare(a, b) == Gt)) }
  function ge_2(a: Term, b: Term): Result { Ok(Boolean(compare(a, b) != Lt)) }
}
