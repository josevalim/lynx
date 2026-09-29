include "Term.dfy"

module Comparison {
  import opened Terms

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
    decreases a, 1
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
    case (Tuple(x), Tuple(y)) =>
      (match IntCompare(|x|, |y|)
       case Eq => CompareElements(a, b, 0, exact)
       case order => order)
    case (Tuple(_), _) => Lt
    case (_, Tuple(_)) => Gt
    case (Nil, Nil) => Eq
    case (Nil, Cons(_, _)) => Lt
    case (Cons(_, _), Nil) => Gt
    case (Cons(x, xs), Cons(y, ys)) =>
      (match Compare(x, y, exact)
       case Eq => Compare(xs, ys, exact)
       case order => order)
  }

  function CompareElements(a: Term, b: Term, index: nat, exact: bool): Ordering
    requires a.Tuple? && b.Tuple?
    requires |a.elements| == |b.elements| && index <= |a.elements|
    decreases a, 0, |a.elements| - index
  {
    if index == |a.elements| then Eq else
      match Compare(a.elements[index], b.elements[index], exact)
      case Eq => CompareElements(a, b, index + 1, exact)
      case order => order
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
