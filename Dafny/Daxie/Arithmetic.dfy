include "Term.dfy"

module Arithmetic {
  import opened Terms
  function FloatResult(result: fp64): Result {
    if result.IsFinite then Ok(Float(result)) else Error(Atom("badarith"))
  }

  function AddFinite(left: FiniteFloat, right: FiniteFloat): Result {
    FloatResult(left + right)
  }

  function MixedAdd(integer: int, floating: FiniteFloat): Result {
    var converted := fp64.FromReal(integer as real);
    if converted.IsFinite then AddFinite(converted, floating)
    else Error(Atom("badarith"))
  }

  // Integer-list proofs use this verified specification without expanding
  // floating-point arithmetic into their SMT context.
  opaque function add_2(left: Term, right: Term): (result: Result)
    ensures IsPure(result)
    ensures left.Integer? && right.Integer? ==>
      result == Ok(Integer(left.integer + right.integer))
  {
    match (left, right)
    case (Integer(a), Integer(b)) => Ok(Integer(a + b))
    case (Float(a), Float(b)) => AddFinite(a, b)
    case (Integer(a), Float(b)) => MixedAdd(a, b)
    case (Float(a), Integer(b)) => MixedAdd(b, a)
    case _ => Error(Atom("badarith"))
  }
}
