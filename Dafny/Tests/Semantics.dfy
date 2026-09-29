include "../Daxie/Compare.dfy"
include "../Daxie/Sum.dfy"
include "../Benchmarks/NativeSum.dfy"

module SemanticsTests {
  import opened Terms
  import opened Comparison
  import opened Arithmetic
  import opened TermSum
  import N = NativeSum

  lemma IntegerArithmetic(a: int, b: int)
    ensures add_2(Integer(a), Integer(b)) == Ok(Integer(a + b))
  {}

  lemma RejectNonFinite(value: fp64)
    requires !value.IsFinite
    ensures FloatResult(value) == Error(Atom("badarith"))
  {}

  method Check(actual: Result, expected: Result) {
    match (actual, expected) {
      case (Ok(a), Ok(b)) => expect exactCompare(a, b) == Eq;
      case (Error(a), Error(b)) => expect exactCompare(a, b) == Eq;
      case _ => expect false, "Result shape mismatch";
    }
  }

  method CheckMixed(integer: int, floating: FiniteFloat, expected: Result) {
    Check(add_2(Integer(integer), Float(floating)), expected);
    Check(add_2(Float(floating), Integer(integer)), expected);
  }

  method CheckOrder(left: Term, right: Term, expected: Ordering) {
    expect compare(left, right) == expected;
    expect compare(right, left) == Swap(expected);
  }

  method NumericEdges() {
    // Integer conversion rounds ties to even in both directions and signs.
    CheckMixed(9007199254740991, 0.0, Ok(Float(9007199254740991.0)));
    CheckMixed(9007199254740993, 0.0, Ok(Float(9007199254740992.0)));
    CheckMixed(9007199254740995, 0.0, Ok(Float(9007199254740996.0)));
    CheckMixed(-9007199254740993, 0.0, Ok(Float(-9007199254740992.0)));
    CheckMixed(-9007199254740995, 0.0, Ok(Float(-9007199254740996.0)));
    CheckMixed(0, -0.0, Ok(Float(0.0)));
    CheckMixed(1, -1.0, Ok(Float(0.0)));

    CheckOrder(Integer(0), Float(~5e-324), Lt);
    CheckOrder(Integer(0), Float(~-5e-324), Gt);
    CheckOrder(Integer(0), Float(-0.0), Eq);
    CheckOrder(Integer(1), Float(1.5), Lt);
    CheckOrder(Integer(-1), Float(-1.5), Gt);
    CheckOrder(Integer(9007199254740993), Float(9007199254740992.0), Gt);
    CheckOrder(Integer(-9007199254740993), Float(-9007199254740992.0), Lt);
    CheckOrder(Float(~-5e-324), Float(~5e-324), Lt);

    // Build 2^1024 and half the final binary64 spacing using integer arithmetic.
    var overflow := 1;
    for i := 0 to 1024 { overflow := overflow * 2; }
    var halfSpacing := 1;
    for i := 0 to 970 { halfSpacing := halfSpacing * 2; }
    var threshold := overflow - halfSpacing;
    CheckMixed(threshold - 1, 0.0, Ok(Float(fp64.MaxValue)));
    CheckMixed(threshold, 0.0, Error(Atom("badarith")));
    CheckMixed(-threshold, 0.0, Error(Atom("badarith")));
    CheckMixed(overflow, 0.0, Error(Atom("badarith")));
    CheckMixed(-overflow, 0.0, Error(Atom("badarith")));
    // Conversion must fail even if adding the float could otherwise cancel it.
    CheckMixed(overflow, -fp64.MaxValue, Error(Atom("badarith")));
    CheckOrder(Integer(overflow), Float(fp64.MaxValue), Gt);
    CheckOrder(Integer(-overflow), Float(-fp64.MaxValue), Lt);
    CheckOrder(Integer(overflow - 2 * halfSpacing), Float(fp64.MaxValue), Eq);
    Check(add_2(Float(-fp64.MaxValue), Float(-fp64.MaxValue)), Error(Atom("badarith")));
  }

  method Main() {
    var zero := Float(0.0);
    var minusZero := Float(-0.0);
    var one := Float(1.0);
    var two := Float(2.0);
    expect compare(Integer(1), one) == Eq;
    expect exactCompare(Integer(1), one) == Lt;
    expect exactCompare(Integer(100), one) == Lt;
    expect compare(Integer(100), one) == Gt;
    expect compare(Integer(0), Float(~5e-324)) == Lt;
    expect compare(Float(~-5e-324), Integer(0)) == Lt;
    expect compare(Integer(1), Float(1.5)) == Lt;
    expect compare(Integer(-1), Float(-1.5)) == Gt;
    expect compare(zero, minusZero) == Eq;
    expect exactCompare(minusZero, zero) == Lt;
    Check(exact_eq_2(zero, minusZero), Ok(Boolean(false)));
    Check(eq_2(Integer(1), one), Ok(Boolean(true)));
    Check(neq_2(Integer(1), one), Ok(Boolean(false)));
    Check(exact_neq_2(Integer(1), one), Ok(Boolean(true)));
    Check(lt_2(Integer(-1), zero), Ok(Boolean(true)));
    Check(le_2(one, Integer(1)), Ok(Boolean(true)));
    Check(gt_2(Integer(2), one), Ok(Boolean(true)));
    Check(ge_2(Integer(1), one), Ok(Boolean(true)));
    expect compare(Integer(-3), Atom("a")) == Lt;
    expect compare(Atom("a"), Atom("aa")) == Lt;
    expect compare(Atom("z"), Tuple([])) == Lt;
    expect compare(Tuple([Integer(999)]), Tuple([Integer(0), Integer(0)])) == Lt;
    expect compare(Tuple([Cons(Integer(1), Nil)]), Tuple([Cons(one, Nil)])) == Eq;
    expect exactCompare(Tuple([Cons(Integer(1), Nil)]), Tuple([Cons(one, Nil)])) == Lt;
    expect compare(Tuple([]), Nil) == Lt;
    expect compare(Nil, Cons(Integer(0), Nil)) == Lt;
    expect compare(Cons(Integer(1), Atom("a")), Cons(Integer(1), Nil)) == Lt;
    Check(add_2(Integer(2), Integer(-5)), Ok(Integer(-3)));
    Check(add_2(one, one), Ok(two));
    Check(add_2(Integer(1), one), Ok(two));
    Check(add_2(one, Integer(1)), Ok(two));
    Check(add_2(minusZero, minusZero), Ok(minusZero));
    Check(add_2(zero, minusZero), Ok(zero));
    Check(add_2(one, Float(-1.0)), Ok(zero));
    Check(add_2(Atom("x"), Integer(1)), Error(Atom("badarith")));
    Check(add_2(Float(~5e-324), Float(~5e-324)), Ok(Float(~1e-323)));
    Check(add_2(Float(~2.225073858507201e-308), Float(~5e-324)),
      Ok(Float(fp64.MinNormal)));
    // Half an ulp at 1.0 rounds to even; at its successor it rounds upward.
    var halfUlp := Float(0.00000000000000011102230246251565404236316680908203125);
    Check(add_2(one, halfUlp), Ok(one));
    Check(add_2(Float(~1.0000000000000002), halfUlp), Ok(Float(~1.0000000000000004)));
    var largest := Float(fp64.MaxValue);
    Check(add_2(largest, largest), Error(Atom("badarith")));
    Check(FloatResult(fp64.PositiveInfinity), Error(Atom("badarith")));
    Check(FloatResult(fp64.NegativeInfinity), Error(Atom("badarith")));
    Check(FloatResult(fp64.NaN), Error(Atom("badarith")));
    Check(add_2(Integer(9007199254740993), zero), Ok(Float(9007199254740992.0)));
    expect compare(Integer(9007199254740993), Float(9007199254740992.0)) == Gt;
    var list := Cons(Integer(1), Cons(Integer(-2), Cons(Integer(3), Nil)));
    Check(sum_1(Nil), Ok(Integer(0)));
    Check(sum_1(list), Ok(Integer(2)));
    expect N.sum_1(N.Cons(1, N.Cons(-2, N.Cons(3, N.Nil)))) == 2;
    Check(sum_1(Cons(one, Nil)), Ok(one));
    Check(sum_1(Cons(Integer(1), Atom("tail"))), Error(Atom("function_clause")));
    Check(sum_1(Cons(Atom("x"), Nil)), Error(Atom("badarith")));
    Check(sum_1(Cons(Atom("x"), Atom("tail"))), Error(Atom("function_clause")));
    Check(append_2(Nil, Atom("tail")), Ok(Atom("tail")));
    Check(append_2(Integer(1), Nil), Error(Atom("badarg")));
    expect !IsProperIntegerList(Cons(one, Nil));
    expect !IsProperIntegerList(Cons(Integer(1), Integer(2)));
    NumericEdges();
    print "Semantic checks passed\n";
  }
}
