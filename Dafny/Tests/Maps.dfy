include "../Daxie/Maps.dfy"
include "../Benchmarks/TermSets.dfy"

module MapTests {
  import opened Terms
  import opened Lists
  import opened Comparison
  import opened Maps
  import S = TermSets

  function PairMap(key: Term, value: Term): Term { Map(Link((key, value), Empty)) }

  method Check(actual: Result, expected: Result) {
    match (actual, expected) {
      case (Ok(a), Ok(b)) => expect exactCompare(a, b) == Eq;
      case (Error(a), Error(b)) => expect exactCompare(a, b) == Eq;
      case _ => expect false, "Unexpected map operation result";
    }
  }

  lemma ShadowedValuesAreIgnored(key: Term)
    ensures S.IsSet(Map(Link((key, Nil), Link((key, Atom("shadowed")), Empty))))
  {
    reveal Find();
  }

  method Tests() {
    var key := Atom("key");
    var left := Map(Link((key, Integer(1)), Link((Atom("other"), Integer(2)), Empty)));
    var reordered := Map(Link((Atom("other"), Integer(2)), Link((key, Integer(1)), Empty)));
    expect exactCompare(left, reordered) == Eq;
    Check(new_0(), Ok(Map(Empty)));
    Check(get_2(key, left), Ok(Integer(1)));
    Check(get_2(Atom("absent"), left), Error(Tuple([Atom("badkey"), Atom("absent")])));
    Check(get_2(key, Nil), Error(Tuple([Atom("badmap"), Nil])));
    Check(put_3(key, Integer(3), left), Ok(Map(Link((key, Integer(3)), left.entries))));
    Check(put_3(key, Nil, Nil), Error(Tuple([Atom("badmap"), Nil])));
    Check(merge_2(left, Nil), Error(Tuple([Atom("badmap"), Nil])));
    Check(merge_2(Nil, left), Error(Tuple([Atom("badmap"), Nil])));
    var merged := merge_2(left, PairMap(key, Integer(4)));
    expect merged.Ok?;
    Check(get_2(key, merged.value), Ok(Integer(4)));

    // Size is the number of effective keys; old bindings remain harmless.
    var shadowed := Map(Link((key, Integer(1)), Link((key, Integer(99)), Empty)));
    expect exactCompare(shadowed, PairMap(key, Integer(1))) == Eq;
    expect compare(Tuple([]), Map(Empty)) == Lt;
    expect compare(Map(Empty), Nil) == Lt;
    expect compare(Map(Empty), left) == Lt;
    // All keys are compared before any values.
    var a := Map(Link((Integer(1), Integer(999)), Link((Integer(2), Nil), Empty)));
    var b := Map(Link((Integer(1), Integer(0)), Link((Integer(3), Nil), Empty)));
    expect compare(a, b) == Lt;
    expect compare(PairMap(key, Integer(1)), PairMap(key, Float(1.0))) == Eq;
    expect exactCompare(PairMap(key, Integer(1)), PairMap(key, Float(1.0))) == Lt;
    expect compare(PairMap(Integer(1), Nil), PairMap(Float(1.0), Nil)) == Lt;

    // Association-list keys use our comparator, including nested maps and zeros.
    var zeros := Map(Link((Float(0.0), Integer(10)), Link((Float(-0.0), Integer(20)), Empty)));
    Check(get_2(Float(0.0), zeros), Ok(Integer(10)));
    Check(get_2(Float(-0.0), zeros), Ok(Integer(20)));
    Check(get_2(reordered, PairMap(left, Atom("nested"))), Ok(Atom("nested")));
    var funKey := Function(3, 1, [Integer(1)]);
    Check(get_2(funKey, PairMap(funKey, Nil)), Ok(Nil));
    expect exactCompare(funKey, Function(3, 1, [Float(1.0)])) == Lt;
    expect compare(Atom("z"), funKey) == Lt;
    expect compare(funKey, Pid(1)) == Lt;
    expect compare(Pid(1), Tuple([])) == Lt;

    var setA := Map(Link((Integer(1), Nil), Link((Integer(1), Atom("shadowed")), Empty)));
    var setB := Map(Link((Integer(2), Nil), Link((Integer(1), Nil), Empty)));
    var ab := S.union_2(setA, setB);
    var ba := S.union_2(setB, setA);
    expect ab.Ok? && ba.Ok?;
    expect compare(ab.value, ba.value) == Eq;
    Check(S.union_2(setA, Map(Empty)), Ok(setA));
  }
}
