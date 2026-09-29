include "../Daxie/List.dfy"

module NativeSets {
  import opened Lists
  // Same native key/value types as Lean: integers mapped to lists of integers.
  // Nonempty values remain representable, so the set invariant is meaningful.
  type SetMap = map<int, List<int>>

  predicate IsSet(value: SetMap) {
    forall key <- value.Keys :: value[key] == Empty
  }

  function union_2(left: SetMap, right: SetMap): SetMap { left + right }

  lemma UnionContract(left: SetMap, right: SetMap)
    requires IsSet(left) && IsSet(right)
    ensures IsSet(union_2(left, right))
  {}

  lemma UnionCommutative(left: SetMap, right: SetMap)
    requires IsSet(left) && IsSet(right)
    ensures union_2(left, right) == union_2(right, left)
  {
    assert forall key :: key in left || key in right ==>
      union_2(left, right)[key] == union_2(right, left)[key];
  }

  lemma UnionEmpty(value: SetMap)
    requires IsSet(value)
    ensures union_2(value, map[]) == value
  {}
}
