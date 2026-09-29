include "../Daxie/Maps.dfy"

/*
defmodule SetUnion do
  # A set is a map whose effective values are all [].
  defp is_set(value), do: is_map(value, fn _, v -> v == [] end)
  expects is_set(left) and is_set(right)
  ensures (result -> is_set(result))
  property union(left, right) == union(right, left)
  property union(set, %{}) == set
  def union(left, right), do: :maps.merge(left, right)
end
*/
module TermSets {
  import opened Terms
  import opened Lists
  import opened Comparison
  import opened TermHeight
  import opened Maps

  // Quantify over effective lookups, so a shadowed non-nil binding is harmless.
  ghost predicate AllNil(entries: List<(Term, Term)>) {
    forall key: Term ::
      match Find(entries, key)
      case Missing => true
      case Found(value) => value == Nil
  }

  ghost predicate IsSet(value: Term) {
    match value
    case Map(entries) => AllNil(entries)
    case _ => false
  }

  function union_2(left: Term, right: Term): Result { merge_2(left, right) }

  lemma MergeSet(left: List<(Term, Term)>, right: List<(Term, Term)>)
    requires AllNil(left) && AllNil(right)
    ensures AllNil(Append(right, left))
  {
    forall key: Term
      ensures match Find(Append(right, left), key)
        case Missing => true
        case Found(value) => value == Nil
    {
      FindAppend(right, left, key);
    }
  }

  lemma MergeLookupCommutes(left: List<(Term, Term)>, right: List<(Term, Term)>, key: Term)
    requires AllNil(left) && AllNil(right)
    ensures Find(Append(right, left), key) == Find(Append(left, right), key)
  {
    FindAppend(right, left, key);
    FindAppend(left, right, key);
  }

  lemma MatchSetKeys(keys: List<(Term, Term)>, left: List<(Term, Term)>, right: List<(Term, Term)>)
    requires EntriesHeight(keys) <= Max(EntriesHeight(left), EntriesHeight(right))
    requires AllNil(left) && AllNil(right)
    requires forall key: Term :: Find(left, key) == Find(right, key)
    ensures MatchesKeys(keys, left, right, false)
    decreases keys
  {
    match keys {
      case Empty =>
      case Link((key, _), tail) =>
        assert Find(left, key) == Find(right, key);
        MatchSetKeys(tail, left, right);
    }
  }

  lemma EqualSets(left: List<(Term, Term)>, right: List<(Term, Term)>)
    requires AllNil(left) && AllNil(right)
    requires forall key: Term :: Find(left, key) == Find(right, key)
    ensures compare(Map(left), Map(right)) == Eq
  {
    MatchSetKeys(left, left, right);
    MatchSetKeys(right, left, right);
    assert SameBindings(left, right, false);
    reveal Compare();
  }

  // Only these final contracts/properties are measured; support is checked first.
  lemma UnionContract(left: Term, right: Term)
    requires IsSet(left) && IsSet(right)
    ensures union_2(left, right).Ok?
    ensures IsSet(union_2(left, right).value)
  {
    MergeSet(left.entries, right.entries);
  }

  lemma UnionCommutative(left: Term, right: Term)
    requires IsSet(left) && IsSet(right)
    ensures union_2(left, right).Ok? && union_2(right, left).Ok?
    ensures eq_2(union_2(left, right).value, union_2(right, left).value) == Ok(Boolean(true))
  {
    MergeSet(left.entries, right.entries);
    MergeSet(right.entries, left.entries);
    forall key: Term
      ensures Find(Append(right.entries, left.entries), key) == Find(Append(left.entries, right.entries), key)
    {
      MergeLookupCommutes(left.entries, right.entries, key);
    }
    EqualSets(Append(right.entries, left.entries), Append(left.entries, right.entries));
  }

  lemma UnionEmpty(value: Term)
    requires IsSet(value)
    ensures union_2(value, Map(Empty)).Ok?
    ensures eq_2(union_2(value, Map(Empty)).value, value) == Ok(Boolean(true))
  {
    EqualSets(value.entries, value.entries);
  }
}
