# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/bloom_filter.exs
#
# A Bloom filter of m bits and k hash functions, its bits held in an integer.
# Inserting an element sets the k bits it hashes to, and querying it checks
# that all of them are set.
#
# The first laws hold for the actual hash, erlang:phash2/2: the filter has no
# false negatives, inserting keeps earlier members, and the union of two
# filters is the filter of both lists.
#
# The false positive rate is a property of random hash functions instead, where
# every tuple of k positions is equally likely. accepted/1 counts, out of all
# the m^k tuples a query could hash to, those the filter accepts. The last law
# proves that this is s^k, where s is the number of set bits, so a filter accepts
# a query with probability (s/m)^k. The false positive rate after n insertions
# is therefore the average of (s/m)^k over every way the insertions may hash.
#
# Bloom's classical estimate, (1 - (1 - 1/m)^(kn))^k, instead raises the
# average fraction of set bits to the power k, as if the bits were set
# independently. They are not, and the test below shows the estimate is wrong
# for 2 bits, 2 hash functions, and 1 insertion: the rate is 10/16, as Bose et
# al.'s corrected formula gives, not 9/16.
# See "Certifying Certainty and Uncertainty in Approximate Membership Query
# Structures" (Gopinathan and Sergey, CAV 2020).
ExUnit.start()

defmodule BloomFilterProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case
  import Bitwise

  def new(m, k), do: {m, k, 0}

  def insert({m, k, bits}, x), do: {m, k, add(bits, positions(x, m, k))}

  def member?({m, k, bits}, x), do: hit?(bits, positions(x, m, k))

  def union({m, k, left}, {m, k, right}), do: {m, k, bor(left, right)}

  def from_list(m, k, xs), do: insert_all(new(m, k), xs)

  defp insert_all(filter, []), do: filter
  defp insert_all(filter, [x | xs]), do: insert_all(insert(filter, x), xs)

  # The positions x hashes to, one for each hash function.
  defp positions(x, m, k) when k > 0, do: [:erlang.phash2({k, x}, m) | positions(x, m, k - 1)]
  defp positions(_x, _m, _k), do: []

  defp add(bits, []), do: bits
  defp add(bits, [p | ps]), do: add(bor(bits, bsl(1, p)), ps)

  defp hit?(_bits, []), do: true
  defp hit?(bits, [p | ps]), do: band(bsr(bits, p), 1) == 1 and hit?(bits, ps)

  # How many of the m^k tuples of positions the filter accepts.
  def accepted({m, k, bits}), do: accepted(bits, m, k, [])

  defp accepted(bits, m, k, query) when k > 0, do: accepted_from(bits, m, k, query, 0)
  defp accepted(bits, _m, _k, query), do: if(hit?(bits, query), do: 1, else: 0)

  defp accepted_from(bits, m, k, query, p) when p < m,
    do: accepted(bits, m, k - 1, [p | query]) + accepted_from(bits, m, k, query, p + 1)

  defp accepted_from(_bits, _m, _k, _query, _p), do: 0

  # The number of set bits among the first m.
  def set_bits({m, _k, bits}), do: set_bits(bits, m)

  defp set_bits(bits, p) when p > 0, do: band(bsr(bits, p - 1), 1) + set_bits(bits, p - 1)
  defp set_bits(_bits, _p), do: 0

  def power(base, exponent) when exponent > 0, do: base * power(base, exponent - 1)
  def power(_base, _exponent), do: 1

  # phash2/2 accepts ranges up to 2^32.
  def valid?({m, k, bits}),
    do:
      is_integer(m) and m >= 1 and m <= 4_294_967_296 and is_integer(k) and k >= 0 and
        is_integer(bits) and bits >= 0

  def valid?(_), do: false

  def proper_list?([_ | tail]), do: proper_list?(tail)
  def proper_list?([]), do: true
  def proper_list?(_), do: false

  laws "Bloom filter" do
    # Lean cannot infer that these loops, which count towards a bound, terminate.
    # The proofs show they return for the inputs the laws use.
    termination_suffix &__MODULE__.positions/3, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.accepted/4, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.accepted_from/5, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.set_bits/2, ~LEAN"partial_fixpoint"
    termination_suffix &__MODULE__.power/2, ~LEAN"partial_fixpoint"

    prelude "bloom_filter/prelude"

    postlude "bloom_filter/postlude"

    law no_false_negatives(filter, x),
      requires: valid?(filter),
      expects: member?(insert(filter, x), x),
      proof: ~LEAN"""
      obtain ⟨m, k, bits, rfl, positive, bounded⟩ := valid_filter requires
      obtain ⟨ps, hashed⟩ := positions_returns x m positive bounded k
      simp [«no_false_negatives:ensures/2», «insert/2», «member?/2», hashed, add_returns,
        hit_returns, BloomProof.testBit_add]
      exact fun _ mem _ => mem
      """

    law insert_keeps_members(filter, x, y),
      requires: valid?(filter) and member?(filter, y),
      expects: member?(insert(filter, x), y),
      proof: ~LEAN"""
      obtain ⟨valid, member⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp requires
      obtain ⟨m, k, bits, rfl, positive, bounded⟩ := valid_filter valid
      obtain ⟨ps, hashed⟩ := positions_returns x m positive bounded k
      obtain ⟨qs, queried⟩ := positions_returns y m positive bounded k
      simp [«member?/2», queried, hit_returns] at member
      simp [«insert_keeps_members:ensures/3», «insert/2», «member?/2», hashed, queried,
        add_returns, hit_returns, BloomProof.testBit_add]
      intro q mem unset
      simp [member q mem] at unset
      """

    law union_from_lists(m, k, xs, ys),
      requires: valid?(new(m, k)) and proper_list?(xs) and proper_list?(ys),
      expects: union(from_list(m, k, xs), from_list(m, k, ys)) === from_list(m, k, xs ++ ys),
      proof: ~LEAN"""
      simp only [«union_from_lists:requires/4», «new/2»] at requires
      obtain ⟨front, ysProper⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp requires
      obtain ⟨valid, xsProper⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp front
      obtain ⟨m', k', _, filter, positive, bounded⟩ := valid_filter valid
      simp at filter
      obtain ⟨rfl, rfl, -⟩ := filter
      obtain ⟨left, rfl⟩ := proper_list xsProper
      obtain ⟨right, rfl⟩ := proper_list ysProper
      obtain ⟨leftSet, leftInserted⟩ := insert_all_returns m' k' positive bounded left
      obtain ⟨rightSet, rightInserted⟩ := insert_all_returns m' k' positive bounded right
      have leftEmpty := leftInserted 0
      have rightEmpty := rightInserted 0
      simp only [Nat.zero_or, show ((0 : Nat) : Int) = 0 from rfl] at leftEmpty rightEmpty
      simp [«union_from_lists:ensures/4», «from_list/3», «new/2», «union/2», append_lists,
        insert_all_append, leftEmpty, rightEmpty, rightInserted, BloomProof.bor_nat,
        Erlang.erlang.«and/2»]
      """

    law accepted_queries(filter),
      requires: valid?(filter),
      expects: accepted(filter) === power(set_bits(filter), elem(filter, 1)),
      proof: ~LEAN"""
      obtain ⟨m, k, bits, rfl, -, -⟩ := valid_filter requires
      have accepted := accepted_returns bits m k []
      simp only [BloomProof.indices_nil] at accepted
      simp [«accepted_queries:ensures/1», «accepted/1», «set_bits/1», accepted, set_bits_returns,
        power_returns, Erlang.erlang.«element/2»]
      """
  end

  # Every list of positions below m of the given length.
  defp tuples(_m, 0), do: [[]]
  defp tuples(m, length), do: for(p <- 0..(m - 1), rest <- tuples(m, length - 1), do: [p | rest])

  test "Bloom's estimate of the false positive rate is wrong" do
    {m, k, n} = {2, 2, 1}

    # Every way the n insertions may hash, each equally likely, and every query.
    accepted = Enum.sum(for ps <- tuples(m, k * n), do: accepted({m, k, add(0, ps)}))
    assert {accepted, m ** (k * (n + 1))} == {10, 16}

    # (1 - (1 - 1/m)^(kn))^k as a fraction over the same denominator.
    bloom = (m ** (k * n) - (m - 1) ** (k * n)) ** k
    assert {bloom, m ** (k * (n + 1))} == {9, 16}
  end
end
