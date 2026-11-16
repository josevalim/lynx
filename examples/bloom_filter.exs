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

    prelude ~LEAN"""
    module
    public import Lynx
    public import Lynx.Modules.Erlang.erlang
    public section

    namespace BloomProof
    open Lynx

    /-- A proper list of bit positions. -/
    @[expose] def indices (ps : List Nat) : Term := Term.list (ps.map fun p : Nat => .integer (p : Int))

    @[simp] theorem indices_nil : indices [] = .nil := rfl
    @[simp] theorem indices_cons (p : Nat) (ps : List Nat) :
        indices (p :: ps) = .cons (.integer p) (indices ps) := rfl

    /-- The bits after setting each position, as `add/2` computes them. -/
    @[expose] def add (bits : Nat) (ps : List Nat) : Nat := ps.foldl (fun b p => b ||| 2 ^ p) bits

    theorem testBit_add (bits : Nat) (ps : List Nat) (i : Nat) :
        (add bits ps).testBit i = (bits.testBit i || ps.contains i) := by
      induction ps generalizing bits with
      | nil => simp [add]
      | cons p ps ih =>
        simp only [add, List.foldl_cons] at ih ⊢
        rw [ih]
        by_cases h : i = p
        · subst h; simp
        · have other : ¬p = i := fun e => h e.symm
          simp [h, other]

    theorem add_or (bits : Nat) (ps : List Nat) : add bits ps = bits ||| add 0 ps := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp [testBit_add]

    /-- The number of set bits below `p`. -/
    @[expose] def ones (bits : Nat) : Nat → Nat
      | 0 => 0
      | p + 1 => (if bits.testBit p then 1 else 0) + ones bits p

    /-! The bit operations on natural numbers, stated in simp normal form. -/

    theorem bsl_one (p : Nat) :
        Erlang.erlang.«bsl/2» (.integer 1) (.integer p) = .ok (.integer (2 ^ p)) := by
      simp [Erlang.erlang.«bsl/2», Int.shiftLeft_eq]

    theorem bor_two_pow (bits p : Nat) :
        Erlang.erlang.«bor/2» (.integer bits) (.integer (2 ^ p)) =
          .ok (.integer (bits ||| 2 ^ p : Nat)) := by
      have power : (2 : Int) ^ p = ((2 ^ p : Nat) : Int) := by simp
      rw [power]
      rfl

    theorem bor_nat (left right : Nat) :
        Erlang.erlang.«bor/2» (.integer left) (.integer right) =
          .ok (.integer (left ||| right : Nat)) := rfl

    theorem bsr_nat (bits p : Nat) :
        Erlang.erlang.«bsr/2» (.integer bits) (.integer p) = .ok (.integer ((bits : Int) >>> p)) := rfl

    theorem bit (bits p : Nat) :
        Erlang.erlang.«band/2» (.integer ((bits : Int) >>> p)) (.integer 1) =
          .ok (.integer (if bits.testBit p then 1 else 0)) := by
      have h := Nat.testBit_eq_decide_div_mod_eq (x := bits) (i := p)
      have masked : (bits >>> p) &&& 1 = if bits.testBit p then 1 else 0 := by
        rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
        split <;> simp_all <;> omega
      have shifted : (bits : Int) >>> p = ((bits >>> p : Nat) : Int) := rfl
      rw [shifted]
      show (Except.ok (Term.integer ((bits >>> p) &&& 1 : Nat)) : Except Exception Term) = _
      rw [masked]
      split <;> rfl

    end BloomProof
    """

    postlude ~LEAN"""
    namespace Elixir.BloomFilterProofsTest
    open Lynx BloomProof

    /-- `phash2/2` maps every element to `k` positions below `m`. -/
    theorem positions_returns (x : Term) (m : Nat) (positive : 0 < m) (bounded : m ≤ 2 ^ 32)
        (k : Int) : ∃ ps : List Nat, «positions/3» x (.integer m) (.integer k) = .ok (indices ps) := by
      induction h : k.toNat generalizing k with
      | zero =>
        exact ⟨[], by rw [«positions/3».eq_def]; simp [show ¬ 0 < k by omega]⟩
      | succ n ih =>
        obtain ⟨ps, rest⟩ := ih (k - 1) (by omega)
        obtain ⟨hash, hashed, _⟩ :=
          Erlang.erlang.phash2_range_bounded (.tuple #[.integer k, x]) m positive bounded
        exact ⟨hash :: ps, by rw [«positions/3».eq_def]; simp [show 0 < k by omega, hashed, rest]⟩

    theorem add_returns (bits : Nat) (ps : List Nat) :
        «add/2» (.integer bits) (indices ps) = .ok (.integer (add bits ps)) := by
      induction ps generalizing bits with
      | nil => simp [«add/2», add]
      | cons p ps ih => simp [«add/2», bsl_one, bor_two_pow, ih, add]

    theorem hit_returns (bits : Nat) (ps : List Nat) :
        «hit?/2» (.integer bits) (indices ps) =
          .ok (if ps.all bits.testBit then Term.true else Term.false) := by
      induction ps with
      | nil => simp [«hit?/2»]
      | cons p ps ih => by_cases h : bits.testBit p <;> simp [«hit?/2», bsr_nat, bit, ih, h]

    theorem valid_filter {filter : Term} (valid : «valid?/1» filter = .ok Term.true) :
        ∃ m k bits : Nat, filter = .tuple #[.integer m, .integer k, .integer bits] ∧
          0 < m ∧ m ≤ 2 ^ 32 := by
      unfold «valid?/1» at valid
      split at valid
      · rename_i m k bits
        cases m <;> simp [Erlang.erlang.«is_integer/1»] at valid
        cases k <;> simp at valid
        cases bits <;> simp at valid
        rename_i m k bits
        refine ⟨m.toNat, k.toNat, bits.toNat, ?_, by omega, by omega⟩
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
          Int.toNat_of_nonneg (by omega)]
      · simp at valid

    theorem proper_list {xs : Term} (proper : «proper_list?/1» xs = .ok Term.true) :
        ∃ l, xs = Term.list l := by
      induction xs using «proper_list?/1».induct with
      | case1 head tail ih =>
        obtain ⟨l, rfl⟩ := ih (by simpa [«proper_list?/1»] using proper)
        exact ⟨head :: l, rfl⟩
      | case2 => exact ⟨[], rfl⟩
      | case3 xs notCons notNil =>
        rw [«proper_list?/1».eq_def] at proper
        split at proper <;> simp_all

    theorem append_lists (left right : List Term) :
        Erlang.erlang.«++/2» (Term.list left) (Term.list right) = .ok (Term.list (left ++ right)) := by
      induction left with
      | nil => rfl
      | cons head tail ih => simp [Erlang.erlang.«++/2», ih]

    theorem insert_all_append (filter : Term) (left right : List Term) :
        «insert_all/2» filter (Term.list (left ++ right)) =
          («insert_all/2» filter (Term.list left) >>= fun inserted =>
            «insert_all/2» inserted (Term.list right)) := by
      induction left generalizing filter with
      | nil => simp [«insert_all/2»]
      | cons x left ih => simp [«insert_all/2», ih]

    /-- Inserting a list sets the same bits whatever bits were set before. -/
    theorem insert_all_returns (m k : Nat) (positive : 0 < m) (bounded : m ≤ 2 ^ 32)
        (l : List Term) : ∃ set : Nat, ∀ bits : Nat,
          «insert_all/2» (.tuple #[.integer m, .integer k, .integer bits]) (Term.list l) =
            .ok (.tuple #[.integer m, .integer k, .integer (bits ||| set : Nat)]) := by
      induction l with
      | nil => exact ⟨0, fun bits => by simp [«insert_all/2»]⟩
      | cons x l ih =>
        obtain ⟨set, rest⟩ := ih
        obtain ⟨ps, hashed⟩ := positions_returns x m positive bounded k
        refine ⟨add 0 ps ||| set, fun bits => ?_⟩
        simp [«insert_all/2», «insert/2», hashed, add_returns]
        rw [add_or, rest, Nat.or_assoc]

    theorem set_bits_returns (bits p : Nat) :
        «set_bits/2» (.integer bits) (.integer p) = .ok (.integer (ones bits p)) := by
      induction p with
      | zero => rw [«set_bits/2».eq_def]; simp [ones]
      | succ p ih =>
        rw [«set_bits/2».eq_def]
        by_cases h : bits.testBit p <;> simp [ih, bsr_nat, bit, ones, h]

    theorem power_returns (base : Int) (exponent : Nat) :
        «power/2» (.integer base) (.integer exponent) = .ok (.integer (base ^ exponent)) := by
      induction exponent with
      | zero => rw [«power/2».eq_def]; simp
      | succ exponent ih =>
        rw [«power/2».eq_def]
        simp [ih, Int.pow_succ, Int.mul_comm]

    /-- A query of `k` more positions after `query` is accepted for `ones^k` of them,
    if every position in `query` is set. -/
    theorem accepted_returns (bits m k : Nat) (query : List Nat) :
        «accepted/4» (.integer bits) (.integer m) (.integer k) (indices query) =
          .ok (.integer (if query.all bits.testBit then (ones bits m : Int) ^ k else 0)) := by
      induction k generalizing query with
      | zero =>
        rw [«accepted/4».eq_def]
        cases h : query.all bits.testBit <;> simp [hit_returns, h]
      | succ k ih =>
        -- The positions from p on contribute the set bits among them, times ones^k.
        have from_returns (n : Nat) : ∀ p, p + n = m → ∀ query : List Nat,
            «accepted_from/5» (.integer bits) (.integer m) (.integer (k + 1)) (indices query)
                (.integer p) =
              .ok (.integer (if query.all bits.testBit then
                ((ones bits m : Int) - ones bits p) * (ones bits m : Int) ^ k else 0)) := by
          induction n with
          | zero =>
            intro p sum query
            rw [«accepted_from/5».eq_def]
            simp [show p = m by omega]
          | succ n inner =>
            intro p sum query
            have next := ih (p :: query)
            simp only [indices_cons] at next
            have rest := inner (p + 1) (by omega) query
            simp only [Int.natCast_add, Int.cast_ofNat_Int] at rest
            rw [«accepted_from/5».eq_def]
            cases all : query.all bits.testBit <;> cases set : bits.testBit p <;>
              simp [show p < m by omega, next, rest, all, set, ones]
            -- c^k + (c - (1 + o)) * c^k = (c - o) * c^k
            grind
        have start := from_returns m 0 (by omega) query
        simp only [Int.cast_ofNat_Int] at start
        rw [«accepted/4».eq_def]
        simp [start, ones, Int.pow_succ, Int.mul_comm]

    end Elixir.BloomFilterProofsTest
    """

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
