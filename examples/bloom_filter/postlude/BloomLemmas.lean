module

public import BloomProof
public import Elixir.BloomFilterProofsTest

@[expose] public section

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
