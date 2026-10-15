# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/array.exs
# Prove the installed OTP array module, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1, ERTS 17.1.1).
# These proofs depend on implementation details; rerun after OTP upgrades.
ExUnit.start()

defmodule ArrayProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  # Partial correctness over every successful update, at any tree depth.
  def can_set(index, value, array) do
    try do
      :array.set(index, value, array)
      true
    catch
      _, _ -> false
    end
  end

  def update_contract(index, first, last, array) do
    written = :array.set(index, first, array)

    :array.get(index, written) === first and
      :array.size(written) === max(:array.size(array), index + 1) and
      :array.set(index, last, written) === :array.set(index, last, array)
  end

  @array_fixpoint ~LEAN"""
  partial_fixpoint monotonicity by
    intro f g h
    repeat' first
      | exact Lean.Order.PartialOrder.rel_refl
      | exact h _ _
      | exact h _ _ _
      | exact h _ _ _ _
      | apply Lynx.Result.tryWith_mono_pure
      | apply Lynx.Result.bind_mono_left
      | apply Lynx.Result.bind_mono_pure
      | apply Lynx.Result.IsPure.tryWith
      | apply Lynx.Result.IsPure.handle
      | apply Lynx.Result.IsPure.bind
      | apply Lynx.Result.IsPure.bind_explicit
      | (intro)
      | split
      | simp_all
  """

  laws "array updates" do
    termination_suffix :array.find_bits() / 2, @array_fixpoint
    termination_suffix :array.grow_1() / 3, @array_fixpoint
    termination_suffix :array.get_leaf() / 4, @array_fixpoint
    termination_suffix :array.set_leaf_1() / 3, @array_fixpoint
    termination_suffix :array.set_leaf() / 4, @array_fixpoint
    termination_suffix :array.get_1() / 4, @array_fixpoint

    # Check the shared model once for readback, growth, and last-write-wins.
    law set_obeys_update_contract(index, first, last, array),
      requires: can_set(index, first, array),
      expects: update_contract(index, first, last, array),
      proof: ~LEAN"""
      set_option maxRecDepth 2048 in
        let pack (n z : Int) (fixed default : Lynx.Term) (cache : Array Lynx.Term)
            (ci : Int) (tree : Lynx.Term) (bits : Int) : Lynx.Term :=
          .tuple #[.atom "array", .integer n, .integer z, fixed, default, .tuple cache,
            .integer ci, tree, .integer bits]
        have boolAnd (p q : Prop) [Decidable p] [Decidable q] :
            Erlang.erlang.«and/2» (if p then .atom "true" else .atom "false")
              (if q then .atom "true" else .atom "false") =
                .ok (if p ∧ q then .atom "true" else .atom "false") := by
          by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, Erlang.erlang.«and/2»]
        have andTT : Erlang.erlang.«and/2» (.atom "true") (.atom "true") = .ok (.atom "true") := rfl
        have andTF : Erlang.erlang.«and/2» (.atom "true") (.atom "false") = .ok (.atom "false") := rfl
        have andFT : Erlang.erlang.«and/2» (.atom "false") (.atom "true") = .ok (.atom "false") := rfl
        have readCached (i n z ci bits : Int) (fixed default tree value : Lynx.Term)
            (cache : Array Lynx.Term) (nonnegative : 0 ≤ i) (existing : i < n)
            (lower : ci ≤ i + z) (upper : i + z < ci + 16)
            (valid : (1 + (i + z) - ci).toNat - 1 < cache.size) :
            Erlang.array.«get/2» (.integer i)
              (pack n z fixed default (cache.set ((1 + (i + z) - ci).toNat - 1) value) ci tree bits) =
                .ok value := by
          have positive : 1 ≤ 1 + (i + z) - ci := by omega
          simp [pack, Erlang.array.«get/2», nonnegative, existing, lower, upper,
            Erlang.erlang.«and/2», Erlang.erlang.«element/2», positive, valid]
        have overwriteCached (i n z ci bits : Int) (fixed default tree first last : Lynx.Term)
            (cache : Array Lynx.Term) (nonnegative : 0 ≤ i) (existing : i < n)
            (lower : ci ≤ i + z) (upper : i + z < ci + 16)
            (valid : (1 + (i + z) - ci).toNat - 1 < cache.size) :
            Erlang.array.«set/3» (.integer i) last
              (pack n z fixed default (cache.set ((1 + (i + z) - ci).toNat - 1) first) ci tree bits) =
                .ok (pack n z fixed default (cache.set ((1 + (i + z) - ci).toNat - 1) last) ci tree bits) := by
          have positive : 1 ≤ 1 + (i + z) - ci := by omega
          have bound : 1 + (i + z) - ci ≤ cache.size := by omega
          simp [pack, Erlang.array.«set/3», nonnegative, existing, lower, upper,
            Erlang.erlang.«and/2», Erlang.erlang.«setelement/3», positive, bound]
        have mask (i : Int) : ∃ r : Nat, r < 16 ∧
            Erlang.erlang.«band/2» (.integer i) (.integer 15) = .ok (.integer r) := by
          cases i with
          | ofNat k =>
            exact ⟨k &&& 15, Nat.and_lt_two_pow k (by decide : 15 < 2 ^ 4), rfl⟩
          | negSucc k =>
            refine ⟨15 ^^^ (15 &&& k), Nat.xor_lt_two_pow (by decide : 15 < 2 ^ 4) ?_, rfl⟩
            simpa [Nat.and_comm] using Nat.and_lt_two_pow k (by decide : 15 < 2 ^ 4)
        have replace (k : Int) (cache value out : Lynx.Term)
            (returned : Erlang.erlang.«setelement/3» (.integer k) cache value = .ok out) :
            ∃ entries : Array Lynx.Term, cache = .tuple entries ∧ 1 ≤ k ∧ k ≤ entries.size := by
          cases cache <;> simp [Erlang.erlang.«setelement/3»] at returned
          rename_i entries
          by_cases valid : 1 ≤ k ∧ k ≤ entries.size
          · exact ⟨entries, rfl, valid⟩
          · simp [valid] at returned
        -- Fixed point induction rules out fabricated result shapes on divergent paths.
        have findShape : ∀ i (s : Int) out,
            Erlang.array.«find_bits/2» i (.integer s) = .ok out →
              ∃ n : Int, out = .integer n := by
          apply Erlang.array.«find_bits/2».fixpoint_induct
            (motive := fun f => ∀ i (s : Int) out, f i (.integer s) = .ok out → ∃ n : Int, out = .integer n)
          · apply Lean.Order.admissible_pi
            intro i
            apply Lean.Order.admissible_pi
            intro s
            exact Lean.Order.admissible_apply
              (fun (_ : Lynx.Term) (f : Lynx.Term → Lynx.Result) => ∀ out, f (.integer s) = .ok out → ∃ n : Int, out = .integer n) i
              (Lean.Order.admissible_apply
                (fun (_ : Lynx.Term) (r : Lynx.Result) => ∀ out, r = .ok out → ∃ n : Int, out = .integer n) (.integer s)
                (Lynx.Result.admissible_success _))
          · intro f ih i s out returned
            dsimp only at returned
            cases shifted : s + 4 with
            | ofNat k =>
              simp [Erlang.erlang.«bsl/2», Erlang.erlang.«</2», shifted] at returned
              split at returned
              · exact ⟨s, by simpa using returned.symm⟩
              · exact ih i _ out returned
            | negSucc k =>
              simp [Erlang.erlang.«bsl/2», Erlang.erlang.«</2», shifted] at returned
              split at returned
              · exact ⟨s, by simpa using returned.symm⟩
              · exact ih i _ out returned
        have growShape : ∀ i tree (s : Int) out,
            Erlang.array.«grow_1/3» i tree (.integer s) = .ok out →
              ∃ tree' n, out = .tuple #[tree', .integer n] := by
          intro i
          apply Erlang.array.«grow_1/3».fixpoint_induct i
            (motive := fun f => ∀ tree (s : Int) out, f tree (.integer s) = .ok out →
              ∃ tree' n, out = .tuple #[tree', .integer n])
          · apply Lean.Order.admissible_pi
            intro tree
            apply Lean.Order.admissible_pi
            intro s
            exact Lean.Order.admissible_apply
              (fun (_ : Lynx.Term) (f : Lynx.Term → Lynx.Result) => ∀ out, f (.integer s) = .ok out → ∃ tree' n, out = .tuple #[tree', .integer n]) tree
              (Lean.Order.admissible_apply
                (fun (_ : Lynx.Term) (r : Lynx.Result) => ∀ out, r = .ok out → ∃ tree' n, out = .tuple #[tree', .integer n]) (.integer s)
                (Lynx.Result.admissible_success _))
          · intro f ih tree s out returned
            dsimp only at returned
            cases shifted : s + 4 with
            | ofNat k =>
              simp [Erlang.erlang.«bsl/2», Erlang.erlang.«</2», shifted, Erlang.erlang.«setelement/3»] at returned
              split at returned
              · exact ⟨tree, s, by simpa using returned.symm⟩
              · exact ih _ _ out returned
            | negSucc k =>
              simp [Erlang.erlang.«bsl/2», Erlang.erlang.«</2», shifted, Erlang.erlang.«setelement/3»] at returned
              split at returned
              · exact ⟨tree, s, by simpa using returned.symm⟩
              · exact ih _ _ out returned
        have growth (i s : Int) (tree out : Lynx.Term)
            (returned : Erlang.array.«grow/3» (.integer i) tree (.integer s) = .ok out) :
            ∃ tree' n, out = .tuple #[tree', .integer n] := by
          simp only [Erlang.array.«grow/3»] at returned
          split at returned
          · simp [Erlang.erlang.«is_integer/1», Lynx.Result.bind_eq_ok] at returned
            obtain ⟨bits, found, returned⟩ := returned
            obtain ⟨n, rfl⟩ := findShape _ _ _ found
            exact ⟨.nil, n, by simpa using returned.symm⟩
          · exact growShape _ _ _ _ returned
          · exact growShape _ _ _ _ returned
        -- All update paths end with a cached leaf. The tree preparation is
        -- independent of the replacement value, including during growth.
        have prepared (index value array out : Lynx.Term)
            (returned : Erlang.array.«set/3» index value array = .ok out) :
            ∃ (i n z ci bits : Int) (fixed default tree : Lynx.Term) (cache : Array Lynx.Term)
                (valid : (1 + (i + z) - ci).toNat - 1 < cache.size),
              index = .integer i ∧ Erlang.array.«size/1» array = .ok (.integer n) ∧
              0 ≤ i ∧ ci ≤ i + z ∧ i + z < ci + 16 ∧
              ∀ replacement, Erlang.array.«set/3» index replacement array =
                .ok (pack (max n (i + 1)) z fixed default
                  (cache.set ((1 + (i + z) - ci).toNat - 1) replacement) ci tree bits) := by
          simp only [Erlang.array.«set/3»] at returned
          split at returned
          · rename_i i n z fixed default cache ci tree bits
            by_cases nonnegative : 0 ≤ i <;> simp [nonnegative, boolAnd, andTT, andTF, andFT] at returned
            obtain ⟨r, rBound, masked⟩ := mask (i + z)
            have rLower : (0 : Int) ≤ r := by omega
            have rUpper : (r : Int) < 16 := by omega
            by_cases existing : i < n <;> simp [existing] at returned
            · have maxSize : max n (i + 1) = n := by omega
              by_cases hit : ci ≤ i + z ∧ i + z < ci + 16 <;>
                simp [hit, boolAnd, andTT, andTF, andFT, masked] at returned
              · obtain ⟨updatedCache, cacheWrite, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp returned
                obtain ⟨entries, rfl, lo, bound⟩ := replace _ _ _ _ cacheWrite
                refine ⟨i, n, z, ci, bits, fixed, default, tree, entries, by omega, rfl,
                  by simp [Erlang.array.«size/1»], nonnegative, hit.1, hit.2, ?_⟩
                intro replacement
                simp [Erlang.array.«set/3», nonnegative, existing, hit,
                  boolAnd, andTT, andTF, andFT, Erlang.erlang.«setelement/3», lo, bound, maxSize, pack]
              · obtain ⟨newTree, treeReturned, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp returned
                obtain ⟨newCache, cacheReturned, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp rest
                obtain ⟨updatedCache, cacheWrite, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp rest
                obtain ⟨entries, rfl, lo, bound⟩ := replace _ _ _ _ cacheWrite
                have position : 1 + (i + z) - (i + z - r) = 1 + (r : Int) := by omega
                refine ⟨i, n, z, i + z - r, bits, fixed, default, newTree, entries, by omega, rfl,
                  by simp [Erlang.array.«size/1»], nonnegative, by omega, by omega, ?_⟩
                intro replacement
                simp [Erlang.array.«set/3», nonnegative, existing, hit,
                  boolAnd, andTT, andTF, andFT, masked, treeReturned, cacheReturned,
                  Erlang.erlang.«setelement/3», lo, bound, maxSize, pack, position]
            · by_cases fixedTrue : fixed.exactCompare (.atom "true") = .eq <;>
                simp [Erlang.erlang.«=:=/2», fixedTrue] at returned
              have maxSize : max n (i + 1) = i + 1 := by omega
              have shiftInteger (s : Int) : ∃ b : Int,
                  Erlang.erlang.«bsl/2» (.integer 1) (.integer s) = .ok (.integer b) := by
                cases s <;> exact ⟨_, rfl⟩
              obtain ⟨capacity, shifted⟩ := shiftInteger (bits + 4)
              simp [shifted] at returned
              by_cases fits : i + z < capacity <;> simp [fits, masked] at returned
              · by_cases same : i + z - (r : Int) = ci <;>
                  simp [same, Erlang.erlang.«=/=/2»] at returned
                · obtain ⟨updatedCache, cacheWrite, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp returned
                  obtain ⟨entries, rfl, lo, bound⟩ := replace _ _ _ _ cacheWrite
                  have position : 1 + (i + z) - ci = 1 + (r : Int) := by omega
                  refine ⟨i, n, z, ci, bits, fixed, default, tree, entries, by omega, rfl,
                    by simp [Erlang.array.«size/1»], nonnegative, by omega, by omega, ?_⟩
                  intro replacement
                  simp [Erlang.array.«set/3», nonnegative, existing, boolAnd, andTT, andTF, andFT,
                    Erlang.erlang.«=:=/2», fixedTrue, shifted, fits, masked, same,
                    Erlang.erlang.«=/=/2», Erlang.erlang.«setelement/3», lo, bound, maxSize, pack, position]
                · obtain ⟨newTree, treeReturned, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp returned
                  obtain ⟨newCache, cacheReturned, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp rest
                  obtain ⟨updatedCache, cacheWrite, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp rest
                  obtain ⟨entries, rfl, lo, bound⟩ := replace _ _ _ _ cacheWrite
                  have position : 1 + (i + z) - (i + z - r) = 1 + (r : Int) := by omega
                  refine ⟨i, n, z, i + z - r, bits, fixed, default, newTree, entries, by omega, rfl,
                    by simp [Erlang.array.«size/1»], nonnegative, by omega, by omega, ?_⟩
                  intro replacement
                  simp [Erlang.array.«set/3», nonnegative, existing, boolAnd, andTT, andTF, andFT,
                    Erlang.erlang.«=:=/2», fixedTrue, shifted, fits, masked, same,
                    Erlang.erlang.«=/=/2», treeReturned, cacheReturned,
                    Erlang.erlang.«setelement/3», lo, bound, maxSize, pack, position]
              · obtain ⟨grown, grew, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp returned
                obtain ⟨grownTree, grownBits, rfl⟩ := growth _ _ _ _ grew
                simp at rest
                obtain ⟨newTree, treeReturned, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp rest
                obtain ⟨newCache, cacheReturned, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp rest
                obtain ⟨updatedCache, cacheWrite, rest⟩ := (Lynx.Result.bind_eq_ok _ _ _).mp rest
                obtain ⟨entries, rfl, lo, bound⟩ := replace _ _ _ _ cacheWrite
                have position : 1 + (i + z) - (i + z - r) = 1 + (r : Int) := by omega
                refine ⟨i, n, z, i + z - r, grownBits, fixed, default, newTree, entries, by omega, rfl,
                  by simp [Erlang.array.«size/1»], nonnegative, by omega, by omega, ?_⟩
                intro replacement
                simp [Erlang.array.«set/3», nonnegative, existing, boolAnd, andTT, andTF, andFT,
                  Erlang.erlang.«=:=/2», fixedTrue, shifted, fits, masked, grew,
                  treeReturned, cacheReturned, Erlang.erlang.«setelement/3», lo, bound, maxSize, pack, position]
          · simp at returned
        have success (computation : Lynx.Result)
            (valid : Lynx.Result.tryWith (computation >>= fun _ => .ok Lynx.Term.true)
              Lynx.Result.ok (fun _ => .ok Lynx.Term.false) = .ok Lynx.Term.true) :
            ∃ out, computation = .ok out := by
          cases computation <;>
            simp [Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind] at valid
          exact ⟨_, rfl⟩
        change Lynx.Result.tryWith
          (Erlang.array.«set/3» index first array >>= fun _ => .ok Lynx.Term.true)
          Lynx.Result.ok (fun _ => .ok Lynx.Term.false) = .ok Lynx.Term.true at requires
        obtain ⟨out, returned⟩ := success _ requires
        obtain ⟨i, n, z, ci, bits, fixed, default, tree, cache, valid,
          rfl, originalSize, nonnegative, lower, upper, writes⟩ := prepared _ _ _ _ returned
        have existing : i < max n (i + 1) := by omega
        have reads (v : Lynx.Term) := readCached i (max n (i + 1)) z ci bits
          fixed default tree v cache nonnegative existing lower upper valid
        have overwrites (v w : Lynx.Term) := overwriteCached i (max n (i + 1)) z ci bits
          fixed default tree v w cache nonnegative existing lower upper valid
        have sizes (v : Lynx.Term) :
            Erlang.array.«size/1» (pack (max n (i + 1)) z fixed default
              (cache.set ((1 + (i + z) - ci).toNat - 1) v) ci tree bits) =
                .ok (.integer (max n (i + 1))) := by
          simp [pack, Erlang.array.«size/1»]
        have maximum : Erlang.erlang.«max/2» (.integer n) (.integer (i + 1)) =
            .ok (.integer (max n (i + 1))) := by
          by_cases larger : i + 1 ≤ n
          · simp [Erlang.erlang.«max/2», Int.isGE_compare, larger, Int.max_eq_left larger]
          · simp [Erlang.erlang.«max/2», Int.isGE_compare, larger, Int.max_eq_right (by omega : n ≤ i + 1)]
        simp [«set_obeys_update_contract:ensures/4», «update_contract/4», writes,
          reads, sizes, overwrites, originalSize, maximum, Erlang.erlang.«=:=/2»]
      """
  end
end
