# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/gb_trees.exs
# Prove the installed OTP implementation, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1).
# These proofs depend on implementation details; rerun after OTP upgrades.
ExUnit.start()

defmodule GbTreesProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp nodes(nil), do: 0
  defp nodes({_key, _value, left, right}), do: 1 + nodes(left) + nodes(right)

  defp ordered([]), do: true
  defp ordered([_]), do: true
  defp ordered([{a, _}, {b, _} = right | tail]), do: a < b and ordered([right | tail])

  # Check the actual node count and strict arithmetic key order, including skewed trees.
  def valid_tree({count, root} = tree),
    do:
      is_integer(count) and count >= 0 and count == nodes(root) and
        ordered(:gb_trees.to_list(tree))

  def balance_contract(tree, key) do
    balanced = :gb_trees.balance(tree)

    :gb_trees.to_list(balanced) === :gb_trees.to_list(tree) and
      :gb_trees.lookup(key, balanced) === :gb_trees.lookup(key, tree) and
      :gb_trees.size(balanced) === :gb_trees.size(tree)
  end

  laws "balance preserves tree observations" do
    termination_suffix &:gb_trees.balance_list_unchecked_1/2, ~LEAN"""
    termination_by match _1 with | .integer n => n.toNat | _ => 0
    decreasing_by
      all_goals
        rename_i passed
        have divisionShape (input output : Lynx.Term)
            (returned : Erlang.erlang.«div/2» input (.integer 2) = .ok output) :
            ∃ value : Int, input = .integer value ∧ output = .integer (value.tdiv 2) := by
          cases input <;> simp [Erlang.erlang.«div/2»] at returned
          rename_i value
          exact ⟨value, rfl, returned.symm⟩
        obtain ⟨sm, smaller, half⟩ := divisionShape vSm.val vS2.val vS2.property
        have source : vS = .integer (sm+1) :=
          (Erlang.erlang.«-/2_integer_result» vS 1 sm).mp (by
            simpa only [smaller] using vSm.property)
        have positive : 0 < sm := by
          simp [source, Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
            Int.compare_eq_gt] at passed
          by_cases h : 1 < sm+1
          · omega
          · simp [h, Lynx.Result.guardPassed] at passed
        first
        | have next : vS1.val = .integer (sm - sm.tdiv 2) := by
            have returned := vS1.property
            simpa only [smaller, half, Erlang.erlang.«-/2_integers»,
              Lynx.Result.ok.injEq] using returned.symm
          simp only [source, next]
          simp [Int.tdiv_eq_ediv_of_nonneg (Int.le_of_lt positive)]
          omega
        | simp only [source, half]
          simp [Int.tdiv_eq_ediv_of_nonneg (Int.le_of_lt positive)]
          omega
    """

    law balance_preserves_observations(tree, key),
      requires: valid_tree(tree),
      expects: balance_contract(tree, key),
      proof: ~LEAN"""
      let pair (entry : Lynx.Term × Lynx.Term) : Lynx.Term := .tuple ⟨[entry.1, entry.2]⟩
      let encode (xs : List (Lynx.Term × Lynx.Term)) (tail : Lynx.Term := .nil) : Lynx.Term :=
        xs.foldr (fun entry rest => .cons (pair entry) rest) tail
      let less (left right : Lynx.Term × Lynx.Term) := Lynx.Term.compare left.1 right.1 = .lt
      let search (query : Lynx.Term) (xs : List (Lynx.Term × Lynx.Term)) : Lynx.Term :=
        xs.foldr (fun (key, value) rest => match Lynx.Term.compare query key with
          | .lt => .atom "none"
          | .eq => .tuple #[.atom "value", value]
          | .gt => rest) (.atom "none")
      have skipPrefix (query : Lynx.Term) (xs ys : List (Lynx.Term × Lynx.Term))
          (above : ∀ entry ∈ xs, Lynx.Term.compare query entry.1 = .gt) :
          search query (xs ++ ys) = search query ys := by
        induction xs with
        | nil => rfl
        | cons entry xs ih =>
          rcases entry with ⟨key, value⟩
          simp only [List.cons_append, search, List.foldr_cons, above (key, value) (by simp)]
          exact ih (fun entry member => above entry (by simp [member]))
      have emptySuffix (query : Lynx.Term) (xs ys : List (Lynx.Term × Lynx.Term))
          (empty : search query ys = .atom "none") :
          search query (xs ++ ys) = search query xs := by
        simp only [search, List.foldr_append] at empty ⊢
        rw [empty]
      let spec (root : Lynx.Term) (xs : List (Lynx.Term × Lynx.Term)) : Prop :=
        «nodes/1» root = .ok (.integer xs.length) ∧
        (∀ tail, Erlang.gb_trees.«to_list/2» root tail = .ok (encode xs tail)) ∧
        (∀ query, xs.Pairwise less →
          Erlang.gb_trees.«lookup_1/2» query root = .ok (search query xs))
      have emptySpec : spec (.atom "nil") [] := by
        refine ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
      have nodeSpec (key value left right : Lynx.Term) (xs ys : List (Lynx.Term × Lynx.Term))
          (leftSpec : spec left xs) (rightSpec : spec right ys) :
          spec (.tuple ⟨[key, value, left, right]⟩) (xs ++ (key, value) :: ys) := by
        rcases leftSpec with ⟨leftCount, leftList, leftLookup⟩
        rcases rightSpec with ⟨rightCount, rightList, rightLookup⟩
        refine ⟨?_, ?_, ?_⟩
        · simp [«nodes/1», leftCount, rightCount, Int.natCast_add,
            Int.add_left_comm, Int.add_comm]
        · intro tail
          simp [Erlang.gb_trees.«to_list/2», rightList, leftList, encode, pair]
        · intro query sorted
          simp only [List.pairwise_append, List.pairwise_cons] at sorted
          have leftBound (entry : Lynx.Term × Lynx.Term) (member : entry ∈ xs) :
              Lynx.Term.compare entry.1 key = .lt :=
            sorted.2.2 entry member (key, value) (by simp)
          cases comparison : Lynx.Term.compare query key with
          | lt =>
            have empty : search query ((key, value) :: ys) = .atom "none" := by
              simp only [search, List.foldr_cons, comparison]
            have same := emptySuffix query xs ((key, value) :: ys) empty
            rw [same]
            simp [Erlang.gb_trees.«lookup_1/2», Erlang.erlang.«</2»,
              comparison, leftLookup query sorted.1]
          | eq =>
            have past := skipPrefix query xs ((key, value) :: ys) (fun entry member =>
              Std.TransCmp.gt_of_eq_of_gt comparison
                (Std.OrientedCmp.gt_of_lt (leftBound entry member)))
            rw [past]
            simp [Erlang.gb_trees.«lookup_1/2», Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              comparison, search]
          | gt =>
            have past := skipPrefix query xs ((key, value) :: ys) (fun entry member =>
              Std.TransCmp.gt_trans comparison
                (Std.OrientedCmp.gt_of_lt (leftBound entry member)))
            rw [past]
            simp [Erlang.gb_trees.«lookup_1/2», Erlang.erlang.«</2», Erlang.erlang.«>/2»,
              comparison, search, rightLookup query sorted.2.1.2]
      have pureCases (computation : Lynx.Result) (pure : computation.IsPure) :
          (∃ value, computation = .ok value) ∨ (∃ exception, computation = .error exception) := by
        cases computation <;> simp_all [Lynx.Result.IsPure]
      have flatten (root output : Lynx.Term) (returned : «nodes/1» root = .ok output) :
          ∃ xs : List (Lynx.Term × Lynx.Term), spec root xs := by
        induction root using «nodes/1».induct generalizing output with
        | case1 => exact ⟨[], emptySpec⟩
        | case2 key value left right ihl ihr =>
          rcases pureCases («nodes/1» left) («nodes/1_pure» left) with leftOk | leftError
          · obtain ⟨leftValue, leftOk⟩ := leftOk
            obtain ⟨xs, leftSpec⟩ := ihl leftValue leftOk
            rcases pureCases («nodes/1» right) («nodes/1_pure» right) with rightOk | rightError
            · obtain ⟨rightValue, rightOk⟩ := rightOk
              obtain ⟨ys, rightSpec⟩ := ihr rightValue rightOk
              exact ⟨xs ++ (key, value) :: ys, nodeSpec key value left right xs ys leftSpec rightSpec⟩
            · obtain ⟨error, rightError⟩ := rightError
              simp [«nodes/1», leftSpec.1, rightError] at returned
          · obtain ⟨error, leftError⟩ := leftError
            simp [«nodes/1», leftError] at returned
        | case3 root notNil notNode => simp_all [«nodes/1»]
      have greater (a b : Int) : Erlang.erlang.«>/2» (.integer a) (.integer b) =
          .ok (if b < a then Lynx.Term.true else Lynx.Term.false) := by
        simp [Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt]
      -- Rebuilding consumes exactly n pairs and leaves an arbitrary suffix untouched.
      have build (n : Nat) (xs tail : List (Lynx.Term × Lynx.Term)) (length : xs.length = n) :
          ∃ root : Lynx.Term,
            Erlang.gb_trees.«balance_list_unchecked_1/2» (encode (xs ++ tail)) (.integer n) =
              .ok (.tuple #[root, encode tail]) ∧ spec root xs := by
        induction n using Nat.strongRecOn generalizing xs tail with
        | ind n ih =>
          by_cases zero : n = 0
          · cases zero
            have empty : xs = [] := List.eq_nil_iff_length_eq_zero.mpr length
            subst xs
            exact ⟨.atom "nil", by simp [Erlang.gb_trees.«balance_list_unchecked_1/2», greater], emptySpec⟩
          · by_cases one : n = 1
            · cases one
              cases xs with
              | nil => simp at length
              | cons entry xs =>
                have empty : xs = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using length)
                subst xs
                rcases entry with ⟨key, value⟩
                refine ⟨.tuple ⟨[key, value, .atom "nil", .atom "nil"]⟩, ?_, ?_⟩
                · simp [Erlang.gb_trees.«balance_list_unchecked_1/2», greater, encode, pair]
                · exact nodeSpec key value (.atom "nil") (.atom "nil") [] [] emptySpec emptySpec
            · let rn := (n-1)/2
              let ln := n-1-rn
              have rightSmall : rn < n := by dsimp [rn]; omega
              have leftSmall : ln < n := by dsimp [ln, rn]; omega
              have counts : ln+1+rn = n := by dsimp [ln, rn]; omega
              have leftLength : (xs.take ln).length = ln := by simp only [List.length_take]; omega
              have restLength : (xs.drop ln).length = rn+1 := by simp only [List.length_drop]; omega
              cases rest : xs.drop ln with
              | nil => simp [rest] at restLength
              | cons entry restXs =>
                rcases entry with ⟨key, value⟩
                have rightLength : restXs.length = rn := by simp [rest] at restLength; omega
                have joined : xs = xs.take ln ++ (key, value) :: restXs := by
                  rw [← rest, List.take_append_drop]
                obtain ⟨left, leftReturned, leftSpec⟩ := ih ln leftSmall (xs.take ln)
                  (((key, value) :: restXs) ++ tail) leftLength
                obtain ⟨right, rightReturned, rightSpec⟩ := ih rn rightSmall restXs tail rightLength
                refine ⟨.tuple ⟨[key, value, left, right]⟩, ?_, ?_⟩
                · have divided : Erlang.erlang.«div/2» (.integer ((n : Int)-1)) (.integer 2) =
                      .ok (.integer rn) := by
                    have pred : (n : Int)-1 = ↑(n-1) := by omega
                    rw [pred]
                    rfl
                  have subtracted : (n : Int)-1-(rn : Int) = ln := by omega
                  rw [Erlang.gb_trees.«balance_list_unchecked_1/2».eq_def]
                  have positive : (1 : Int) < n := by omega
                  have input : encode (xs ++ tail) =
                      encode (xs.take ln ++ (((key, value) :: restXs) ++ tail)) := by
                    rw [← List.append_assoc, ← joined]
                  simp only [greater, positive, if_true, Lynx.Result.guard_eq, Lynx.Result.tryWith_ok,
                    Lynx.Term.true, Erlang.erlang.«-/2_integers», Lynx.Result.ok_bind, divided, subtracted,
                    input, leftReturned]
                  simp only [encode, List.foldr_cons, pair, List.cons_append] at rightReturned ⊢
                  simp only [rightReturned, Lynx.Result.ok_bind]
                  rfl
                · rw [joined]
                  exact nodeSpec key value left right (xs.take ln) restXs leftSpec rightSpec
      have pairwiseStep (entry next : Lynx.Term × Lynx.Term) (tail : List (Lynx.Term × Lynx.Term)) :
          ((entry :: next :: tail).Pairwise less) ↔
            less entry next ∧ (next :: tail).Pairwise less := by
        constructor
        · intro sorted
          exact ⟨(List.pairwise_cons.mp sorted).1 next (by simp),
            (List.pairwise_cons.mp sorted).2⟩
        · rintro ⟨first, rest⟩
          apply List.pairwise_cons.mpr
          refine ⟨?_, rest⟩
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact Std.TransCmp.lt_trans first ((List.pairwise_cons.mp rest).1 item member)
      have orderedModel (xs : List (Lynx.Term × Lynx.Term)) :
          «ordered/1» (encode xs) = .ok (if xs.Pairwise less then Lynx.Term.true else Lynx.Term.false) := by
        induction xs with
        | nil => simp [«ordered/1», encode]
        | cons entry xs ih =>
          rcases entry with ⟨key, value⟩
          cases xs with
          | nil => simp [«ordered/1», encode]
          | cons next tail =>
            rcases next with ⟨nextKey, nextValue⟩
            simp only [encode, List.foldr_cons, pair] at ih
            by_cases first : Lynx.Term.compare key nextKey = .lt <;>
              by_cases rest : ((nextKey, nextValue) :: tail).Pairwise less <;>
              simp [«ordered/1», encode, pair, Erlang.erlang.«</2»,
                Ordering.isLT_iff_eq_lt, first, rest, ih, pairwiseStep, less]
      cases tree <;> simp [«balance_preserves_observations:requires/2», «valid_tree/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [«valid_tree/1»] at requires
      | [count, root] =>
        cases count <;> simp [Erlang.erlang.«is_integer/1»] at requires
        rename_i count
        have nonnegative : 0 ≤ count := by
          by_cases h : 0 ≤ count <;> simp [h] at requires <;> omega
        simp only [nonnegative, if_true, Lynx.Result.ok_bind] at requires
        rcases pureCases («nodes/1» root) («nodes/1_pure» root) with returned | failed
        · obtain ⟨output, returned⟩ := returned
          obtain ⟨xs, original⟩ := flatten root output returned
          have countEq : count = xs.length := by
            by_cases h : count = xs.length
            · exact h
            · simp [original.1, Erlang.erlang.«==/2», h] at requires
          cases countEq
          have sorted : xs.Pairwise less := by
            by_cases h : xs.Pairwise less
            · exact h
            · simp [original.1, Erlang.erlang.«==/2»,
                Erlang.gb_trees.«to_list/1», original.2.1, orderedModel, h] at requires
          obtain ⟨balanced, rebuilt, balancedSpec⟩ := build xs.length xs [] rfl
          simp only [List.append_nil] at rebuilt
          have balancedReturned : Erlang.gb_trees.«balance/1» (.tuple ⟨[.integer xs.length, root]⟩) =
              .ok (.tuple #[.integer xs.length, balanced]) := by
            simp [Erlang.gb_trees.«balance/1», Erlang.gb_trees.«balance/2»,
              Erlang.gb_trees.«to_list_1/1», original.2.1,
              Erlang.gb_trees.«balance_list_unchecked/2», rebuilt, Erlang.erlang.«and/2»,
              show encode [] = .nil from rfl]
          simp [«balance_preserves_observations:ensures/2», «balance_contract/2»,
            balancedReturned, Erlang.gb_trees.«to_list/1», original.2.1, balancedSpec.2.1,
            Erlang.gb_trees.«lookup/2», original.2.2 key sorted, balancedSpec.2.2 key sorted,
            Erlang.gb_trees.«size/1», Erlang.erlang.«and/2», Erlang.erlang.«=:=/2»]
        · obtain ⟨error, failed⟩ := failed
          simp [failed] at requires
      """
  end
end
