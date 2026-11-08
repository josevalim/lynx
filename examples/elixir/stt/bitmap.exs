# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/stt/bitmap.exs
# Prove set operations on bitmap types of Elixir's type system.
# Checked against Elixir 1.21.0-dev (1323fce0d), Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/module/types/descr.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule STTBitmapProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case
  import Bitwise, only: [&&&: 2]
  alias Module.Types.Descr

  # A bitmap type, such as integer() or binary(), is a non-empty set of bits.
  def bitmap?(bits), do: is_integer(bits) and bits >= 1 and bits <= 255

  laws "bitmap" do
    # Elixir's default map field access falls back to a remote call on non-maps.
    cutoff &:elixir_erl_pass.no_parens_remote/2

    # Enum reaches the Enumerable protocol, but descr only enumerates lists.
    cutoff &Enumerable.reduce/3
    cutoff &Enumerable.count/1
    cutoff &Enumerable.member?/2
    cutoff &Enumerable.slice/1
    cutoff &Enumerable.impl_for/1

    # Errors and warnings are only formatted on unreachable paths.
    cutoff &Kernel.inspect/2
    cutoff &IO.warn/1
    cutoff &String.Chars.to_string/1
    cutoff &ArgumentError.exception/1

    # Descr only uses version 2 sets, which are maps.
    cutoff &:sets.get_slot/2
    cutoff &:sets.get_bucket/2
    cutoff &:sets.fold_set/3
    cutoff &:sets.filter_set/2
    cutoff &:sets.maybe_expand/1
    cutoff &:sets.maybe_contract/2
    cutoff &:sets.mk_seg/1

    termination_suffix &:lists.seq_loop/4, ~LEAN"partial_fixpoint"
    termination_suffix &:orddict.merge/3, ~LEAN"partial_fixpoint"
    termination_suffix &:sets.fold_1/3, ~LEAN"partial_fixpoint"
    termination_suffix &:sets.intersection_decided/3, ~LEAN"partial_fixpoint"
    termination_suffix &:sets.intersection_heuristic/6, ~LEAN"partial_fixpoint"
    termination_suffix &:sets.subtract_decided/3, ~LEAN"partial_fixpoint"
    termination_suffix &:sets.subtract_heuristic/6, ~LEAN"partial_fixpoint"
    termination_suffix &Enum.map_range/4, ~LEAN"partial_fixpoint"
    termination_suffix &Enum.predicate_range/5, ~LEAN"partial_fixpoint"
    termination_suffix &Enum.reduce_range/5, ~LEAN"partial_fixpoint"
    termination_suffix &Enum.take_every_list/3, ~LEAN"partial_fixpoint"
    termination_suffix &List.duplicate/3, ~LEAN"partial_fixpoint"

    # Recursive types are unfolded on demand, so descr's recursion is partial.
    termination_suffix &Descr.unfold/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_seen?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_difference_subtype?/3, ~LEAN"partial_fixpoint"
    termination_suffix &Descr.iterator_empty_difference_subtype?/3, ~LEAN"partial_fixpoint"
    termination_suffix &Descr.fun_line_empty?/3, ~LEAN"partial_fixpoint"
    termination_suffix &Descr.fields_merge_with_defaults/5, ~LEAN"partial_fixpoint"
    termination_suffix &Descr.bdd_union/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_difference/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_intersection/2, ~LEAN"partial_fixpoint", recur: true

    # Map iteration recurses on the iterator that maps:next/1 returns.
    termination_suffix &Descr.iterator_merge/3, ~LEAN"partial_fixpoint"
    termination_suffix &Descr.iterator_intersection/4, ~LEAN"partial_fixpoint"
    termination_suffix &Descr.iterator_dynamic_difference/3, ~LEAN"partial_fixpoint"

    law union_nonempty(left, right),
      requires: bitmap?(left) and bitmap?(right),
      expects: not Descr.empty?(Descr.bare_union(%{bitmap: left}, %{bitmap: right})),
      proof: ~LEAN"""
      simp only [«union_nonempty:requires/2», «bitmap?/1», Lynx.Except.andAlso_eq_true] at requires
      cases left <;> simp [Erlang.erlang.«is_integer/1»] at requires
      cases right <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ x)
      obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ y)
      simp only [Lynx.apply_eq, «union_nonempty:ensures/2»]
      unfold Elixir.Module.Types.Descr.«bare_union/2»
      simp [Lynx.Term.getMapKeys, Erlang.erlang.«==/2»]
      unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
      simp [Erlang.erlang.«map_size/1», Erlang.erlang.«>/2», Erlang.maps.«iterator/1», Erlang.maps.«next/1»]
      rw [Elixir.Module.Types.Descr.«iterator_merge/3».eq_def]
      simp [Lynx.Term.getMapKeys, Erlang.program.fun_table_pure_1, Erlang.erlang.«is_map/1»,
        Erlang.maps.«update/3», Erlang.maps.«next/1»]
      unfold Elixir.Module.Types.Descr.«bare_union/3»
      simp [Erlang.erlang.«bor/2»]
      rw [Elixir.Module.Types.Descr.«iterator_merge/3».eq_def]
      simp
      unfold Elixir.Module.Types.Descr.«empty?/1»
      dsimp only
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
      simp [Lynx.Term.getMapKeys, Erlang.erlang.«==/2», Erlang.erlang.«is_map_key/2», Erlang.erlang.«not/1»]
      """

    law intersection_empty(left, right),
      requires: bitmap?(left) and bitmap?(right),
      expects:
        Descr.empty?(Descr.bare_intersection(%{bitmap: left}, %{bitmap: right})) ==
          ((left &&& right) == 0),
      proof: ~LEAN"""
      simp only [«intersection_empty:requires/2», «bitmap?/1», Lynx.Except.andAlso_eq_true] at requires
      cases left <;> simp [Erlang.erlang.«is_integer/1»] at requires
      cases right <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ x)
      obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ y)
      simp only [Lynx.apply_eq, «intersection_empty:ensures/2»]
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»
      simp [Lynx.Term.getMapKeys, Erlang.erlang.«==/2»]
      unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
      simp [Erlang.erlang.«map_size/1», Erlang.erlang.«>/2», Erlang.maps.«iterator/1», Erlang.maps.«next/1»]
      rw [Elixir.Module.Types.Descr.«iterator_intersection/4».eq_def]
      simp [Lynx.Term.getMapKeys, Erlang.program.fun_table_pure_12]
      unfold Elixir.Module.Types.Descr.«bare_intersection/3»
      simp [Erlang.erlang.«band/2»]
      by_cases disjoint : x &&& y = 0 <;> simp [disjoint, Erlang.maps.«next/1»]
      all_goals
        rw [Elixir.Module.Types.Descr.«iterator_intersection/4».eq_def]
        simp [Erlang.maps.«from_list/1», Lynx.Term.pairList?]
        unfold Elixir.Module.Types.Descr.«empty?/1»
        try dsimp only
        rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
        simp [Lynx.Term.getMapKeys, Erlang.erlang.«==/2», Erlang.erlang.«is_map_key/2»,
          Erlang.erlang.«not/1», disjoint]
      """

    law difference_empty(left, right),
      requires: bitmap?(left) and bitmap?(right),
      expects:
        Descr.empty?(Descr.bare_difference(%{bitmap: left}, %{bitmap: right})) ==
          ((left &&& right) == left),
      proof: ~LEAN"""
      simp only [«difference_empty:requires/2», «bitmap?/1», Lynx.Except.andAlso_eq_true] at requires
      cases left <;> simp [Erlang.erlang.«is_integer/1»] at requires
      cases right <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i x y
      obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ x)
      obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ y)
      have unfolded (d : Lynx.Dispatcher) (entries : List (Lynx.Term × Lynx.Term)) :
          Elixir.Module.Types.Descr.«unfold/1» d (.map entries) = .ok (.map entries) := by
        rw [Elixir.Module.Types.Descr.«unfold/1».eq_def]; rfl
      simp only [Lynx.apply_eq, «difference_empty:ensures/2»]
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Lynx.Term.getMapKeys, Erlang.erlang.«==/2», Erlang.erlang.«is_map_key/2», unfolded]
      unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
      simp [Erlang.erlang.«==/2», unfolded, Erlang.maps.«iterator/1», Erlang.maps.«next/1»]
      rw [Elixir.Module.Types.Descr.«iterator_dynamic_difference/3».eq_def]
      simp [Lynx.Term.getMapKeys, Erlang.program.fun_table_pure_13]
      unfold Elixir.Module.Types.Descr.«bare_difference/3»
      simp [Erlang.erlang.«band/2»]
      have within : x &&& y ≤ x := Nat.and_le_left
      by_cases covered : x &&& y = x
      · simp [covered, Erlang.maps.«remove/2», Erlang.maps.«next/1»]
        rw [Elixir.Module.Types.Descr.«iterator_dynamic_difference/3».eq_def]
        simp
        unfold Elixir.Module.Types.Descr.«empty?/1»
        try dsimp only
        rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
        simp [Lynx.Term.getMapKeys, Erlang.erlang.«==/2», Int.natCast_inj, covered]
      · have remains : (x : Int) - (x &&& y : Nat) ≠ 0 := by omega
        simp [covered, remains, Erlang.erlang.«is_map/1», Erlang.maps.«update/3», Erlang.maps.«next/1»]
        rw [Elixir.Module.Types.Descr.«iterator_dynamic_difference/3».eq_def]
        simp
        unfold Elixir.Module.Types.Descr.«empty?/1»
        try dsimp only
        rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
        simp [Lynx.Term.getMapKeys, Erlang.erlang.«==/2», Erlang.erlang.«is_map_key/2»,
          Erlang.erlang.«not/1», Int.natCast_inj, covered]
      """
  end
end
