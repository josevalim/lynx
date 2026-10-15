# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/array.exs
# Prove the installed OTP array module, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1, ERTS 17.1.1).
# These proofs depend on implementation details; rerun after OTP upgrades.
ExUnit.start()

defmodule ArrayProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  # Capacity search and option parsing use fixed points. Each law below also
  # proves that its concrete constructor call returns successfully.
  laws "array" do
    termination_suffix :array.find_bits() / 2, ~LEAN"""
    partial_fixpoint monotonicity by
      intro f g h i s
      have addEq := Lynx.Result.ofExcept_toExcept
        (Erlang.erlang.«+/2» s (.integer 4)) (by simp)
      cases add : Lynx.Result.toExcept (Erlang.erlang.«+/2» s (.integer 4)) (by simp) with
      | error e =>
        simp [add] at addEq
        simp [← addEq, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind, Lynx.Result.ofExcept]
        exact Lean.Order.PartialOrder.rel_refl
      | ok value =>
        simp [add] at addEq
        have shiftEq := Lynx.Result.ofExcept_toExcept
          (Erlang.erlang.«bsl/2» (.integer 1) value) (by simp)
        cases shift : Lynx.Result.toExcept (Erlang.erlang.«bsl/2» (.integer 1) value) (by simp) with
        | error e =>
          simp [shift] at shiftEq
          simp [← addEq, ← shiftEq, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind, Lynx.Result.ofExcept]
          exact h _ _
        | ok bound =>
          simp [shift] at shiftEq
          simp [← addEq, ← shiftEq, Erlang.erlang.«</2», Lynx.Result.tryWith,
            Lynx.Result.handle, Lynx.Result.bind, Lynx.Result.ofExcept]
          split
          · exact Lean.Order.PartialOrder.rel_refl
          · exact h _ _
    """

    termination_suffix :array.new_1() / 4, ~LEAN"""
    partial_fixpoint monotonicity by
      intro f g h options size fixed default
      repeat' first
        | exact h _ _ _ _
        | exact Lean.Order.PartialOrder.rel_refl
        | simp [Erlang.erlang.«is_boolean/1», Erlang.erlang.«and/2»,
            Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind]
        | split
    """

    law new_metadata(default),
      expects:
        :array.is_array(:array.new(default: default)) and
          :array.size(:array.new(default: default)) === 0 and
          :array.default(:array.new(default: default)) === default,
      proof: ~LEAN"""
      have capacity : Erlang.array.«find_bits/2» (.integer (-1)) (.integer 0) =
          .ok (.integer 0) := by
        rw [Erlang.array.«find_bits/2».eq_def]
        simp [Erlang.erlang.«bsl/2», Int.shiftLeft_eq]
      have empty (d : Lynx.Term) :
          Erlang.array.«new_1/4» .nil (.integer 0) (.atom "false") d =
            .ok (.tuple #[.atom "array", .integer 0, .integer 0, (.atom "false"), d,
              .tuple (Array.replicate 16 d), .integer 0, .nil, .integer 0]) := by
        rw [Erlang.array.«new_1/4».eq_def]
        simp [Erlang.array.«new/3», capacity, Erlang.erlang.«make_tuple/2»]
      simp [«new_metadata:ensures/1», Erlang.array.«new/1», Erlang.array.«new_0/3»,
        Erlang.erlang.«is_list/1»]
      rw [Erlang.array.«new_1/4».eq_def]
      simp [empty, Erlang.array.«is_array/1», Erlang.array.«size/1», Erlang.array.«default/1», Erlang.erlang.«=:=/2»]
      """

    law default_option_precedence(first, last),
      expects: :array.new([{:default, first}, {:default, last}]) === :array.new(default: last),
      proof: ~LEAN"""
      have capacity : Erlang.array.«find_bits/2» (.integer (-1)) (.integer 0) =
          .ok (.integer 0) := by
        rw [Erlang.array.«find_bits/2».eq_def]
        simp [Erlang.erlang.«bsl/2», Int.shiftLeft_eq]
      have empty (d : Lynx.Term) :
          Erlang.array.«new_1/4» .nil (.integer 0) (.atom "false") d =
            .ok (.tuple #[.atom "array", .integer 0, .integer 0, (.atom "false"), d,
              .tuple (Array.replicate 16 d), .integer 0, .nil, .integer 0]) := by
        rw [Erlang.array.«new_1/4».eq_def]
        simp [Erlang.array.«new/3», capacity, Erlang.erlang.«make_tuple/2»]
      simp [«default_option_precedence:ensures/2», Erlang.array.«new/1»,
        Erlang.array.«new_0/3», Erlang.erlang.«is_list/1»]
      rw [Erlang.array.«new_1/4».eq_def]
      rw [Erlang.array.«new_1/4».eq_def]
      simp [empty, Erlang.erlang.«=:=/2»]
      rw [Erlang.array.«new_1/4».eq_def]
      simp [empty, Erlang.erlang.«=:=/2»]
      """
  end
end
