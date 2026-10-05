# LYNX_PROFILE=1 mix run examples/sum.exs
ExUnit.start()

defmodule SumProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def sum([]), do: 0
  def sum([x | xs]), do: x + sum(xs)

  laws "sum" do
    law sum_empty,
      expects: sum([]) == 0,
      proof: ~LEAN"""
      simp [«sum_empty:ensures/0», «sum/1», Erlang.erlang.«==/2»]
      """

    law sum_append(l, r),
      requires: is_integer_list(l) and is_integer_list(r),
      expects: sum(l) + sum(r) == sum(l ++ r),
      proof: ~LEAN"""
      have sums (input : Lynx.Term)
          (valid : «is_integer_list/1» input = .ok Lynx.Term.true) :
          ∃ value, «sum/1» input = .ok (.integer value) ∧
            ∀ right total, «sum/1» right = .ok (.integer total) →
              ∃ joined, Erlang.erlang.«++/2» input right = .ok joined ∧
                «sum/1» joined = .ok (.integer (value + total)) := by
        induction input using «sum/1».induct with
        | case1 => exact ⟨0, rfl, fun right total returned => ⟨right, rfl, by simpa using returned⟩⟩
        | case2 head tail ih =>
          cases head <;> simp [«is_integer_list/1», Erlang.erlang.«is_integer/1»] at valid
          rename_i value
          obtain ⟨subtotal, returned, append⟩ := ih valid
          refine ⟨value + subtotal, by simp [«sum/1», returned], ?_⟩
          intro right total rightReturned
          obtain ⟨joined, appended, combined⟩ := append right total rightReturned
          exact ⟨.cons (.integer value) joined, by simp [Erlang.erlang.«++/2», appended],
            by simp [«sum/1», combined, Int.add_assoc]⟩
        | case3 input notNil notCons => simp_all [«is_integer_list/1»]
      have validity : «is_integer_list/1» l = .ok Lynx.Term.true ∧
          «is_integer_list/1» r = .ok Lynx.Term.true := by
        cases left : «is_integer_list/1» l <;> simp [«sum_append:requires/2», left] at requires
        split at requires <;> simp_all [Lynx.Term.true]
      obtain ⟨leftSum, leftReturned, append⟩ := sums l validity.1
      obtain ⟨rightSum, rightReturned, _⟩ := sums r validity.2
      obtain ⟨joined, appended, combined⟩ := append r rightSum rightReturned
      simp [«sum_append:ensures/2», leftReturned, rightReturned, appended, combined,
        Erlang.erlang.«==/2»]
      """
  end

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
