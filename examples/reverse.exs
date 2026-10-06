# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/reverse.exs
ExUnit.start()

defmodule ReverseProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def reverse([], acc), do: acc
  def reverse([head | tail], acc), do: reverse(tail, [head | acc])

  laws "reverse" do
    law reverse_empty(acc),
      expects: reverse([], acc) === acc,
      proof: ~LEAN"""
      simp [«reverse_empty:ensures/1», «reverse/2», Erlang.erlang.«=:=/2»]
      """

    law reverse_list(list, acc),
      requires: proper_list(list) and proper_list(acc),
      expects: proper_list(reverse(list, acc)),
      proof: ~LEAN"""
      have reverses (input acc : Lynx.Term)
          (valid : «proper_list/1» input = .ok Lynx.Term.true)
          (accValid : «proper_list/1» acc = .ok Lynx.Term.true) :
          ∃ output, «reverse/2» input acc = .ok output ∧
            «proper_list/1» output = .ok Lynx.Term.true := by
        induction input, acc using «reverse/2».induct with
        | case1 acc => exact ⟨acc, rfl, accValid⟩
        | case2 head tail acc ih =>
          simp [«proper_list/1»] at valid
          obtain ⟨output, returned, proper⟩ := ih valid (by simp [«proper_list/1», accValid])
          exact ⟨output, by simpa [«reverse/2»] using returned, proper⟩
        | case3 input acc notNil notCons => simp_all [«proper_list/1»]
      have validity : «proper_list/1» list = .ok Lynx.Term.true ∧
          «proper_list/1» acc = .ok Lynx.Term.true := by
        cases left : «proper_list/1» list <;> simp [«reverse_list:requires/2», left] at requires
        split at requires <;> simp_all [Lynx.Term.true]
      obtain ⟨output, returned, proper⟩ := reverses list acc validity.1 validity.2
      simp [«reverse_list:ensures/2», returned, proper]
      """
  end

  defp proper_list([]), do: true
  defp proper_list([_ | tail]), do: proper_list(tail)
  defp proper_list(_), do: false
end
