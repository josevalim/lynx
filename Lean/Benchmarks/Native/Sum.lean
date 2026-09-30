module

/-
defmodule Sum do
  def sum(list)
  def sum([]), do: 0
  def sum([x | xs]), do: x + sum(xs)

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
-/

import LynxTest.Bench

set_option Elab.async false

namespace LynxBench

def sum_1 : List Int → Int
  | [] => 0
  | x :: xs => x + sum_1 xs

/- law sum_append(l, r), expects: sum(l) + sum(r) == sum(l ++ r) -/
#bench "native/sum-append"
theorem native_sum_append (left right : List Int) :
    sum_1 left + sum_1 right = sum_1 (left ++ right) := by
  induction left <;> simp_all [sum_1, Int.add_assoc]

end LynxBench
