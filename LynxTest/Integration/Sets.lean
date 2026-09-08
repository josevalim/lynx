/-
defmodule SetUnion do
  # A set is a map whose values are all [].
  defp is_set(value), do: is_map(value, fn _, v -> v == [] end)

  expects is_set(left) and is_set(right)
  ensures (result -> is_set(result))
  property union(left, right) == union(right, left)
  property union(set, %{}) == set
  def union(left, right), do: :maps.merge(left, right)
end
-/
import LynxTest.Bench

namespace LynxTest.Integration.Sets
open Lynx Lynx.Modules
set_option Elab.async false

/-- Translation of the map-backed set union. -/
def union_2 (left right : Term) : Result := Maps.merge_2 left right

/-- Translated `is_map(value, fn _, v -> v == [] end)`. -/
def setExpects (input : Term) : Result :=
  Extensions.is_map_2 input (fun _ value => Erlang.equal_2 value .nil)

def unionExpects (args : Term × Term) : Result :=
  Erlang.andalso_2 (setExpects args.1) (fun _ => setExpects args.2)

def unionEnsures (_args : Term × Term) (result : Term) : Result := setExpects result

/-- Translated `union(left, right) == union(right, left)`. -/
def unionCommutative (args : Term × Term) : Result := do
  let leftRight ← union_2 args.1 args.2
  let rightLeft ← union_2 args.2 args.1
  Erlang.equal_2 leftRight rightLeft

/-- Translated `union(set, %{}) == set`. -/
def unionEmpty (input : Term) : Result := do
  let result ← union_2 input Term.empty_map
  Erlang.equal_2 result input

#bench "erlang/sets-union-contract"
theorem union_satisfies_contract :
    Satisfies (fun args => union_2 args.1 args.2) unionExpects unionEnsures := by
  lynx_verify

#bench "erlang/sets-union-commutative"
theorem union_commutative : Property unionExpects unionCommutative := by
  lynx_verify

#bench "erlang/sets-union-empty"
theorem union_empty : Property setExpects unionEmpty := by
  lynx_verify

end LynxTest.Integration.Sets
