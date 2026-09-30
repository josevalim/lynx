module

/-
defmodule SetUnion do
  # A set is a map whose values are all [].
  defp is_set(value), do: is_map(value, fn _, v -> v == [] end)

  def union(left, right), do: :maps.merge(left, right)
end
-/

import LynxTest.Bench

namespace LynxBench.Sets
set_option Elab.async false

/-- Native maps retain the `[]` marker and can also contain non-set bindings.
Integer keys and list values use native Lean types, without Term or Result. -/
abbrev SetMap := Std.ExtTreeMap Int (List Int) compare

def union_2 (left right : SetMap) : SetMap := left ∪ right

def isSet (input : SetMap) : Bool := input.toList.all (fun (_, v) => v.isEmpty)

/-- The same binding invariant as the translated executable expectation. -/
@[simp] theorem isSet_iff (input : SetMap) :
    isSet input = true ↔ ∀ (k : Int) v, input[k]? = some v → v = [] := by
  simp only [isSet, List.all_eq_true, List.isEmpty_iff]
  constructor
  · intro h k v hv
    exact h (k,v) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hv)
  · intro h ⟨k,v⟩ hv
    exact h k v (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hv)

/- law union_result(left, right), requires: is_set(left) and is_set(right),
     expects: (result -> is_set(result)) -/
#bench "native/sets-union-result"
theorem union_result (a b : SetMap)
    (ha : isSet a = true) (hb : isSet b = true) :
    isSet (union_2 a b) = true := by
  rw [isSet_iff]
  intro k v hv
  rw [union_2, Std.ExtTreeMap.getElem?_union] at hv
  cases hk : b[k]? with
  | none => exact (isSet_iff a).mp ha k v (by simpa [hk] using hv)
  | some w =>
    have : w = v := by simpa [hk] using hv
    subst w
    exact (isSet_iff b).mp hb k v hk

/- law union_commutative(left, right), requires: is_set(left) and is_set(right),
     expects: union(left, right) == union(right, left) -/
#bench "native/sets-union-commutative"
theorem union_commutative (a b : SetMap)
    (ha : isSet a = true) (hb : isSet b = true) :
    union_2 a b = union_2 b a := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [union_2, Std.ExtTreeMap.getElem?_union]
  cases ea : a[k]? <;> cases eb : b[k]? <;> simp_all
  exact (hb _ _ eb).trans (ha _ _ ea).symm

/- law union_empty(set), requires: is_set(set), expects: union(set, %{}) == set -/
#bench "native/sets-union-empty"
theorem union_empty (input : SetMap) (_valid : isSet input = true) :
    union_2 input ∅ = input := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp [union_2, Std.ExtTreeMap.getElem?_union]

open Lean in
run_cmd do
  for name in #[``union_result, ``union_commutative, ``union_empty] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"

end LynxBench.Sets
