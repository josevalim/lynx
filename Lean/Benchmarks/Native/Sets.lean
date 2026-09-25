import LynxTest.Bench

namespace LynxBench.Sets
set_option Elab.async false

/-- Native maps retain the `[]` marker and can also contain non-set bindings.
Integer keys and list values use native Lean types, without Term or Result. -/
abbrev SetMap := Std.ExtTreeMap Int (List Int) compare

def union_2 (left right : SetMap) : SetMap := left ∪ right

def setExpects (input : SetMap) : Bool := input.toList.all (fun (_, v) => v.isEmpty)

def unionExpects (args : SetMap × SetMap) : Bool := setExpects args.1 && setExpects args.2

def unionEnsures (_args : SetMap × SetMap) (result : SetMap) : Bool := setExpects result

def unionCommutative (args : SetMap × SetMap) : Prop :=
  union_2 args.1 args.2 = union_2 args.2 args.1

def unionEmpty (input : SetMap) : Prop := union_2 input ∅ = input

/-- The same binding invariant as the translated executable expectation. -/
@[simp] theorem setExpects_iff (input : SetMap) :
    setExpects input = true ↔ ∀ (k : Int) v, input[k]? = some v → v = [] := by
  simp only [setExpects, List.all_eq_true, List.isEmpty_iff]
  constructor
  · intro h k v hv
    exact h (k,v) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hv)
  · intro h ⟨k,v⟩ hv
    exact h k v (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hv)

#bench "native/sets-union-contract"
theorem union_satisfies_contract :
    (∃ args, unionExpects args = true) ∧
      ∀ args, unionExpects args = true →
        ∃ result, union_2 args.1 args.2 = result ∧ unionEnsures args result = true := by
  constructor
  · exact ⟨(∅, ∅), rfl⟩
  · intro ⟨a,b⟩ h
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    refine ⟨a ∪ b, rfl, ?_⟩
    rw [unionEnsures, setExpects_iff]
    intro k v hv
    rw [Std.ExtTreeMap.getElem?_union] at hv
    cases hk : b[k]? with
    | none => exact (setExpects_iff a).mp ha k v (by simpa [hk] using hv)
    | some w =>
      have : w = v := by simpa [hk] using hv
      subst w
      exact (setExpects_iff b).mp hb k v hk

#bench "native/sets-union-commutative"
theorem union_commutative :
    (∃ args, unionExpects args = true) ∧
      ∀ args, unionExpects args = true → unionCommutative args := by
  constructor
  · exact ⟨(∅, ∅), rfl⟩
  · intro ⟨a,b⟩ h
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    simp only [union_2, Std.ExtTreeMap.getElem?_union]
    cases ea : a[k]? <;> cases eb : b[k]? <;> simp_all
    exact (hb _ _ eb).trans (ha _ _ ea).symm

#bench "native/sets-union-empty"
theorem union_empty :
    (∃ input, setExpects input = true) ∧
      ∀ input, setExpects input = true → unionEmpty input := by
  constructor
  · exact ⟨∅, rfl⟩
  · intro input _
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    simp [union_2, Std.ExtTreeMap.getElem?_union]

open Lean in
run_cmd do
  for name in #[``union_satisfies_contract, ``union_commutative, ``union_empty] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"

end LynxBench.Sets
