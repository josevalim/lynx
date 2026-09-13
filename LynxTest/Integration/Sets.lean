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
open Lynx.Term.Map
set_option Elab.async false

private def findEntry (xs : Entries) (q : Term) : Option (Term × Term) :=
  xs.find? fun e => decide (Term.compare q e.1 = .eq)

/-- A predicate on effective stored bindings only, excluding shadowed entries. -/
def All (predicate : Term → Term → Prop) (xs : Entries) : Prop :=
  ∀ q k v, findEntry xs q = some (k,v) → predicate k v

private def all (xs : Entries) (predicate : Term → Term → Bool) : Bool :=
  xs.all fun (k,_) => match findEntry xs k with
    | some (key,value) => predicate key value
    | none => true

private def allM (xs : Entries) (predicate : Term → Term → Result Bool) : Result Bool :=
  xs.allM fun (k,_) => match findEntry xs k with
    | some (key,value) => predicate key value
    | none => .ok true

private theorem findEntry_self {xs : Entries} {q : Term} {e : Term × Term}
    (h : findEntry xs q = some e) : findEntry xs e.1 = some e := by
  have accepted : decide (Term.compare q e.1 = .eq) = true :=
    List.find?_some
      (p := fun (e : Term × Term) => decide (Term.compare q e.1 = .eq)) h
  have key : Term.compare q e.1 = .eq := of_decide_eq_true accepted
  simpa only [findEntry, Std.TransCmp.congr_left key] using h

@[simp] private theorem allM_ok (xs : Entries) (predicate : Term → Term → Bool) :
    allM xs (fun k v => .ok (predicate k v)) = .ok (all xs predicate) := by
  have listAll (test : (Term × Term) → Bool) (entries : Entries) :
      entries.allM (fun entry => Result.ok (test entry)) = Result.ok (entries.all test) := by
    exact List.allM_pure
  unfold allM all
  have pointwise : (fun (entry : Term × Term) =>
      match findEntry xs entry.1 with
      | some (k,v) => (Result.ok (predicate k v) : Result Bool)
      | none => .ok true) = fun entry => Result.ok
        (match findEntry xs entry.1 with | some (k,v) => predicate k v | none => true) := by
    funext entry
    cases findEntry xs entry.1 <;> rfl
  rw [pointwise]
  exact listAll _ _

@[simp] private theorem all_iff (xs : Entries) (predicate : Term → Term → Bool) :
    all xs predicate = true ↔ All (fun k v => predicate k v = true) xs := by
  simp only [all, List.all_eq_true]
  constructor
  · intro h q k v found
    have mem := List.mem_of_find?_eq_some found
    have self := findEntry_self found
    simpa [self] using h (k,v) mem
  · intro h ⟨k,v⟩ _
    cases found : findEntry xs k with
    | none => rfl
    | some e => exact h k e.1 e.2 found

@[simp] private theorem all_empty (predicate : Term → Term → Prop) : All predicate [] := by
  intro q k v h; cases h

@[simp] private theorem all_put (predicate : Term → Term → Prop) (xs : Entries)
    (k v : Term) (h : All predicate xs) (hv : predicate k v) :
    All predicate (put k v xs) := by
  intro q a b found
  unfold findEntry at found
  simp only [put, List.find?_cons] at found
  split at found
  · cases found; exact hv
  · exact h q a b found

@[simp] private theorem all_merge (predicate : Term → Term → Prop) (a b : Entries)
    (ha : All predicate a) (hb : All predicate b) : All predicate (merge a b) := by
  intro q k v found
  unfold findEntry at found
  simp only [merge, List.find?_append] at found
  cases h : List.find? (fun e => decide (Term.compare q e.1 = .eq)) b with
  | none => exact ha q k v (by simpa [findEntry, h] using found)
  | some e => simp only [h] at found; cases found; exact hb q k v (by simpa [findEntry] using h)

private theorem all_find (predicate : Term → Prop) {xs : Entries}
    (h : All (fun _ v => predicate v) xs) {q v : Term} (found : find q xs = some v) :
    predicate v := by
  change (findEntry xs q).map Prod.snd = some v at found
  cases raw : findEntry xs q with
  | none => simp [raw] at found
  | some e =>
    simp only [raw, Option.map_some, Option.some.injEq] at found
    exact found ▸ h q e.1 e.2 raw

private theorem merge_comm_of_equivalent_constant (value : Term) (a b : Entries)
    (ha : All (fun _ v => Term.compare v value = .eq) a)
    (hb : All (fun _ v => Term.compare v value = .eq) b) :
    Term.compare (.map (merge a b)) (.map (merge b a)) = .eq := by
  change Term.Equivalent (.map (merge a b)) (.map (merge b a))
  apply equivalent_of_find
  intro q
  simp only [find_merge]
  cases ea : find q a <;> cases eb : find q b <;> simp_all [Term.Equivalent]
  exact Std.TransCmp.eq_trans (all_find _ hb eb)
    (Std.OrientedCmp.eq_symm (all_find _ ha ea))

@[simp] theorem merge_comm_of_constant (value : Term) (a b : Entries)
    (ha : All (fun _ v => v = value) a) (hb : All (fun _ v => v = value) b) :
    Term.compare (.map (merge a b)) (.map (merge b a)) = .eq := by
  apply merge_comm_of_equivalent_constant value a b
  · intro q k v h; rw [ha q k v h]; exact Term.compare_self value
  · intro q k v h; rw [hb q k v h]; exact Term.compare_self value

#lynx_pure @[lynx_opaque] def isSet (input : Term) : Result := do
  let accepted ← match input with
    | .map entries => allM entries (fun _ value => .ok (value == .nil))
    | _ => Result.ok false
  .ok (if accepted then Term.true else Term.false)

@[simp] theorem isSet_iff (input : Term) :
    isSet input = .ok (.atom "true") ↔
      ∃ entries, input = .map entries ∧
        All (fun _ value => value = .nil) entries := by
  cases input <;>
    simp [isSet, Term.true, Term.false, Term.beq_iff_equivalent, Term.Equivalent]

/-- Translation of the map-backed set union. -/
def union_2 (left right : Term) : Result := Maps.merge_2 left right

/-- Translated `is_map(value, fn _, v -> v == [] end)`. -/
def setExpects (input : Term) : Result :=
  isSet input

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
  let result ← union_2 input Term.emptyMap
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
