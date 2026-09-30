module

/-
defmodule SetUnion do
  # A set is a map whose values are all [].
  defp is_set(value), do: is_map(value, fn _, v -> v == [] end)

  def union(left, right), do: :maps.merge(left, right)
end
-/
import Erlang.erlang
import Erlang.maps
import LynxTest.Bench
import all Lynx.Term.Runner
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control

namespace LynxTest.Integration.Sets
open Lynx
set_option Elab.async false

private def findEntry (xs : List (Term × Term)) (q : Term) : Option (Term × Term) :=
  xs.find? fun e => decide (Term.exactCompare q e.1 = .eq)

/-- A predicate on effective stored bindings only, excluding shadowed entries. -/
def All (predicate : Term → Term → Prop) (xs : List (Term × Term)) : Prop :=
  ∀ q k v, findEntry xs q = some (k,v) → predicate k v

private def all (xs : List (Term × Term)) (predicate : Term → Term → Bool) : Bool :=
  xs.all fun (k,_) => match findEntry xs k with
    | some (key,value) => predicate key value
    | none => true

private def allM (xs : List (Term × Term)) (predicate : Term → Term → Result Bool) : Result Bool :=
  xs.allM fun (k,_) => match findEntry xs k with
    | some (key,value) => predicate key value
    | none => .ok true

private theorem findEntry_self {xs : List (Term × Term)} {q : Term} {e : Term × Term}
    (h : findEntry xs q = some e) : findEntry xs e.1 = some e := by
  have accepted : decide (Term.exactCompare q e.1 = .eq) = true :=
    List.find?_some
      (p := fun (e : Term × Term) => decide (Term.exactCompare q e.1 = .eq)) h
  have key : Term.exactCompare q e.1 = .eq := of_decide_eq_true accepted
  simpa only [findEntry, Std.TransCmp.congr_left key] using h

@[simp] private theorem allM_ok (xs : List (Term × Term)) (predicate : Term → Term → Bool) :
    allM xs (fun k v => .ok (predicate k v)) = .ok (all xs predicate) := by
  have listAll (test : (Term × Term) → Bool) (entries : List (Term × Term)) :
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

@[simp] private theorem all_iff (xs : List (Term × Term)) (predicate : Term → Term → Bool) :
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

@[simp] private theorem all_merge (predicate : Term → Term → Prop) (a b : List (Term × Term))
    (ha : All predicate a) (hb : All predicate b) : All predicate (b ++ a) := by
  intro q k v found
  unfold findEntry at found
  simp only [List.find?_append] at found
  cases h : List.find? (fun e => decide (Term.exactCompare q e.1 = .eq)) b with
  | none => exact ha q k v (by simpa [findEntry, h] using found)
  | some e => simp only [h] at found; cases found; exact hb q k v (by simpa [findEntry] using h)

private theorem all_get (value : Term) {xs : List (Term × Term)}
    (h : All (fun _ v => v = value) xs) (q : Term) :
    Erlang.maps.«get/2» q (.map xs) = .ok value ∨
      Erlang.maps.«get/2» q (.map xs) = .error (.error (.tuple #[.atom "badkey", q])) := by
  change (let result : Result := match (findEntry xs q).map Prod.snd with
    | some value => Result.ok value
    | none => .error (.error (.tuple #[.atom "badkey", q]))
    result = .ok value ∨ result = .error (.error (.tuple #[.atom "badkey", q])))
  cases raw : findEntry xs q with
  | none => exact Or.inr rfl
  | some e => exact Or.inl (congrArg Result.ok (h q e.1 e.2 raw))

@[simp] theorem merge_comm_of_constant (value : Term) (a b : List (Term × Term))
    (ha : All (fun _ v => v = value) a) (hb : All (fun _ v => v = value) b) :
    Term.compare (.map (b ++ a)) (.map (a ++ b)) = .eq := by
  apply Erlang.maps.compare_eq_of_get
  intro q
  change (Erlang.maps.«merge/2» (.map a) (.map b) >>= Erlang.maps.«get/2» q) =
    (Erlang.maps.«merge/2» (.map b) (.map a) >>= Erlang.maps.«get/2» q)
  rw [Erlang.maps.get_merge, Erlang.maps.get_merge]
  rcases all_get value ha q with ea | ea <;>
    rcases all_get value hb q with eb | eb <;> simp [ea, eb]

-- Use `isSet_iff` instead of unfolding recursive entry validation in clients.
#lynx_pure def isSet (input : Term) : Result := do
  let accepted ← match input with
    | .map entries => allM entries (fun _ value => .ok (value == .nil))
    | _ => Result.ok false
  .ok (if accepted then Term.true else Term.false)

@[simp] theorem isSet_iff (input : Term) :
    isSet input = .ok (.atom "true") ↔
      ∃ entries, input = .map entries ∧
        All (fun _ value => value = .nil) entries := by
  cases input <;>
    simp [isSet, Term.beq_iff_compare_eq]

/-- Translation of the map-backed set union. -/
#lynx_pure def union_2 (left right : Term) : Result := Erlang.maps.«merge/2» left right

/- law union_result(left, right), requires: is_set(left) and is_set(right),
     expects: (result -> is_set(result)) -/
#bench "erlang/sets-union-result"
theorem union_result (left right : Term)
    (leftValid : isSet left = .ok Term.true)
    (rightValid : isSet right = .ok Term.true) :
    ∃ result, union_2 left right = .ok result ∧ isSet result = .ok Term.true := by
  obtain ⟨a, rfl, ha⟩ := (isSet_iff left).mp leftValid
  obtain ⟨b, rfl, hb⟩ := (isSet_iff right).mp rightValid
  refine ⟨.map (b ++ a), rfl, ?_⟩
  exact (isSet_iff _).mpr ⟨b ++ a, rfl, all_merge _ a b ha hb⟩

/- law union_commutative(left, right), requires: is_set(left) and is_set(right),
     expects: union(left, right) == union(right, left) -/
def unionCommutative (left right : Term) : Result := do
  let leftRight ← union_2 left right
  let rightLeft ← union_2 right left
  Erlang.erlang.«==/2» leftRight rightLeft

#bench "erlang/sets-union-commutative"
theorem union_commutative (left right : Term)
    (leftValid : isSet left = .ok Term.true)
    (rightValid : isSet right = .ok Term.true) :
    unionCommutative left right = .ok Term.true := by
  obtain ⟨a, rfl, ha⟩ := (isSet_iff left).mp leftValid
  obtain ⟨b, rfl, hb⟩ := (isSet_iff right).mp rightValid
  simp [unionCommutative, union_2, Erlang.maps.«merge/2»,
    Erlang.erlang.«==/2», merge_comm_of_constant .nil a b ha hb]

/- law union_empty(set), requires: is_set(set), expects: union(set, %{}) == set -/
def unionEmpty (input : Term) : Result := do
  let result ← union_2 input (Term.map [])
  Erlang.erlang.«==/2» result input

#bench "erlang/sets-union-empty"
theorem union_empty (input : Term) (valid : isSet input = .ok Term.true) :
    unionEmpty input = .ok Term.true := by
  obtain ⟨entries, rfl, _⟩ := (isSet_iff input).mp valid
  simp [unionEmpty, union_2, Erlang.maps.«merge/2», Erlang.erlang.«==/2»]

end LynxTest.Integration.Sets
