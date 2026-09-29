module Foxy.Bench.TermSets
// SetUnion: a set is a map whose effective values are all [].
// def union(left, right), do: :maps.merge(left, right)
// expects is_set(left) and is_set(right); ensures is_set(result)
// property union(left, right) == union(right, left)
// property union(set, %{}) == set
open Foxy.Term
open Foxy.Compare
open Foxy.Sets
module L = FStar.List.Tot.Base
let union_contract (left:term) (right:term) : Lemma
  (requires (is_set left /\ is_set right))
  (ensures (exists v. union_2 left right == Ok v /\ is_set v)) =
  match left,right with | Map a,Map b -> merge_set a b
let union_commutative (left:term) (right:term) : Lemma
  (requires (is_set left /\ is_set right))
  (ensures (bind (union_2 left right) (fun a -> bind (union_2 right left) (fun b -> eq_2 a b)) == Ok (boolean true))) =
  match left,right with
  | Map a,Map b ->
    merge_set a b; merge_set b a;
    let _ = introduce forall key. find (L.append b a) key == find (L.append a b) key
      with lookup_commutes a b key in
    equal_sets (L.append b a) (L.append a b)
let union_empty (value:term) : Lemma
  (requires (is_set value))
  (ensures (bind (union_2 value (Map [])) (fun v -> eq_2 v value) == Ok (boolean true))) =
  match value with | Map xs -> equal_sets xs xs
