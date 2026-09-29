module Foxy.Sets
open Foxy.Term
open Foxy.Compare
open Foxy.Maps
module L = FStar.List.Tot.Base
let all_nil (xs:list (term & term)) : prop = forall key. match find xs key with | None -> True | Some v -> v == Nil
let is_set (x:term) : prop = match x with | Map xs -> all_nil xs | _ -> False
let union_2 = merge_2
let merge_set (a:list (term & term)) (b:list (term & term)) : Lemma
  (requires (all_nil a /\ all_nil b)) (ensures (all_nil (L.append b a))) =
  introduce forall key. (match find (L.append b a) key with | None -> True | Some v -> v == Nil)
  with find_append b a key
let lookup_commutes (a:list (term & term)) (b:list (term & term)) (key:term) : Lemma
  (requires (all_nil a /\ all_nil b)) (ensures (find (L.append b a) key == find (L.append a b) key)) =
  find_append b a key; find_append a b key
let rec match_set_keys (keys:list (term & term)) (a:list (term & term)) (b:list (term & term)) : Lemma
  (requires (entries_height keys <= max (entries_height a) (entries_height b) /\ all_nil a /\ all_nil b /\
    (forall key. find a key == find b key)))
  (ensures (matches_keys keys a b false)) (decreases keys) =
  match keys with | [] -> () | (key,_)::tl -> match_set_keys tl a b
let equal_sets (a:list (term & term)) (b:list (term & term)) : Lemma
  (requires (all_nil a /\ all_nil b /\ (forall key. find a key == find b key)))
  (ensures (compare (Map a) (Map b) false == Eq)) =
  match_set_keys a a b; match_set_keys b a b
