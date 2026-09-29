module Foxy.Bench.NativeSets
module M = FStar.FiniteMap.Base
open FStar.FiniteMap.Ambient
// Native finite maps retain list values, including nonempty non-set markers.
open FStar.FiniteSet.Ambient
type set_map = M.map int (list int)
let empty : set_map = M.emptymap
let is_set (m:set_map) : prop = forall key. M.elements m key == None \/ M.elements m key == Some []
let union_2 (a:set_map) (b:set_map) : set_map = M.merge a b
let union_contract (a:set_map) (b:set_map) : Lemma
  (requires (is_set a /\ is_set b)) (ensures (is_set (union_2 a b))) = ()
let union_commutative (a:set_map) (b:set_map) : Lemma
  (requires (is_set a /\ is_set b)) (ensures (M.equal (union_2 a b) (union_2 b a))) = ()
let union_empty (a:set_map) : Lemma
  (requires (is_set a)) (ensures (M.equal (union_2 a empty) a)) = ()
