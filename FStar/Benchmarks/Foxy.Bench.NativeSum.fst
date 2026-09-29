module Foxy.Bench.NativeSum
module L = FStar.List.Tot.Base
let rec sum (xs:list int) : Tot int = match xs with | [] -> 0 | h::tl -> h + sum tl
let rec sum_append (a:list int) (b:list int) : Lemma (sum (L.append a b) == sum a + sum b) =
  match a with | [] -> () | _::tl -> sum_append tl b
