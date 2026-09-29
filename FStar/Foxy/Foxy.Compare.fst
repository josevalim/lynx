module Foxy.Compare
open Foxy.Term
module F = Foxy.Float
module L = FStar.List.Tot.Base
open FStar.Mul

type ordering = | Lt | Eq | Gt
let int_compare (a:int) (b:int) : ordering = if a < b then Lt else if a = b then Eq else Gt
let swap (x:ordering) : ordering = match x with | Lt -> Gt | Eq -> Eq | Gt -> Lt
let float_compare (a:F.t) (b:F.t) (exact:bool) : ordering =
  match int_compare (F.units a) (F.units b) with
  | Eq -> if exact && a.negative <> b.negative then (if a.negative then Lt else Gt) else Eq
  | order -> order
let rank (x:term) : nat = match x with
  | Integer _ | Float _ -> 0 | Atom _ -> 1 | Function _ _ _ -> 2 | Pid _ -> 3
  | Tuple _ -> 4 | Map _ -> 5 | Nil -> 6 | Cons _ _ -> 7

let rec compare (a:term) (b:term) (exact:bool) : Tot ordering
  (decreases %[(max (height a) (height b) <: int); 5; 0]) =
  match a,b with
  | Integer x,Integer y -> int_compare x y
  | Float x,Float y -> float_compare x y exact
  | Integer x,Float y -> if exact then Lt else int_compare (x * F.pow2 1074) (F.units y)
  | Float x,Integer y -> if exact then Gt else swap (int_compare (y * F.pow2 1074) (F.units x))
  | Atom x,Atom y -> int_compare (FStar.String.compare x y) 0
  | Function i _ xs,Function j _ ys ->
    (match int_compare i j with | Eq -> compare_list xs ys true | order -> order)
  | Pid x,Pid y -> int_compare x y
  | Tuple xs,Tuple ys ->
    (match int_compare (L.length xs) (L.length ys) with | Eq -> compare_list xs ys exact | order -> order)
  | Map xs,Map ys ->
    if same_bindings xs ys exact then Eq else
    let left = normalize xs in let right = normalize ys in
    (match int_compare (L.length left) (L.length right) with
     | Eq -> (match compare_keys left right with | Eq -> compare_values left right exact | order -> order)
     | order -> order)
  | Nil,Nil -> Eq
  | Cons x xs,Cons y ys ->
    (match compare x y exact with | Eq -> compare xs ys exact | order -> order)
  | _ -> int_compare (rank a) (rank b)
and compare_list (a:list term) (b:list term) (exact:bool) : Tot ordering
  (decreases %[1 + max (heights a) (heights b); 4; (L.length a <: int)]) =
  match a,b with
  | [],[] -> Eq | [],_ -> Lt | _,[] -> Gt
  | x::xs,y::ys -> (match compare x y exact with | Eq -> compare_list xs ys exact | order -> order)
and find (xs:list (term & term)) (key:term)
  : Tot (r:option term{match r with | None -> True | Some v -> height v <= entries_height xs})
  (decreases %[1 + max (entries_height xs) (height key); 2; (L.length xs <: int)]) =
  match xs with
  | [] -> None
  | (k,v)::tl -> (match compare key k true with | Eq -> Some v | _ -> find tl key)
and matches_keys (keys:list (term & term)) (a:list (term & term)) (b:list (term & term)) (exact:bool)
  : Pure bool (requires (entries_height keys <= max (entries_height a) (entries_height b)))
    (ensures (fun _ -> True))
    (decreases %[1 + max (entries_height a) (entries_height b); 3; (L.length keys <: int)]) =
  match keys with
  | [] -> true
  | (k,_)::tl ->
    (match find a k,find b k with
     | Some x,Some y -> compare x y exact = Eq && matches_keys tl a b exact
     | None,None -> matches_keys tl a b exact
     | _ -> false)
and same_bindings (a:list (term & term)) (b:list (term & term)) (exact:bool) : Tot bool
  (decreases %[1 + max (entries_height a) (entries_height b); 4; 0]) =
  matches_keys a a b exact && matches_keys b a b exact
and insert (entry:term & term) (xs:list (term & term))
  : Tot (r:list (term & term){entries_height r <= max (max (height (fst entry)) (height (snd entry))) (entries_height xs)})
    (decreases %[1 + max (max (height (fst entry)) (height (snd entry))) (entries_height xs); 3; (L.length xs <: int)]) =
  match xs with
  | [] -> [entry]
  | h::tl -> (match compare (fst entry) (fst h) true with
    | Lt -> entry::xs | Eq -> entry::tl | Gt -> h::insert entry tl)
and normalize (xs:list (term & term))
  : Tot (r:list (term & term){entries_height r <= entries_height xs})
    (decreases %[1 + entries_height xs; 4; (L.length xs <: int)]) =
  match xs with | [] -> [] | h::tl -> insert h (normalize tl)
and compare_keys (a:list (term & term)) (b:list (term & term)) : Tot ordering
  (decreases %[1 + max (entries_height a) (entries_height b); 4; (L.length a <: int)]) =
  match a,b with
  | [],[] -> Eq | [],_ -> Lt | _,[] -> Gt
  | (k,_)::xs,(j,_)::ys -> (match compare k j true with | Eq -> compare_keys xs ys | order -> order)
and compare_values (a:list (term & term)) (b:list (term & term)) (exact:bool) : Tot ordering
  (decreases %[1 + max (entries_height a) (entries_height b); 4; (L.length a <: int)]) =
  match a,b with
  | [],[] -> Eq | [],_ -> Lt | _,[] -> Gt
  | (_,v)::xs,(_,w)::ys -> (match compare v w exact with | Eq -> compare_values xs ys exact | order -> order)

let eq_2 a b = Ok (boolean (compare a b false = Eq))
let neq_2 a b = Ok (boolean (compare a b false <> Eq))
let exact_eq_2 a b = Ok (boolean (compare a b true = Eq))
let exact_neq_2 a b = Ok (boolean (compare a b true <> Eq))
let lt_2 a b = Ok (boolean (compare a b false = Lt))
let le_2 a b = Ok (boolean (compare a b false <> Gt))
let gt_2 a b = Ok (boolean (compare a b false = Gt))
let ge_2 a b = Ok (boolean (compare a b false <> Lt))
