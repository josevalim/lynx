module Foxy.Term
module F = Foxy.Float
module L = FStar.List.Tot.Base

type term =
| Integer : int -> term
| Float : F.t -> term
| Atom : string -> term
| Function : id:nat -> arity:nat -> captures:list term -> term
| Pid : nat -> term
| Tuple : list term -> term
| Map : list (term & term) -> term
| Nil : term
| Cons : term -> term -> term

type reply = | Returned : term -> reply | Raised : term -> reply
noeq type result =
| Ok : term -> result
| Error : term -> result
| Apply : term -> list term -> (reply -> Tot result) -> result
| Spawn : term -> (reply -> Tot result) -> result
| Send : term -> term -> (reply -> Tot result) -> result
| Self : (reply -> Tot result) -> result
| Then : result -> (term -> Tot result) -> result

let resume (r:reply) : result = match r with | Returned v -> Ok v | Raised e -> Error e
let bind (r:result) (next:term -> Tot result) : result =
  match r with | Ok v -> next v | Error e -> Error e | _ -> Then r next
let boolean (b:bool) : term = Atom (if b then "true" else "false")
let max (a:nat) (b:nat) : nat = if a < b then b else a
let rec height (t:term) : Tot pos (decreases t) =
  match t with
  | Function _ _ xs | Tuple xs -> 1 + heights xs
  | Map xs -> 1 + entries_height xs
  | Cons h tl -> 1 + max (height h) (height tl)
  | _ -> 1
and heights (xs:list term) : Tot nat (decreases xs) =
  match xs with | [] -> 0 | h::tl -> max (height h) (heights tl)
and entries_height (xs:list (term & term)) : Tot nat (decreases xs) =
  match xs with | [] -> 0 | (k,v)::tl -> max (max (height k) (height v)) (entries_height tl)
