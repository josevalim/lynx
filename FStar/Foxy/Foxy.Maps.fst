module Foxy.Maps
open Foxy.Term
open Foxy.Compare
module L = FStar.List.Tot.Base
let new_0 () = Ok (Map [])
let get_2 key input = match input with
  | Map entries -> (match find entries key with | Some v -> Ok v | None -> Error (Tuple [Atom "badkey";key]))
  | _ -> Error (Tuple [Atom "badmap";input])
let put_3 key value input = match input with
  | Map entries -> Ok (Map ((key,value)::entries))
  | _ -> Error (Tuple [Atom "badmap";input])
let merge_2 left right = match left,right with
  | Map a,Map b -> Ok (Map (L.append b a))
  | Map _,_ -> Error (Tuple [Atom "badmap";right])
  | _ -> Error (Tuple [Atom "badmap";left])
let rec find_append (a:list (term & term)) (b:list (term & term)) (key:term)
  : Lemma (ensures (find (L.append a b) key == (match find a key with | None -> find b key | found -> found)))
    (decreases a) =
  match a with | [] -> () | _::tl -> find_append tl b key
