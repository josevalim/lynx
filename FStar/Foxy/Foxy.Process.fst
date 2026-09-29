module Foxy.Process
open Foxy.Term
module L = FStar.List.Tot.Base
let rec argument_list (xs:list term) : Tot term = match xs with
  | [] -> Nil | h::tl -> Cons h (argument_list tl)
let bad_arity callee args = Tuple [Atom "badarity";Tuple [callee;argument_list args]]
let apply_2 callee args = match callee with
  | Function _ arity _ -> if L.length args = arity then Apply callee args resume else Error (bad_arity callee args)
  | _ -> Error (Tuple [Atom "badfun";callee])
let spawn_1 callee = match callee with
  | Function _ 0 _ -> Spawn callee resume
  | _ -> Error (Atom "badarg")
let send_2 destination message = match destination with
  | Pid _ -> Send destination message resume | _ -> Error (Atom "badarg")
let self_0 () = Self resume
