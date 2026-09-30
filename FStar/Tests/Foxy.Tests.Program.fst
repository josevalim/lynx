module Foxy.Tests.Program
open Foxy.Term
open Foxy.Process
open Foxy.Arithmetic
open Foxy.Runner
// A.make_adder(n) = fn x -> n + x end
// B.worker(parent) = send(parent, self())
let dispatch (id:nat) (captures:list term) (args:list term) : result =
  match id,captures,args with
  | 0,[offset],[arg] -> add_2 offset arg
  | 1,[parent],[] -> bind (self_0 ()) (fun pid -> send_2 parent pid)
  | 2,[offset],[arg] -> bind (apply_2 (Function 0 1 [offset]) [arg])
      (fun value -> apply_2 (Function 0 1 [offset]) [value])
  | 3,_,_ -> apply_2 (Function 3 0 []) []
  | 4,_,_ -> Error (Atom "child_error")
  | _ -> Error (Atom "function_clause")
let context : program = {arities=[(0,1);(1,0);(2,1);(3,0);(4,0)];
  entries=[(0,Pure (fun captures args -> match captures,args with
      | [offset],[arg] -> to_reply (add_2 offset arg)
      | _ -> Raised (Atom "function_clause")));(1,Effectful (dispatch 1));
    (2,Effectful (dispatch 2));(3,Effectful (dispatch 3));
    (4,Pure (fun _ _ -> Raised (Atom "child_error")))]}
let start_worker () = bind (self_0 ()) (fun parent -> spawn_1 (Function 1 0 [parent]))
let rec completion (pid:nat) (xs:list Foxy.Runner.completion) : Tot (option Foxy.Runner.completion) =
  match xs with | [] -> None | h::tl -> if h.finished_pid=pid then Some h else completion pid tl
