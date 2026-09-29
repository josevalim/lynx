module Foxy.Runner
open Foxy.Term
open Foxy.Process
module L = FStar.List.Tot.Base
noeq type program = { arities:list (nat & nat); dispatch:nat -> list term -> list term -> Tot result }
noeq type process = { pid:nat; computation:result; frames:list (reply -> Tot result); mailbox:list term }
type completion = { finished_pid:nat; returned:reply; messages:list term }
noeq type runtime = { next_pid:nat; runnable:list process; finished:list completion }
noeq type outcome = | Completed : runtime -> outcome | Exhausted : runtime -> outcome

let continue_with reply next = match reply with | Returned v -> next v | Raised e -> Error e
let rec known (xs:list (nat & nat)) (id:nat) (arity:nat) : Tot bool = match xs with
  | [] -> false | (i,a)::tl -> if i=id then a=arity else known tl id arity
let rec deliver (xs:list process) (pid:nat) (message:term) : Tot (list process) = match xs with
  | [] -> []
  | p::tl -> (if p.pid=pid then {p with mailbox=L.append p.mailbox [message]} else p)::deliver tl pid message
let finish (state:runtime) (p:process) (rest:list process) (reply:reply) : runtime =
  match p.frames with
  | [] -> {state with runnable=rest; finished={finished_pid=p.pid;returned=reply;messages=p.mailbox}::state.finished}
  | f::fs -> {state with runnable={p with computation=f reply;frames=fs}::rest}
let step (program:program) (state:runtime) : Tot (runtime & bool) =
  match state.runnable with
  | [] -> state,false
  | p::rest ->
    let update c fs = {state with runnable={p with computation=c;frames=fs}::rest} in
    match p.computation with
    | Ok v -> finish state p rest (Returned v),false
    | Error e -> finish state p rest (Raised e),false
    | Then source next -> update source ((fun r -> continue_with r next)::p.frames),false
    | Self resume -> update (resume (Returned (Pid p.pid))) p.frames,false
    | Apply callee args resume ->
      (match callee with
       | Function id arity captures ->
         if not (known program.arities id arity) then update (resume (Raised (Tuple [Atom "badfun";callee]))) p.frames,false
         else if L.length args <> arity then update (resume (Raised (bad_arity callee args))) p.frames,false
         else update (program.dispatch id captures args) (resume::p.frames),false
       | _ -> update (resume (Raised (Tuple [Atom "badfun";callee]))) p.frames,false)
    | Spawn callee resume ->
      (match callee with
       | Function id 0 captures ->
         if known program.arities id 0 then
           let pid=state.next_pid in
           let parent={p with computation=resume (Returned (Pid pid))} in
           let child={pid;computation=program.dispatch id captures [];frames=[];mailbox=[]} in
           {state with next_pid=pid+1;runnable=parent::L.append rest [child]},true
         else update (resume (Raised (Atom "badarg"))) p.frames,false
       | _ -> update (resume (Raised (Atom "badarg"))) p.frames,false)
    | Send destination message resume ->
      (match destination with
       | Pid pid -> let updated=update (resume (Returned message)) p.frames in
         {updated with runnable=deliver updated.runnable pid message},true
       | _ -> update (resume (Raised (Atom "badarg"))) p.frames,false)
let rec select (xs:list process) (pid:nat) : Tot (list process) = match xs with
  | [] -> []
  | p::tl -> if p.pid=pid then xs else
    match select tl pid with
    | q::qs -> if q.pid=pid then q::p::qs else p::q::qs
    | [] -> [p]
let rec run_from (program:program) (state:runtime) (schedule:list nat) (fuel:nat) : Tot outcome (decreases fuel) =
  match state.runnable,fuel with
  | [],_ -> Completed state
  | _,0 -> Exhausted state
  | _ ->
    let next,boundary=step program state in
    match boundary,schedule with
    | true,pid::tl -> run_from program {next with runnable=select next.runnable pid} tl (fuel-1)
    | _ -> run_from program next schedule (fuel-1)
let run program computation schedule fuel =
  run_from program {next_pid=2;runnable=[{pid=1;computation;frames=[];mailbox=[]}];finished=[]} schedule fuel

// Pure request evaluation for translated expectations; no process effects.
let rec evaluate_pure (program:program) (computation:result) (fuel:nat)
  : Tot (option reply) (decreases fuel) =
  match fuel with
  | 0 -> None
  | _ -> match computation with
    | Ok v -> Some (Returned v)
    | Error e -> Some (Raised e)
    | Then source next ->
      (match evaluate_pure program source (fuel-1) with
       | None -> None | Some (Raised e) -> Some (Raised e)
       | Some (Returned v) -> evaluate_pure program (next v) (fuel-1))
    | Apply callee args resume ->
      (match callee with
       | Function id arity captures ->
         if not (known program.arities id arity) then
           evaluate_pure program (resume (Raised (Tuple [Atom "badfun";callee]))) (fuel-1)
         else if L.length args <> arity then
           evaluate_pure program (resume (Raised (bad_arity callee args))) (fuel-1)
         else (match evaluate_pure program (program.dispatch id captures args) (fuel-1) with
           | None -> None | Some reply -> evaluate_pure program (resume reply) (fuel-1))
       | _ -> evaluate_pure program (resume (Raised (Tuple [Atom "badfun";callee]))) (fuel-1))
    | _ -> None
