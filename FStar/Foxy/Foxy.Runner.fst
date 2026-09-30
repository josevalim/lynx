module Foxy.Runner
open Foxy.Term
open Foxy.Process
module L = FStar.List.Tot.Base
noeq type fun_entry =
| Pure : (list term -> list term -> Tot reply) -> fun_entry
| Effectful : (list term -> list term -> Tot result) -> fun_entry
noeq type program = { arities:list (nat & nat); entries:list (nat & fun_entry) }
noeq type process = { pid:nat; computation:result; frames:list (reply -> Tot result); mailbox:list term }
type completion = { finished_pid:nat; returned:reply; messages:list term }
noeq type runtime = { next_pid:nat; runnable:list process; finished:list completion }
noeq type outcome = | Completed : runtime -> outcome | Exhausted : runtime -> outcome

let rec entry (entries:list (nat & fun_entry)) (id:nat) : Tot (option fun_entry) =
  match entries with | [] -> None | (i,f)::tl -> if i=id then Some f else entry tl id
let invoke (f:fun_entry) (captures args:list term) : result =
  match f with | Pure body -> resume (body captures args) | Effectful body -> body captures args
let dispatch (program:program) (id:nat) (captures args:list term) : result =
  match entry program.entries id with
  | Some f -> invoke f captures args | None -> Error (Atom "undef")
// A pure callable returns only a value/error; effectful calls remain requests.
let pureApply (program:program) (callee:term) (args:list term) : result =
  match callee with
  | Function id arity captures ->
    if L.length args = arity then
      match entry program.entries id with
      | Some (Pure body) -> resume (body captures args)
      | Some (Effectful _) -> apply_2 callee args
      | None -> Error (Tuple [Atom "badfun";callee])
    else apply_2 callee args
  | _ -> apply_2 callee args

let continue_with reply next = match reply with | Returned v -> next v | Raised e -> Error e
let rec known (xs:list (nat & nat)) (id:nat) (arity:nat) : Tot bool = match xs with
  | [] -> false | (i,a)::tl -> if i=id then a=arity else known tl id arity
let known_program (program:program) (id:nat) (arity:nat) : Tot bool =
  match entry program.entries id with
  | None -> false | Some _ -> known program.arities id arity
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
         if not (known_program program id arity) then update (resume (Raised (Tuple [Atom "badfun";callee]))) p.frames,false
         else if L.length args <> arity then update (resume (Raised (bad_arity callee args))) p.frames,false
         else update (dispatch program id captures args) (resume::p.frames),false
       | _ -> update (resume (Raised (Tuple [Atom "badfun";callee]))) p.frames,false)
    | Spawn callee resume ->
      (match callee with
       | Function id 0 captures ->
         if known_program program id 0 then
           let pid=state.next_pid in
           let parent={p with computation=resume (Returned (Pid pid))} in
           let child={pid;computation=dispatch program id captures [];frames=[];mailbox=[]} in
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
