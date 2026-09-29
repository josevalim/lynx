module Foxy.Tests.Proofs
open Foxy.Term
open Foxy.Runner
open Foxy.Process
open Foxy.Tests.Program
module S = Foxy.Sum
module N = Foxy.Bench.NativeSum
module L = FStar.List.Tot.Base
let rec encode (xs:list int) : Tot term = match xs with | [] -> Nil | h::tl -> Cons (Integer h) (encode tl)
let rec correspondence (xs:list int) : Lemma (S.sum_1 (encode xs) == Ok (Integer (N.sum xs))) =
  match xs with | [] -> () | _::tl -> correspondence tl
let send_returns_message (pid:nat) (message:term) : Lemma
  (send_2 (Pid pid) message == Send (Pid pid) message resume) = ()
let rec delivery_length (xs:list process) (pid:nat) (message:term) : Lemma
  (L.length (deliver xs pid message) == L.length xs) =
  match xs with | [] -> () | _::tl -> delivery_length tl pid message
let delivery_head (p:process) (xs:list process) (pid:nat) (message:term) : Lemma
  (ensures (match deliver (p::xs) pid message with
   | q::_ -> q.pid == p.pid /\ q.mailbox == (if p.pid=pid then L.append p.mailbox [message] else p.mailbox)
   | [] -> False)) = ()
#push-options "--fuel 4 --ifuel 2"
let captured_adder (offset:int) (arg:int) : Lemma
  (ensures (match run context (apply_2 (Function 0 1 [Integer offset]) [Integer arg]) [] 3 with
   | Completed state -> (match completion 1 state.finished with | Some c -> c.returned == Returned (Integer (offset+arg)) | None -> False)
   | _ -> False)) = ()
#pop-options
let empty_set_witness () : Lemma
  (Foxy.Sets.is_set (Map []) /\ Foxy.Bench.NativeSets.is_set Foxy.Bench.NativeSets.empty) = ()
