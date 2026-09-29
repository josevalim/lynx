module Foxy.Tests.Main
open Foxy.Term
open FStar.All
open Foxy.Compare
open Foxy.Arithmetic
open Foxy.Process
open Foxy.Runner
open Foxy.Tests.Program
module F = Foxy.Float
module M = Foxy.Maps
module S = Foxy.Sum
module L = FStar.List.Tot.Base

let check (name:string) (accepted:bool) : ML unit =
  if accepted then () else (FStar.IO.print_string ("FAIL: " ^ name ^ "\n"); FStar.All.exit 1)
let check_term name actual expected = check name (compare actual expected true = Eq)
let check_result name actual expected : ML unit =
  match actual,expected with
  | Ok a,Ok b | Error a,Error b -> check_term name a b
  | _ -> check name false
let floating (bits:nat) : ML term = match F.of_bits bits with
  | Some v -> Float v | None -> FStar.All.failwith "invalid finite float fixture"
let finished (outcome:outcome) (pid:nat) : ML Foxy.Runner.completion = match outcome with
  | Exhausted _ -> FStar.All.failwith "unexpected fuel exhaustion"
  | Completed state -> (match completion pid state.finished with
    | Some c -> c | None -> FStar.All.failwith "missing process completion")
let check_reply name reply expected = match reply with
  | Returned value -> check_term name value expected | _ -> check name false
let check_error name outcome reason = match (finished outcome 1).returned with
  | Raised e -> check_term name e reason | _ -> check name false
let pair_map key value = Map [(key,value)]

let numeric_tests () : ML unit =
  let zero=floating 0 in let negative_zero=floating 0x8000000000000000 in
  let one=floating 0x3ff0000000000000 in let two=floating 0x4000000000000000 in
  let half=floating 0x3fe0000000000000 in let negative_half=floating 0xbfe0000000000000 in
  let tiny=floating 1 in let negative_tiny=floating 0x8000000000000001 in
  let huge=floating 0x7fefffffffffffff in
  check "numeric int/float equality" (compare (Integer 1) one false=Eq);
  check "exact int/float distinction" (compare (Integer 1) one true=Lt);
  check "numeric signed zero" (compare zero negative_zero false=Eq);
  check "exact signed zero" (compare negative_zero zero true=Lt);
  check "fractional mixed positive" (compare (Integer 0) half false=Lt);
  check "fractional mixed negative" (compare (Integer 0) negative_half false=Gt);
  check "positive subnormal" (compare (Integer 0) tiny false=Lt);
  check "negative subnormal" (compare negative_tiny (Integer 0) false=Lt);
  let large=floating 0x4340000000000000 in
  check "no mixed comparison rounding" (compare (Integer 9007199254740993) large false=Gt);
  check "mixed comparison reverse" (compare large (Integer 9007199254740993) false=Lt);
  check_result "integer add" (add_2 (Integer 10) (Integer 20)) (Ok (Integer 30));
  check_result "float add" (add_2 one one) (Ok two);
  check_result "mixed add" (add_2 (Integer 1) half) (Ok (Float {F.negative=false;F.exponent=1023;F.fraction=2251799813685248}));
  check_result "mixed reverse" (add_2 half (Integer 1)) (add_2 (Integer 1) half);
  check_result "overflow" (add_2 huge huge) (Error (Atom "badarith"));
  check_result "nonfinite integer conversion" (add_2 (Integer (F.pow2 1024)) zero) (Error (Atom "badarith"));
  check_result "cancellation" (add_2 half negative_half) (Ok zero);
  check_result "negative zeros" (add_2 negative_zero negative_zero) (Ok negative_zero);
  check_result "opposite zeros" (add_2 negative_zero zero) (Ok zero);
  check_result "mixed zero" (add_2 (Integer 0) negative_zero) (Ok zero);
  let twice_tiny=floating 2 in
  check_result "subnormal addition" (add_2 tiny tiny) (Ok twice_tiny);
  let min_normal=floating 0x0010000000000000 in
  let max_subnormal=floating 0x000fffffffffffff in
  check_result "subnormal to normal" (add_2 max_subnormal tiny) (Ok min_normal);
  check_result "normal to subnormal" (add_2 min_normal negative_tiny) (Ok max_subnormal);
  check_result "nearest-even lower" (add_2 (Integer 9007199254740993) zero) (Ok large);
  let rounded_up=floating 0x4340000000000002 in
  check_result "nearest-even upper" (add_2 (Integer 9007199254740995) zero) (Ok rounded_up);
  let half_ulp=floating 0x3ca0000000000000 in
  let next_one=floating 0x3ff0000000000001 in
  let next_next_one=floating 0x3ff0000000000002 in
  check_result "float tie rounds down" (add_2 one half_ulp) (Ok one);
  check_result "float tie rounds up" (add_2 next_one half_ulp) (Ok next_next_one);
  let overflow_threshold=F.pow2 1024 - F.pow2 970 in
  check_result "below overflow threshold" (add_2 (Integer (overflow_threshold-1)) zero) (Ok huge);
  check_result "at overflow threshold" (add_2 (Integer overflow_threshold) zero) (Error (Atom "badarith"));
  check_result "invalid arithmetic" (add_2 Nil one) (Error (Atom "badarith"));
  check "reject infinity bits" (F.of_bits 0x7ff0000000000000 = None);
  check "reject nan bits" (F.of_bits 0x7ff8000000000000 = None);
  check "reject oversized bits" (F.of_bits 0x10000000000000000 = None);
  let xs=Cons (Integer 3) (Cons (Integer 4) Nil) in
  check_result "sum" (S.sum_1 xs) (Ok (Integer 7));
  check_result "bad sum element" (S.sum_1 (Cons Nil Nil)) (Error (Atom "badarith"));
  check_result "improper sum" (S.sum_1 (Cons (Integer 1) (Integer 2))) (Error (Atom "function_clause"));
  check_result "improper append" (S.append_2 (Integer 1) Nil) (Error (Atom "badarg"))

let map_tests () : ML unit =
  let a=Map [(Atom "a",Integer 1);(Atom "b",Integer 2)] in
  let b=Map [(Atom "b",Integer 2);(Atom "a",Integer 1)] in
  check_term "map order independence" a b;
  check_result "map get" (M.get_2 (Atom "a") a) (Ok (Integer 1));
  check_result "map missing" (M.get_2 Nil a) (Error (Tuple [Atom "badkey";Nil]));
  check_result "badmap" (M.get_2 Nil Nil) (Error (Tuple [Atom "badmap";Nil]));
  check_result "put" (bind (M.put_3 (Atom "a") Nil a) (M.get_2 (Atom "a"))) (Ok Nil);
  check_result "merge right precedence" (bind (M.merge_2 a (pair_map (Atom "a") (Integer 9))) (M.get_2 (Atom "a"))) (Ok (Integer 9));
  check_term "shadowed binding" (Map [(Nil,Integer 1);(Nil,Integer 2)]) (pair_map Nil (Integer 1));
  check_result "nested map key" (M.get_2 b (pair_map a Nil)) (Ok Nil);
  let positive=floating 0 in let negative=floating 0x8000000000000000 in
  let zeros=Map [(positive,Integer 1);(negative,Integer 2)] in
  check_result "positive zero key" (M.get_2 positive zeros) (Ok (Integer 1));
  check_result "negative zero key" (M.get_2 negative zeros) (Ok (Integer 2));
  let one=floating 0x3ff0000000000000 in
  check "numeric map values" (compare (pair_map Nil (Integer 1)) (pair_map Nil one) false=Eq);
  check "exact map values" (compare (pair_map Nil (Integer 1)) (pair_map Nil one) true=Lt);
  check "exact map keys" (compare (pair_map (Integer 1) Nil) (pair_map one Nil) false=Lt);
  check "map size" (compare (Map []) a false=Lt);
  check "keys before values" (compare (Map [(Integer 1,Integer 999);(Integer 2,Nil)]) (Map [(Integer 1,Integer 0);(Integer 3,Nil)]) false=Lt);
  let fn=Function 0 1 [Integer 1] in
  check_result "closure key" (M.get_2 fn (pair_map fn Nil)) (Ok Nil);
  check "closure exact captures" (compare fn (Function 0 1 [one]) false=Lt);
  check "term type order" (compare (Atom "z") fn false=Lt && compare fn (Pid 1) false=Lt && compare (Pid 1) (Tuple []) false=Lt && compare (Tuple []) (Map []) false=Lt && compare (Map []) Nil false=Lt);
  let left=Map [(Integer 1,Nil);(Integer 1,Atom "shadowed")] in
  let right=Map [(Integer 2,Nil);(Integer 1,Nil)] in
  check_result "set commutativity" (M.merge_2 left right) (M.merge_2 right left);
  check_result "set empty identity" (M.merge_2 left (Map [])) (Ok left)

let process_tests () : ML unit =
  let run = run context in
  let closure=Function 0 1 [Integer 10] in
  check_reply "captured adder" (finished (run (apply_2 closure [Integer 5]) [] 20) 1).returned (Integer 15);
  check_reply "cross-body apply" (finished (run (apply_2 (Function 2 1 [Integer 10]) [Integer 5]) [] 40) 1).returned (Integer 25);
  check_error "badfun" (run (apply_2 Nil []) [] 10) (Tuple [Atom "badfun";Nil]);
  check_error "badarity" (run (apply_2 closure []) [] 10) (bad_arity closure []);
  let unknown=Function 99 0 [] in
  check_error "unknown ID" (run (apply_2 unknown []) [] 10) (Tuple [Atom "badfun";unknown]);
  check_error "spawn invalid arity" (run (spawn_1 closure) [] 10) (Atom "badarg");
  check_error "invalid destination" (run (send_2 Nil Nil) [] 10) (Atom "badarg");
  check "recursive exhaustion" (match run (apply_2 (Function 3 0 []) []) [] 20 with | Exhausted _ -> true | _ -> false);
  let spawned=run (start_worker ()) [2;1] 40 in
  let parent=finished spawned 1 in let child=finished spawned 2 in
  check_reply "spawn pid" parent.returned (Pid 2);
  check_reply "child self" child.returned (Pid 2);
  check "delivery to parent" (match parent.messages with | [value] -> compare value (Pid 2) true=Eq | _ -> false);
  check "empty child mailbox" (L.length child.messages=0);
  check "dead recipient" (L.length (finished (run (start_worker ()) [] 40) 1).messages=0);
  let twice=bind (spawn_1 (Function 4 0 [])) (fun first -> bind (spawn_1 (Function 4 0 [])) (fun second -> Ok (Tuple [first;second]))) in
  let two=run twice [] 40 in
  check_reply "fresh pids" (finished two 1).returned (Tuple [Pid 2;Pid 3]);
  let _=finished two 2 in let _=finished two 3 in
  let sends=bind (self_0 ()) (fun pid -> bind (send_2 pid (Atom "first")) (fun _ -> send_2 pid (Atom "second"))) in
  let sent=finished (run sends [] 30) 1 in
  check_reply "send return" sent.returned (Atom "second");
  check "mailbox FIFO" (match sent.messages with | [Atom "first";Atom "second"] -> true | _ -> false);
  check_reply "absent recipient" (finished (run (send_2 (Pid 999) (Integer 7)) [] 10) 1).returned (Integer 7);
  let caught=Apply (Function 4 0 []) [] (fun reply -> match reply with | Raised _ -> Ok (Atom "caught") | Returned v -> Ok v) in
  check_reply "apply error handler" (finished (run caught [] 10) 1).returned (Atom "caught");
  check_error "bind error propagation" (run (bind (apply_2 (Function 4 0 []) []) (fun _ -> Ok Nil)) [] 10) (Atom "child_error")

let native_tests () : ML unit =
  check "native sum" (Foxy.Bench.NativeSum.sum [3;4] = 7);
  let a=FStar.FiniteMap.Base.insert 1 [] Foxy.Bench.NativeSets.empty in
  let b=FStar.FiniteMap.Base.insert 2 [] Foxy.Bench.NativeSets.empty in
  let ab=Foxy.Bench.NativeSets.union_2 a b in
  check "native union left key" (FStar.FiniteMap.Base.elements ab 1 = Some []);
  check "native union right key" (FStar.FiniteMap.Base.elements ab 2 = Some []);
  check "native missing key" (FStar.FiniteMap.Base.elements ab 3 = None);
  let replaced=Foxy.Bench.NativeSets.union_2 ab (FStar.FiniteMap.Base.insert 1 [9] Foxy.Bench.NativeSets.empty) in
  check "native right precedence" (FStar.FiniteMap.Base.elements replaced 1 = Some [9])

let main () : ML unit =
  numeric_tests (); map_tests (); process_tests (); native_tests ();
  FStar.IO.print_string "Foxy semantic checks passed\n"
// Entry-point execution is intentionally in ML; the model above remains total.
#push-options "--warn_error -272"
let _ = main ()
#pop-options
