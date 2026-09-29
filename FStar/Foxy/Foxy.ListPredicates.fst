module Foxy.ListPredicates
open Foxy.Term
open Foxy.Process
open Foxy.Runner
module L = FStar.List.Tot.Base
// A Term closure is applied to each element through the request interpreter.
let rec is_proper_list_2 (xs:term) (predicate:term) : Tot result =
  match xs with
  | Nil -> Ok (boolean true)
  | Cons h tl -> bind (apply_2 predicate [h]) (fun answer ->
      match answer with | Atom "true" -> is_proper_list_2 tl predicate | _ -> Ok (boolean false))
  | _ -> Ok (boolean false)
let rec spine_depth (xs:term) : Tot nat =
  match xs with | Cons _ tl -> 1 + spine_depth tl | _ -> 0
let is_integer_1 (x:term) : result =
  match x with | Integer _ -> Ok (boolean true) | _ -> Ok (boolean false)
let integer_dispatch (id:nat) (captures args:list term) : result =
  match id,args with | 0,[x] -> is_integer_1 x | _ -> Error (Atom "function_clause")
let integer_program : program = {arities=[(0,1)];dispatch=integer_dispatch}
let integer_closure : term = Function 0 1 []
[@@ "opaque_to_smt"]
let integer_expectation (xs:term) : option reply =
  evaluate_pure integer_program (is_proper_list_2 xs integer_closure) (spine_depth xs + 4)
