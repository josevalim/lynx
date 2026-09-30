module Foxy.ListPredicates
open Foxy.Term
open Foxy.Process
open Foxy.Runner
// Generic traversal accepts a Term closure, with the typed pure dispatch path.
let rec is_proper_list_2 (program:program) (xs:term) (predicate:term) : Tot result =
  match xs with
  | Nil -> Ok (boolean true)
  | Cons h tl -> bind (pureApply program predicate [h]) (fun answer ->
      match answer with | Atom "true" -> is_proper_list_2 program tl predicate | _ -> Ok (boolean false))
  | _ -> Ok (boolean false)
let integer_body (captures args:list term) : reply =
  match args with
  | [x] -> Returned (match x with | Integer _ -> boolean true | _ -> boolean false)
  | _ -> Raised (Atom "badarg")
let integer_program : program = {arities=[(0,1)];entries=[(0,Pure integer_body)]}
let integer_closure : term = Function 0 1 []
// Verified callback summary; no sum-value theorem is moved out of timing.
[@@ "opaque_to_smt"]
let integer_callback (x:term) : Tot (answer:result{
  answer == Ok (match x with | Integer _ -> boolean true | _ -> boolean false)}) =
  pureApply integer_program integer_closure [x]
let rec integer_expectation (xs:term) : Tot result =
  match xs with
  | Nil -> Ok (boolean true)
  | Cons h tl -> bind (integer_callback h) (fun answer ->
      match answer with | Atom "true" -> integer_expectation tl | _ -> Ok (boolean false))
  | _ -> Ok (boolean false)
let rec integer_callback_specialization (xs:term) : Lemma
  (is_proper_list_2 integer_program xs integer_closure == integer_expectation xs) =
  match xs with | Cons _ tl -> integer_callback_specialization tl | _ -> ()
