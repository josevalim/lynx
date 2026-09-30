module Foxy.Sum
open Foxy.Term
open Foxy.Arithmetic
open Foxy.ListPredicates
let is_integer_list (xs:term) : Tot bool =
  match integer_expectation xs with | Ok (Atom "true") -> true | _ -> false
let rec sum_1 (xs:term) : Tot result = match xs with
  | Nil -> Ok (Integer 0)
  | Cons h tl -> bind (sum_1 tl) (fun v -> add_2 h v)
  | _ -> Error (Atom "function_clause")
let rec append (a:term) (b:term) : Tot term = match a with
  | Nil -> b | Cons h tl -> Cons h (append tl b) | _ -> b
let rec append_2 (a:term) (b:term) : Tot result = match a with
  | Nil -> Ok b | Cons h tl -> bind (append_2 tl b) (fun rest -> Ok (Cons h rest))
  | _ -> Error (Atom "badarg")
// Domain preservation only, matching the Lean/Dafny supporting lemma.
let rec append_preserves_integers (a:term) (b:term) : Lemma
  (requires (is_integer_list a /\ is_integer_list b))
  (ensures (is_integer_list (append a b) /\ append_2 a b == Ok (append a b))) =
  match a with | Cons (Integer _) tl -> append_preserves_integers tl b | _ -> ()
