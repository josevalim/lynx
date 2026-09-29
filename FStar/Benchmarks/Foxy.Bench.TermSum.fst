module Foxy.Bench.TermSum
// def sum([]), do: 0
// def sum([head | tail]), do: head + sum(tail)
// expects integer_list(xs); ensures integer(result)
// property sum(left ++ right) == sum(left) + sum(right)
open Foxy.Term
open Foxy.Sum
open Foxy.Arithmetic
// Both inductions belong to the measured declarations.
let rec sum_contract (xs:term) : Lemma
  (requires (is_integer_list xs))
  (ensures (exists n. sum_1 xs == Ok (Integer n))) =
  match xs with | Cons (Integer _) tl -> sum_contract tl | _ -> ()
let rec sum_append (a:term) (b:term) : Lemma
  (requires (is_integer_list a /\ is_integer_list b))
  (ensures ((exists n. sum_1 a == Ok (Integer n)) /\
    (exists n. sum_1 b == Ok (Integer n)) /\
    append_2 a b == Ok (append a b) /\
    bind (append_2 a b) sum_1 ==
    bind (sum_1 a) (fun x -> bind (sum_1 b) (fun y -> add_2 x y)))) =
  sum_contract a;
  sum_contract b;
  append_preserves_integers a b;
  match a with
  | Cons (Integer _) tl ->
    sum_contract tl;
    append_preserves_integers tl b;
    sum_contract (append tl b);
    sum_append tl b
  | _ -> ()
