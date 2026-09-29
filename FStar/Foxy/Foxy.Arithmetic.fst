module Foxy.Arithmetic
open Foxy.Term
module F = Foxy.Float
let float_result (x:option F.t) : result =
  match x with | Some value -> Ok (Float value) | None -> Error (Atom "badarith")
let mixed_add (n:int) (x:F.t) : result =
  match F.of_int n with | None -> Error (Atom "badarith") | Some y -> float_result (F.add y x)
let add_2 (a:term) (b:term) : Tot result =
  match a,b with
  | Integer x,Integer y -> Ok (Integer (x+y))
  | Float x,Float y -> float_result (F.add x y)
  | Integer x,Float y | Float y,Integer x -> mixed_add x y
  | _ -> Error (Atom "badarith")
