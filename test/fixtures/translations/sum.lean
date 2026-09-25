module

import Lynx

#lynx_pure
  def sum_1 (input : Lynx.Term) : Lynx.Result :=
    match input with
    | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
    | Lynx.Term.cons x xs =>
      Lynx.Result.bind (sum_1 xs) fun subtotal => Lynx.Modules.Erlang.add_2 x subtotal
    | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
