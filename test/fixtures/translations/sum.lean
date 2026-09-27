module

import Lynx

#lynx_pure
  def sum_1 (v0 : Lynx.Term) : Lynx.Result :=
    match v0 with
    | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
    | Lynx.Term.cons v_X v_Xs =>
      Lynx.Result.bind (sum_1 v_Xs) fun v1 => Lynx.Modules.Erlang.add_2 v_X v1
    | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
