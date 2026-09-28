module

import Lynx

namespace Erlang.sum

#lynx_pure
  public def sum_1 (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
    | Lynx.Term.cons vX vXs =>
      Lynx.Result.bind (sum_1 vXs) fun _1 => Lynx.Modules.Erlang.add_2 vX _1
    | _2 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))

end Erlang.sum
