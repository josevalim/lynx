module

public import Lynx
import Erlang.erlang

namespace Erlang.sum

#lynx_pure
  public def «sum/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
    | Lynx.Term.cons vX vXs => Lynx.Result.bind («sum/1» vXs) fun _1 => Erlang.erlang.«+/2» vX _1
    | _2 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))

end Erlang.sum
