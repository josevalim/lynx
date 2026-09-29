module

public import Lynx
import Erlang.erlang

namespace Erlang.literals

#lynx_pure
  public def «one_two/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    |
    Lynx.Term.cons (Lynx.Term.integer 1) (Lynx.Term.cons (Lynx.Term.integer (-2)) Lynx.Term.nil) =>
      Lynx.Result.ok (Lynx.Term.atom "yes")
    | _3 =>
      Lynx.Result.ok
        (Lynx.Term.cons (Lynx.Term.atom "no")
          (Lynx.Term.cons (Lynx.Term.integer (-1)) Lynx.Term.nil))

#lynx_pure
  public def «sign/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.integer (-1) => Lynx.Result.ok (Lynx.Term.atom "minus_one")
    | vX => Erlang.erlang.«+/2» vX (Lynx.Term.integer (-5))

#lynx_pure
  public def «zero/0» : Lynx.Result :=
    Lynx.Result.ok (Lynx.Term.integer 0)

#lynx_pure
  public def «call_zero/1» (_0 : Lynx.Term) : Lynx.Result :=
    «zero/0»

end Erlang.literals
