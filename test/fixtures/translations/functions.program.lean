module

public import Lynx
import Erlang.functions

namespace Lynx.Program

public def functions : Lynx.Term.FunTable :=
  #[Lynx.Term.FunTable.entry 1 1 fun _lynx_captures _lynx_args =>
      Erlang.functions.«$lynx_fun_0/2» (Array.getD _lynx_captures 0 Lynx.Term.nil)
        (Array.getD _lynx_args 0 Lynx.Term.nil),
    Lynx.Term.FunTable.entry 0 1 fun _lynx_captures _lynx_args =>
      Erlang.functions.«inc/1» (Array.getD _lynx_args 0 Lynx.Term.nil)]

end Lynx.Program
