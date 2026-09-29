module

public import Lynx
import Erlang.functions

namespace Erlang.program

public def fun_table : Lynx.Term.FunTable :=
  #[fun captures args =>
    match Prod.mk captures args with
    | Prod.mk #[cap1] #[arg1] => Erlang.functions.«$lynx_fun_0/2» cap1 arg1
    | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    fun captures args =>
    match Prod.mk captures args with
    | Prod.mk #[] #[arg1] => Erlang.functions.«inc/1» arg1
    | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))]

end Erlang.program
