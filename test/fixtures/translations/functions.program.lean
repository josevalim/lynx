module

public import Lynx
import Erlang.functions

namespace Erlang.program

public def fun_table : Lynx.Term.FunTable :=
  #[Lynx.Term.FunEntry.pure
      (fun captures args =>
        match captures, args with
        | #[cap1], #[arg1] =>
          Lynx.Result.toExcept (Erlang.functions.«$lynx_fun_0/2» cap1 arg1) (by simp)
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunEntry.effectful
      (fun captures args =>
        match captures, args with
        | #[cap1], #[arg1] => Erlang.functions.«$lynx_fun_1/2» cap1 arg1
        | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunEntry.pure
      (fun captures args =>
        match captures, args with
        | #[], #[] => Lynx.Result.toExcept Erlang.functions.«zero/0» (by simp)
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunEntry.pure
      (fun captures args =>
        match captures, args with
        | #[], #[arg1] => Lynx.Result.toExcept (Erlang.functions.«inc/1» arg1) (by simp)
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunEntry.effectful
      (fun captures args =>
        match captures, args with
        | #[], #[arg1] => Erlang.functions.«remember/1» arg1
        | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))]

end Erlang.program
