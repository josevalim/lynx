module

public import Lynx
import Erlang.erlang

namespace Erlang.functions

#lynx_neutral
  public def «explicit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«apply/2» _0 _1

#lynx_pure
  public def «inc/1» (_0 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)

#lynx_pure
  public def «make/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.ok (Lynx.Term.function 1 1 (Array.mk (List.cons _0 List.nil)))

#lynx_pure
  public def «$lynx_fun_0» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«+/2» _0 _1

#lynx_neutral
  public def «run/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.bind («make/1» _0) fun vF =>
      Lynx.Result.bind (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 10)) fun _2 =>
        Lynx.Result.bind («make/1» _2) fun vG =>
          Lynx.Result.bind
            (Erlang.erlang.«apply/2» vF (Lynx.Term.cons (Lynx.Term.integer 1) Lynx.Term.nil))
            fun vA =>
            Lynx.Result.bind («explicit/2» vG (Lynx.Term.cons (Lynx.Term.integer 2) Lynx.Term.nil))
              fun vB =>
              Lynx.Result.bind (Lynx.Result.ok (Lynx.Term.function 0 1 (Array.mk List.nil)))
                fun _6 =>
                Lynx.Result.bind (Erlang.erlang.«+/2» vA vB) fun _8 =>
                  Erlang.erlang.«apply/2» _6 (Lynx.Term.cons _8 Lynx.Term.nil)

end Erlang.functions
