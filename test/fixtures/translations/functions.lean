module

public import Lynx
import Erlang.erlang

namespace Erlang.functions

#lynx_pure
  public def «$lynx_fun_0/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«+/2» _0 _1

public def «$lynx_fun_1/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«put/2» _0 _1

public def «explicit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«apply/2» _0 _1

#lynx_pure
  public def «inc/1» (_0 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)

#lynx_pure
  public def «make/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.ok (Lynx.Term.function 0 1 #[_0])

#lynx_pure
  public def «make_store/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.ok (Lynx.Term.function 1 1 #[_0])

public def «remember/1» (_0 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«put/2» (Lynx.Term.atom "last") _0

#lynx_pure
  public def «zero/0» : Lynx.Result :=
    Lynx.Result.ok (Lynx.Term.integer 0)

public def «run/1» (_0 : Lynx.Term) : Lynx.Result :=
  Lynx.Result.bind («make/1» _0)
    (fun vF =>
      Lynx.Result.bind (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 10))
        (fun _2 =>
          Lynx.Result.bind («make/1» _2)
            (fun vG =>
              Lynx.Result.bind (Lynx.Term.apply vF #[Lynx.Term.integer 1])
                (fun vA =>
                  Lynx.Result.bind
                    («explicit/2» vG (Lynx.Term.cons (Lynx.Term.integer 2) Lynx.Term.nil))
                    (fun vB =>
                      Lynx.Result.bind «zero/0»
                        (fun vZ =>
                          Lynx.Result.bind (Lynx.Result.ok (Lynx.Term.function 2 0 #[]))
                            (fun _7 =>
                              Lynx.Result.bind (Lynx.Term.apply _7 #[])
                                (fun vC =>
                                  Lynx.Result.bind (Lynx.Result.ok (Lynx.Term.function 3 1 #[]))
                                    (fun _10 =>
                                      Lynx.Result.bind (Lynx.Result.ok (Lynx.Term.function 4 1 #[]))
                                        (fun _12 =>
                                          Lynx.Result.bind («make_store/1» _0)
                                            (fun vStore =>
                                              Lynx.Result.bind (Erlang.erlang.«+/2» vA vB)
                                                (fun _15 =>
                                                  Lynx.Result.bind (Erlang.erlang.«+/2» _15 vZ)
                                                    (fun _16 =>
                                                      Lynx.Result.bind (Erlang.erlang.«+/2» _16 vC)
                                                        (fun _17 =>
                                                          Lynx.Result.bind
                                                            (Lynx.Term.apply _10 #[_17])
                                                            (fun _18 =>
                                                              Lynx.Result.bind
                                                                (Lynx.Term.apply _12 #[_18])
                                                                (fun _19 =>
                                                                  Lynx.Term.apply vStore
                                                                    #[_19]))))))))))))))))

end Erlang.functions
