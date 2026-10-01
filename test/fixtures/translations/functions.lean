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
    pure (Lynx.Term.function 0 1 #[_0])

#lynx_pure
  public def «make_store/1» (_0 : Lynx.Term) : Lynx.Result :=
    pure (Lynx.Term.function 1 1 #[_0])

public def «remember/1» (_0 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«put/2» (Lynx.Term.atom "last") _0

#lynx_pure
  public def «zero/0» : Lynx.Result :=
    pure (Lynx.Term.integer 0)

public def «run/1» (_0 : Lynx.Term) : Lynx.Result := do
  let vF ← «make/1» _0
  let _2 ← Erlang.erlang.«+/2» _0 (Lynx.Term.integer 10)
  let vG ← «make/1» _2
  let vA ← Lynx.Term.apply vF #[Lynx.Term.integer 1]
  let vB ← «explicit/2» vG (Lynx.Term.cons (Lynx.Term.integer 2) Lynx.Term.nil)
  let vZ ← «zero/0»
  let _7 ← pure (Lynx.Term.function 2 0 #[])
  let vC ← Lynx.Term.apply _7 #[]
  let _10 ← pure (Lynx.Term.function 3 1 #[])
  let _12 ← pure (Lynx.Term.function 4 1 #[])
  let vStore ← «make_store/1» _0
  let _15 ← Erlang.erlang.«+/2» vA vB
  let _16 ← Erlang.erlang.«+/2» _15 vZ
  let _17 ← Erlang.erlang.«+/2» _16 vC
  let _18 ← Lynx.Term.apply _10 #[_17]
  let _19 ← Lynx.Term.apply _12 #[_18]
  Lynx.Term.apply vStore #[_19]

end Erlang.functions
