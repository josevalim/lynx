module

public import Lynx
import Erlang.erlang

namespace Erlang.functions

#lynx_pure
  public def «$lynx_fun_0/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«+/2» _0 _1

public def «$lynx_fun_3/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
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
    pure (Lynx.Term.function 3 1 #[_0])

public def «remember/1» (_0 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«put/2» (Lynx.Term.atom "last") _0

#lynx_pure
  public def «zero/0» : Lynx.Result :=
    pure (Lynx.Term.integer 0)

public def «apply_calls/1» (_0 : Lynx.Term) : Lynx.Result := do
  let vF ← «make/1» _0
  let vA ← «explicit/2» vF (Lynx.Term.cons (Lynx.Term.integer 2) Lynx.Term.nil)
  let _3 ← pure (Lynx.Term.function 1 1 #[])
  let _5 ← pure (Lynx.Term.function 2 1 #[])
  let vStore ← «make_store/1» _0
  let _8 ← Lynx.Term.apply _3 #[vA]
  let _9 ← Lynx.Term.apply _5 #[_8]
  Lynx.Term.apply vStore #[_9]

public def «captured_closures/1» (_0 : Lynx.Term) : Lynx.Result := do
  let vF ← «make/1» _0
  let _2 ← Erlang.erlang.«+/2» _0 (Lynx.Term.integer 10)
  let vG ← «make/1» _2
  let vA ← Lynx.Term.apply vF #[Lynx.Term.integer 1]
  let vB ← Lynx.Term.apply vG #[Lynx.Term.integer 2]
  Erlang.erlang.«+/2» vA vB

public def «sequence_calls/1» (_0 : Lynx.Term) : Lynx.Result := do
  let _ ← «remember/1» _0
  pure _0

public def «zero_arity_calls/0» : Lynx.Result := do
  let vZ ← «zero/0»
  let _1 ← pure (Lynx.Term.function 4 0 #[])
  let vC ← Lynx.Term.apply _1 #[]
  Erlang.erlang.«+/2» vZ vC

end Erlang.functions
