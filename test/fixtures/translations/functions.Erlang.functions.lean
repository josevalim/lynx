module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.functions

section

set_option «match».ignoreUnusedAlts true

def «make/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  pure (Lynx.Term.function 0 1 #[_0])

def «$lynx_fun_0/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Erlang.erlang.«+/2» _0 _1

def «explicit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«apply/2» _0 _1

def «inc/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)

def «zero/0» : Except Lynx.Exception Lynx.Term :=
  pure (Lynx.Term.integer 0)

def «remember/1» (_0 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«put/2» (Lynx.Term.atom "last") _0

def «make_store/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  pure (Lynx.Term.function 3 1 #[_0])

def «$lynx_fun_3/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
  Erlang.erlang.«put/2» _0 _1

def «references/0» : Lynx.Result := do
  let vFirst ← Erlang.erlang.«make_ref/0»
  let vSecond ← Erlang.erlang.«make_ref/0»
  let _5 ← Lynx.Result.ofExcept (Erlang.erlang.«is_reference/1» vFirst)
  let _4 ← Lynx.Result.ofExcept (Erlang.erlang.«=:=/2» vFirst vSecond)
  let _3 ← pure (Lynx.Term.map [(vFirst, vSecond)])
  pure (Lynx.Term.tuple #[_5, _4, _3])

def «captured_closures/1» (_0 : Lynx.Term) : Lynx.Result := do
  let vF ← Lynx.Result.ofExcept («make/1» _0)
  let _2 ← Lynx.Result.ofExcept (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 10))
  let vG ← Lynx.Result.ofExcept («make/1» _2)
  let vA ← Lynx.Term.apply vF #[Lynx.Term.integer 1]
  let vB ← Lynx.Term.apply vG #[Lynx.Term.integer 2]
  Lynx.Result.ofExcept (Erlang.erlang.«+/2» vA vB)

def «zero_arity_calls/0» : Lynx.Result := do
  let vZ ← Lynx.Result.ofExcept «zero/0»
  let _1 ← pure (Lynx.Term.function 5 0 #[])
  let vC ← Lynx.Term.apply _1 #[]
  Lynx.Result.ofExcept (Erlang.erlang.«+/2» vZ vC)

def «apply_calls/1» (_0 : Lynx.Term) : Lynx.Result := do
  let vF ← Lynx.Result.ofExcept («make/1» _0)
  let vA ← «explicit/2» vF (Lynx.Term.list [Lynx.Term.integer 2])
  let _3 ← pure (Lynx.Term.function 1 1 #[])
  let _5 ← pure (Lynx.Term.function 2 1 #[])
  let vStore ← Lynx.Result.ofExcept («make_store/1» _0)
  let _8 ← Lynx.Term.apply _3 #[vA]
  let _9 ← Lynx.Term.apply _5 #[_8]
  Lynx.Term.apply vStore #[_9]

def «sequence_calls/1» (_0 : Lynx.Term) : Lynx.Result := do
  let _ ← «remember/1» _0
  pure _0

def «qualified_capture/1» (_0 : Lynx.Term) : Lynx.Result := do
  let _3 ← Lynx.Result.ofExcept («inc/1» _0)
  let _2 ← «explicit/2» (Lynx.Term.function 4 1 #[]) (Lynx.Term.list [_0])
  pure (Lynx.Term.tuple #[_3, _2])

def «$lynx_fun_4/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  «inc/1» _0

end

end Erlang.functions
