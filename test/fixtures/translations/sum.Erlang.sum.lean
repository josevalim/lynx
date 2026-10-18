module

public import Lynx
public import Lynx.Modules.Erlang.erlang
public import Erlang.lists

@[expose] public section

namespace Erlang.sum

section

set_option «match».ignoreUnusedAlts true

def «sum/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Erlang.lists.«sum/1» _0

def «sum_singleton_requires/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Erlang.erlang.«is_integer/1» _0

def «sum_empty_ensures/0» : Except Lynx.Exception Lynx.Term := do
  let _0 ← «sum/1» Lynx.Term.nil
  Erlang.erlang.«==/2» _0 (Lynx.Term.integer 0)

def «sum_singleton_ensures/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let _1 ← «sum/1» (Lynx.Term.list [_0])
  Erlang.erlang.«==/2» _1 _0

end

end Erlang.sum
