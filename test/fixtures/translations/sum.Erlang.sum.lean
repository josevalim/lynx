module

public import Lynx
public import Lynx.Modules.Erlang.erlang
public import Erlang.lists

@[expose] public section

namespace Erlang.sum

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  def «sum/1» (_0 : Lynx.Term) : Lynx.Result :=
    Erlang.lists.«sum/1» _0

#lynx_pure
  def «sum_singleton_requires/1» (_0 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«is_integer/1» _0

#lynx_pure
  def «sum_empty_ensures/0» : Lynx.Result := do
    let _0 ← «sum/1» Lynx.Term.nil
    Erlang.erlang.«==/2» _0 (Lynx.Term.integer 0)

#lynx_pure
  def «sum_singleton_ensures/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _1 ← «sum/1» (Lynx.Term.cons _0 Lynx.Term.nil)
    Erlang.erlang.«==/2» _1 _0

end

end Erlang.sum
