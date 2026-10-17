module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.lists

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  def «sum/2» (_0 : Lynx.Term) (vSum : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.cons vH vT => do
      let _2 ← Erlang.erlang.«+/2» vSum vH
      «sum/2» vT _2
    | Lynx.Term.nil => pure vSum
    | _4 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))

#lynx_pure
  def «sum/1» (_0 : Lynx.Term) : Lynx.Result :=
    «sum/2» _0 (Lynx.Term.integer 0)

end

end Erlang.lists
