module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.lists

section

set_option «match».ignoreUnusedAlts true

def «sum/2» (_0 : Lynx.Term) (vSum : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | Lynx.Term.cons vH vT => do
    let _2 ← Erlang.erlang.«+/2» vSum vH
    «sum/2» vT _2
  | Lynx.Term.nil => pure vSum
  | _4 => Except.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))

def «sum/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  «sum/2» _0 (Lynx.Term.integer 0)

end

end Erlang.lists
