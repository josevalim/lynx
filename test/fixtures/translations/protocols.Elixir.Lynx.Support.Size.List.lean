module

public import Lynx
import Lynx.Runner.Elab
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Elixir.Lynx.Support.Size.List

section

set_option «match».ignoreUnusedAlts true

def «size/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Erlang.erlang.«length/1» _0

end

end Elixir.Lynx.Support.Size.List
