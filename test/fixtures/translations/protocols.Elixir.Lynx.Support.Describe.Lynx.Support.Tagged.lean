module

public import Lynx
import Lynx.Runner.Elab
public import Elixir.Lynx.Support.Describe.Any

@[expose] public section

namespace Elixir.Lynx.Support.Describe.Lynx.Support.Tagged

section

set_option «match».ignoreUnusedAlts true

def «describe/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Elixir.Lynx.Support.Describe.Any.«describe/2» _0 _1

end

end Elixir.Lynx.Support.Describe.Lynx.Support.Tagged
