module

public import Lynx
import Lynx.Runner.Elab

@[expose] public section

namespace Elixir.Lynx.Support.Depth.Integer

section

set_option «match».ignoreUnusedAlts true

def «depth/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  pure (Lynx.Term.integer 0)

end

end Elixir.Lynx.Support.Depth.Integer
