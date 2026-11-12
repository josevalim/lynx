module

public import Lynx
import Lynx.Runner.Elab

@[expose] public section

namespace Elixir.Lynx.Support.Size.Lynx.Support.Point

section

set_option «match».ignoreUnusedAlts true

def «size/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  pure (Lynx.Term.integer 2)

end

end Elixir.Lynx.Support.Size.Lynx.Support.Point
