module

public import Lynx
import Lynx.Runner.Elab

@[expose] public section

namespace Elixir.Lynx.Support.Describe.Atom

section

set_option «match».ignoreUnusedAlts true

def «describe/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  pure (Lynx.Term.tuple #[_1, _0])

end

end Elixir.Lynx.Support.Describe.Atom
