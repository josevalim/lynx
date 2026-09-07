import Lean

namespace Lynx

/-- Treat an executable function through its specifications rather than adding
its body to `lynx_verify`'s unfolding context. This is not logical opacity:
ordinary Lean reduction and explicit unfolding remain available. -/
initialize opaqueAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `lynx_opaque
    "Use specifications instead of discovering/unfolding this function's body in lynx_verify"

end Lynx
