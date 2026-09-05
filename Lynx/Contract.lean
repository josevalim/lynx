import Lynx.Term

namespace Lynx

/-! A contract accepts exactly when its translated Elixir expression returns `true`. -/
def accepts (outcome : Outcome Term) : Prop :=
  outcome = .value Term.true

/-!
For every input accepted by `pre`, the function must return normally and its
actual result must be accepted by `post`.
-/
def SatisfiesUnary
    (function : Term → Outcome Term)
    (pre : Term → Outcome Term)
    (post : Term → Term → Outcome Term) : Prop :=
  ∀ input,
    accepts (pre input) →
    ∃ result,
      function input = .value result ∧
      accepts (post input result)

end Lynx
