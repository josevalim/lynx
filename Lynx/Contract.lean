import Lynx.Term

namespace Lynx

def trueTerm : Term :=
  .atom "true"

def falseTerm : Term :=
  .atom "false"

/-! A contract accepts exactly when its translated Elixir expression returns `true`. -/
def accepts (outcome : Outcome) : Prop :=
  outcome = .value trueTerm

/-!
For every input accepted by `pre`, the function must return normally and its
actual result must be accepted by `post`.
-/
def SatisfiesUnary
    (function : Term → Outcome)
    (pre : Term → Outcome)
    (post : Term → Term → Outcome) : Prop :=
  ∀ input,
    accepts (pre input) →
    ∃ result,
      function input = .value result ∧
      accepts (post input result)

end Lynx
