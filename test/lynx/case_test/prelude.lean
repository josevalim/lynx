module
public import Lynx
public section
namespace PreludeTest
theorem truth : True := by trivial
end PreludeTest
open Lean Elab Tactic
elab "test_partial" : tactic => do evalTactic (← `(tactic| (
  intro f g h n
  cases n <;> simp
  all_goals first | exact h _ | exact Lean.Order.PartialOrder.rel_refl)))
