module

import Lynx
import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit

namespace LynxTest.Term.Order
open Lynx Lean.Order

-- Exercise recursion under bind through the ordinary public proof interface.
private def count (n : Nat) : Result :=
  if n = 0 then .ok (.integer 0)
  else do
    let value ← count (n - 1)
    Result.ofExcept (Erlang.erlang.«+/2» value (.integer 1))
partial_fixpoint monotonicity by
  intro f g below n
  dsimp only
  split
  · exact PartialOrder.rel_refl
  · exact Result.bind_mono_left _ (below _)

theorem count_returns (n : Nat) : count n = .ok (.integer n) := by
  induction n with
  | zero => rw [count.eq_def]; simp
  | succ n ih => rw [count.eq_def]; simp [ih]

private def diverge : Result := diverge
partial_fixpoint monotonicity by
  intro f g below
  exact below

-- A diverging fixed point cannot manufacture a successful return.
theorem diverge_not_success (value : Term) : diverge ≠ .ok value := by
  have post : ∀ value, diverge = .ok value → False := by
    apply diverge.fixpoint_induct (motive := fun computation => ∀ value, computation = .ok value → False)
    · exact Result.admissible_success (fun _ => False)
    · intro approximation ih
      exact ih
  exact post value

end LynxTest.Term.Order

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.Order
run_cmd LynxTest.ProofAudit.checkModule `Lynx.Term.Order
