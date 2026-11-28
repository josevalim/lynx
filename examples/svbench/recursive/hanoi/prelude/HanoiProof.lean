module

public import Lynx

public section

namespace HanoiProof

theorem moves_ge (k : Nat) : (k : Int) + 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

end HanoiProof
