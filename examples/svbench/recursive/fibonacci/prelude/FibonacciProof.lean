module

public import Lynx

public section

namespace FibonacciProof

/-- The Fibonacci numbers the translated function computes on naturals. -/
@[expose] def fibNat : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibNat (n + 1) + fibNat n

theorem fibNat_pos (n : Nat) (positive : 1 ≤ n) : 1 ≤ fibNat n := by
  induction n using fibNat.induct with
  | case1 => omega
  | case2 => simp [fibNat]
  | case3 n ih _ =>
    simp only [fibNat]
    have := ih (by omega)
    omega

theorem fibNat_mono {n m : Nat} (le : n ≤ m) : fibNat n ≤ fibNat m := by
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i k _
    refine Nat.le_trans ih ?_
    cases k with
    | zero => simp [fibNat]
    | succ k => simp only [fibNat]; omega

theorem fibNat_ge (n : Nat) : n ≤ fibNat n + 1 := by
  induction n using fibNat.induct with
  | case1 => simp [fibNat]
  | case2 => simp [fibNat]
  | case3 n ih _ =>
    simp only [fibNat]
    cases n with
    | zero => simp [fibNat]
    | succ n =>
      have := fibNat_pos (n + 1) (by omega)
      simp only [fibNat] at ih ⊢
      omega

end FibonacciProof
