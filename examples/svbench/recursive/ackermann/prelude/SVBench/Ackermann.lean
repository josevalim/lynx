module
public import Lynx
public section

namespace SVBench.Ackermann

/-- The Ackermann function over natural numbers, structural in both arguments
so that its equations hold by definition. -/
@[expose] noncomputable def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, n => Nat.rec (motive := fun _ => Nat) (ack m 1) (fun _ r => ack m r) n

theorem ack_zero (n : Nat) : ack 0 n = n + 1 := rfl
theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := rfl
theorem ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := rfl

theorem lt_ack : ∀ m n, n < ack m n
  | 0, n => by rw [ack_zero]; omega
  | m + 1, 0 => by have := lt_ack m 1; rw [ack_succ_zero]; omega
  | m + 1, n + 1 => by
    have inner := lt_ack (m + 1) n
    have outer := lt_ack m (ack (m + 1) n)
    rw [ack_succ_succ]; omega

theorem ack_lt_succ (m n : Nat) : ack m n < ack m (n + 1) := by
  cases m with
  | zero => rw [ack_zero, ack_zero]; omega
  | succ m => rw [ack_succ_succ]; exact lt_ack m (ack (m + 1) n)

theorem ack_mono (m : Nat) {n n' : Nat} (le : n ≤ n') : ack m n ≤ ack m n' := by
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_of_lt (ack_lt_succ _ _))

theorem ack_succ_le : ∀ m n, ack m (n + 1) ≤ ack (m + 1) n
  | m, 0 => by rw [ack_succ_zero]; exact Nat.le_refl _
  | m, n + 1 => by
    have bound : n + 2 ≤ ack (m + 1) n := by
      have := ack_succ_le m n; have := lt_ack m (n + 1); omega
    rw [ack_succ_succ]; exact ack_mono m bound

theorem ack_le_succ_left (m n : Nat) : ack m n ≤ ack (m + 1) n :=
  Nat.le_trans (Nat.le_of_lt (ack_lt_succ m n)) (ack_succ_le m n)

theorem ack_two (n : Nat) : ack 2 n = 2 * n + 3 := by
  have one (n : Nat) : ack 1 n = n + 2 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have step : ack 1 (n + 1) = ack 1 n + 1 := by rw [ack_succ_succ 0 n, ack_zero]
      omega
  induction n with
  | zero => rfl
  | succ n ih =>
    have step : ack 2 (n + 1) = ack 1 (ack 2 n) := by rw [ack_succ_succ 1 n]
    rw [step, one]; omega

theorem ack_ge (m n : Nat) (two : 2 ≤ m) : 2 * n + 3 ≤ ack m n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le two
  clear two
  induction k with
  | zero => simp [ack_two]
  | succ k ih => exact Nat.le_trans ih (ack_le_succ_left (2 + k) n)

end SVBench.Ackermann
