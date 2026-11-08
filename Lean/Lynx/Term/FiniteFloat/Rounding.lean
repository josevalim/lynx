module


/-! Facts about rounding in Lean's `Float.Model`, which comes without lemmas. -/

namespace Lynx.Term.Rounding

open Float.Model Float.Model.UnpackedFloat

/-- `em` is the floor of `y`, with round and sticky bits for the fraction:
whether it reaches one half, and whether anything else remains. -/
def Describes (y : Rat) (em : ExtendedMantissa) : Prop :=
  (em.mantissa : Rat) ≤ y ∧ y < em.mantissa + 1 ∧
  (em.roundBit = true ↔ 2 * (em.mantissa : Rat) + 1 ≤ 2 * y) ∧
  (em.stickyBit = true ↔ 2 * y ≠ 2 * em.mantissa + (if em.roundBit then 1 else 0))

theorem describes_shiftRightOne {y : Rat} {em : ExtendedMantissa} (d : Describes y em) :
    Describes (y / 2) em.shiftRightOne := by
  cases em with
  | mk m r s =>
  obtain ⟨low, high, round, sticky⟩ := d
  simp only at low high round sticky
  simp only [Describes, ExtendedMantissa.shiftRightOne]
  have half : y / 2 * 2 = y := by grind
  rcases Nat.mod_two_eq_zero_or_one m with even | odd
  · obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q := ⟨m / 2, by omega⟩
    have div : 2 * q / 2 = q := by omega
    simp only [div, even, bne_self_eq_false, Bool.false_eq_true, false_iff, ite_false,
      Rat.natCast_mul] at *
    refine ⟨by grind, by grind, by grind, ?_⟩
    cases r <;> cases s <;> simp only [Bool.false_eq_true, false_iff, true_iff,
      Bool.false_or, Bool.true_or, ite_true, ite_false] at round sticky ⊢ <;> grind
  · obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q + 1 := ⟨m / 2, by omega⟩
    have div : (2 * q + 1) / 2 = q := by omega
    simp only [div, odd, show (1 != 0) = true from rfl, true_iff, ite_true,
      Rat.natCast_mul, Rat.natCast_add] at *
    refine ⟨by grind, by grind, by grind, ?_⟩
    cases r <;> cases s <;> simp only [Bool.false_eq_true, false_iff, true_iff,
      Bool.false_or, Bool.true_or, ite_true, ite_false] at round sticky ⊢ <;> grind

theorem describes_shift {y : Rat} {em : ExtendedMantissa} (d : Describes y em) (k : Nat) :
    Describes (y / 2 ^ k) (em >>> k) := by
  induction k with
  | zero =>
    have : y / 2 ^ 0 = y := by grind
    rw [this]
    exact d
  | succ k ih =>
    have step := describes_shiftRightOne ih
    have eq : y / 2 ^ (k + 1) = y / 2 ^ k / 2 := by
      rw [Rat.pow_succ, Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc,
        Rat.mul_comm (2 : Rat)⁻¹]
    rw [eq]
    exact step

theorem describes_unique {y : Rat} {a b : ExtendedMantissa} (da : Describes y a)
    (db : Describes y b) : a = b := by
  cases a with
  | mk m r s =>
  cases b with
  | mk m' r' s' =>
  obtain ⟨low, high, round, sticky⟩ := da
  obtain ⟨low', high', round', sticky'⟩ := db
  simp only at *
  have lt : (m : Rat) < m' + 1 := by grind
  have lt' : (m' : Rat) < m + 1 := by grind
  have mm : m = m' := by
    have : m < m' + 1 := by exact_mod_cast lt
    have : m' < m + 1 := by exact_mod_cast lt'
    omega
  subst mm
  have rr : r = r' := Bool.eq_iff_iff.mpr (round.trans round'.symm)
  subst rr
  have ss : s = s' := Bool.eq_iff_iff.mpr (sticky.trans sticky'.symm)
  subst ss
  rfl

theorem two_zpow_pos (a : Int) : 0 < (2 : Rat) ^ a := Rat.zpow_pos (by decide)

theorem two_zpow_add (a b : Int) : (2 : Rat) ^ (a + b) = 2 ^ a * 2 ^ b :=
  Rat.zpow_add (by decide) a b

theorem one_le_two_pow (n : Nat) : (1 : Rat) ≤ 2 ^ n := by
  have : ((2 ^ n : Nat) : Rat) = (2 : Rat) ^ n := by simp [Rat.natCast_pow]
  rw [← this]
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  exact_mod_cast this

theorem two_zpow_le {a b : Int} (h : a ≤ b) : (2 : Rat) ^ a ≤ 2 ^ b := by
  have eq : b = a + ((b - a).toNat : Int) := by omega
  rw [eq, two_zpow_add, Rat.zpow_natCast]
  have one := one_le_two_pow (b - a).toNat
  have := Rat.mul_le_mul_of_nonneg_left one (Rat.le_of_lt (two_zpow_pos a))
  grind

theorem two_zpow_lt {a b : Int} (h : a < b) : (2 : Rat) ^ a < 2 ^ b := by
  have le := two_zpow_le (show a + 1 ≤ b by omega)
  rw [two_zpow_add, Rat.zpow_one] at le
  have := two_zpow_pos a
  grind

theorem natCast_two_pow (n : Nat) : ((2 ^ n : Nat) : Rat) = (2 : Rat) ^ (n : Int) := by
  simp [Rat.natCast_pow, Rat.zpow_natCast]

/-- `t` is the exponent the format gives `x`: at least the minimum, with `x`
below `2 ^ (t + mantissaBits)`, and with the leading bit set unless `t` is the
minimum. -/
def Good (spec : Format) (x : Rat) (t : Int) : Prop :=
  spec.minExponent ≤ t ∧ x < 2 ^ (t + spec.mantissaBits) ∧
    (t = spec.minExponent ∨ 2 ^ (t + spec.mantissaBits - 1) ≤ x)

theorem good_unique {spec : Format} {x : Rat} {t u : Int} (gt : Good spec x t)
    (gu : Good spec x u) : t = u := by
  obtain ⟨tmin, tlt, tlead⟩ := gt
  obtain ⟨umin, ult, ulead⟩ := gu
  have bits : 1 < spec.mantissaBits := by
    have := spec.hm; simp only [Format.mantissaBits]; omega
  have lt (a b : Int) (lead : 2 ^ (a + spec.mantissaBits - 1) ≤ x)
      (below : x < 2 ^ (b + spec.mantissaBits)) : a < b + 1 := by
    have : (2 : Rat) ^ (a + spec.mantissaBits - 1) < 2 ^ (b + spec.mantissaBits) := by grind
    by_cases h : a < b + 1
    · exact h
    · have := two_zpow_le (show b + spec.mantissaBits ≤ a + spec.mantissaBits - 1 by omega)
      grind
  rcases tlead with teq | tlead <;> rcases ulead with ueq | ulead
  · omega
  · have := lt u t ulead tlt; omega
  · have := lt t u tlead ult; omega
  · have := lt u t ulead tlt; have := lt t u tlead ult; omega

theorem mul_le_of_le_div {a b c : Rat} (pos : 0 < c) (h : a ≤ b / c) : a * c ≤ b := by
  have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt pos)
  have eq : b / c * c = b := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt pos), Rat.mul_one]
  grind

theorem lt_mul_of_div_lt {a b c : Rat} (pos : 0 < c) (h : b / c < a) : b < a * c := by
  have := Rat.mul_lt_mul_of_pos_right h pos
  have eq : b / c * c = b := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt pos), Rat.mul_one]
  grind

theorem good_of_describes {spec : Format} {x : Rat} {m : Nat} {e : Int} {em : ExtendedMantissa}
    (d : Describes (x / 2 ^ e) em) (hm : em.mantissa = m)
    (he : e ≤ spec.targetExponent (totalExponent m e)) :
    Good spec x (spec.targetExponent (totalExponent m e)) := by
  obtain ⟨low, high, -, -⟩ := d
  rw [hm] at low high
  have low := mul_le_of_le_div (two_zpow_pos e) low
  have high := lt_mul_of_div_lt (two_zpow_pos e) high
  have bits : 1 < spec.mantissaBits := by
    have := spec.hm; simp only [Format.mantissaBits]; omega
  simp only [Format.targetExponent, totalExponent] at he ⊢
  refine ⟨Int.le_max_right _ _, ?_, ?_⟩
  · have above : m + 1 ≤ 2 ^ (m.log2 + 1) := Nat.lt_log2_self
    have above : ((m + 1 : Nat) : Rat) ≤ ((2 ^ (m.log2 + 1) : Nat) : Rat) := by exact_mod_cast above
    rw [natCast_two_pow, Rat.natCast_add] at above
    have := Rat.mul_le_mul_of_nonneg_right above (Rat.le_of_lt (two_zpow_pos e))
    rw [← two_zpow_add] at this
    have := two_zpow_le (show ((m.log2 + 1 : Nat) : Int) + e ≤
      max (↑m.log2 + 1 + e - ↑spec.mantissaBits) spec.minExponent + ↑spec.mantissaBits by omega)
    grind
  · by_cases zero : m = 0
    · left
      subst zero
      simp only [Nat.log2_zero] at he ⊢
      omega
    · by_cases eq : max (↑m.log2 + 1 + e - ↑spec.mantissaBits) spec.minExponent = spec.minExponent
      · exact Or.inl eq
      · right
        have teq : max (↑m.log2 + 1 + e - ↑spec.mantissaBits) spec.minExponent + ↑spec.mantissaBits - 1 =
            ((m.log2 : Nat) : Int) + e := by omega
        rw [teq, two_zpow_add]
        have below : 2 ^ m.log2 ≤ m := Nat.log2_self_le zero
        have below : ((2 ^ m.log2 : Nat) : Rat) ≤ (m : Rat) := by exact_mod_cast below
        rw [natCast_two_pow] at below
        have := Rat.mul_le_mul_of_nonneg_right below (Rat.le_of_lt (two_zpow_pos e))
        grind

theorem mantissa_ofMantissaAndAccuracy (m : Nat) (a : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m a).mantissa = m := by
  unfold ExtendedMantissa.ofMantissaAndAccuracy
  split <;> rfl

/-- Rounding depends only on the value its input describes, provided the input
exponent leaves room for every mantissa bit. -/
theorem roundWithAccuracy_congr {spec : Format} {sign : Sign} {x : Rat}
    {m₁ m₂ : Nat} {e₁ e₂ : Int} {a₁ a₂ : Accuracy}
    (d₁ : Describes (x / 2 ^ e₁) (.ofMantissaAndAccuracy m₁ a₁))
    (d₂ : Describes (x / 2 ^ e₂) (.ofMantissaAndAccuracy m₂ a₂))
    (h₁ : e₁ ≤ spec.targetExponent (totalExponent m₁ e₁))
    (h₂ : e₂ ≤ spec.targetExponent (totalExponent m₂ e₂)) :
    roundWithAccuracy spec sign m₁ e₁ a₁ = roundWithAccuracy spec sign m₂ e₂ a₂ := by
  have same := good_unique (good_of_describes d₁ (mantissa_ofMantissaAndAccuracy m₁ a₁) h₁)
    (good_of_describes d₂ (mantissa_ofMantissaAndAccuracy m₂ a₂) h₂)
  have shift : shiftToTargetExponent spec m₁ e₁ a₁ = shiftToTargetExponent spec m₂ e₂ a₂ := by
    simp only [shiftToTargetExponent, shiftToExponent]
    generalize spec.targetExponent (totalExponent m₁ e₁) = t at same h₁ ⊢
    subst same
    have scale (e : Int) (h : e ≤ spec.targetExponent (totalExponent m₂ e₂)) :
        x / 2 ^ e / 2 ^ (spec.targetExponent (totalExponent m₂ e₂) - e).toNat =
          x / 2 ^ (spec.targetExponent (totalExponent m₂ e₂)) := by
      have eq : spec.targetExponent (totalExponent m₂ e₂) =
          e + (((spec.targetExponent (totalExponent m₂ e₂) - e).toNat : Nat) : Int) := by omega
      conv => rhs; rw [eq, two_zpow_add, Rat.zpow_natCast]
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc,
        Rat.mul_comm (2 ^ (spec.targetExponent (totalExponent m₂ e₂) - e).toNat)⁻¹]
    have s₁ := describes_shift d₁ (spec.targetExponent (totalExponent m₂ e₂) - e₁).toNat
    have s₂ := describes_shift d₂ (spec.targetExponent (totalExponent m₂ e₂) - e₂).toNat
    rw [scale e₁ h₁] at s₁
    rw [scale e₂ h₂] at s₂
    rw [describes_unique s₁ s₂]
    congr 1
    omega
  simp only [roundWithAccuracy, shift]

theorem describes_exact (n : Nat) : Describes n (.ofMantissaAndAccuracy n .exact) := by
  simp only [Describes, ExtendedMantissa.ofMantissaAndAccuracy]
  refine ⟨Rat.le_refl, by grind, ?_, ?_⟩ <;> simp <;> grind

/-- The quotient and remainder of `n / d` describe the fraction. -/
theorem describes_fraction (n d : Nat) (pos : 0 < d) :
    Describes ((n : Rat) / d) (.ofMantissaAndAccuracy (n / d) (accuracyOfFraction (n % d) d)) := by
  have split : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
  have lt : n % d < d := Nat.mod_lt _ pos
  generalize n / d = q at split
  generalize n % d = r at split lt
  subst split
  have dpos : (0 : Rat) < d := by exact_mod_cast pos
  have value : ((d * q + r : Nat) : Rat) / d = q + (r : Rat) / d := by
    rw [Rat.natCast_add, Rat.natCast_mul, Rat.div_def, Rat.add_mul, Rat.mul_comm (d : Rat),
      Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt dpos), Rat.mul_one, ← Rat.div_def]
  rw [value]
  have rlt : (r : Rat) / d < 1 := by
    rw [Rat.div_lt_iff dpos]; have : (r : Rat) < d := by exact_mod_cast lt
    grind
  have rnn : 0 ≤ (r : Rat) / d := by
    rw [Rat.div_def]; exact Rat.mul_nonneg (by exact_mod_cast Nat.zero_le r)
      (Rat.le_of_lt (Rat.inv_pos.mpr dpos))
  -- Twice the fraction against one.
  have twice : (2 * (r : Rat) / d < 1 ↔ 2 * r < d) ∧ (2 * (r : Rat) / d = 1 ↔ 2 * r = d) := by
    have mul : 2 * (r : Rat) / d * d = 2 * r := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt dpos), Rat.mul_one]
    constructor
    · rw [Rat.div_lt_iff dpos]
      constructor
      · intro h; have : ((2 * r : Nat) : Rat) < d := by rw [Rat.natCast_mul]; grind
        exact_mod_cast this
      · intro h; have : ((2 * r : Nat) : Rat) < d := by exact_mod_cast h
        rw [Rat.natCast_mul] at this; grind
    · constructor
      · intro h; have : ((2 * r : Nat) : Rat) = d := by rw [Rat.natCast_mul]; grind
        exact_mod_cast this
      · intro h; have : ((2 * r : Nat) : Rat) = d := by exact_mod_cast h
        rw [Rat.natCast_mul] at this
        have : 2 * (r : Rat) / d = d / d := by grind
        rw [this, Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt dpos)]
  have frac : 2 * ((r : Rat) / d) = 2 * (r : Rat) / d := by
    rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]
  simp only [Describes, accuracyOfFraction]
  by_cases zero : r = 0
  · subst zero
    simp only [ite_eq_left, ExtendedMantissa.ofMantissaAndAccuracy]
    refine ⟨by grind, by grind, ?_, ?_⟩ <;> simp <;> grind
  · simp only [ite_eq_right zero]
    have rpos : (0 : Rat) < (r : Rat) / d := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by exact_mod_cast Nat.pos_of_ne_zero zero) (Rat.inv_pos.mpr dpos)
    rcases Nat.lt_trichotomy (2 * r) d with less | equal | greater
    · have c : compare (2 * r) d = .lt := Nat.compare_eq_lt.mpr less
      have := twice.1.mpr less
      simp only [c, ExtendedMantissa.ofMantissaAndAccuracy]
      refine ⟨by grind, by grind, ?_, ?_⟩ <;> simp <;> grind
    · have c : compare (2 * r) d = .eq := Nat.compare_eq_eq.mpr equal
      have := twice.2.mpr equal
      simp only [c, ExtendedMantissa.ofMantissaAndAccuracy]
      refine ⟨by grind, by grind, ?_, ?_⟩ <;> simp <;> grind
    · have c : compare (2 * r) d = .gt := Nat.compare_eq_gt.mpr greater
      have h1 : ¬ 2 * r < d := by omega
      have h2 : ¬ 2 * r = d := by omega
      have := mt twice.1.mp h1
      have := mt twice.2.mp h2
      simp only [c, ExtendedMantissa.ofMantissaAndAccuracy]
      refine ⟨by grind, by grind, ?_, ?_⟩ <;> simp <;> grind

theorem log2_le_of_pow_le {n k : Nat} (h : 2 ^ k ≤ n) : k ≤ n.log2 :=
  (Nat.le_log2 (by have := Nat.one_le_two_pow (n := k); omega)).mpr h

/-- An input to `roundWithAccuracy` that describes `x` and leaves room for every
mantissa bit. -/
def Input (spec : Format) (x : Rat) (m : Nat) (e : Int) (a : Accuracy) : Prop :=
  Describes (x / 2 ^ e) (.ofMantissaAndAccuracy m a) ∧ e ≤ spec.targetExponent (totalExponent m e)

theorem mul_input {spec : Format} {m k : Nat} (hm : m ≠ 0) :
    Input spec ((m : Rat) * 10 ^ (k : Int)) ((m <<< spec.mantissaBits) * 10 ^ k)
      (-spec.mantissaBits + 0) .exact := by
  have value : (m : Rat) * 10 ^ (k : Int) / 2 ^ (-(spec.mantissaBits : Int) + 0) =
      (((m <<< spec.mantissaBits) * 10 ^ k : Nat) : Rat) := by
    rw [Int.add_zero, Rat.zpow_neg, Rat.zpow_natCast, Rat.zpow_natCast, Nat.shiftLeft_eq,
      Rat.natCast_mul, Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_pow, Rat.div_def, Rat.inv_inv]
    grind
  refine ⟨by rw [value]; exact describes_exact _, ?_⟩
  have big : 2 ^ spec.mantissaBits ≤ (m <<< spec.mantissaBits) * 10 ^ k := by
    rw [Nat.shiftLeft_eq]
    have : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by decide)
    have : 2 ^ spec.mantissaBits ≤ m * 2 ^ spec.mantissaBits :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm)
    exact Nat.le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  have := log2_le_of_pow_le big
  simp only [Format.targetExponent, totalExponent]
  omega

theorem div_input {spec : Format} {m k : Nat} (hm : m ≠ 0) :
    let t := min (0 - 0) (spec.targetExponent (totalExponent m 0 - totalExponent (10 ^ k) 0))
    let n := m <<< (0 - 0 - t).toNat
    Input spec ((m : Rat) * 10 ^ (-(k : Int))) (n / 10 ^ k) t
      (accuracyOfFraction (n % 10 ^ k) (10 ^ k)) := by
  intro t n
  have tle : t ≤ 0 := Int.min_le_left _ _
  have dpos : 0 < 10 ^ k := Nat.pow_pos (by decide)
  have value : (m : Rat) * 10 ^ (-(k : Int)) / 2 ^ t = (n : Rat) / ((10 ^ k : Nat) : Rat) := by
    have teq : t = -((0 - 0 - t).toNat : Int) := by omega
    conv => lhs; rw [teq]
    simp only [n]
    rw [Rat.zpow_neg, Rat.zpow_neg, Rat.zpow_natCast, Rat.zpow_natCast, Nat.shiftLeft_eq,
      Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_pow, Rat.div_def, Rat.div_def, Rat.inv_inv]
    grind
  refine ⟨by rw [value]; exact describes_fraction n (10 ^ k) dpos, ?_⟩
  have tdef : t = min 0 (max ((m.log2 : Int) - (10 ^ k).log2 - spec.mantissaBits)
      spec.minExponent) := by
    simp only [t, Format.targetExponent, totalExponent]; omega
  simp only [Format.targetExponent, totalExponent]
  by_cases capped : max ((m.log2 : Int) - (10 ^ k).log2 - spec.mantissaBits)
      spec.minExponent = spec.minExponent
  · omega
  · -- The shift leaves at least `mantissaBits` bits in the quotient.
    have bits : 1 ≤ spec.mantissaBits := by simp only [Format.mantissaBits]; omega
    have shift : spec.mantissaBits + (10 ^ k).log2 ≤ m.log2 + (0 - 0 - t).toNat := by omega
    have low : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm
    have high : 10 ^ k < 2 ^ ((10 ^ k).log2 + 1) := Nat.lt_log2_self
    have enough : 2 ^ (spec.mantissaBits - 1) * 10 ^ k ≤ n := by
      simp only [n, Nat.shiftLeft_eq]
      calc 2 ^ (spec.mantissaBits - 1) * 10 ^ k
          ≤ 2 ^ (spec.mantissaBits - 1) * 2 ^ ((10 ^ k).log2 + 1) :=
            Nat.mul_le_mul_left _ (Nat.le_of_lt high)
        _ = 2 ^ (spec.mantissaBits + (10 ^ k).log2) := by
            rw [← Nat.pow_add]; congr 1; omega
        _ ≤ 2 ^ (m.log2 + (0 - 0 - t).toNat) := Nat.pow_le_pow_right (by decide) shift
        _ = 2 ^ m.log2 * 2 ^ (0 - 0 - t).toNat := Nat.pow_add _ _ _
        _ ≤ m * 2 ^ (0 - 0 - t).toNat := Nat.mul_le_mul_right _ low
    have quotient : 2 ^ (spec.mantissaBits - 1) ≤ n / 10 ^ k := (Nat.le_div_iff_mul_le dpos).mpr enough
    have := log2_le_of_pow_le quotient
    omega

/-- Away from its overflow and underflow shortcuts, `ofScientific` rounds an
input describing `m * 10 ^ e`. -/
theorem ofScientific_regular {spec : Format} {m : Nat} {e : Int} (hm : m ≠ 0)
    (big : ¬e > 2 ^ spec.exponentBits) (small : ¬e < -((2 ^ spec.exponentBits : Int) + m.log2)) :
    ∃ n t a, Input spec ((m : Rat) * 10 ^ e) n t a ∧
      UnpackedFloat.ofScientific spec m e = roundWithAccuracy spec .positive n t a := by
  rw [UnpackedFloat.ofScientific, dite_eq_right hm, ite_eq_right big, ite_eq_right small]
  by_cases nonneg : 0 ≤ e
  · rw [ite_eq_left nonneg]
    have input := mul_input (spec := spec) (k := e.toNat) hm
    rw [show ((e.toNat : Nat) : Int) = e by omega] at input
    exact ⟨_, _, _, input, rfl⟩
  · rw [ite_eq_right nonneg]
    have input := div_input (spec := spec) (k := (-e).toNat) hm
    rw [show -(((-e).toNat : Nat) : Int) = e by omega] at input
    exact ⟨_, _, _, input, rfl⟩

/-- The second stage of `roundWithAccuracy`: round the shifted mantissa, then
renormalize if rounding carried into a new bit. -/
def finish (spec : Format) (sign : Sign) (em : ExtendedMantissa) (e : Int) : UnpackedFloat :=
  let (fem, fe) := shiftToTargetExponent spec em.roundedMantissa e .exact
  if h : fem.mantissa = 0 then .zero sign else .finite sign fem.mantissa fe (Nat.pos_of_ne_zero h)

theorem roundWithAccuracy_finish (spec : Format) (sign : Sign) (n : Nat) (t : Int) (a : Accuracy) :
    roundWithAccuracy spec sign n t a =
      finish spec sign (shiftToTargetExponent spec n t a).1 (shiftToTargetExponent spec n t a).2 :=
  rfl

theorem shift_mantissa (em : ExtendedMantissa) (k : Nat) : (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
    show (ExtendedMantissa.shiftRightOne (em >>> k)).mantissa = _
    simp only [ExtendedMantissa.shiftRightOne, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- The first stage of rounding an input shifts to the exponent the format gives its value. -/
theorem shape {spec : Format} {x : Rat} {n : Nat} {t : Int} {a : Accuracy}
    (input : Input spec x n t a) :
    Describes (x / 2 ^ spec.targetExponent (totalExponent n t))
        (shiftToTargetExponent spec n t a).1 ∧
      (shiftToTargetExponent spec n t a).2 = spec.targetExponent (totalExponent n t) ∧
      Good spec x (spec.targetExponent (totalExponent n t)) := by
  obtain ⟨d, h⟩ := input
  refine ⟨?_, ?_, good_of_describes d (mantissa_ofMantissaAndAccuracy n a) h⟩
  · simp only [shiftToTargetExponent, shiftToExponent]
    have eq : spec.targetExponent (totalExponent n t) =
        t + (((spec.targetExponent (totalExponent n t) - t).toNat : Nat) : Int) := by omega
    have := describes_shift d (spec.targetExponent (totalExponent n t) - t).toNat
    have scale : x / 2 ^ t / 2 ^ (spec.targetExponent (totalExponent n t) - t).toNat =
        x / 2 ^ spec.targetExponent (totalExponent n t) := by
      conv => rhs; rw [eq, two_zpow_add, Rat.zpow_natCast]
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc,
        Rat.mul_comm (2 ^ (spec.targetExponent (totalExponent n t) - t).toNat)⁻¹]
    rwa [scale] at this
  · simp only [shiftToTargetExponent, shiftToExponent]
    omega

theorem le_roundedMantissa (em : ExtendedMantissa) : em.mantissa ≤ em.roundedMantissa := by
  obtain ⟨m, r, st⟩ := em
  cases r <;> cases st <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]

theorem finish_finite {spec : Format} {sign : Sign} {em : ExtendedMantissa} {e : Int}
    (pos : 1 ≤ em.mantissa) (he : spec.minExponent ≤ e) :
    ∃ m fe h, finish spec sign em e = .finite sign m fe h ∧ e ≤ fe := by
  have r := le_roundedMantissa em
  have k : (spec.targetExponent (totalExponent em.roundedMantissa e) - e).toNat ≤
      em.roundedMantissa.log2 := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits]
    omega
  have nonzero : (shiftToTargetExponent spec em.roundedMantissa e .exact).1.mantissa ≠ 0 := by
    simp only [shiftToTargetExponent, shiftToExponent]
    rw [shift_mantissa, mantissa_ofMantissaAndAccuracy]
    have : 2 ^ (spec.targetExponent (totalExponent em.roundedMantissa e) - e).toNat ≤
        em.roundedMantissa :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) k) (Nat.log2_self_le (by omega))
    have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [Nat.one_mul]; exact this)
    omega
  have grows : e ≤ (shiftToTargetExponent spec em.roundedMantissa e .exact).2 := by
    simp only [shiftToTargetExponent, shiftToExponent]
    omega
  simp only [finish]
  generalize shiftToTargetExponent spec em.roundedMantissa e .exact = p at nonzero grows
  obtain ⟨fem, fe⟩ := p
  simp only at nonzero grows ⊢
  rw [dite_eq_right nonzero]
  exact ⟨_, _, Nat.pos_of_ne_zero nonzero, rfl, grows⟩

theorem finish_zero {spec : Format} {sign : Sign} {em : ExtendedMantissa} {e : Int}
    (zero : em.mantissa = 0) (round : em.roundBit = false) : finish spec sign em e = .zero sign := by
  obtain ⟨m, r, st⟩ := em
  simp only at zero round
  subst zero round
  have rounded : ExtendedMantissa.roundedMantissa ⟨0, false, st⟩ = 0 := by
    cases st <;> rfl
  simp only [finish, rounded, shiftToTargetExponent, shiftToExponent]
  rw [dite_eq_left (by rw [shift_mantissa, mantissa_ofMantissaAndAccuracy]; simp)]

theorem minExponent_binary64 : Format.binary64.minExponent = -1074 := by decide

/-- Values from `2 ^ 1024` round past the largest finite binary64 value. -/
theorem pack_overflow {sign : Sign} {x : Rat} {n : Nat} {t : Int} {a : Accuracy}
    (input : Input .binary64 x n t a) (big : 2 ^ (1024 : Int) ≤ x) :
    UnpackedFloat.pack .binary64 (roundWithAccuracy .binary64 sign n t a) =
      packedInfinity .binary64 sign := by
  obtain ⟨d, eq, good⟩ := shape input
  rw [roundWithAccuracy_finish, eq]
  generalize (shiftToTargetExponent .binary64 n t a).1 = em at d
  generalize Format.binary64.targetExponent (totalExponent n t) = t' at d good
  obtain ⟨tmin, below, lead⟩ := good
  have bits : Format.binary64.mantissaBits = 53 := rfl
  rw [bits] at below lead
  have large : 972 ≤ t' := by
    by_cases h : 972 ≤ t'
    · exact h
    · have := two_zpow_le (show t' + ((53 : Nat) : Int) ≤ 1024 by omega)
      grind
  have lead : 2 ^ (t' + ((53 : Nat) : Int) - 1) ≤ x := by
    rcases lead with h | h
    · rw [minExponent_binary64] at h; omega
    · exact h
  obtain ⟨low, high, -, -⟩ := d
  have pos : 1 ≤ em.mantissa := by
    have scaled : (1 : Rat) ≤ x / 2 ^ t' := by
      rw [show t' + ((53 : Nat) : Int) - 1 = t' + 52 by omega, two_zpow_add] at lead
      have one := two_zpow_le (show (0 : Int) ≤ 52 by omega)
      rw [Rat.zpow_zero] at one
      have p := two_zpow_pos t'
      have : 2 ^ t' ≤ x := by
        have := Rat.mul_le_mul_of_nonneg_left one (Rat.le_of_lt p)
        grind
      have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt (Rat.inv_pos.mpr p))
      rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt p), ← Rat.div_def] at this
      exact this
    have : (0 : Rat) < em.mantissa := by grind
    have : 0 < em.mantissa := by exact_mod_cast this
    omega
  obtain ⟨m, fe, h, eq, le⟩ := finish_finite (spec := .binary64) (sign := sign) pos tmin
  rw [eq]
  simp only [UnpackedFloat.pack]
  rw [ite_eq_left (by
    simp only [Format.exponentBias]
    omega)]

/-- Values below half the smallest subnormal round to zero. -/
theorem round_underflow {sign : Sign} {x : Rat} {n : Nat} {t : Int} {a : Accuracy}
    (input : Input .binary64 x n t a) (small : x < 2 ^ (-1075 : Int)) :
    roundWithAccuracy .binary64 sign n t a = .zero sign := by
  obtain ⟨d, eq, good⟩ := shape input
  rw [roundWithAccuracy_finish, eq]
  generalize (shiftToTargetExponent .binary64 n t a).1 = em at d
  generalize Format.binary64.targetExponent (totalExponent n t) = t' at d good
  obtain ⟨tmin, -, lead⟩ := good
  rw [minExponent_binary64] at tmin lead
  have bits : Format.binary64.mantissaBits = 53 := rfl
  rw [bits] at lead
  have teq : t' = -1074 := by
    rcases lead with h | h
    · exact h
    · by_cases low : t' + ((53 : Nat) : Int) - 1 < -1075
      · omega
      · have := two_zpow_le (show (-1075 : Int) ≤ t' + ((53 : Nat) : Int) - 1 by omega)
        grind
  subst teq
  obtain ⟨low, high, round, -⟩ := d
  have half : x / 2 ^ (-1074 : Int) < 1 / 2 := by
    have p := two_zpow_pos (-1074)
    have eq : (2 : Rat) ^ (-1075 : Int) = 2 ^ (-1074 : Int) / 2 := by
      rw [show (-1074 : Int) = -1075 + 1 by omega, Rat.zpow_add_one (by decide)]
      grind
    rw [Rat.div_lt_iff p]
    grind
  have zero : em.mantissa = 0 := by
    have : (em.mantissa : Rat) < 1 := by grind
    have : em.mantissa < 1 := by exact_mod_cast this
    omega
  have notRound : em.roundBit = false := by
    cases h : em.roundBit
    · rfl
    · have := round.mp h
      rw [zero] at this
      grind
  exact finish_zero zero notRound

theorem two_pow_le_scaled {m n k : Nat} (hm : m ≠ 0) (h : n ≤ k) :
    (2 : Rat) ^ (n : Int) ≤ (m : Rat) * 10 ^ (k : Int) := by
  have nat : 2 ^ n ≤ m * 10 ^ k :=
    calc 2 ^ n ≤ 10 ^ n := Nat.pow_le_pow_left (by decide) _
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) h
      _ ≤ m * 10 ^ k := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm)
  have cast : ((2 ^ n : Nat) : Rat) ≤ ((m * 10 ^ k : Nat) : Rat) := Rat.natCast_le_natCast.mpr nat
  rw [natCast_two_pow, Rat.natCast_mul, Rat.natCast_pow] at cast
  rwa [Rat.zpow_natCast]

theorem scaled_lt_two_pow {m n k : Nat} (h : m.log2 + 1 + n ≤ k) :
    (m : Rat) * 10 ^ (-(k : Int)) < 2 ^ (-(n : Int)) := by
  have nat : m * 2 ^ n < 10 ^ k :=
    calc m * 2 ^ n < 2 ^ (m.log2 + 1) * 2 ^ n :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
      _ = 2 ^ (m.log2 + 1 + n) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h
      _ ≤ 10 ^ k := Nat.pow_le_pow_left (by decide) _
  have cast : ((m * 2 ^ n : Nat) : Rat) < ((10 ^ k : Nat) : Rat) := Rat.natCast_lt_natCast.mpr nat
  rw [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_pow] at cast
  rw [Rat.zpow_neg, Rat.zpow_natCast, Rat.zpow_neg, Rat.zpow_natCast]
  have pa : (0 : Rat) < 10 ^ k := Rat.pow_pos (by decide)
  have pb : (0 : Rat) < 2 ^ n := Rat.pow_pos (by decide)
  generalize (10 : Rat) ^ k = a at cast pa ⊢
  generalize (2 : Rat) ^ n = b at cast pb ⊢
  apply Rat.lt_of_mul_lt_mul_right (c := a * b) _ (Rat.le_of_lt (Rat.mul_pos pa pb))
  have l : (m : Rat) * a⁻¹ * (a * b) = m * b := by
    rw [Rat.mul_assoc, ← Rat.mul_assoc a⁻¹, Rat.inv_mul_cancel _ (Rat.ne_of_gt pa), Rat.one_mul]
  have r : b⁻¹ * (a * b) = a := by
    rw [Rat.mul_comm a, ← Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt pb), Rat.one_mul]
  rw [l, r]
  exact cast

theorem overflow_bound {m : Nat} {e : Int} (hm : m ≠ 0) (big : e > 2 ^ Format.binary64.exponentBits) :
    2 ^ (1024 : Int) ≤ (m : Rat) * 10 ^ e := by
  have bits : Format.binary64.exponentBits = 11 := rfl
  rw [bits] at big
  have := two_pow_le_scaled (n := 1024) (k := e.toNat) hm (by omega)
  rwa [show ((e.toNat : Nat) : Int) = e by omega] at this

theorem underflow_bound {m : Nat} {e : Int}
    (small : e < -((2 ^ Format.binary64.exponentBits : Int) + m.log2)) :
    (m : Rat) * 10 ^ e < 2 ^ (-1075 : Int) := by
  have bits : Format.binary64.exponentBits = 11 := rfl
  rw [bits] at small
  have := scaled_lt_two_pow (m := m) (n := 1075) (k := (-e).toNat) (by omega)
  rwa [show -(((-e).toNat : Nat) : Int) = e by omega] at this

/-- `ofScientific` away from zero: an overflow, an underflow, or the rounding of
an input describing the value. -/
theorem ofScientific_cases {m : Nat} {e : Int} (hm : m ≠ 0) :
    (2 ^ (1024 : Int) ≤ (m : Rat) * 10 ^ e ∧
        UnpackedFloat.ofScientific .binary64 m e = .infinity .positive) ∨
      ((m : Rat) * 10 ^ e < 2 ^ (-1075 : Int) ∧
        UnpackedFloat.ofScientific .binary64 m e = .zero .positive) ∨
      ∃ n t a, Input .binary64 ((m : Rat) * 10 ^ e) n t a ∧
        UnpackedFloat.ofScientific .binary64 m e = roundWithAccuracy .binary64 .positive n t a := by
  by_cases big : e > 2 ^ Format.binary64.exponentBits
  · left
    refine ⟨overflow_bound hm big, ?_⟩
    rw [UnpackedFloat.ofScientific, dite_eq_right hm, ite_eq_left big]
  · by_cases small : e < -((2 ^ Format.binary64.exponentBits : Int) + m.log2)
    · right; left
      refine ⟨underflow_bound small, ?_⟩
      rw [UnpackedFloat.ofScientific, dite_eq_right hm, ite_eq_right big, ite_eq_left small]
    · right; right
      exact ofScientific_regular hm big small

theorem ofScientific_zero (e : Int) : UnpackedFloat.ofScientific .binary64 0 e = .zero .positive := by
  rw [UnpackedFloat.ofScientific, dite_eq_left rfl]

theorem pack_ofScientific_congr {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h : (m₁ : Rat) * 10 ^ e₁ = m₂ * 10 ^ e₂) :
    UnpackedFloat.pack .binary64 (UnpackedFloat.ofScientific .binary64 m₁ e₁) =
      UnpackedFloat.pack .binary64 (UnpackedFloat.ofScientific .binary64 m₂ e₂) := by
  have p₁ : (0 : Rat) < 10 ^ e₁ := Rat.zpow_pos (by decide)
  have p₂ : (0 : Rat) < 10 ^ e₂ := Rat.zpow_pos (by decide)
  by_cases z₁ : m₁ = 0
  · have z₂ : m₂ = 0 := by
      subst z₁
      have : (m₂ : Rat) * 10 ^ e₂ = 0 := by grind
      rcases Rat.mul_eq_zero.mp this with h | h
      · exact_mod_cast h
      · grind
    subst z₁ z₂
    rw [ofScientific_zero, ofScientific_zero]
  · have z₂ : m₂ ≠ 0 := by
      intro z₂
      subst z₂
      have : (m₁ : Rat) * 10 ^ e₁ = 0 := by grind
      rcases Rat.mul_eq_zero.mp this with h | h
      · exact z₁ (by exact_mod_cast h)
      · grind
    have apart : (2 : Rat) ^ (-1075 : Int) < 2 ^ (1024 : Int) := two_zpow_lt (by omega)
    have c₁ := ofScientific_cases (e := e₁) z₁
    have c₂ := ofScientific_cases (e := e₂) z₂
    rw [h] at c₁
    generalize (m₂ : Rat) * 10 ^ e₂ = x at c₁ c₂
    rcases c₁ with ⟨b₁, eq₁⟩ | ⟨b₁, eq₁⟩ | ⟨n₁, t₁, a₁, i₁, eq₁⟩ <;>
    rcases c₂ with ⟨b₂, eq₂⟩ | ⟨b₂, eq₂⟩ | ⟨n₂, t₂, a₂, i₂, eq₂⟩ <;>
    rw [eq₁, eq₂]
    · exfalso; grind
    · exact (pack_overflow i₂ b₁).symm
    · exfalso; grind
    · rw [round_underflow i₂ b₁]
    · exact pack_overflow i₁ b₂
    · rw [round_underflow i₁ b₂]
    · rw [roundWithAccuracy_congr i₁.1 i₂.1 i₁.2 i₂.2]

/-- `Float.Model.ofScientific m e` depends only on the value `m * 10 ^ e`. -/
public theorem model_ofScientific_congr {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h : (m₁ : Rat) * 10 ^ e₁ = m₂ * 10 ^ e₂) :
    Float.Model.ofScientific m₁ e₁ = Float.Model.ofScientific m₂ e₂ := by
  simp only [Float.Model.ofScientific, Float.Model.pack, pack_ofScientific_congr h]

theorem toNat_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    (packComponents .binary64 s e m).toNat = s.toBitVec.toNat * 2 ^ 63 + e.toNat * 2 ^ 52 + m.toNat := by
  simp only [packComponents, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt m.isLt, ← Nat.shiftLeft_add_eq_or_of_lt e.isLt]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]

theorem pack_normal {F : Nat} {E : Int} (h : 0 < F) (low : 2 ^ 52 ≤ F) (high : F < 2 ^ 53)
    (emin : -1074 ≤ E) (emax : E ≤ 971) :
    (UnpackedFloat.pack .binary64 (.finite .positive F E h)).toNat =
      (E + 1075).toNat * 2 ^ 52 + (F - 2 ^ 52) := by
  have log : F.log2 = 52 := by
    have a := (Nat.le_log2 (k := 52) (by omega)).mpr low
    have b := (Nat.log2_lt (k := 53) (by omega)).mpr high
    omega
  simp only [UnpackedFloat.pack, log]
  have bias : Format.binary64.exponentBias = 1023 := by decide
  rw [bias, ite_eq_right (by omega), ite_eq_left (by simp only [Format.mantissaBits]), toNat_packComponents]
  simp only [Sign.toBitVec, BitVec.toNat_ofNat]
  omega

theorem pack_subnormal {F : Nat} (h : 0 < F) (high : F < 2 ^ 52) :
    (UnpackedFloat.pack .binary64 (.finite .positive F (-1074) h)).toNat = F := by
  have log : F.log2 < 52 := (Nat.log2_lt (by omega)).mpr high
  simp only [UnpackedFloat.pack]
  have bias : Format.binary64.exponentBias = 1023 := by decide
  rw [bias, ite_eq_right (by omega), ite_eq_right (by simp only [Format.mantissaBits]; omega), toNat_packComponents]
  simp only [Sign.toBitVec, BitVec.toNat_ofNat]
  omega

theorem fields (b : BitVec 64) :
    (unpackMantissa (spec := .binary64) b).toNat = b.toNat % 2 ^ 52 ∧
    (unpackExponent (spec := .binary64) b).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 ∧
    (unpackSign (spec := .binary64) b).toNat = b.toNat / 2 ^ 63 % 2 := by
  simp only [unpackMantissa, unpackExponent, unpackSign, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  simp

/-- Negating a finite value flips its sign bit. -/
public theorem toNat_neg (a : Float.Model) (finite : a.toBits.toNat / 2 ^ 52 % 2048 < 2047) :
    a.neg.toBits.toNat = (a.toBits.toNat + 2 ^ 63) % 2 ^ 64 := by
  have lt := a.toBits.toNat_lt
  have bv : a.toBits.toBitVec.toNat = a.toBits.toNat := rfl
  simp only [Float.Model.neg, Float.Model.pack, Float.Model.unpack, UInt64.toNat_ofBitVec]
  generalize a.toBits.toBitVec = b at bv
  obtain ⟨fm, fe, fs⟩ := fields b
  rw [bv] at fm fe fs
  generalize a.toBits.toNat = N at *
  have bias : Format.binary64.exponentBias = 1023 := by decide
  have sign : (-(Sign.ofBitVec (unpackSign (spec := .binary64) b))).toBitVec.toNat =
      1 - N / 2 ^ 63 % 2 := by
    simp only [Sign.ofBitVec]
    by_cases h : unpackSign (spec := .binary64) b = 0#1
    · rw [ite_eq_left h]; rw [h] at fs; simp at fs; simp only [Sign.toBitVec]; simp; omega
    · rw [ite_eq_right h]
      have : (unpackSign (spec := .binary64) b).toNat ≠ 0 := by
        intro z; exact h (BitVec.eq_of_toNat_eq (by simp [z]))
      simp only [Sign.toBitVec]; simp; omega
  have notInf : ¬unpackExponent (spec := .binary64) b = -1#11 := by
    intro h; rw [h] at fe; simp at fe; omega
  simp only [UnpackedFloat.unpack]
  rw [ite_eq_right notInf]
  by_cases ez : unpackExponent (spec := .binary64) b = 0#11
  · have ez' : N / 2 ^ 52 % 2 ^ 11 = 0 := by rw [← fe, ez]; rfl
    rw [ite_eq_left ez]
    by_cases mz : unpackMantissa (spec := .binary64) b = 0#52
    · have mz' : N % 2 ^ 52 = 0 := by rw [← fm, mz]; rfl
      rw [dite_eq_left mz]
      simp only [UnpackedFloat.neg, UnpackedFloat.pack, packedZero, toNat_packComponents, sign]
      -- Avoid `simp` here: external checkers exhaust their reduction fuel on its proof.
      rw [show BitVec.toNat (0 : BitVec 11) = 0 from rfl, show BitVec.toNat (0 : BitVec 52) = 0 from rfl]
      clear fm fe fs sign notInf ez mz bv bias
      omega
    · have mz' : N % 2 ^ 52 ≠ 0 := by
        intro z; exact mz (BitVec.eq_of_toNat_eq (by rw [fm, z]; rfl))
      rw [dite_eq_right mz]
      have log : (unpackMantissa (spec := .binary64) b).toNat.log2 < 52 :=
        (Nat.log2_lt (by omega)).mpr (by rw [fm]; omega)
      simp only [UnpackedFloat.neg, UnpackedFloat.pack, bias]
      rw [ite_eq_right (by rw [ez]; simp), ite_eq_right (by simp only [Format.mantissaBits]; omega),
        toNat_packComponents, sign]
      simp only [BitVec.toNat_ofNat, fm]
      clear fm fe fs sign notInf ez mz log bv bias
      omega
  · have ez' : N / 2 ^ 52 % 2 ^ 11 ≠ 0 := by
      intro z; exact ez (BitVec.eq_of_toNat_eq (by rw [fe, z]; rfl))
    rw [ite_eq_right ez]
    have append : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat = 2 ^ 52 + N % 2 ^ 52 := by
      rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (by rw [fm]; omega), fm]
      simp [Nat.shiftLeft_eq]
    have log : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat.log2 = 52 := by
      rw [append]
      have := (Nat.le_log2 (n := 2 ^ 52 + N % 2 ^ 52) (k := 52) (by omega)).mpr (by omega)
      have := (Nat.log2_lt (n := 2 ^ 52 + N % 2 ^ 52) (k := 53) (by omega)).mpr (by omega)
      omega
    simp only [UnpackedFloat.neg, UnpackedFloat.pack, bias, log]
    rw [ite_eq_right (by rw [fe]; omega), ite_eq_left (by simp only [Format.mantissaBits]),
      toNat_packComponents, sign]
    simp only [BitVec.toNat_ofNat, fe, append]
    clear fm fe fs sign append log notInf ez bv bias
    omega

theorem canonical_target {F : Nat} {E : Int}
    (canon : (2 ^ 52 ≤ F ∧ F < 2 ^ 53 ∧ -1074 ≤ E) ∨ (0 < F ∧ F < 2 ^ 52 ∧ E = -1074)) :
    Format.binary64.targetExponent (totalExponent F E) = E := by
  simp only [Format.targetExponent, totalExponent, minExponent_binary64, Format.mantissaBits]
  rcases canon with ⟨low, high, emin⟩ | ⟨pos, high, eq⟩
  · have a := (Nat.le_log2 (n := F) (k := 52) (by omega)).mpr low
    have b := (Nat.log2_lt (n := F) (k := 53) (by omega)).mpr high
    omega
  · have b := (Nat.log2_lt (n := F) (k := 52) (by omega)).mpr high
    omega

theorem exact_input {F : Nat} {E : Int}
    (canon : (2 ^ 52 ≤ F ∧ F < 2 ^ 53 ∧ -1074 ≤ E) ∨ (0 < F ∧ F < 2 ^ 52 ∧ E = -1074)) :
    Input .binary64 ((F : Rat) * 2 ^ E) F E .exact := by
  refine ⟨?_, by rw [canonical_target canon]; exact Int.le_refl _⟩
  have p := two_zpow_pos E
  have : (F : Rat) * 2 ^ E / 2 ^ E = F := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt p), Rat.mul_one]
  rw [this]
  exact describes_exact F

theorem round_exact {F : Nat} {E : Int} (pos : 0 < F)
    (canon : (2 ^ 52 ≤ F ∧ F < 2 ^ 53 ∧ -1074 ≤ E) ∨ (0 < F ∧ F < 2 ^ 52 ∧ E = -1074)) :
    roundWithAccuracy .binary64 .positive F E .exact = .finite .positive F E pos := by
  have target := canonical_target canon
  have first : shiftToTargetExponent .binary64 F E .exact = (⟨F, false, false⟩, E) := by
    simp only [shiftToTargetExponent, shiftToExponent, target, Int.sub_self]
    rw [show Int.toNat 0 = 0 from rfl, Int.ofNat_zero, Int.add_zero]
    rfl
  rw [roundWithAccuracy_finish, first]
  simp only [finish]
  have rounded : ExtendedMantissa.roundedMantissa ⟨F, false, false⟩ = F := rfl
  rw [rounded, first]
  simp only
  rw [dite_eq_right (by omega)]

/-- A value with an exact binary64 encoding converts to it. -/
theorem ofScientific_exact {m F : Nat} {e E : Int} (pos : 0 < F)
    (canon : (2 ^ 52 ≤ F ∧ F < 2 ^ 53 ∧ -1074 ≤ E ∧ E ≤ 971) ∨ (0 < F ∧ F < 2 ^ 52 ∧ E = -1074))
    (h : (m : Rat) * 10 ^ e = F * 2 ^ E) :
    UnpackedFloat.ofScientific .binary64 m e = .finite .positive F E pos := by
  have canon' : (2 ^ 52 ≤ F ∧ F < 2 ^ 53 ∧ -1074 ≤ E) ∨ (0 < F ∧ F < 2 ^ 52 ∧ E = -1074) := by
    rcases canon with ⟨a, b, c, -⟩ | c
    · exact Or.inl ⟨a, b, c⟩
    · exact Or.inr c
  have pE := two_zpow_pos E
  have xpos : (0 : Rat) < (F : Rat) * 2 ^ E := Rat.mul_pos (by exact_mod_cast pos) pE
  have hm : m ≠ 0 := by
    intro z; subst z
    have : (F : Rat) * 2 ^ E = 0 := by rw [← h]; grind
    grind
  -- The value lies within the finite range.
  have below : (F : Rat) * 2 ^ E < 2 ^ (1024 : Int) := by
    have F53 : (F : Rat) < 2 ^ (53 : Int) := by
      have : ((F : Nat) : Rat) < ((2 ^ 53 : Nat) : Rat) := by
        apply Rat.natCast_lt_natCast.mpr; rcases canon with ⟨-, b, -⟩ | ⟨-, b, -⟩ <;> omega
      rwa [natCast_two_pow] at this
    have Emax : E ≤ 971 := by rcases canon with ⟨-, -, -, d⟩ | ⟨-, -, d⟩ <;> omega
    have := Rat.mul_lt_mul_of_pos_right F53 pE
    have := two_zpow_le (show (53 : Int) + E ≤ 1024 by omega)
    rw [two_zpow_add] at this
    grind
  have above : 2 ^ (-1075 : Int) ≤ (F : Rat) * 2 ^ E := by
    have F1 : (1 : Rat) ≤ F := by exact_mod_cast pos
    have Emin : -1075 ≤ E := by rcases canon with ⟨-, -, c, -⟩ | ⟨-, -, c⟩ <;> omega
    have := two_zpow_le Emin
    have := Rat.mul_le_mul_of_nonneg_right F1 (Rat.le_of_lt pE)
    grind
  rcases ofScientific_cases (e := e) hm with ⟨b, -⟩ | ⟨b, -⟩ | ⟨n, t, a, input, eq⟩
  · rw [h] at b; exfalso; grind
  · rw [h] at b; exfalso; grind
  · rw [h] at input
    rw [eq, roundWithAccuracy_congr input.1 (exact_input canon').1 input.2 (exact_input canon').2]
    exact round_exact pos canon'

/-- The bits `Float.Model.ofScientific` produces for a value with a normal encoding. -/
public theorem toNat_ofScientific_normal {m F : Nat} {e E : Int} (low : 2 ^ 52 ≤ F) (high : F < 2 ^ 53)
    (emin : -1074 ≤ E) (emax : E ≤ 971) (h : (m : Rat) * 10 ^ e = F * 2 ^ E) :
    (Float.Model.ofScientific m e).toBits.toNat = (E + 1075).toNat * 2 ^ 52 + (F - 2 ^ 52) := by
  have pos : 0 < F := by omega
  simp only [Float.Model.ofScientific, Float.Model.pack, UInt64.toNat_ofBitVec,
    ofScientific_exact pos (Or.inl ⟨low, high, emin, emax⟩) h]
  exact pack_normal pos low high emin emax

/-- The bits `Float.Model.ofScientific` produces for a value with a subnormal encoding. -/
public theorem toNat_ofScientific_subnormal {m F : Nat} {e : Int} (pos : 0 < F) (high : F < 2 ^ 52)
    (h : (m : Rat) * 10 ^ e = F * 2 ^ (-1074 : Int)) :
    (Float.Model.ofScientific m e).toBits.toNat = F := by
  simp only [Float.Model.ofScientific, Float.Model.pack, UInt64.toNat_ofBitVec,
    ofScientific_exact pos (Or.inr ⟨pos, high, rfl⟩) h]
  exact pack_subnormal pos high

public theorem toNat_ofScientific_zero (e : Int) : (Float.Model.ofScientific 0 e).toBits.toNat = 0 := by
  simp only [Float.Model.ofScientific, Float.Model.pack, UInt64.toNat_ofBitVec, ofScientific_zero]
  rfl

/-! ### Finite products -/

/-- The exponent after shifting a mantissa to its target exponent. -/
theorem shift_exponent (m : Nat) (e : Int) (a : Accuracy) :
    (shiftToTargetExponent .binary64 m e a).2 =
      max e (max ((m.log2 : Int) + 1 + e - 53) (-1074)) := by
  simp only [shiftToTargetExponent, shiftToExponent, Format.targetExponent, totalExponent]
  have : Format.binary64.mantissaBits = 53 := rfl
  have : Format.binary64.minExponent = -1074 := by decide
  simp only [*]
  omega

/-- Shifting never grows the mantissa. -/
theorem shift_mantissa_le (m : Nat) (e : Int) (a : Accuracy) :
    (shiftToTargetExponent .binary64 m e a).1.mantissa ≤ m := by
  simp only [shiftToTargetExponent, shiftToExponent]
  rw [shift_mantissa, mantissa_ofMantissaAndAccuracy]
  exact Nat.div_le_self _ _

/-- Rounding adds at most one to the mantissa. -/
theorem roundedMantissa_le (em : ExtendedMantissa) : em.roundedMantissa ≤ em.mantissa + 1 := by
  obtain ⟨m, r, st⟩ := em
  cases r <;> cases st <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven] <;>
    (try split) <;> omega

/-- A product `m₁ * m₂ * 2 ^ (e₁ - k)` of a finite value `m₁ * 2 ^ e₁` and a value
`m₂ * 2 ^ -k` below one rounds to zero or a finite value. -/
theorem round_below_one (s : Sign) (m₁ m₂ k : Nat) (e₁ : Int) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (small₁ : m₁ < 2 ^ 53) (small₂ : m₂ < 2 ^ k) (top : e₁ ≤ 971) :
    roundWithAccuracy .binary64 s (m₁ * m₂) (e₁ - k) .exact = .zero s ∨
      ∃ fm fe h, roundWithAccuracy .binary64 s (m₁ * m₂) (e₁ - k) .exact = .finite s fm fe h ∧ fe ≤ 971 := by
  have product : m₁ * m₂ < m₁ * 2 ^ k := Nat.mul_lt_mul_of_pos_left small₂ hm₁
  have pos : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  have below : m₁ * m₂ < 2 ^ (53 + k) := by
    rw [Nat.pow_add]
    exact Nat.lt_of_lt_of_le product (Nat.mul_le_mul_right _ (Nat.le_of_lt small₁))
  have log : (m₁ * m₂).log2 < 53 + k := (Nat.log2_lt (by omega)).mpr below
  rw [roundWithAccuracy_finish]
  have first := shift_exponent (m₁ * m₂) (e₁ - k) .exact
  have mantissa : (shiftToTargetExponent .binary64 (m₁ * m₂) (e₁ - k) .exact).1.mantissa =
      m₁ * m₂ / 2 ^ ((shiftToTargetExponent .binary64 (m₁ * m₂) (e₁ - k) .exact).2 - (e₁ - k)).toNat := by
    simp only [shiftToTargetExponent, shiftToExponent]
    rw [shift_mantissa, mantissa_ofMantissaAndAccuracy]
    congr 2
    omega
  generalize shiftToTargetExponent .binary64 (m₁ * m₂) (e₁ - k) .exact = p at first mantissa
  obtain ⟨em, t⟩ := p
  simp only at first mantissa
  generalize shift : (t - (e₁ - k)).toNat = sh at mantissa
  -- The shifted mantissa fits in 53 bits.
  have fits : em.mantissa < 2 ^ 53 := by
    rw [mantissa, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    have := Nat.lt_log2_self (n := m₁ * m₂)
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have rounded := roundedMantissa_le em
  have target : t ≤ 971 := by omega
  -- A carry into a 54th bit only happens below the largest exponent.
  have carry : 2 ^ 53 ≤ em.roundedMantissa → t ≤ 970 := by
    intro big
    have full : 2 ^ 53 - 1 ≤ em.mantissa := by omega
    have scaled : (2 ^ 53 - 1) * 2 ^ sh ≤ m₁ * m₂ := by
      have := Nat.div_mul_le_self (m₁ * m₂) (2 ^ sh)
      rw [← mantissa] at this
      exact Nat.le_trans (Nat.mul_le_mul_right _ full) this
    by_cases at971 : t = 971
    · exfalso
      have big' : (2 ^ 53 - 1) * 2 ^ k ≤ (2 ^ 53 - 1) * 2 ^ sh :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      have : m₁ * 2 ^ k ≤ (2 ^ 53 - 1) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
  simp only [finish]
  have second := shift_exponent em.roundedMantissa t .exact
  generalize shiftToTargetExponent .binary64 em.roundedMantissa t .exact = q at second
  obtain ⟨fem, fe⟩ := q
  simp only at second ⊢
  have logRounded : em.roundedMantissa.log2 ≤ 53 := by
    rcases Nat.eq_zero_or_pos em.roundedMantissa with z | z
    · simp [z]
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt (by omega)).mpr (by omega))
  have exponent : fe ≤ 971 := by
    by_cases big : 2 ^ 53 ≤ em.roundedMantissa
    · have := carry big; omega
    · have : em.roundedMantissa.log2 < 53 := by
        rcases Nat.eq_zero_or_pos em.roundedMantissa with z | z
        · simp [z]
        · exact (Nat.log2_lt (by omega)).mpr (by omega)
      omega
  split
  · exact Or.inl rfl
  · rename_i nonzero
    exact Or.inr ⟨_, _, Nat.pos_of_ne_zero nonzero, rfl, exponent⟩

theorem exponent_not_top (b : BitVec 64) (finite : b.toNat / 2 ^ 52 % 2048 < 2047) :
    unpackExponent (spec := .binary64) b ≠ -1#_ := by
  obtain ⟨fm, fe, fs⟩ := fields b
  intro h
  have := congrArg BitVec.toNat h
  simp only [fe] at this
  simp at this
  omega

/-- Finite bit patterns unpack to zero or a 53-bit mantissa with a bounded exponent. -/
theorem unpack_bounds (b : BitVec 64) (finite : b.toNat / 2 ^ 52 % 2048 < 2047) :
    (∃ s, UnpackedFloat.unpack .binary64 b = .zero s) ∨
      ∃ s m e h, UnpackedFloat.unpack .binary64 b = .finite s m e h ∧ m < 2 ^ 53 ∧
        (e = ((b.toNat / 2 ^ 52 % 2048 : Nat) : Int) - 1075 ∨ (e = -1074 ∧ m < 2 ^ 52)) := by
  obtain ⟨fm, fe, -⟩ := fields b
  have bias : Format.binary64.exponentBias = 1023 := by decide
  simp only [UnpackedFloat.unpack]
  have notTop := exponent_not_top b finite
  rw [ite_eq_right_iff.mpr (fun h => absurd h notTop)]
  split
  · rename_i zero
    split
    · exact Or.inl ⟨_, rfl⟩
    · rename_i nz
      refine Or.inr ⟨_, _, _, ?_, rfl, ?_, ?_⟩
      · exact Nat.pos_of_ne_zero fun h => nz (BitVec.eq_of_toNat_eq (by simpa using h))
      · have := (unpackMantissa (spec := .binary64) b).isLt
        simp only at this
        omega
      · have ez := congrArg BitVec.toNat zero
        have mlt : (unpackMantissa (spec := .binary64) b).toNat < 2 ^ 52 :=
          (unpackMantissa (spec := .binary64) b).isLt
        simp only [fe] at ez
        simp at ez
        simp [bias]
        omega
  · rename_i nonzero
    have append : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat =
        2 ^ 52 + (unpackMantissa (spec := .binary64) b).toNat := by
      rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (unpackMantissa (spec := .binary64) b).isLt]
      simp [Nat.shiftLeft_eq]
    have := (unpackMantissa (spec := .binary64) b).isLt
    refine Or.inr ⟨_, _, _, ?_, rfl, ?_, ?_⟩
    · omega
    · omega
    · left
      simp [bias, fe]

theorem sign_toNat (b : BitVec 64) :
    (Sign.ofBitVec (unpackSign (spec := .binary64) b)).toBitVec.toNat = b.toNat / 2 ^ 63 % 2 := by
  obtain ⟨-, -, fs⟩ := fields b
  rw [← fs]
  generalize unpackSign (spec := .binary64) b = v
  match v with
  | 0#1 => rfl
  | 1#1 => rfl

/-- A 64-bit pattern is the sum of its sign, exponent, and mantissa fields. The proof
avoids omega, whose certificates for these divisions exceed external checkers' fuel. -/
theorem fields_sum (x : Nat) (lt : x < 2 ^ 64) :
    x / 2 ^ 63 % 2 * 2 ^ 63 + x / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 + x % 2 ^ 52 = x := by
  have high : x / 2 ^ 63 % 2 = x / 2 ^ 52 / 2 ^ 11 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (by decide)).mpr lt)
  have low := Nat.div_add_mod x (2 ^ 52)
  have middle := Nat.div_add_mod (x / 2 ^ 52) (2 ^ 11)
  rw [high]
  generalize x / 2 ^ 52 / 2 ^ 11 = h at middle ⊢
  generalize x / 2 ^ 52 % 2 ^ 11 = e at middle ⊢
  generalize x % 2 ^ 52 = r at low ⊢
  generalize x / 2 ^ 52 = q at low middle ⊢
  rw [← low, ← middle, show (2 : Nat) ^ 63 = 2 ^ 52 * 2 ^ 11 from Nat.pow_add 2 52 11]
  -- Keep the powers opaque, so checking the rewrites never multiplies them out.
  generalize (2 : Nat) ^ 52 = P
  generalize (2 : Nat) ^ 11 = Q
  rw [Nat.mul_add, Nat.mul_comm h, Nat.mul_assoc, Nat.mul_comm e]

theorem normal_fields (b : BitVec 64) :
    b.toNat / 2 ^ 63 % 2 * 2 ^ 63 +
        (BitVec.ofNat 11 (((unpackExponent (spec := .binary64) b).toNat : Int) -
          ((Format.binary64.exponentBias : Nat) + (52 : Nat)) +
          (Format.binary64.exponentBias : Nat) + (52 : Nat)).toNat).toNat * 2 ^ 52 +
      (BitVec.ofNat 52 (1#1 ++ unpackMantissa (spec := .binary64) b).toNat).toNat = b.toNat := by
  obtain ⟨fm, fe, -⟩ := fields b
  have append : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat =
      2 ^ 52 + (unpackMantissa (spec := .binary64) b).toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (unpackMantissa (spec := .binary64) b).isLt]
    simp [Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, append, fm, fe, Int.add_assoc, Int.sub_add_cancel, Int.toNat_natCast,
    Nat.mod_mod, Nat.add_mod_left]
  exact fields_sum b.toNat b.isLt

theorem zero_fields (b : BitVec 64) (ez : b.toNat / 2 ^ 52 % 2 ^ 11 = (0#11).toNat)
    (mz : b.toNat % 2 ^ 52 = (0#52).toNat) :
    b.toNat / 2 ^ 63 % 2 * 2 ^ 63 + BitVec.toNat (0 : BitVec 11) * 2 ^ 52 +
      BitVec.toNat (0 : BitVec 52) = b.toNat := by
  have sum := fields_sum b.toNat b.isLt
  rw [ez, mz] at sum
  exact sum

theorem subnormal_fields (b : BitVec 64) (ez : b.toNat / 2 ^ 52 % 2 ^ 11 = (0#11).toNat) :
    b.toNat / 2 ^ 63 % 2 * 2 ^ 63 + (0#11).toNat * 2 ^ 52 +
      (BitVec.ofNat 52 (unpackMantissa (spec := .binary64) b).toNat).toNat = b.toNat := by
  obtain ⟨fm, -, -⟩ := fields b
  have sum := fields_sum b.toNat b.isLt
  rw [ez] at sum
  have mantissa : (BitVec.ofNat 52 (unpackMantissa (spec := .binary64) b).toNat).toNat =
      b.toNat % 2 ^ 52 := by
    rw [BitVec.toNat_ofNat, fm, Nat.mod_mod]
  rw [mantissa]
  exact sum

theorem pack_unpack_subnormal (b : BitVec 64) (finite : b.toNat / 2 ^ 52 % 2048 < 2047)
    (exponent : unpackExponent (spec := .binary64) b = 0#11) :
    UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 b) = b := by
  apply BitVec.eq_of_toNat_eq
  obtain ⟨fm, fe, fs⟩ := fields b
  have sign := sign_toNat b
  have lt := b.isLt
  have bias : Format.binary64.exponentBias = 1023 := by decide
  have notTop := exponent_not_top b finite
  simp only [UnpackedFloat.unpack]
  rw [ite_eq_right_iff.mpr (fun h => absurd h notTop)]
  split
  · rename_i zero
    have ez := congrArg BitVec.toNat zero
    simp only [fe] at ez
    split
    · rename_i mz
      have mz := congrArg BitVec.toNat mz
      simp only [fm] at mz
      simp only [UnpackedFloat.pack, packedZero, toNat_packComponents, sign]
      exact zero_fields b ez mz
    · rename_i nz
      have mlt := (unpackMantissa (spec := .binary64) b).isLt
      have mpos : (unpackMantissa (spec := .binary64) b).toNat ≠ 0 :=
        fun h => nz (BitVec.eq_of_toNat_eq (by simpa using h))
      have log : (unpackMantissa (spec := .binary64) b).toNat.log2 < 52 := (Nat.log2_lt mpos).mpr mlt
      simp only [UnpackedFloat.pack]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp at ez; simp [bias, fe]; omega)),
        ite_eq_right_iff.mpr (fun h => absurd h (by simp only [Format.mantissaBits]; omega)),
        toNat_packComponents, sign]
      exact subnormal_fields b ez
  · exact absurd exponent ‹_›

theorem pack_unpack_normal (b : BitVec 64) (finite : b.toNat / 2 ^ 52 % 2048 < 2047)
    (exponent : unpackExponent (spec := .binary64) b ≠ 0#11) :
    UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 b) = b := by
  apply BitVec.eq_of_toNat_eq
  obtain ⟨fm, fe, fs⟩ := fields b
  have sign := sign_toNat b
  have lt := b.isLt
  have bias : Format.binary64.exponentBias = 1023 := by decide
  have notTop := exponent_not_top b finite
  simp only [UnpackedFloat.unpack]
  rw [ite_eq_right_iff.mpr (fun h => absurd h notTop)]
  split
  · exact absurd ‹_› exponent
  · rename_i nonzero
    have ne := fun h => nonzero (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [fe] at ne
    have append : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat =
        2 ^ 52 + (unpackMantissa (spec := .binary64) b).toNat := by
      rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (unpackMantissa (spec := .binary64) b).isLt]
      simp [Nat.shiftLeft_eq]
    have mlt := (unpackMantissa (spec := .binary64) b).isLt
    have log : (1#1 ++ unpackMantissa (spec := .binary64) b).toNat.log2 = 52 := by
      rw [append]
      generalize (unpackMantissa (spec := .binary64) b).toNat = M at mlt ⊢
      have mlt : M < 2 ^ 52 := mlt
      have a := (Nat.le_log2 (n := 2 ^ 52 + M) (k := 52) (by omega)).mpr (by omega)
      have c := (Nat.log2_lt (n := 2 ^ 52 + M) (k := 53) (by omega)).mpr (by omega)
      omega
    simp only [UnpackedFloat.pack]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [bias, fe]; omega)),
      ite_eq_left_iff.mpr (fun h => absurd (by simp only [Format.mantissaBits, log]) h),
      toNat_packComponents, sign]
    exact normal_fields b

/-- Finite bit patterns survive unpacking and packing. -/
theorem pack_unpack (b : BitVec 64) (finite : b.toNat / 2 ^ 52 % 2048 < 2047) :
    UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 b) = b := by
  by_cases exponent : unpackExponent (spec := .binary64) b = 0#11
  · exact pack_unpack_subnormal b finite exponent
  · exact pack_unpack_normal b finite exponent

/-- The exponent field of a 64-bit pattern assembled from its fields. -/
theorem exponent_field (S E R : Nat) (he : E < 2 ^ 11) (hr : R < 2 ^ 52) :
    (S * 2 ^ 63 + E * 2 ^ 52 + R) / 2 ^ 52 % 2048 = E := by
  rw [show (2048 : Nat) = 2 ^ 11 from rfl, show (2 : Nat) ^ 63 = 2 ^ 11 * 2 ^ 52 from Nat.pow_add 2 11 52]
  have positive : 0 < 2 ^ 52 := Nat.two_pow_pos 52
  -- Keep the powers opaque, so checking the rewrites never multiplies them out.
  generalize (2 : Nat) ^ 52 = P at hr positive ⊢
  generalize (2 : Nat) ^ 11 = Q at he ⊢
  rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.add_comm _ R, Nat.add_mul_div_right _ _ positive,
    Nat.div_eq_of_lt hr, Nat.zero_add, Nat.mul_comm S Q, Nat.mul_add_mod, Nat.mod_eq_of_lt he]

/-- Zero and values with a bounded exponent pack to finite bit patterns. -/
theorem pack_finite (u : UnpackedFloat)
    (bounded : (∃ s, u = .zero s) ∨ ∃ s m fe h, u = .finite s m fe h ∧ fe ≤ 971) :
    (UnpackedFloat.pack .binary64 u).toNat / 2 ^ 52 % 2048 < 2047 := by
  have bias : Format.binary64.exponentBias = 1023 := by decide
  rcases bounded with ⟨s, rfl⟩ | ⟨s, m, fe, h, rfl, small⟩
  · simp only [UnpackedFloat.pack, packedZero, toNat_packComponents]
    rw [exponent_field _ _ _ (BitVec.isLt _) (BitVec.isLt _)]
    decide
  · simp only [UnpackedFloat.pack]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp [bias]; omega))]
    split
    · rw [toNat_packComponents, exponent_field _ _ _ (BitVec.isLt _) (BitVec.isLt _)]
      simp [bias]
      omega
    · rw [toNat_packComponents, exponent_field _ _ _ (BitVec.isLt _) (BitVec.isLt _)]
      decide

/-- Products of a finite value and a value below one in magnitude, that is, with
an exponent field below 1023, are finite. -/
public theorem ofBits_mul_finite (u v : UInt64) (fu : u.toNat / 2 ^ 52 % 2048 < 2047)
    (fv : v.toNat / 2 ^ 52 % 2048 < 1023) :
    (Float.Model.ofBits u * Float.Model.ofBits v).toBits.toNat / 2 ^ 52 % 2048 < 2047 := by
  have ru := pack_unpack u.toBitVec fu
  have below : v.toNat / 2 ^ 52 % 2048 < 2047 := Nat.lt_of_lt_of_le fv (by decide)
  have rv := pack_unpack v.toBitVec below
  show (UInt64.ofBitVec (UnpackedFloat.pack .binary64 (UnpackedFloat.mul .binary64
    (UnpackedFloat.unpack .binary64 (UInt64.ofBitVec (UnpackedFloat.pack .binary64
      (UnpackedFloat.unpack .binary64 u.toBitVec))).toBitVec)
    (UnpackedFloat.unpack .binary64 (UInt64.ofBitVec (UnpackedFloat.pack .binary64
      (UnpackedFloat.unpack .binary64 v.toBitVec))).toBitVec)))).toNat / 2 ^ 52 % 2048 < 2047
  simp only [ru, rv, UInt64.toNat_ofBitVec]
  apply pack_finite
  rcases unpack_bounds u.toBitVec fu with ⟨s₁, eq₁⟩ | ⟨s₁, m₁, e₁, h₁, eq₁, mb₁, eb₁⟩ <;>
  rcases unpack_bounds v.toBitVec below with ⟨s₂, eq₂⟩ | ⟨s₂, m₂, e₂, h₂, eq₂, mb₂, eb₂⟩ <;>
  rw [eq₁, eq₂] <;> simp only [UnpackedFloat.mul]
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · simp only [UInt64.toNat_toBitVec] at eb₁ eb₂
    generalize u.toNat / 2 ^ 52 % 2048 = E₁ at fu eb₁
    generalize v.toNat / 2 ^ 52 % 2048 = E₂ at fv eb₂
    have top : e₁ ≤ 971 := by omega
    have shift : e₁ + e₂ = e₁ - ((-e₂).toNat : Nat) := by omega
    have below : m₂ < 2 ^ (-e₂).toNat := by
      rcases eb₂ with eb₂ | ⟨eb₂, mb₂⟩
      · exact Nat.lt_of_lt_of_le mb₂ (Nat.pow_le_pow_right (by decide) (by omega))
      · exact Nat.lt_of_lt_of_le mb₂ (Nat.pow_le_pow_right (by decide) (by omega))
    rw [shift]
    rcases round_below_one (s₁ * s₂) m₁ m₂ _ e₁ h₁ h₂ mb₁ below top with zero | ⟨fm, fe, h, eq, le⟩
    · exact Or.inl ⟨_, zero⟩
    · exact Or.inr ⟨_, _, _, _, eq, le⟩

end Lynx.Term.Rounding
