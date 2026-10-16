module

public import Std

namespace Lynx.Term

/-- A finite IEEE binary64 value, stored in its canonical encoded fields.
Exponent 2047 is reserved for infinities and NaNs and is unrepresentable here. -/
public structure FiniteFloat where
  negative : Bool
  exponent : Fin 2047
  fraction : Fin (2 ^ 52)
deriving DecidableEq, Repr

namespace FiniteFloat

private def toModel (value : FiniteFloat) : Float.Model :=
  Float.Model.ofBits (UInt64.ofNat
    ((if value.negative then 2 ^ 63 else 0) +
      value.exponent.val * 2 ^ 52 + value.fraction.val))

/-- Exponent 2047 rejects both infinities and NaNs. -/
private def ofModel (value : Float.Model) : Option FiniteFloat :=
  let bits := value.toBits.toNat
  let exponent := bits / 2 ^ 52 % 2048
  if h : exponent < 2047 then
    some ⟨bits / 2 ^ 63 != 0, ⟨exponent, h⟩,
      ⟨bits % 2 ^ 52, Nat.mod_lt _ (by decide)⟩⟩
  else none

/-- Convert with binary64 rounding, failing if the integer overflows. -/
@[expose] public def ofInt (value : Int) : Option FiniteFloat :=
  let bits := (Float.Model.ofInt value).toBits.toNat
  let exponent := bits / 2 ^ 52 % 2048
  if h : exponent < 2047 then
    some ⟨bits / 2 ^ 63 != 0, ⟨exponent, h⟩,
      ⟨bits % 2 ^ 52, Nat.mod_lt _ (by decide)⟩⟩
  else none

/-- Round `mantissa * 10 ^ exponent` to binary64 with the given sign, failing on
overflow. -/
public def ofScientific (negative : Bool) (mantissa : Nat) (exponent : Int) :
    Option FiniteFloat :=
  let value := Float.Model.ofScientific mantissa exponent
  ofModel (if negative then value.neg else value)

/-- IEEE binary64 addition, failing on any non-finite result. -/
public def add (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel + right.toModel)

/-- IEEE binary64 multiplication, failing on any non-finite result. -/
public def mul (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel * right.toModel)

/-- IEEE binary64 subtraction, failing on any non-finite result. -/
public def sub (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel - right.toModel)

/-- IEEE binary64 division, failing on zero divisors and non-finite results. -/
public def div (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel / right.toModel)

/-- The nonnegative mathematical magnitude of a finite binary64 value. -/
@[expose] public def magnitude (value : FiniteFloat) : Rat :=
  if value.exponent.val = 0 then
    if value.fraction.val = 0 then 0
    else (value.fraction.val : Rat) * (2 : Rat) ^ (-1074 : Int)
  else
    ((2 ^ 52 + value.fraction.val : Nat) : Rat) *
      (2 : Rat) ^ (Int.ofNat value.exponent.val - 1075)

/-- The exact mathematical value represented by this binary64 encoding.
Positive and negative zero have the same value but remain distinct structures. -/
@[expose] public def toRat (value : FiniteFloat) : Rat :=
  if value.negative then -value.magnitude else value.magnitude

@[simp] public theorem toRat_zero (negative : Bool) :
    toRat ⟨negative, 0, 0⟩ = 0 := by
  cases negative <;> rfl

public theorem toRat_eq_zero (value : FiniteFloat) :
    value.toRat = 0 ↔ value.exponent.val = 0 ∧ value.fraction.val = 0 := by
  have magnitude_zero : value.magnitude = 0 ↔ value.exponent.val = 0 ∧ value.fraction.val = 0 := by
    by_cases exp0 : value.exponent.val = 0
    · by_cases frac0 : value.fraction.val = 0
      · simp [Lynx.Term.FiniteFloat.magnitude, exp0, frac0]
      · have nonzero : (value.fraction.val : Rat) * (2 : Rat) ^ (-1074 : Int) ≠ 0 :=
          Rat.ne_of_gt (Rat.mul_pos (Rat.natCast_pos.mpr (by omega)) (Rat.zpow_pos (by decide)))
        simp only [Lynx.Term.FiniteFloat.magnitude, if_pos exp0, if_neg frac0]
        exact ⟨fun h => False.elim (nonzero h), fun h => False.elim (frac0 h.2)⟩
    · have nonzero : ((2 ^ 52 + value.fraction.val : Nat) : Rat) *
          (2 : Rat) ^ ((value.exponent.val : Int) - 1075) ≠ 0 :=
        Rat.ne_of_gt (Rat.mul_pos (Rat.natCast_pos.mpr (by omega)) (Rat.zpow_pos (by decide)))
      simp only [Lynx.Term.FiniteFloat.magnitude, if_neg exp0]
      exact ⟨fun h => False.elim (nonzero h), fun h => False.elim (exp0 h.1)⟩
  unfold Lynx.Term.FiniteFloat.toRat
  cases hn : value.negative
  · simpa only [hn, Bool.false_eq_true, ↓reduceIte] using magnitude_zero
  · simp only [↓reduceIte]
    have neg_zero : -value.magnitude = 0 ↔ value.magnitude = 0 := by
      constructor
      · intro h
        have := congrArg Neg.neg h
        simpa only [Rat.neg_neg, Rat.neg_zero] using this
      · intro h; rw [h, Rat.neg_zero]
    exact neg_zero.trans magnitude_zero

/-- A binary64 value with no fractional bit positions represents an integer. -/
public theorem toRat_integral_of_exponent (value : FiniteFloat) (large : 1075 ≤ value.exponent.val) :
    ∃ n : Int, value.toRat = (n : Rat) := by
  let n : Nat := (2 ^ 52 + value.fraction.val) * 2 ^ (value.exponent.val - 1075)
  have exp0 : value.exponent.val ≠ 0 := by omega
  have exponent : (value.exponent.val : Int) - 1075 = ((value.exponent.val - 1075 : Nat) : Int) := by omega
  have magnitude : value.magnitude = (n : Rat) := by
    simp [Lynx.Term.FiniteFloat.magnitude, exp0, exponent, n, Rat.natCast_mul,
      Rat.natCast_pow, Rat.zpow_natCast]
  cases sign : value.negative
  · exact ⟨n, by simp [Lynx.Term.FiniteFloat.toRat, sign, magnitude, Rat.intCast_natCast]⟩
  · exact ⟨-(n : Int), by simp [Lynx.Term.FiniteFloat.toRat, sign, magnitude, Rat.intCast_natCast, Rat.intCast_neg]⟩

end FiniteFloat
end Lynx.Term
