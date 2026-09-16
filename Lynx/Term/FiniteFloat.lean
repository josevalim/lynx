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

@[simp] theorem magnitude_zero (negative : Bool) :
    magnitude ⟨negative, 0, 0⟩ = 0 := rfl

@[simp] theorem toRat_zero (negative : Bool) :
    toRat ⟨negative, 0, 0⟩ = 0 := by
  cases negative <;> rfl

end FiniteFloat
end Lynx.Term
