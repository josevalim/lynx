module

import all Lynx.Modules.Erlang.math
meta import LynxTest.ProofAudit

namespace LynxTest.Modules.Math
open Lynx

theorem floor_signed_zero (negative : Bool) :
    Erlang.math.«floor/1» (.float ⟨negative, 0, 0⟩) = .ok (.float ⟨negative, 0, 0⟩) := by
  simp [Erlang.math.floor_float, Term.FiniteFloat.toRat, Term.FiniteFloat.magnitude, Rat.floor]

theorem ceil_signed_zero (negative : Bool) :
    Erlang.math.«ceil/1» (.float ⟨negative, 0, 0⟩) = .ok (.float ⟨negative, 0, 0⟩) := by
  simp [Erlang.math.ceil_float, Term.FiniteFloat.toRat, Term.FiniteFloat.magnitude, Rat.ceil]

theorem floor_unit_interval (value : Term.FiniteFloat)
    (lower : (0 : Rat) ≤ value.toRat) (upper : value.toRat < 1) :
    Erlang.math.«floor/1» (.float value) = .ok (.float ⟨value.negative, 0, 0⟩) := by
  have lo : 0 ≤ value.toRat.floor := Rat.le_floor_iff.mpr (by simpa using lower)
  have hi : value.toRat.floor < 1 := Rat.floor_lt_iff.mpr (by simpa using upper)
  have rounded : value.toRat.floor = 0 := by omega
  by_cases large : 1075 ≤ value.exponent.val
  · obtain ⟨n, exact⟩ := Term.FiniteFloat.toRat_integral_of_exponent value large
    have integer : value.toRat.floor = n := by simp [exact]
    have zero : n = 0 := by omega
    have valueZero : value.toRat = 0 := by simpa [zero] using exact
    have fields := (Term.FiniteFloat.toRat_eq_zero value).mp valueZero
    omega
  · simp [Erlang.math.floor_float, large, rounded]

theorem ceil_negative_unit_interval (value : Term.FiniteFloat)
    (lower : (-1 : Rat) < value.toRat) (upper : value.toRat ≤ 0) :
    Erlang.math.«ceil/1» (.float value) = .ok (.float ⟨value.negative, 0, 0⟩) := by
  have lo : -1 < value.toRat.ceil := Rat.lt_ceil_iff.mpr (by simpa using lower)
  have hi : value.toRat.ceil ≤ 0 := Rat.ceil_le_iff.mpr (by simpa using upper)
  have rounded : value.toRat.ceil = 0 := by omega
  by_cases large : 1075 ≤ value.exponent.val
  · obtain ⟨n, exact⟩ := Term.FiniteFloat.toRat_integral_of_exponent value large
    have integer : value.toRat.ceil = n := by simp [exact]
    have zero : n = 0 := by omega
    have valueZero : value.toRat = 0 := by simpa [zero] using exact
    have fields := (Term.FiniteFloat.toRat_eq_zero value).mp valueZero
    omega
  · simp [Erlang.math.ceil_float, large, rounded]

theorem large_values_are_fixed_and_integral (value : Term.FiniteFloat)
    (large : 1075 ≤ value.exponent.val) :
    Erlang.math.«floor/1» (.float value) = .ok (.float value) ∧
    Erlang.math.«ceil/1» (.float value) = .ok (.float value) ∧
    (value.toRat.floor : Rat) = value.toRat ∧ (value.toRat.ceil : Rat) = value.toRat := by
  obtain ⟨n, exact⟩ := Term.FiniteFloat.toRat_integral_of_exponent value large
  simp [Erlang.math.floor_large value large, Erlang.math.ceil_large value large, exact]

end LynxTest.Modules.Math

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Math
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.math
