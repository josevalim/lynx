# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/rand.exs
# Prove the installed OTP rand module, translated from its BEAM debug information.
# Verified against Erlang/OTP 28.1.1 (stdlib 7.1, ERTS 16.1.1).
# The proofs depend on mwc59/1's implementation and constants; rerun them after OTP upgrades.
ExUnit.start()

defmodule RandProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case
  import Bitwise

  @multiplier 0x7FA6502
  @modulus @multiplier * (1 <<< 32) - 1

  # OTP's commented mwc59_r/1 verification helper, expressed independently.
  def inverse(state), do: rem(state <<< 32, @modulus)
  def valid_state(state), do: is_integer(state) and state >= 1 and state < @modulus

  # Write state = carry * 2^32 + digit. OTP returns multiplier * digit + carry.
  # Multiplying that result by 2^32 gives state modulo @modulus, proving recovery.
  # These laws quantify over every valid state; they do not assert statistical quality.
  laws "MWC59 state transition" do
    law preserves_state(state),
      requires: valid_state(state),
      expects: valid_state(:rand.mwc59(state)),
      proof: ~LEAN"""
      cases state <;> simp [«preserves_state:requires/1», «valid_state/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      by_cases lower : 1 ≤ n <;> by_cases upper : n < 574882961707499519 <;>
        simp [lower, upper] at requires
      have nonnegative : 0 ≤ n := by omega
      have returned : Erlang.rand.«mwc59/1» (.integer n) =
          .ok (.integer (133850370 * (n % 4294967296) + n / 4294967296)) := by
        have mask := Erlang.erlang.«band/2_mask» n 32 nonnegative
        change Erlang.erlang.«band/2» (.integer n) (.integer 4294967295) =
          .ok (.integer (n % 4294967296)) at mask
        simp [Erlang.rand.«mwc59/1», Erlang.erlang.«is_integer/1»,
          lower, upper, show n ≤ 574882961707499518 by omega,
          Erlang.erlang.«bsr/2», Int.shiftRight_eq_div_pow, mask,
          Erlang.erlang.«=:=/2», Erlang.erlang.«and/2»]
      have remainder_lower := Int.emod_nonneg n (by decide : (4294967296 : Int) ≠ 0)
      have remainder_upper := Int.emod_lt_of_pos n (by decide : (0 : Int) < 4294967296)
      have decomposition := Int.emod_add_mul_ediv n 4294967296
      have next_lower : 1 ≤ 133850370 * (n % 4294967296) + n / 4294967296 := by omega
      have next_upper : 133850370 * (n % 4294967296) + n / 4294967296 <
          574882961707499519 := by omega
      simp [«preserves_state:ensures/1», returned, «valid_state/1»,
        Erlang.erlang.«is_integer/1», next_lower, next_upper]
      """

    law inverse_recovers_state(state),
      requires: valid_state(state),
      expects: inverse(:rand.mwc59(state)) === state,
      proof: ~LEAN"""
      cases state <;> simp [«inverse_recovers_state:requires/1», «valid_state/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      by_cases lower : 1 ≤ n <;> by_cases upper : n < 574882961707499519 <;>
        simp [lower, upper] at requires
      have nonnegative : 0 ≤ n := by omega
      have returned : Erlang.rand.«mwc59/1» (.integer n) =
          .ok (.integer (133850370 * (n % 4294967296) + n / 4294967296)) := by
        have mask := Erlang.erlang.«band/2_mask» n 32 nonnegative
        change Erlang.erlang.«band/2» (.integer n) (.integer 4294967295) =
          .ok (.integer (n % 4294967296)) at mask
        simp [Erlang.rand.«mwc59/1», Erlang.erlang.«is_integer/1»,
          lower, upper, show n ≤ 574882961707499518 by omega,
          Erlang.erlang.«bsr/2», Int.shiftRight_eq_div_pow, mask,
          Erlang.erlang.«=:=/2», Erlang.erlang.«and/2»]
      have remainder_lower := Int.emod_nonneg n (by decide : (4294967296 : Int) ≠ 0)
      have remainder_upper := Int.emod_lt_of_pos n (by decide : (0 : Int) < 4294967296)
      have decomposition := Int.emod_add_mul_ediv n 4294967296
      have next_lower : 1 ≤ 133850370 * (n % 4294967296) + n / 4294967296 := by omega
      have next_upper : 133850370 * (n % 4294967296) + n / 4294967296 <
          574882961707499519 := by omega
      have inverse_value :
          ((133850370 * (n % 4294967296) + n / 4294967296) * 4294967296) %
            574882961707499519 = n := by
        omega
      simp [«inverse_recovers_state:ensures/1», returned, «inverse/1»,
        Erlang.erlang.«bsl/2», Int.shiftLeft_eq, Erlang.erlang.«rem/2»,
        Int.tmod_eq_emod_of_nonneg (by omega :
          0 ≤ (133850370 * (n % 4294967296) + n / 4294967296) * 4294967296),
        inverse_value, Erlang.erlang.«=:=/2»]
      """
  end
end
