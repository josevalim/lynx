# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/elixir/calendar_iso.exs
# Prove the installed Calendar.ISO, translated from BEAM debug information.
# Checked against Elixir 1.21.0-dev (3790cd8), Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/calendar/iso.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule CalendarISOProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def valid_year(year), do: is_integer(year)
  def valid_month(month), do: is_integer(month) and month >= 1 and month <= 12
  def era_year({year, 1}), do: year
  def era_year({year, 0}), do: 1 - year

  def quarter_contains_month(quarter, month),
    do: quarter >= 1 and quarter <= 4 and (quarter - 1) * 3 < month and month <= quarter * 3

  laws "Calendar.ISO" do
    law year_of_era_roundtrips(year),
      requires: valid_year(year),
      expects: era_year(Calendar.ISO.year_of_era(year)) === year,
      proof: ~LEAN"""
      cases year <;> simp [«year_of_era_roundtrips:requires/1», «valid_year/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i y
      by_cases ce : 1 ≤ y
      · simp [«year_of_era_roundtrips:ensures/1», Elixir.Calendar.ISO.«year_of_era/1»,
          ce, «era_year/1», Erlang.erlang.«=:=/2»]
      · simp [«year_of_era_roundtrips:ensures/1», Elixir.Calendar.ISO.«year_of_era/1»,
          ce, show y ≤ 0 by omega, «era_year/1», Erlang.erlang.«=:=/2»]
        omega
      """

    law leap_year_cycle(year),
      requires: valid_year(year),
      expects: Calendar.ISO.leap_year?(year + 400) === Calendar.ISO.leap_year?(year),
      proof: ~LEAN"""
      have leap (y : Int) : Elixir.Calendar.ISO.«leap_year?/1» (.integer y) =
          .ok (if y % 4 = 0 ∧ (y % 16 = 0 ∨ y % 100 ≠ 0)
            then Lynx.Term.true else Lynx.Term.false) := by
        have zero (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
          constructor
          · intro h
            have := congrArg (fun x => a ^^^ x) h
            simpa [← Nat.xor_assoc] using this.symm
          · rintro rfl; exact Nat.xor_self _
        have remZero (y : Int) : y.tmod 100 = 0 ↔ y % 100 = 0 := by
          rw [← Int.dvd_iff_tmod_eq_zero, ← Int.dvd_iff_emod_eq_zero]
        cases y with
        | ofNat n =>
          have m4 : n &&& 3 = n % 4 := Nat.and_two_pow_sub_one_eq_mod n 2
          have m16 : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4
          by_cases four : (n : Int) % 4 = 0 <;>
            by_cases sixteen : (n : Int) % 16 = 0 <;>
            by_cases hundred : (n : Int) % 100 = 0 <;>
          simp [Elixir.Calendar.ISO.«leap_year?/1», Erlang.erlang.«band/2»,
            Erlang.erlang.«=:=/2», Erlang.erlang.«=/=/2», Erlang.erlang.«rem/2», m4, m16, remZero, four, sixteen, hundred]
        | negSucc n =>
          have m4 : 3 &&& n = n % 4 := by simpa [Nat.and_comm] using Nat.and_two_pow_sub_one_eq_mod n 2
          have m16 : 15 &&& n = n % 16 := by simpa [Nat.and_comm] using Nat.and_two_pow_sub_one_eq_mod n 4
          have fourZero : (3 ^^^ n % 4 = 0) ↔ Int.negSucc n % 4 = 0 := by
            rw [zero]
            omega
          have sixteenZero : (15 ^^^ n % 16 = 0) ↔ Int.negSucc n % 16 = 0 := by
            rw [zero]
            omega
          by_cases four : Int.negSucc n % 4 = 0 <;>
            by_cases sixteen : Int.negSucc n % 16 = 0 <;>
            by_cases hundred : Int.negSucc n % 100 = 0 <;>
          simp [Elixir.Calendar.ISO.«leap_year?/1», Erlang.erlang.«band/2»,
            Erlang.erlang.«=:=/2», Erlang.erlang.«=/=/2», Erlang.erlang.«rem/2», m4, m16, remZero, fourZero, sixteenZero, four, sixteen, hundred]
      cases year <;> simp [«leap_year_cycle:requires/1», «valid_year/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i y
      simp [«leap_year_cycle:ensures/1», leap, Int.add_emod]
      split <;> simp [Erlang.erlang.«=:=/2»]
      """

    law twelve_months_in_year(year),
      requires: valid_year(year),
      expects: Calendar.ISO.months_in_year(year) === 12,
      proof: ~LEAN"""
      cases year <;> simp [«twelve_months_in_year:requires/1», «valid_year/1»,
        Erlang.erlang.«is_integer/1»] at requires
      simp [«twelve_months_in_year:ensures/1», Elixir.Calendar.ISO.«months_in_year/1»,
        Erlang.erlang.«=:=/2»]
      """

    law quarter_contains_month(year, month, day),
      requires:
        valid_year(year) and valid_month(month) and is_integer(day) and day >= 1 and day <= 31,
      expects: quarter_contains_month(Calendar.ISO.quarter_of_year(year, month, day), month),
      proof: ~LEAN"""
      cases year <;> simp [«quarter_contains_month:requires/3», «valid_year/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i y
      cases month <;> simp [«valid_month/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i m
      by_cases mLo : 1 ≤ m <;> by_cases mHi : m ≤ 12 <;> simp [mLo, mHi] at requires
      cases day <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i d
      by_cases dLo : 1 ≤ d <;> by_cases dHi : d ≤ 31 <;> simp [dLo, dHi] at requires
      have nonnegative : 0 ≤ m - 1 := by omega
      have qLo : 1 ≤ (m - 1) / 3 + 1 := by omega
      have qHi : (m - 1) / 3 + 1 ≤ 4 := by omega
      have first : (m - 1) / 3 * 3 < m := by omega
      have last : m ≤ ((m - 1) / 3 + 1) * 3 := by omega
      simp [«quarter_contains_month:ensures/3», Elixir.Calendar.ISO.«quarter_of_year/3»,
        mLo, mHi, dLo, dHi, Erlang.erlang.«is_integer/1», Erlang.erlang.«=:=/2», Erlang.erlang.«div/2»,
        Int.tdiv_eq_ediv_of_nonneg nonnegative, «quarter_contains_month/2», qLo, qHi, first, last]
      """

    law days_in_month_bounds(year, month),
      requires: valid_year(year) and valid_month(month),
      expects: month_length_in_bounds(Calendar.ISO.days_in_month(year, month)),
      proof: ~LEAN"""
      cases year <;> simp [«days_in_month_bounds:requires/2», «valid_year/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i y
      cases month <;> simp [«valid_month/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i m
      by_cases mLo : 1 ≤ m <;> by_cases mHi : m ≤ 12 <;> simp [mLo, mHi] at requires
      by_cases february : m = 2
      · subst m
        have band (mask : Int) : ∃ bits : Int,
            Erlang.erlang.«band/2» (.integer y) (.integer mask) = .ok (.integer bits) := by
          cases y <;> cases mask <;> exact ⟨_, rfl⟩
        obtain ⟨fourBits, fourReturned⟩ := band 3
        obtain ⟨sixteenBits, sixteenReturned⟩ := band 15
        by_cases four : fourBits = 0 <;> by_cases sixteen : sixteenBits = 0 <;>
          by_cases hundred : y.tmod 100 = 0 <;>
          simp [«days_in_month_bounds:ensures/2», Elixir.Calendar.ISO.«days_in_month/2»,
            Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«is_integer/1»,
            Erlang.erlang.«=:=/2», Erlang.erlang.«=/=/2», Erlang.erlang.«rem/2»,
            fourReturned, sixteenReturned, four, sixteen, hundred, «month_length_in_bounds/1»]
      · by_cases april : m = 4 <;> by_cases june : m = 6 <;>
          by_cases september : m = 9 <;> by_cases november : m = 11 <;>
          simp [«days_in_month_bounds:ensures/2», Elixir.Calendar.ISO.«days_in_month/2»,
            Elixir.Calendar.ISO.«days_in_month_guarded/2», mLo, mHi, february,
            april, june, september, november, Erlang.erlang.«is_integer/1»,
            Erlang.erlang.«=:=/2», «month_length_in_bounds/1»]
      """

    law date_from_iso_days_total(days),
      requires: is_integer(days),
      expects: is_tuple(Calendar.ISO.date_from_iso_days(days)),
      proof: ~LEAN"""
      cases days <;> simp [«date_from_iso_days_total:requires/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      by_cases era : 60 ≤ n <;>
        simp [«date_from_iso_days_total:ensures/1», Elixir.Calendar.ISO.«date_from_iso_days/1»,
          Erlang.erlang.«div/2», era]
      all_goals split <;> simp_all [Erlang.erlang.«is_tuple/1»]
      all_goals split <;> simp_all [Erlang.erlang.«is_tuple/1»]
      """

    law time_fraction_bounds(hour, minute, second, microsecond, precision),
      requires: Calendar.ISO.valid_time?(hour, minute, second, {microsecond, precision}),
      expects:
        fraction_in_day(
          Calendar.ISO.time_to_day_fraction(hour, minute, second, {microsecond, precision})
        ),
      proof: ~LEAN"""
      cases hour <;> simp [«time_fraction_bounds:requires/5»,
        Elixir.Calendar.ISO.«valid_time?/4», Erlang.erlang.«is_integer/1»,
        Erlang.erlang.«=:=/2»] at requires
      rename_i h
      cases minute <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i m
      cases second <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i s
      cases microsecond <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i u
      cases precision <;> simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«=:=/2»] at requires
      rename_i p
      by_cases hLo : 0 ≤ h <;> by_cases hHi : h ≤ 23 <;> simp [hLo, hHi] at requires
      by_cases mLo : 0 ≤ m <;> by_cases mHi : m ≤ 59 <;> simp [mLo, mHi] at requires
      by_cases sLo : 0 ≤ s <;> by_cases sHi : s ≤ 59 <;> simp [sLo, sHi] at requires
      by_cases uLo : 0 ≤ u <;> by_cases uHi : u ≤ 999999 <;> simp [uLo, uHi] at requires
      have lo : 0 ≤ (h * 3600 + m * 60 + s) * 1000000 + u := by omega
      have hi : (h * 3600 + m * 60 + s) * 1000000 + u < 86400000000 := by omega
      simp [«time_fraction_bounds:ensures/5», Elixir.Calendar.ISO.«time_to_day_fraction/4»,
        «fraction_in_day/1», lo, hi]
      split <;> simp_all [«fraction_in_day/1»]
      obtain ⟨hu, hp⟩ := ‹Lynx.Term.integer u = _ ∧ Lynx.Term.integer p = _›
      rw [← hu]
      simp [lo, hi]
      """
  end

  def month_length_in_bounds(days), do: days >= 28 and days <= 31

  def fraction_in_day({parts, per_day}), do: parts >= 0 and parts < per_day
end
