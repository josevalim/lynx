# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/calendar.exs
# Prove the installed OTP calendar module, translated from BEAM debug information.
# Checked against Erlang/OTP 28.1.1 (stdlib 7.1, ERTS 16.1.1).
# These proofs depend on implementation details; rerun them after OTP upgrades.
ExUnit.start()

defmodule CalendarProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def valid_time({h, m, s}) do
    is_integer(h) and h >= 0 and h < 24 and
      is_integer(m) and m >= 0 and m < 60 and
      is_integer(s) and s >= 0 and s < 60
  end

  def daystime_roundtrips(seconds) do
    {days, time} = :calendar.seconds_to_daystime(seconds)
    valid_time(time) and days * 86400 + :calendar.time_to_seconds(time) === seconds
  end

  def valid_year(year), do: is_integer(year) and year >= 0

  laws "calendar" do
    law seconds_to_daystime_roundtrips(seconds),
      requires: is_integer(seconds),
      expects: daystime_roundtrips(seconds),
      proof: ~LEAN"""
      cases seconds <;> simp [«seconds_to_daystime_roundtrips:requires/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have time (s : Int) (lo : 0 ≤ s) (hi : s < 86400) :
          Erlang.calendar.«seconds_to_time/1» (.integer s) =
            .ok (.tuple #[.integer (s / 3600), .integer ((s % 3600) / 60),
              .integer (s % 60)]) := by
        have rem0 : 0 ≤ s % 3600 := Int.emod_nonneg _ (by decide)
        simp [Erlang.calendar.«seconds_to_time/1», lo, hi,
          Erlang.erlang.«and/2», Erlang.erlang.«div/2», Erlang.erlang.«rem/2»,
          Int.tmod_eq_emod_of_nonneg lo, Int.emod_eq_of_lt lo hi,
          Int.tdiv_eq_ediv_of_nonneg lo, Int.tdiv_eq_ediv_of_nonneg rem0,
          Int.tmod_eq_emod_of_nonneg rem0, Int.emod_emod_of_dvd]
      have lo : 0 ≤ n % 86400 := Int.emod_nonneg _ (by decide)
      have hi : n % 86400 < 86400 := Int.emod_lt_of_pos _ (by decide)
      have returned : Erlang.calendar.«seconds_to_daystime/1» (.integer n) =
          .ok (.tuple #[.integer (n / 86400),
            .tuple #[.integer ((n % 86400) / 3600),
              .integer (((n % 86400) % 3600) / 60),
              .integer ((n % 86400) % 60)]]) := by
        by_cases normal : 0 ≤ n ∨ (86400 : Int) ∣ n
        · simp [Erlang.calendar.«seconds_to_daystime/1», Erlang.erlang.«div/2»,
            Erlang.erlang.«rem/2», Int.tdiv_eq_ediv, Int.tmod_eq_emod, normal,
            show ¬ n % 86400 < 0 by omega, time _ lo hi]
        · have negative : n % 86400 - 86400 < 0 := by omega
          simp [Erlang.calendar.«seconds_to_daystime/1», Erlang.erlang.«div/2»,
            Erlang.erlang.«rem/2», Int.tdiv_eq_ediv, Int.tmod_eq_emod, normal,
            negative, time _ lo hi, show Int.sign 86400 = 1 by rfl]
      have hourLo : 0 ≤ (n % 86400) / 3600 := Int.ediv_nonneg lo (by decide)
      have hourHi : (n % 86400) / 3600 < 24 := by omega
      have minuteLo : 0 ≤ ((n % 86400) % 3600) / 60 := by omega
      have minuteHi : ((n % 86400) % 3600) / 60 < 60 := by omega
      have secondLo : 0 ≤ (n % 86400) % 60 := Int.emod_nonneg _ (by decide)
      have secondHi : (n % 86400) % 60 < 60 := Int.emod_lt_of_pos _ (by decide)
      have reconstruct : n / 86400 * 86400 +
          ((n % 86400) / 3600 * 3600 + ((n % 86400) % 3600) / 60 * 60 +
            (n % 86400) % 60) = n := by omega
      simp at minuteLo minuteHi secondLo secondHi reconstruct
      simp [«seconds_to_daystime_roundtrips:ensures/1», «daystime_roundtrips/1»,
        returned, Erlang.calendar.«time_to_seconds/1», «valid_time/1»,
        Erlang.erlang.«is_integer/1», hourLo, hourHi, minuteLo, minuteHi,
        secondLo, secondHi, reconstruct, Erlang.erlang.«=:=/2»]
      """

    law seconds_to_time_roundtrips(hour, minute, second),
      requires: valid_time({hour, minute, second}),
      expects:
        :calendar.seconds_to_time(:calendar.time_to_seconds({hour, minute, second})) ===
          {hour, minute, second},
      proof: ~LEAN"""
      cases hour <;> simp [«seconds_to_time_roundtrips:requires/3», «valid_time/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i h
      by_cases hLo : 0 ≤ h <;> simp [hLo] at requires
      by_cases hHi : h < 24 <;> simp [hHi] at requires
      cases minute <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i m
      by_cases mLo : 0 ≤ m <;> simp [mLo] at requires
      by_cases mHi : m < 60 <;> simp [mHi] at requires
      cases second <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i s
      by_cases sLo : 0 ≤ s <;> simp [sLo] at requires
      by_cases sHi : s < 60 <;> simp [sHi] at requires
      have lo : 0 ≤ h * 3600 + m * 60 + s := by omega
      have hi : h * 3600 + m * 60 + s < 86400 := by omega
      have hRecovered : (h * 3600 + m * 60 + s) / 3600 = h := by omega
      have remainder : (h * 3600 + m * 60 + s) % 3600 = m * 60 + s := by omega
      have mRecovered : (m * 60 + s) / 60 = m := by omega
      have sRecovered : (m * 60 + s) % 60 = s := by omega
      have remLo : 0 ≤ m * 60 + s := by omega
      simp [«seconds_to_time_roundtrips:ensures/3»,
        Erlang.calendar.«time_to_seconds/1», Erlang.calendar.«seconds_to_time/1»,
        lo, hi, Erlang.erlang.«and/2», Erlang.erlang.«div/2», Erlang.erlang.«rem/2»,
        Int.tmod_eq_emod_of_nonneg lo, Int.emod_eq_of_lt lo hi,
        Int.tdiv_eq_ediv_of_nonneg lo, remainder, hRecovered,
        Int.tdiv_eq_ediv_of_nonneg remLo, Int.tmod_eq_emod_of_nonneg remLo,
        mRecovered, sRecovered, Erlang.erlang.«=:=/2»]
      """

    law is_leap_year_cycle(year),
      requires: valid_year(year),
      expects: :calendar.is_leap_year(year + 400) === :calendar.is_leap_year(year),
      proof: ~LEAN"""
      cases year <;> simp [«is_leap_year_cycle:requires/1», «valid_year/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have nonnegative : 0 ≤ n := by
        by_cases h : 0 ≤ n <;> simp [h] at requires <;> omega
      have shifted : 0 ≤ n + 400 := by omega
      by_cases four : n % 4 = 0 <;>
        by_cases century : 0 < n % 100 <;>
        by_cases fourHundred : n % 400 = 0 <;>
        simp [«is_leap_year_cycle:ensures/1», Erlang.calendar.«is_leap_year/1»,
        Erlang.calendar.«is_leap_year1/1», nonnegative, shifted,
        Erlang.erlang.«rem/2», Int.tmod_eq_emod_of_nonneg nonnegative,
        Int.tmod_eq_emod_of_nonneg shifted, Int.add_emod, four, century,
        fourHundred, Erlang.erlang.«and/2», Erlang.erlang.«=:=/2»,
        Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt]
      """

    law date_to_gregorian_days_cycle(year),
      requires: valid_year(year),
      expects:
        :calendar.date_to_gregorian_days({year + 400, 1, 1}) ===
          :calendar.date_to_gregorian_days({year, 1, 1}) + 146_097,
      proof: ~LEAN"""
      cases year <;> simp [«date_to_gregorian_days_cycle:requires/1», «valid_year/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have nonnegative : 0 ≤ n := by
        by_cases h : 0 ≤ n <;> simp [h] at requires <;> omega
      have shifted : 0 ≤ n + 400 := by omega
      have january (y : Int) (lo : 0 ≤ y) :
          Erlang.calendar.«date_to_gregorian_days/1»
              (.tuple #[.integer y, .integer 1, .integer 1]) =
            .ok (.integer (if y = 0 then 0 else
              (y - 1) / 4 - (y - 1) / 100 + (y - 1) / 400 + (y - 1) * 365 + 366)) := by
        by_cases zero : y = 0
        · subst y
          simp [Erlang.calendar.«date_to_gregorian_days/1»,
            Erlang.calendar.«date_to_gregorian_days/3»,
            Erlang.calendar.«last_day_of_the_month/2»,
            Erlang.calendar.«last_day_of_the_month1/2»,
            Erlang.calendar.«dy/1», Erlang.calendar.«dm/1», Erlang.calendar.«df/2»,
            Erlang.erlang.«is_integer/1», Erlang.erlang.«>/2»,
            Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»]
        · have positive : ¬ y ≤ 0 := by omega
          have previous : 0 ≤ y - 1 := by omega
          simp [Erlang.calendar.«date_to_gregorian_days/1»,
            Erlang.calendar.«date_to_gregorian_days/3»,
            Erlang.calendar.«last_day_of_the_month/2»,
            Erlang.calendar.«last_day_of_the_month1/2»,
            Erlang.calendar.«dy/1», Erlang.calendar.«dm/1», Erlang.calendar.«df/2»,
            lo, positive, zero, Erlang.erlang.«is_integer/1», Erlang.erlang.«>/2»,
            Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
            Erlang.erlang.«div/2», Int.tdiv_eq_ediv_of_nonneg previous]
      have cycle : (n + 400 - 1) / 4 - (n + 400 - 1) / 100 +
          (n + 400 - 1) / 400 + (n + 400 - 1) * 365 + 366 =
          (if n = 0 then 0 else
            (n - 1) / 4 - (n - 1) / 100 + (n - 1) / 400 + (n - 1) * 365 + 366) +
            146097 := by
        by_cases zero : n = 0
        · subst n; rfl
        · simp [zero]; omega
      simp [«date_to_gregorian_days_cycle:ensures/1», january _ nonnegative,
        january _ shifted, show ¬ n + 400 = 0 by omega, cycle, Erlang.erlang.«=:=/2»]
      """
  end

  # Expected to fail on OTP 28.1.1: valid dates {0, 1, 1} and {0, 1, 2}
  # reach a rejected negative year when computing the previous ISO week-year.
  laws "ISO week totality" do
    law iso_week_number_valid_date(date),
      requires: :calendar.valid_date(date),
      expects: is_tuple(:calendar.iso_week_number(date)),
      proof: ~LEAN"""
      by_cases boundary : date = .tuple #[.integer 0, .integer 1, .integer 1]
      · subst date
        simp [«iso_week_number_valid_date:ensures/1»,
          Erlang.calendar.«iso_week_number/1»,
          Erlang.calendar.«gregorian_days_of_iso_w01_1/1»,
          Erlang.calendar.«day_of_the_week/3»,
          Erlang.calendar.«date_to_gregorian_days/1»,
          Erlang.calendar.«date_to_gregorian_days/3»,
          Erlang.calendar.«last_day_of_the_month/2»,
          Erlang.calendar.«last_day_of_the_month1/2»,
          Erlang.calendar.«dy/1», Erlang.calendar.«dm/1», Erlang.calendar.«df/2»,
          Erlang.erlang.«is_integer/1», Erlang.erlang.«>/2»,
          Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
          Erlang.erlang.«div/2», Erlang.erlang.«rem/2», Erlang.erlang.«=:=/2»]
      · simp [«iso_week_number_valid_date:ensures/1»]
      """
  end
end
