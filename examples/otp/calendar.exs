# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/calendar.exs
# Prove the installed OTP calendar module, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1, ERTS 17.1.1).
# ISO-week verification needs general support for domain-restricted termination.
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
        returned, Erlang.calendar.«time_to_seconds/1», Erlang.erlang.«is_integer/3»,
        show (n % 86400) / 3600 ≤ 23 by omega,
        show (n % 3600) / 60 ≤ 59 by omega, show n % 60 ≤ 59 by omega, «valid_time/1»,
        Erlang.erlang.«is_integer/1», hourLo, hourHi, minuteLo, minuteHi,
        secondLo, secondHi, reconstruct, Erlang.erlang.«and/2», Erlang.erlang.«=:=/2»]
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
        lo, hi, Erlang.erlang.«is_integer/3»,
        show h ≤ 23 by omega, show m ≤ 59 by omega, show s ≤ 59 by omega,
        hLo, mLo, sLo, Erlang.erlang.«and/2», Erlang.erlang.«div/2», Erlang.erlang.«rem/2»,
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
        by_cases century : n % 100 = 0 <;>
        by_cases fourHundred : n % 400 = 0 <;>
        simp [«is_leap_year_cycle:ensures/1», Erlang.calendar.«is_leap_year/1»,
        Erlang.calendar.«is_leap_year1/1», nonnegative, shifted,
        Erlang.erlang.«rem/2», Int.tmod_eq_emod_of_nonneg nonnegative,
        Int.tmod_eq_emod_of_nonneg shifted, Int.add_emod, four, century,
        fourHundred, Erlang.erlang.«and/2», Erlang.erlang.«=:=/2», Erlang.erlang.«=/=/2»,
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
            .ok (.integer (((y - 1) / 400) * 146097 +
              365 * ((y - 1) % 400) + ((y - 1) % 400) / 4 -
              ((y - 1) % 400) / 100 + 366)) := by
        by_cases zero : y = 0
        · subst y
          simp [Erlang.calendar.«date_to_gregorian_days/1»,
            Erlang.calendar.«date_to_gregorian_days/3», Erlang.erlang.«div/2»,
            Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt,
            Erlang.erlang.«and/2»]
        · have previous : 0 ≤ y - 1 := by omega
          have remainder : y - 1 - (y - 1) / 400 * 400 = (y - 1) % 400 := by omega
          have remLo : 0 ≤ (y - 1) % 400 := Int.emod_nonneg _ (by decide)
          simp [Erlang.calendar.«date_to_gregorian_days/1»,
            Erlang.calendar.«date_to_gregorian_days/3»,
            show 1 ≤ y by omega, Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
            Int.compare_eq_gt, Erlang.erlang.«and/2», Erlang.erlang.«div/2»,
            Int.tdiv_eq_ediv_of_nonneg previous, remainder,
            Int.tdiv_eq_ediv_of_nonneg remLo]
          omega
      have cycle : ((n + 400 - 1) / 400) * 146097 +
          365 * ((n + 400 - 1) % 400) + ((n + 400 - 1) % 400) / 4 -
          ((n + 400 - 1) % 400) / 100 + 366 =
          ((n - 1) / 400) * 146097 +
          365 * ((n - 1) % 400) + ((n - 1) % 400) / 4 -
          ((n - 1) % 400) / 100 + 366 + 146097 := by omega
      simp [«date_to_gregorian_days_cycle:ensures/1», january _ nonnegative,
        january _ shifted, cycle, Erlang.erlang.«=:=/2»]
      """
  end

  # Includes dates whose ISO week belongs to the preceding, negative year.
  laws "ISO week totality" do
    termination_suffix &:calendar.mod/2, ~LEAN"""
    partial_fixpoint monotonicity by
      intro f g h n
      cases n <;> cases _1 <;>
        simp [Erlang.erlang.«rem/2», Erlang.erlang.«</2»,
          Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind]
      all_goals try exact Lean.Order.PartialOrder.rel_refl
      rename_i n d
      by_cases zero : d = 0
      · simp [zero]
        exact Lean.Order.PartialOrder.rel_refl
      · by_cases negative : n.tmod d < 0 <;>
          simp [zero, negative, Int.compare_eq_lt]
        · exact h _
        · exact Lean.Order.PartialOrder.rel_refl
    """

    law iso_week_number_valid_date(date),
      requires: :calendar.valid_date(date),
      expects: is_tuple(:calendar.iso_week_number(date)),
      proof: ~LEAN"""
      have modulo (n d : Int) (positive : 0 < d) :
          ∃ r, Erlang.calendar.«mod/2» (.integer n) (.integer d) = .ok (.integer r) := by
        have nonzero : d ≠ 0 := by omega
        have nonnegative (value : Int) (lo : 0 ≤ value) :
            Erlang.calendar.«mod/2» (.integer value) (.integer d) = .ok (.integer (value.tmod d)) := by
          have remLo := Int.tmod_nonneg d lo
          rw [Erlang.calendar.«mod/2».eq_def]
          simp [Erlang.erlang.«rem/2», nonzero, Erlang.erlang.«</2»,
            Ordering.isLT_iff_eq_lt, Int.compare_eq_lt, show ¬ value.tmod d < 0 by omega]
        by_cases negative : n.tmod d < 0
        · have corrected : 0 ≤ n.tmod d + d := by
            have := Int.lt_tmod_of_pos n positive
            omega
          rw [Erlang.calendar.«mod/2».eq_def]
          simp [Erlang.erlang.«rem/2», nonzero, Erlang.erlang.«</2»,
            Ordering.isLT_iff_eq_lt, Int.compare_eq_lt, negative, nonnegative _ corrected]
        · rw [Erlang.calendar.«mod/2».eq_def]
          simp [Erlang.erlang.«rem/2», nonzero, Erlang.erlang.«</2»,
            Ordering.isLT_iff_eq_lt, Int.compare_eq_lt, negative]

      have days (y m d : Int) (positive : 0 < d) :
          ∃ n, Erlang.calendar.«date_to_gregorian_days/3» (.integer y) (.integer m) (.integer d) =
            .ok (.integer n) := by
        by_cases march : m ≤ 2
        · by_cases era : 1 ≤ y
          · simp [Erlang.calendar.«date_to_gregorian_days/3», Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
              Erlang.erlang.«div/2», positive, march, show ¬ 2 < m by omega,
              era]
          · simp [Erlang.calendar.«date_to_gregorian_days/3», Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
              Erlang.erlang.«div/2», positive, march, show ¬ 2 < m by omega,
              era]
        · by_cases era : 0 ≤ y
          · simp [Erlang.calendar.«date_to_gregorian_days/3», Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
              Erlang.erlang.«div/2», positive, march, show 2 < m by omega, era]
          · simp [Erlang.calendar.«date_to_gregorian_days/3», Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
              Erlang.erlang.«div/2», positive, march, show 2 < m by omega, era]

      have weekday (y m d : Int) (positive : 0 < d) :
          ∃ n, Erlang.calendar.«day_of_the_week/3» (.integer y) (.integer m) (.integer d) =
            .ok (.integer n) := by
        obtain ⟨n, returned⟩ := days y m d positive
        obtain ⟨r, returnedMod⟩ := modulo (n + 5) 7 (by decide)
        simp [Erlang.calendar.«day_of_the_week/3», returned, returnedMod]

      have firstWeek (y : Int) :
          ∃ n, Erlang.calendar.«gregorian_days_of_iso_w01_1/1» (.integer y) = .ok (.integer n) := by
        obtain ⟨n, returned⟩ := days y 1 1 (by decide)
        obtain ⟨w, weekReturned⟩ := weekday y 1 1 (by decide)
        by_cases early : w ≤ 4 <;>
          simp [Erlang.calendar.«gregorian_days_of_iso_w01_1/1», returned, weekReturned, early]

      have iso (y m d : Int) (positive : 0 < d) :
          ∃ fields, Erlang.calendar.«iso_week_number/1» (.tuple #[.integer y, .integer m, .integer d]) =
            .ok (.tuple fields) := by
        obtain ⟨n, returned⟩ := days y m d positive
        obtain ⟨w, first⟩ := firstWeek y
        obtain ⟨next, nextFirst⟩ := firstWeek (y + 1)
        obtain ⟨jan, january⟩ := weekday (y - 1) 1 1 (by decide)
        obtain ⟨dec, december⟩ := weekday (y - 1) 12 31 (by decide)
        by_cases current : w ≤ n ∧ n < next
        · simp [Erlang.calendar.«iso_week_number/1», Erlang.calendar.«date_to_gregorian_days/1»,
            returned, first, nextFirst, current.1, current.2, Erlang.erlang.«=:=/2», Erlang.erlang.«div/2»]
        · by_cases previous : n < w
          · by_cases janFour : jan = 4 <;> by_cases decFour : dec = 4 <;>
              simp [Erlang.calendar.«iso_week_number/1», Erlang.calendar.«date_to_gregorian_days/1»,
                returned, first, nextFirst, january, december, previous, show ¬ w ≤ n by omega,
                Erlang.erlang.«=:=/2», janFour, decFour]
          · have nextYear : next ≤ n := by omega
            simp [Erlang.calendar.«iso_week_number/1», Erlang.calendar.«date_to_gregorian_days/1»,
              returned, first, nextFirst, previous, nextYear, show w ≤ n by omega,
              show ¬ n < next by omega, Erlang.erlang.«=:=/2»]

      have dateShape (date : Lynx.Term) (valid : Erlang.calendar.«valid_date/1» date = .ok Lynx.Term.true) :
          ∃ y m d : Int, date = .tuple #[.integer y, .integer m, .integer d] ∧ 0 < d := by
        cases date <;> simp [Erlang.calendar.«valid_date/1»] at valid
        rename_i fields
        rcases fields with ⟨fields⟩
        match fields with
        | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ =>
          simp at valid
        | [y, m, d] =>
          cases y <;> simp [Erlang.calendar.«valid_date/3»] at valid
          rename_i y
          cases m <;> try simp at valid
          rename_i m
          cases d <;> try simp at valid
          rename_i d
          by_cases monthLo : 0 < m <;> by_cases monthHi : m < 13 <;> by_cases dayLo : 0 < d <;>
            simp [Erlang.calendar.«valid_date1/3», Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
              monthLo, monthHi, dayLo] at valid
          exact ⟨y, m, d, rfl, dayLo⟩

      obtain ⟨y, m, d, rfl, positive⟩ := dateShape date (by
        simpa [«iso_week_number_valid_date:requires/1»] using requires)
      obtain ⟨fields, returned⟩ := iso y m d positive
      simp [«iso_week_number_valid_date:ensures/1», returned, Erlang.erlang.«is_tuple/1»]
      """
  end
end
