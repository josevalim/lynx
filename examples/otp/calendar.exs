# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/calendar.exs
# Prove the installed OTP calendar module, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1, ERTS 17.1.1).
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

  def gregorian_days_contract(days) do
    date = :calendar.gregorian_days_to_date(days)
    :calendar.valid_date(date) and :calendar.date_to_gregorian_days(date) === days
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

  laws "Gregorian day round trip", options: [maxHeartbeats: 500_000] do
    law gregorian_days_roundtrip(days),
      requires: is_integer(days),
      expects: gregorian_days_contract(days),
      proof: ~LEAN"""
      let rawEra (n : Int) := if 0 ≤ n-60 then (n-60).tdiv 146097 else (n-60-146097+1).tdiv 146097
      let rawD (n : Int) := n-60-rawEra n*146097
      let rawY (n : Int) := (rawD n-(rawD n).tdiv 1460+(rawD n).tdiv 36524-(rawD n).tdiv 146096).tdiv 365
      let rawR (n : Int) := rawD n-(365*rawY n+(rawY n).tdiv 4-(rawY n).tdiv 100)
      let rawMP (n : Int) := (5*rawR n+2).tdiv 153
      let rawMonth (n : Int) := if rawMP n<10 then rawMP n+3 else rawMP n-9

      have decodedRaw (n : Int) : Erlang.calendar.«gregorian_days_to_date/1» (.integer n) =
          .ok (.tuple #[.integer (rawY n+rawEra n*400+if rawMonth n≤2 then 1 else 0),
            .integer (rawMonth n), .integer (rawR n-(153*rawMP n+2).tdiv 5+1)]) := by
        have pureOk {α : Type} (a : α) : (pure a : Lynx.Result α) = .ok a := rfl
        have okBind {α β : Type} (a : α) (k : α → Lynx.Result β) : (Lynx.Result.ok a >>= k) = k a := rfl
        have divide (a b : Int) (nonzero : b ≠ 0) :
            Erlang.erlang.«div/2» (.integer a) (.integer b) = .ok (.integer (a.tdiv b)) := by
          simp [Erlang.erlang.«div/2», nonzero]
        have branch (p : Prop) [Decidable p] (yes no : Unit → Lynx.Result) :
            Lynx.Result.guard (.ok (if p then Lynx.Term.true else Lynx.Term.false)) yes no =
              if p then yes () else no () := by
          by_cases h : p <;> simp [h]
        have iteResult (p : Prop) [Decidable p] (a b : Lynx.Term) :
            (if p then Lynx.Result.ok a else Lynx.Result.ok b) = Lynx.Result.ok (if p then a else b) := by split <;> rfl
        have iteInteger (p : Prop) [Decidable p] (a b : Int) :
            (if p then Lynx.Term.integer a else Lynx.Term.integer b) = Lynx.Term.integer (if p then a else b) := by split <;> rfl
        simp (disch := decide) only [Erlang.calendar.«gregorian_days_to_date/1»,
          Erlang.erlang.«+/2_integers», Erlang.erlang.«-/2_integers»,
          Erlang.erlang.«*/2_integers», divide, Erlang.erlang.«>=/2_integers»,
          Erlang.erlang.«</2_integers», Erlang.erlang.«=</2_integers», branch,
          iteResult, iteInteger, pureOk, okBind]
        change (Lynx.Result.ok (Lynx.Term.tuple #[.integer (if rawMonth n≤2 then rawY n+rawEra n*400+1 else rawY n+rawEra n*400),
          .integer (rawMonth n), .integer (rawR n-(153*rawMP n+2).tdiv 5+1)])) = _
        by_cases h : rawMonth n≤2 <;> simp [h]

      let dateNumber (year month day : Int) : Int :=
        let y := if month≤2 then year-1 else year
        let era := if 0≤y then y.tdiv 400 else (y-399).tdiv 400
        let yo := y-era*400
        let mp := if 2<month then month-3 else month+9
        era*146097+(365*yo+yo.tdiv 4-yo.tdiv 100+(153*mp+2).tdiv 5+day-1)+60

      have encodedRaw (year month day : Int) (positive : 0 < day) :
          Erlang.calendar.«date_to_gregorian_days/1»
            (.tuple #[.integer year, .integer month, .integer day]) = .ok (.integer (dateNumber year month day)) := by
        have pureOk {α : Type} (a : α) : (pure a : Lynx.Result α) = .ok a := rfl
        have okBind {α β : Type} (a : α) (k : α → Lynx.Result β) : (Lynx.Result.ok a >>= k) = k a := rfl
        have divide (a b : Int) (nonzero : b ≠ 0) :
            Erlang.erlang.«div/2» (.integer a) (.integer b) = .ok (.integer (a.tdiv b)) := by
          simp [Erlang.erlang.«div/2», nonzero]
        have branch (p : Prop) [Decidable p] (yes no : Unit → Lynx.Result) :
            Lynx.Result.guard (.ok (if p then Lynx.Term.true else Lynx.Term.false)) yes no =
              if p then yes () else no () := by
          by_cases h : p <;> simp [h]
        have iteResult (p : Prop) [Decidable p] (a b : Lynx.Term) :
            (if p then Lynx.Result.ok a else Lynx.Result.ok b) = Lynx.Result.ok (if p then a else b) := by split <;> rfl
        have iteInteger (p : Prop) [Decidable p] (a b : Int) :
            (if p then Lynx.Term.integer a else Lynx.Term.integer b) = Lynx.Term.integer (if p then a else b) := by split <;> rfl
        have branchTrue (yes no : Unit → Lynx.Result) :
            Lynx.Result.guard (.ok Lynx.Term.true) yes no = yes () := rfl
        have greater (a b : Int) : Erlang.erlang.«>/2» (.integer a) (.integer b) =
            .ok (if b<a then Lynx.Term.true else Lynx.Term.false) := by
          simp [Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt]
        simp (disch := decide) only [Erlang.calendar.«date_to_gregorian_days/1»,
          Erlang.calendar.«date_to_gregorian_days/3»,
          Erlang.erlang.«+/2_integers», Erlang.erlang.«-/2_integers»,
          Erlang.erlang.«*/2_integers», divide, Erlang.erlang.«>=/2_integers», greater,
          Erlang.erlang.«=</2_integers», branch, iteResult, iteInteger, pureOk, okBind,
          positive, if_true, Erlang.erlang.«and/2», branchTrue, Lynx.Result.tryWith_ok]
        simp only [Lynx.Term.true, branchTrue]
        apply congrArg (fun value : Int => Lynx.Result.ok (Lynx.Term.integer value))
        dsimp [dateNumber]
        omega

      let leap (year : Int) : Prop := year%4=0 ∧ (year%100≠0 ∨ year%400=0)
      letI leapDecidable (year : Int) : Decidable (leap year) := inferInstanceAs (Decidable (_ ∧ _))
      let monthDays (year month : Int) : Int :=
        if month=2 then if leap year then 29 else 28
        else if month=4 ∨ month=6 ∨ month=9 ∨ month=11 then 30 else 31

      have modelSpec (n : Int) :
          let e := (n-60)/146097
          let d := (n-60)%146097
          let y := (d-d/1460+d/36524-d/146096)/365
          let r := d-(365*y+y/4-y/100)
          let mp := (5*r+2)/153
          let year := y+e*400+if mp<10 then 0 else 1
          let month := if mp<10 then mp+3 else mp-9
          let day := r-(153*mp+2)/5+1
          dateNumber year month day = n ∧
            1≤month ∧ month≤12 ∧ 1≤day ∧ day≤monthDays year month := by
        dsimp only
        let e := (n-60)/146097
        let d := (n-60)%146097
        let y := (d-d/1460+d/36524-d/146096)/365
        let r := d-(365*y+y/4-y/100)
        let mp := (5*r+2)/153
        change dateNumber (y+e*400+if mp<10 then 0 else 1)
          (if mp<10 then mp+3 else mp-9) (r-(153*mp+2)/5+1) = n ∧
            1≤(if mp<10 then mp+3 else mp-9) ∧ (if mp<10 then mp+3 else mp-9)≤12 ∧
            1≤r-(153*mp+2)/5+1 ∧ r-(153*mp+2)/5+1≤
              monthDays (y+e*400+if mp<10 then 0 else 1) (if mp<10 then mp+3 else mp-9)
        have dLo : 0≤d := Int.emod_nonneg _ (by decide)
        have dHi : d<146097 := Int.emod_lt_of_pos _ (by decide)
        have yBounds : 0≤y ∧ y<400 := by dsimp [y]; omega
        have rBounds : 0≤r ∧ r≤365 := by
          have century : y/100=0 ∨ y/100=1 ∨ y/100=2 ∨ y/100=3 := by omega
          have residue : y%4=0 ∨ y%4=1 ∨ y%4=2 ∨ y%4=3 := by omega
          rcases century with h|h|h|h <;> rcases residue with rem|rem|rem|rem <;>
            dsimp [r,y] at * <;> omega
        have leapSpec (d : Int) (lo : 0≤d) (hi : d<146097) :
            let y := (d-d/1460+d/36524-d/146096)/365
            d-(365*y+y/4-y/100) ≤ if leap (y+1) then 365 else 364 := by
          dsimp only
          let y := (d-d/1460+d/36524-d/146096)/365
          change d-(365*y+y/4-y/100) ≤ if leap (y+1) then 365 else 364
          have yBounds : 0≤y ∧ y<400 := by dsimp [y]; omega
          have century : y/100=0 ∨ y/100=1 ∨ y/100=2 ∨ y/100=3 := by omega
          have residue : y%4=0 ∨ y%4=1 ∨ y%4=2 ∨ y%4=3 := by omega
          by_cases isLeap : leap (y+1)
          all_goals simp only [isLeap, if_true, if_false]
          all_goals rcases century with h|h|h|h <;>
            rcases residue with rem|rem|rem|rem <;> dsimp [leap,y] at * <;> omega
        have leapBound := leapSpec d dLo dHi
        change r ≤ if leap (y+1) then 365 else 364 at leapBound
        have mpBounds : 0≤mp ∧ mp≤11 := by dsimp [mp]; omega
        have dayLo : 1≤r-(153*mp+2)/5+1 := by dsimp [mp]; omega
        have floor400 (z : Int) :
            (if 0≤z then z.tdiv 400 else (z-399).tdiv 400) = z/400 := by
          by_cases h : 0≤z
          · simp [h, Int.tdiv_eq_ediv_of_nonneg h]
          · simp only [h, if_false, Int.tdiv_eq_ediv, show Int.sign 400=1 by rfl]
            split <;> omega
        have adjusted : (if (if mp<10 then mp+3 else mp-9)≤2 then
            (y+e*400+if mp<10 then 0 else 1)-1 else y+e*400+if mp<10 then 0 else 1) = y+e*400 := by
          split <;> split <;> omega
        have monthPrime : (if 2<(if mp<10 then mp+3 else mp-9) then
            (if mp<10 then mp+3 else mp-9)-3 else (if mp<10 then mp+3 else mp-9)+9) = mp := by
          split <;> split <;> omega
        have era : (y+e*400)/400=e := by omega
        constructor
        · simp only [dateNumber, adjusted, floor400, era, monthPrime]
          have ye : y+e*400-e*400=y := by omega
          simp only [ye, Int.tdiv_eq_ediv_of_nonneg yBounds.1,
            Int.tdiv_eq_ediv_of_nonneg (show 0≤153*mp+2 by omega)]
          dsimp [r,e,d] at *
          omega
        · refine ⟨?_, ?_, dayLo, ?_⟩
          · split <;> omega
          · split <;> omega
          · have casesMP : mp=0 ∨ mp=1 ∨ mp=2 ∨ mp=3 ∨ mp=4 ∨ mp=5 ∨
                mp=6 ∨ mp=7 ∨ mp=8 ∨ mp=9 ∨ mp=10 ∨ mp=11 := by omega
            rcases casesMP with h|h|h|h|h|h|h|h|h|h|h|h
            all_goals simp only [h, Int.reduceLT, if_true, if_false, Int.add_zero, Int.reduceAdd,
              Int.reduceSub, monthDays, Int.reduceEq, or_false, or_true]
            all_goals try (dsimp [mp] at h; omega)

      have leapReturned (year : Int) : Erlang.calendar.«is_leap_year/1» (.integer year) =
          .ok (if leap year then Lynx.Term.true else Lynx.Term.false) := by
        have modZero (a b : Int) : a.tmod b=0 ↔ a%b=0 := by
          rw [← Int.dvd_iff_tmod_eq_zero, Int.dvd_iff_emod_eq_zero]
        by_cases four : year%4=0 <;> by_cases hundred : year%100=0 <;> by_cases era : year%400=0
        all_goals simp [Erlang.calendar.«is_leap_year/1», Erlang.calendar.«is_leap_year1/1»,
          Erlang.erlang.«rem/2», Erlang.erlang.«=:=/2», Erlang.erlang.«=/=/2»,
          Erlang.erlang.«and/2», modZero, four, hundred, era, leap]
        all_goals omega

      have lastDayReturned (year month : Int) (lo : 1≤month) (hi : month≤12) :
          Erlang.calendar.«last_day_of_the_month/2» (.integer year) (.integer month) =
            .ok (.integer (monthDays year month)) := by
        by_cases four : month=4
        · subst month; rfl
        by_cases six : month=6
        · subst month; rfl
        by_cases nine : month=9
        · subst month; rfl
        by_cases eleven : month=11
        · subst month; rfl
        by_cases two : month=2
        · subst month
          by_cases h : leap year <;>
            simp [Erlang.calendar.«last_day_of_the_month/2», Erlang.calendar.«last_day_of_the_month1/2»,
              leapReturned, h, monthDays]
        have mPos : 0<month := by omega
        have mHi : month<13 := by omega
        simp [Erlang.calendar.«last_day_of_the_month/2», Erlang.calendar.«last_day_of_the_month1/2»,
          monthDays, four, six, nine, eleven, two,
          Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, mPos, mHi,
          Erlang.erlang.«and/2»]

      have validReturned (year month day : Int) (mLo : 1≤month) (mHi : month≤12)
          (dLo : 1≤day) (dHi : day≤monthDays year month) :
          Erlang.calendar.«valid_date/1» (.tuple #[.integer year, .integer month, .integer day]) = .ok Lynx.Term.true := by
        simp [Erlang.calendar.«valid_date/1», Erlang.calendar.«valid_date/3»,
          Erlang.calendar.«valid_date1/3», Erlang.erlang.«is_integer/1»,
          Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt,
          show 0<month by omega, show month<13 by omega, show 0<day by omega,
          Erlang.erlang.«and/2», lastDayReturned year month mLo mHi, dHi]

      have normalizedDecoded (n : Int) :
          let e := (n-60)/146097
          let d := (n-60)%146097
          let y := (d-d/1460+d/36524-d/146096)/365
          let r := d-(365*y+y/4-y/100)
          let mp := (5*r+2)/153
          Erlang.calendar.«gregorian_days_to_date/1» (.integer n) =
            .ok (.tuple #[.integer (y+e*400+if mp<10 then 0 else 1),
              .integer (if mp<10 then mp+3 else mp-9), .integer (r-(153*mp+2)/5+1)]) := by
        let e := (n-60)/146097
        let d := (n-60)%146097
        let y := (d-d/1460+d/36524-d/146096)/365
        let r := d-(365*y+y/4-y/100)
        let mp := (5*r+2)/153
        change Erlang.calendar.«gregorian_days_to_date/1» (.integer n) = .ok (.tuple #[
          .integer (y+e*400+if mp<10 then 0 else 1), .integer (if mp<10 then mp+3 else mp-9),
          .integer (r-(153*mp+2)/5+1)])
        have dLo : 0≤d := Int.emod_nonneg _ (by decide)
        have dHi : d<146097 := Int.emod_lt_of_pos _ (by decide)
        have yBounds : 0≤y ∧ y<400 := by dsimp [y]; omega
        have rBounds : 0≤r ∧ r≤365 := by
          have century : y/100=0 ∨ y/100=1 ∨ y/100=2 ∨ y/100=3 := by omega
          have residue : y%4=0 ∨ y%4=1 ∨ y%4=2 ∨ y%4=3 := by omega
          rcases century with h|h|h|h <;> rcases residue with rem|rem|rem|rem <;>
            dsimp [r,y] at * <;> omega
        have floorEra (z : Int) :
            (if 0≤z then z.tdiv 146097 else (z-146096).tdiv 146097) = z/146097 := by
          by_cases h : 0≤z
          · simp [h, Int.tdiv_eq_ediv_of_nonneg h]
          · simp only [h, if_false, Int.tdiv_eq_ediv, show Int.sign 146097=1 by rfl]
            split <;> omega
        have eEq : rawEra n=e := by
          have regroup : n-60-146097+1=n-60-146096 := by omega
          simpa only [rawEra,regroup] using floorEra (n-60)
        have dEq : rawD n=d := by
          dsimp only [rawD]
          rw [eEq]
          dsimp [e,d]
          omega
        have adjustedLo : 0≤d-d/1460+d/36524-d/146096 := by omega
        have yEq : rawY n=y := by
          simp only [rawY,dEq,Int.tdiv_eq_ediv_of_nonneg dLo,
            Int.tdiv_eq_ediv_of_nonneg adjustedLo]
          rfl
        have rEq : rawR n=r := by
          simp only [rawR,dEq,yEq,Int.tdiv_eq_ediv_of_nonneg yBounds.1]
          rfl
        have mpEq : rawMP n=mp := by
          simp only [rawMP,rEq,Int.tdiv_eq_ediv_of_nonneg (show 0≤5*r+2 by omega)]
          rfl
        have mpBounds : 0≤mp ∧ mp≤11 := by dsimp [mp]; omega
        have monthCondition : (if mp<10 then mp+3 else mp-9)≤2 ↔ ¬mp<10 := by split <;> omega
        have translated := decodedRaw n
        simp only [eEq,yEq,rEq,mpEq,rawMonth,monthCondition,
          Int.tdiv_eq_ediv_of_nonneg (show 0≤153*mp+2 by omega)] at translated
        by_cases h : mp<10 <;> simpa only [h,if_true,if_false,not_false_eq_true,not_true_eq_false] using translated

      cases days <;> simp [«gregorian_days_roundtrip:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      let e := (n-60)/146097
      let d := (n-60)%146097
      let y := (d-d/1460+d/36524-d/146096)/365
      let r := d-(365*y+y/4-y/100)
      let mp := (5*r+2)/153
      let year := y+e*400+if mp<10 then 0 else 1
      let month := if mp<10 then mp+3 else mp-9
      let day := r-(153*mp+2)/5+1
      have returned := normalizedDecoded n
      change Erlang.calendar.«gregorian_days_to_date/1» (.integer n) =
        .ok (.tuple #[.integer year, .integer month, .integer day]) at returned
      have spec := modelSpec n
      change dateNumber year month day=n ∧ 1≤month ∧ month≤12 ∧ 1≤day ∧ day≤monthDays year month at spec
      obtain ⟨reconstructed, mLo, mHi, dLo, dHi⟩ := spec
      have encoded := encodedRaw year month day (by omega)
      rw [reconstructed] at encoded
      simp [«gregorian_days_roundtrip:ensures/1», «gregorian_days_contract/1», returned, encoded,
        validReturned year month day mLo mHi dLo dHi, Erlang.erlang.«=:=/2»]
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
