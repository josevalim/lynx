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

  laws "Calendar.ISO time round trip" do
    law time_fraction_roundtrips(hour, minute, second, microsecond, precision),
      requires: Calendar.ISO.valid_time?(hour, minute, second, {microsecond, precision}),
      expects:
        Calendar.ISO.time_from_day_fraction(
          Calendar.ISO.time_to_day_fraction(hour, minute, second, {microsecond, precision})
        ) === {hour, minute, second, {microsecond, 6}},
      proof: ~LEAN"""
      cases hour <;> simp [«time_fraction_roundtrips:requires/5»,
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
      let x := m * 60000000 + s * 1000000 + u
      have xLo : 0 ≤ x := by dsimp [x]; omega
      have xHi : x ≤ 3599999999 := by dsimp [x]; omega
      have minute : (((x >>> 8) * 18764999) >>> 42) = m := by
        simp only [Int.shiftRight_eq_div_pow]
        change (x / 256 * 18764999) / 4398046511104 = m
        have lo : m * 234375 ≤ x / 256 := by dsimp [x]; omega
        have hi : x / 256 < (m + 1) * 234375 := by dsimp [x]; omega
        omega
      have second : (((x >>> 6) * 70368745) >>> 40) = m * 60 + s := by
        simp only [Int.shiftRight_eq_div_pow]
        change (x / 64 * 70368745) / 1099511627776 = m * 60 + s
        dsimp [x]
        omega
      have mask : Erlang.erlang.«band/2» (.integer (m * 60 + s + m * 4)) (.integer 63) =
          .ok (.integer s) := by
        have nonnegative : 0 ≤ m * 60 + s + m * 4 := by omega
        have modulo : (m * 60 + s + m * 4) % 64 = s := by omega
        simpa [show (2 : Int) ^ 6 = 64 by decide, modulo] using
          Erlang.erlang.«band/2_mask» (m * 60 + s + m * 4) 6 nonnegative
      have micros : x - (m * 60 + s) * 1000000 = u := by dsimp [x]; omega
      let total := (h * 3600 + m * 60 + s) * 1000000 + u
      have totalLo : 0 ≤ total := by dsimp [total]; omega
      have hours : total.tdiv 3600000000 = h := by
        rw [Int.tdiv_eq_ediv_of_nonneg totalLo]
        dsimp [total]
        omega
      have remainder : total - h * 3600000000 = x := by dsimp [total, x]; omega
      have positiveRemainder : 0 ≤ total - h * 3600000000 := by omega
      have divided : Elixir.Calendar.ISO.«div_rem/2» (.integer total) (.integer 3600000000) =
          .ok (.tuple #[.integer h, .integer x]) := by
        simp [Elixir.Calendar.ISO.«div_rem/2», Erlang.erlang.«div/2»,
          hours, remainder, xLo]
      have restored : Elixir.Calendar.ISO.«time_from_day_fraction/1»
          (.tuple #[.integer total, .integer 86400000000]) =
          .ok (.tuple #[.integer h, .integer m, .integer s, .tuple #[.integer u, .integer 6]]) := by
        by_cases zero : total = 0
        · have hz : h = 0 := by dsimp [total] at zero; omega
          have mz : m = 0 := by dsimp [total] at zero; omega
          have sz : s = 0 := by dsimp [total] at zero; omega
          have uz : u = 0 := by dsimp [total] at zero; omega
          simp [Elixir.Calendar.ISO.«time_from_day_fraction/1», zero, hz, mz, sz, uz]
        · simp [Elixir.Calendar.ISO.«time_from_day_fraction/1», zero,
            Elixir.Calendar.ISO.«divide_by_parts_per_day/2», divided,
            Erlang.erlang.«bsr/2», Erlang.erlang.«is_integer/1», Erlang.erlang.«=:=/2»,
            xLo, xHi, minute, second, mask, micros]
      have encoded : Elixir.Calendar.ISO.«time_to_day_fraction/4» (.integer h) (.integer m)
          (.integer s) (.tuple #[.integer u, .integer p]) =
          .ok (.tuple #[.integer total, .integer 86400000000]) := by
        by_cases hz : h = 0 <;> by_cases mz : m = 0 <;>
          by_cases sz : s = 0 <;> by_cases uz : u = 0 <;>
          simp [Elixir.Calendar.ISO.«time_to_day_fraction/4», hz, mz, sz, uz, total]
      simp [«time_fraction_roundtrips:ensures/5», encoded, restored, Erlang.erlang.«=:=/2»]
      """
  end

  def date_roundtrip(days) do
    {year, month, day} = Calendar.ISO.date_from_iso_days(days)

    month >= 1 and month <= 12 and day >= 1 and
      day <= Calendar.ISO.days_in_month(year, month) and
      Calendar.ISO.date_to_iso_days(year, month, day) === days
  end

  laws "Calendar.ISO date round trip" do
    # Error construction uses a dynamic remote call; valid decoded dates must
    # never reach it. Date formatting itself is translated normally.
    cutoff &ArgumentError.exception/1
    cutoff &String.Chars.to_string/1

    # zero_pad/2 can diverge for unsupported widths; this law never formats
    # an invalid date, so keep that helper partial instead of assuming totality.
    termination_suffix &Calendar.ISO.zero_pad/2, ~LEAN"""
    partial_fixpoint monotonicity by
      intro f g h
      repeat' first
        | exact Lean.Order.PartialOrder.rel_refl
        | exact h _ _
        | apply Lynx.Result.tryWith_mono_pure
        | apply Lynx.Result.bind_mono_left
        | apply Lynx.Result.bind_mono_pure
        | apply Lynx.Result.IsPure.tryWith
        | apply Lynx.Result.IsPure.handle
        | apply Lynx.Result.IsPure.bind
        | apply Lynx.Result.IsPure.bind_explicit
        | (intro)
        | split
        | simp_all
    """

    law date_conversion_roundtrips_every_day(days),
      max_heartbeats: 1_000_000,
      requires: is_integer(days),
      expects: date_roundtrip(days),
      proof: ~LEAN"""
      -- The expectation reaches functions with termination suffixes, so it has no
      -- purity lemma; prove its direct statement under a pure precondition.
      refine Lynx.law_of_pure_requires (by simp) ?_ requires
      clear requires schedule
      intro requires
      have inverse (n : Int) : Elixir.Calendar.ISO.«date_from_iso_days/1» (.integer n) =
          .ok (let z := n - 60
            let era := if 0 ≤ z then z.tdiv 146097 else (z - 146097 + 1).tdiv 146097
            let r := z - era * 146097
            let y := (r - r.tdiv 1460 + r.tdiv 36524 - r.tdiv 146096).tdiv 365
            let d := r - (365 * y + y.tdiv 4 - y.tdiv 100)
            let mp := (5 * d + 2).tdiv 153
            let day := d - (153 * mp + 2).tdiv 5 + 1
            let month := if mp < 10 then mp + 3 else mp - 9
            let year := y + era * 400
            .tuple #[.integer (if month ≤ 2 then year + 1 else year), .integer month, .integer day]) := by
        by_cases sign : 60 ≤ n <;>
          simp [Elixir.Calendar.ISO.«date_from_iso_days/1», Erlang.erlang.«div/2», sign,
            show (0 ≤ n - 60) ↔ 60 ≤ n by omega,
            show n - 60 - 146097 + 1 = n - 146156 by omega]
        all_goals split <;> simp_all
        all_goals split <;> simp_all
        all_goals omega
      -- Inversion within a March-based 400-year era.
      have eraBounds (z : Int) (lo : 0 ≤ z) (hi : z < 146097) :
          let y := (z - z / 1460 + z / 36524 - z / 146096) / 365
          let d := z - (365 * y + y / 4 - y / 100)
          0 ≤ y ∧ y < 400 ∧ 0 ≤ d ∧ d ≤ 365 ∧ (d = 365 → y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399)) := by
        dsimp
        let y := (z - z / 1460 + z / 36524 - z / 146096) / 365
        have rem : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
        have centuries : z / 36524 = 0 ∨ z / 36524 = 1 ∨ z / 36524 = 2 ∨ z / 36524 = 3 ∨ z / 36524 = 4 := by omega
        have last : z / 146096 = 0 ∨ z / 146096 = 1 := by omega
        have century : y / 100 = min (z / 36524) 3 := by
          change ((z - z / 1460 + z / 36524 - z / 146096) / 365) / 100 = min (z / 36524) 3
          have c : z / 36524 = 0 ∨ z / 36524 = 1 ∨ z / 36524 = 2 ∨ z / 36524 = 3 ∨ z / 36524 = 4 := by omega
          have e : z / 146096 = 0 ∨ z / 146096 = 1 := by omega
          rcases c with c|c|c|c|c <;> rcases e with e|e <;> simp [c] <;> omega
        rcases rem with h | h | h | h <;> dsimp [y] at h <;>
          rcases centuries with c | c | c | c | c <;> rcases last with e | e <;> simp [c] at century <;> simp only [y] at century <;> omega

      have monthBounds (y d : Int) (yl : 0 ≤ y) (yh : y < 400) (dl : 0 ≤ d) (dh : d ≤ 365)
          (extra : d = 365 → y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399)) :
          let mp := (5 * d + 2) / 153
          let day := d - (153 * mp + 2) / 5 + 1
          let month := if mp < 10 then mp + 3 else mp - 9
          1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧
            day ≤ (if month = 2 then
              if y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399) then 29 else 28
              else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31) := by
        let mp := (5 * d + 2) / 153
        have choices : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨
            mp = 6 ∨ mp = 7 ∨ mp = 8 ∨ mp = 9 ∨ mp = 10 ∨ mp = 11 := by dsimp [mp]; omega
        rcases choices with h|h|h|h|h|h|h|h|h|h|h|h <;>
          simp only [← show (5 * d + 2) / 153 = mp from rfl, h] <;>
          dsimp [mp] at h <;> split <;> omega

      have adjustedDivision (z : Int) (b : Int) (choice : b = 400 ∨ b = 146097) :
          (if 0 ≤ z then z.tdiv b else (z - b + 1).tdiv b) = z / b := by
        rcases choice with rfl | rfl <;>
          by_cases sign : 0 ≤ z
        all_goals try { simp [sign, Int.tdiv_eq_ediv_of_nonneg sign] }
        all_goals simp only [if_neg sign]
        all_goals rw [Int.tdiv_eq_ediv]
        all_goals simp only [Int.dvd_iff_emod_eq_zero]
        all_goals split <;> (try simp only [show Int.sign 400 = 1 from rfl, show Int.sign 146097 = 1 from rfl]) <;> omega
      have february (y : Int) : Elixir.Calendar.ISO.«days_in_month_guarded/2» (.integer y) (.integer 2) =
          .ok (.integer (if y % 4 = 0 ∧ (y % 16 = 0 ∨ y % 100 ≠ 0) then 29 else 28)) := by
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
          simp [Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«band/2»,
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
          simp [Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«band/2»,
            Erlang.erlang.«=:=/2», Erlang.erlang.«=/=/2», Erlang.erlang.«rem/2», m4, m16, remZero, fourZero, sixteenZero, four, sixteen, hundred]
      have forward (year month day : Int) :
          Elixir.Calendar.ISO.«valid_date_to_iso_days/3» (.integer year) (.integer month) (.integer day) =
            .ok (.integer (let y := if month ≤ 2 then year - 1 else year
              let era := if 0 ≤ y then y.tdiv 400 else (y - 399).tdiv 400
              let yo := y - era * 400
              let mp := if 2 < month then month - 3 else month + 9
              era * 146097 + (365 * yo + yo.tdiv 4 - yo.tdiv 100 +
                ((153 * mp + 2).tdiv 5 + day - 1)) + 60)) := by
        unfold Elixir.Calendar.ISO.«valid_date_to_iso_days/3»
        split
        · simp only [Lynx.Term.integer.injEq] at *
          subst_vars
          rfl
        · simp only [Lynx.Term.integer.injEq] at *
          subst_vars
          rfl
        · by_cases early : month ≤ 2 <;>
            by_cases positive : 1 ≤ year <;> by_cases nonnegative : 0 ≤ year <;>
            simp [Erlang.erlang.«div/2», Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
              Int.compare_eq_gt, early, positive, nonnegative,
              show (0 ≤ year - 1) ↔ 1 ≤ year by omega,
              show (2 < month) ↔ ¬ month ≤ 2 by omega]
      have monthModel (year month : Int) (lower : 1 ≤ month) (upper : month ≤ 12) :
          Elixir.Calendar.ISO.«days_in_month/2» (.integer year) (.integer month) =
            .ok (.integer (if month = 2 then
              if year % 4 = 0 ∧ (year % 16 = 0 ∨ year % 100 ≠ 0) then 29 else 28
              else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31)) := by
        have guarded : Elixir.Calendar.ISO.«days_in_month_guarded/2» (.integer year) (.integer month) =
            .ok (.integer (if month = 2 then
              if year % 4 = 0 ∧ (year % 16 = 0 ∨ year % 100 ≠ 0) then 29 else 28
              else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31)) := by
          by_cases feb : month = 2
          · simpa [feb] using february year
          by_cases april : month = 4
          · subst month; simp [Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«=:=/2»]
          by_cases june : month = 6
          · subst month; simp [Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«=:=/2»]
          by_cases september : month = 9
          · subst month; simp [Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«=:=/2»]
          by_cases november : month = 11
          · subst month; simp [Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«=:=/2»]
          simp [Elixir.Calendar.ISO.«days_in_month_guarded/2», Erlang.erlang.«=:=/2»,
            feb, april, june, september, november]
        simp [Elixir.Calendar.ISO.«days_in_month/2», Erlang.erlang.«is_integer/1»,
          Erlang.erlang.«=:=/2», lower, upper, guarded]
      have checkedForward (year month day total capacity : Int)
          (monthLength : Elixir.Calendar.ISO.«days_in_month/2» (.integer year) (.integer month) =
            .ok (.integer capacity)) (lower : 1 ≤ day) (upper : day ≤ capacity)
          (encoded : Elixir.Calendar.ISO.«valid_date_to_iso_days/3»
            (.integer year) (.integer month) (.integer day) = .ok (.integer total)) :
          Elixir.Calendar.ISO.«date_to_iso_days/3» (.integer year) (.integer month) (.integer day) =
            .ok (.integer total) := by
        simp [Elixir.Calendar.ISO.«date_to_iso_days/3», Elixir.Calendar.ISO.«ensure_day_in_month!/3»,
          Erlang.erlang.«is_integer/1», Erlang.erlang.«=:=/2», monthLength,
          show ¬ day < 1 by omega, show ¬ capacity < day by omega, encoded,
          Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt]
      have contract (n year month day capacity : Int)
          (decoded : Elixir.Calendar.ISO.«date_from_iso_days/1» (.integer n) =
            .ok (.tuple #[.integer year, .integer month, .integer day]))
          (monthLength : Elixir.Calendar.ISO.«days_in_month/2» (.integer year) (.integer month) =
            .ok (.integer capacity)) (monthLo : 1 ≤ month) (monthHi : month ≤ 12)
          (dayLo : 1 ≤ day) (fits : day ≤ capacity)
          (encoded : Elixir.Calendar.ISO.«date_to_iso_days/3»
            (.integer year) (.integer month) (.integer day) = .ok (.integer n)) :
          «date_roundtrip/1» (.integer n) = .ok (.atom "true") := by
        simp [«date_roundtrip/1», decoded, monthLength, monthLo, monthHi, dayLo, fits,
          encoded, Erlang.erlang.«=:=/2»]
      have leapNext (year era y : Int) (same : year = era * 400 + y + 1)
          (next : y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399)) :
          year % 4 = 0 ∧ (year % 16 = 0 ∨ year % 100 ≠ 0) := by
        subst year
        rcases next.2 with ordinary | last <;> omega
      have capacityFits (year era y month day : Int)
          (same : year = y + era * 400 + if month ≤ 2 then 1 else 0)
          (bound : day ≤ (if month = 2 then
            if y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399) then 29 else 28
            else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31)) :
          day ≤ (if month = 2 then
            if year % 4 = 0 ∧ (year % 16 = 0 ∨ year % 100 ≠ 0) then 29 else 28
            else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31) := by
        by_cases feb : month = 2
        · by_cases next : y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399)
          · have eqYear : year = era * 400 + y + 1 := by rw [same]; simp [feb]; omega
            have actual := leapNext year era y eqYear next
            simpa [feb, actual] using (show day ≤ 29 by simpa [feb, next] using bound)
          · have small : day ≤ 28 := by simpa [feb, next] using bound
            simp only [if_pos feb]
            split <;> omega
        · simpa [feb] using bound
      have marchYear (era y month : Int) :
          (if month ≤ 2 then (y + era * 400 + if month ≤ 2 then 1 else 0) - 1
            else y + era * 400 + if month ≤ 2 then 1 else 0) = era * 400 + y := by
        by_cases early : month ≤ 2 <;> simp [early] <;> omega
      have eraInverse (era y : Int) (lower : 0 ≤ y) (upper : y < 400) :
          (if 0 ≤ era * 400 + y then (era * 400 + y).tdiv 400
            else (era * 400 + y - 399).tdiv 400) = era := by
        have adjusted := adjustedDivision (era * 400 + y) 400 (Or.inl rfl)
        have eqEra : (era * 400 + y) / 400 = era := by omega
        simpa [show era * 400 + y - 400 + 1 = era * 400 + y - 399 by omega, eqEra] using adjusted
      have monthInverse (mp : Int) (lower : 0 ≤ mp) (upper : mp ≤ 11) :
          (if 2 < (if mp < 10 then mp + 3 else mp - 9) then
            (if mp < 10 then mp + 3 else mp - 9) - 3 else
            (if mp < 10 then mp + 3 else mp - 9) + 9) = mp := by
        by_cases early : mp < 10 <;> simp [early] <;> omega
      have reconstruct (n era y mp : Int) :
          let z := n - 60 - era * 146097
          let d := z - (365 * y + y / 4 - y / 100)
          let day := d - (153 * mp + 2) / 5 + 1
          era * 146097 + (365 * y + y / 4 - y / 100 +
            ((153 * mp + 2) / 5 + day - 1)) + 60 = n := by dsimp; omega
      cases days <;> simp [«date_conversion_roundtrips_every_day:requires/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      generalize he : (n - 60) / 146097 = era
      generalize hz : n - 60 - era * 146097 = z
      have zLo : 0 ≤ z := by rw [← hz, ← he]; omega
      have zHi : z < 146097 := by rw [← hz, ← he]; omega
      generalize hy : (z - z / 1460 + z / 36524 - z / 146096) / 365 = y
      generalize hd : z - (365 * y + y / 4 - y / 100) = d
      have eraFacts : 0 ≤ y ∧ y < 400 ∧ 0 ≤ d ∧ d ≤ 365 ∧
          (d = 365 → y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399)) := by
        simpa only [hy, hd] using eraBounds z zLo zHi
      obtain ⟨yLo, yHi, dLo, dHi, leapDay⟩ := eraFacts
      generalize hmp : (5 * d + 2) / 153 = mp
      generalize hday : d - (153 * mp + 2) / 5 + 1 = day
      generalize hmonth : (if mp < 10 then mp + 3 else mp - 9) = month
      generalize hyear : (y + era * 400 + if month ≤ 2 then 1 else 0) = year
      have mpLo : 0 ≤ mp := by rw [← hmp]; omega
      have mpHi : mp ≤ 11 := by rw [← hmp]; omega
      have ym : 0 ≤ z - z / 1460 + z / 36524 - z / 146096 := by omega
      have zDiv (k : Int) : z.tdiv k = z / k := Int.tdiv_eq_ediv_of_nonneg zLo
      have yDiv (k : Int) : y.tdiv k = y / k := Int.tdiv_eq_ediv_of_nonneg yLo
      have ymDiv (k : Int) : (z - z / 1460 + z / 36524 - z / 146096).tdiv k =
          (z - z / 1460 + z / 36524 - z / 146096) / k := Int.tdiv_eq_ediv_of_nonneg ym
      have dDiv (k : Int) : (5 * d + 2).tdiv k = (5 * d + 2) / k :=
        Int.tdiv_eq_ediv_of_nonneg (by omega)
      have mpDiv (k : Int) : (153 * mp + 2).tdiv k = (153 * mp + 2) / k :=
        Int.tdiv_eq_ediv_of_nonneg (by omega)
      have decoded : Elixir.Calendar.ISO.«date_from_iso_days/1» (.integer n) =
          .ok (.tuple #[.integer year, .integer month, .integer day]) := by
        rw [inverse]
        dsimp only
        have chosen : (if 0 ≤ n - 60 then (n - 60).tdiv 146097
            else (n - 60 - 146097 + 1).tdiv 146097) = era := by
          rw [adjustedDivision (n - 60) 146097 (Or.inr rfl), he]
        rw [chosen]
        simp only [hz]
        simp only [zDiv]
        simp only [ymDiv]
        simp only [hy]
        simp only [yDiv]
        simp only [hd]
        simp only [dDiv]
        simp only [hmp]
        simp only [mpDiv]
        simp only [hday]
        simp only [hmonth]
        by_cases early : month ≤ 2 <;>
          simp only [early, ↓reduceIte, Int.add_zero] at hyear ⊢ <;> simp only [hyear]
      have fieldFacts : 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧
          day ≤ (if month = 2 then
            if y % 4 = 3 ∧ (y % 100 ≠ 99 ∨ y = 399) then 29 else 28
            else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31) :=
        by simpa only [hmp, hday, hmonth] using monthBounds y d yLo yHi dLo dHi leapDay
      obtain ⟨monthLo, monthHi, dayLo, dayLimit⟩ := fieldFacts
      let capacity : Int := if month = 2 then
        if year % 4 = 0 ∧ (year % 16 = 0 ∨ year % 100 ≠ 0) then 29 else 28
        else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31
      have monthLength : Elixir.Calendar.ISO.«days_in_month/2» (.integer year) (.integer month) =
          .ok (.integer capacity) := monthModel year month monthLo monthHi
      have fits : day ≤ capacity := capacityFits year era y month day hyear.symm dayLimit
      have baseYear : (if month ≤ 2 then year - 1 else year) = era * 400 + y :=
        by simpa only [hyear] using marchYear era y month
      have baseEra : (if 0 ≤ era * 400 + y then (era * 400 + y).tdiv 400
          else (era * 400 + y - 399).tdiv 400) = era := eraInverse era y yLo yHi
      have prime : (if 2 < month then month - 3 else month + 9) = mp := by
        simpa only [hmonth] using monthInverse mp mpLo mpHi
      have actualYo : era * 400 + y - era * 400 = y := by omega
      have exact : era * 146097 + (365 * y + y / 4 - y / 100 +
          ((153 * mp + 2) / 5 + day - 1)) + 60 = n := by
        simpa only [hz, hd, hday] using reconstruct n era y mp
      have encoded : Elixir.Calendar.ISO.«valid_date_to_iso_days/3»
          (.integer year) (.integer month) (.integer day) = .ok (.integer n) := by
        rw [forward]
        dsimp (config := { zetaDelta := false }) only
        rw [baseYear, baseEra, actualYo, prime,
          Int.tdiv_eq_ediv_of_nonneg yLo, Int.tdiv_eq_ediv_of_nonneg yLo,
          Int.tdiv_eq_ediv_of_nonneg (show 0 ≤ 153 * mp + 2 by omega), exact]
      have returned := checkedForward year month day n capacity monthLength dayLo fits encoded
      simpa only [«date_conversion_roundtrips_every_day:ensures/1», Lynx.Term.true] using
        contract n year month day capacity decoded monthLength monthLo monthHi dayLo fits returned
      """
  end

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
