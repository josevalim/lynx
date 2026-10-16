# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/elixir/range.exs
# Verify installed Range and Integer implementations translated from BEAM.
# Checked against Elixir 1.21.0-dev (3790cd8), Erlang/OTP 29.1.2.
# Source references: ../elixir/lib/elixir/lib/{range,integer}.ex.
ExUnit.start()

defmodule RangeProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def divides(divisor, integer) do
    if divisor === 0, do: integer === 0, else: rem(integer, divisor) === 0
  end

  def bezout_contract(left, right, {gcd, s, t}) do
    is_integer(gcd) and is_integer(s) and is_integer(t) and
      gcd >= 0 and s * left + t * right === gcd and
      divides(gcd, left) and divides(gcd, right)
  end

  def valid_range(first, last, step),
    do: is_integer(first) and is_integer(last) and is_integer(step) and step != 0

  def member?(first, last, step, value) do
    if(step > 0, do: first <= value and value <= last, else: last <= value and value <= first) and
      rem(value - first, step) === 0
  end

  @extended_gcd_fixpoint ~LEAN"""
  partial_fixpoint monotonicity by
    intro f g h
    repeat' first
      | exact Lean.Order.PartialOrder.rel_refl
      | exact h _ _ _ _ _ _
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

  laws "Range intersection arithmetic" do
    termination_suffix &Integer.extended_gcd/6, @extended_gcd_fixpoint

    law extended_gcd_obeys_bezout(left, right),
      max_heartbeats: 1_000_000,
      requires: is_integer(left) and is_integer(right),
      expects: bezout_contract(left, right, Integer.extended_gcd(left, right)),
      proof: ~LEAN"""
      have leftPositive (b : Int) (positive : 0 < b) :
          Elixir.Integer.«extended_gcd/2» (.integer 0) (.integer b) =
            .ok (.tuple #[.integer b, .integer 0, .integer 1]) := by
        unfold Elixir.Integer.«extended_gcd/2»
        split
        · simp only [Lynx.Term.integer.injEq] at *
          omega
        · simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«=:=/2»,
            Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt,
            positive, show b ≠ 0 by omega, show ¬ b < 0 by omega]
      cases left <;>
        simp [«extended_gcd_obeys_bezout:requires/2», Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      cases right <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i b
      have run (n : Nat) :
        ∀ (r1 r0 s1 s0 t1 t0 : Int),
          r1.natAbs = n →
            r1 ≠ 0 →
              r1 = s1 * a + t1 * b →
                r0 = s0 * a + t0 * b →
                  ∃ (s t : Int),
                    Elixir.Integer.«extended_gcd/6» (.integer r1) (.integer r0) (.integer s1)
                          (.integer s0) (.integer t1) (.integer t0) =
                        .ok (.tuple #[.integer (Int.gcd r0 r1), .integer s, .integer t]) ∧
                      s * a + t * b = (Int.gcd r0 r1 : Int) :=
        by
        induction n using Nat.strongRecOn with
        | ind n ih =>
          intro r1 r0 s1 s0 t1 t0 magnitude nonzero first second
          have remainder : r0 - r0.tdiv r1 * r1 = r0.tmod r1 := by
            simpa [Int.mul_comm] using (Int.tmod_def r0 r1).symm
          by_cases finished : r0.tmod r1 = 0
          · have divides : r1 ∣ r0 := Int.dvd_iff_tmod_eq_zero.mpr finished
            have gcd : Int.gcd r0 r1 = r1.natAbs := Int.gcd_eq_natAbs_right_iff_dvd.mpr divides
            by_cases positive : 0 < r1
            · refine ⟨s1, t1, ?_, ?_⟩
              · rw [Elixir.Integer.«extended_gcd/6».eq_def]
                simp [Erlang.erlang.«div/2», nonzero, remainder, finished, Erlang.erlang.«>/2»,
                  Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, positive, gcd,
                  Int.natAbs_of_nonneg (by omega : 0 ≤ r1)]
              · rw [gcd, Int.natAbs_of_nonneg (by omega : 0 ≤ r1)]
                exact first.symm
            · have negative : r1 < 0 := by omega
              refine ⟨-s1, -t1, ?_, ?_⟩
              · rw [Elixir.Integer.«extended_gcd/6».eq_def]
                simp [Erlang.erlang.«div/2», Erlang.erlang.«-/1», nonzero, remainder, finished,
                  Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, positive, negative,
                  gcd, Int.ofNat_natAbs_of_nonpos (by omega : r1 ≤ 0)]
              · rw [gcd, Int.ofNat_natAbs_of_nonpos (by omega : r1 ≤ 0)]
                simp only [Int.neg_mul]
                omega
          · have smaller : (r0.tmod r1).natAbs < n :=
              by
              rw [Int.natAbs_tmod, ← magnitude]
              exact Nat.mod_lt _ (by omega)
            have next : r0.tmod r1 = (s0 - r0.tdiv r1 * s1) * a + (t0 - r0.tdiv r1 * t1) * b := by
              grind only
            obtain ⟨s, t, returned, identity⟩ :=
              ih _ smaller (r0.tmod r1) r1 (s0 - r0.tdiv r1 * s1) s1 (t0 - r0.tdiv r1 * t1) t1 rfl
                finished next first
            have gcd : Int.gcd r1 (r0.tmod r1) = Int.gcd r0 r1 :=
              by
              rw [Int.tmod_def]
              simp [Int.gcd_comm]
            refine ⟨s, t, ?_, by simpa [gcd] using identity⟩
            rw [Elixir.Integer.«extended_gcd/6».eq_def]
            simp [Erlang.erlang.«div/2», nonzero, remainder, finished, returned, gcd]
      have returned : ∃ s t : Int,
          Elixir.Integer.«extended_gcd/2» (.integer a) (.integer b) =
            .ok (.tuple #[.integer (Int.gcd a b), .integer s, .integer t]) ∧
          s * a + t * b = (Int.gcd a b : Int) := by
        by_cases aZero : a = 0
        · clear run
          subst a
          by_cases bZero : b = 0
          · subst b; exact ⟨0, 0, rfl, rfl⟩
          by_cases positive : 0 < b
          · have abs := Int.natAbs_of_nonneg (show 0 ≤ b by omega)
            refine ⟨0, 1, ?_, by simp [abs]⟩
            rw [show (Int.gcd 0 b : Int) = b by simp only [Int.zero_gcd, abs]]
            exact leftPositive b positive
          · have negative : b < 0 := by omega
            have abs := Int.ofNat_natAbs_of_nonpos (show b ≤ 0 by omega)
            refine ⟨0, -1, ?_, by simp [abs]⟩
            unfold Elixir.Integer.«extended_gcd/2»
            simp [Erlang.erlang.«is_integer/1»,
              Erlang.erlang.«=:=/2», Erlang.erlang.«-/1», Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
              Int.compare_eq_gt, bZero, positive, negative, abs]
        · by_cases bZero : b = 0
          · clear run
            subst b
            by_cases positive : 0 < a
            · have abs := Int.natAbs_of_nonneg (show 0 ≤ a by omega)
              refine ⟨1, 0, ?_, by simp [abs]⟩
              unfold Elixir.Integer.«extended_gcd/2»
              simp [Erlang.erlang.«is_integer/1»,
                Erlang.erlang.«=:=/2», Erlang.erlang.«-/1», Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
                Int.compare_eq_gt, aZero, positive, abs, show ¬ a < 0 by omega]
            · have negative : a < 0 := by omega
              have abs := Int.ofNat_natAbs_of_nonpos (show a ≤ 0 by omega)
              refine ⟨-1, 0, ?_, by simp [abs]⟩
              unfold Elixir.Integer.«extended_gcd/2»
              simp [Erlang.erlang.«is_integer/1»,
                Erlang.erlang.«=:=/2», Erlang.erlang.«-/1», Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
                Int.compare_eq_gt, aZero, positive, negative, abs]
          · obtain ⟨s, t, result, identity⟩ := run b.natAbs b a 0 1 1 0 rfl bZero (by simp) (by simp)
            refine ⟨s, t, ?_, identity⟩
            unfold Elixir.Integer.«extended_gcd/2»
            simpa [aZero, bZero, Erlang.erlang.«is_integer/1», Erlang.erlang.«=:=/2»] using result
      obtain ⟨s, t, result, identity⟩ := returned
      have divides (d n : Int) :
        «divides/2» (.integer d) (.integer n) =
          .ok (if d ∣ n then Lynx.Term.true else Lynx.Term.false) :=
        by
        by_cases zero : d = 0
        · subst d
          by_cases nZero : n = 0 <;> simp [«divides/2», Erlang.erlang.«=:=/2», nZero]
        ·
          by_cases divisible : d ∣ n <;>
            simp [«divides/2», Erlang.erlang.«=:=/2», Erlang.erlang.«rem/2», zero,
              ← Int.dvd_iff_tmod_eq_zero, divisible]
      simp [«extended_gcd_obeys_bezout:ensures/2», result, «bezout_contract/3», Erlang.erlang.«is_integer/1», identity,
        Erlang.erlang.«=:=/2», divides, Int.gcd_dvd_left, Int.gcd_dvd_right]
      """
  end

  # Cardinalities plus every valid index characterize an ordered partition,
  # without materializing either range as a list.
  def split_contract(first, last, step, cut, index) do
    input = %Range{first: first, last: last, step: step}

    {%Range{first: lf, step: ls} = left, %Range{first: rf, step: rs} = right} =
      Range.split(input, cut)

    count = Range.size(input)
    prefix = max(0, min(if(cut < 0, do: count + cut, else: cut), count))

    Range.size(left) === prefix and Range.size(right) === count - prefix and
      ls === step and rs === step and
      if index < count do
        original = first + index * step

        if index < prefix,
          do: lf + index * ls === original,
          else: rf + (index - prefix) * rs === original
      else
        true
      end
  end

  @range_size_fixpoint ~LEAN"""
  partial_fixpoint monotonicity by
    intro f g h
    repeat' first
      | exact Lean.Order.PartialOrder.rel_refl
      | exact h _
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

  laws "Range split" do
    cutoff &Kernel.inspect/1
    cutoff &ArgumentError.exception/1

    termination_suffix &Range.size/1, @range_size_fixpoint

    law split_preserves_ordered_partition(first, last, step, cut, index),
      max_heartbeats: 1_000_000,
      requires:
        is_integer(first) and is_integer(last) and is_integer(step) and step != 0 and
          is_integer(cut) and is_integer(index) and index >= 0,
      expects: split_contract(first, last, step, cut, index),
      proof: ~LEAN"""
      -- The expectation reaches functions with termination suffixes, so it has no
      -- purity lemma; prove its direct statement under a pure precondition.
      refine Lynx.law_of_pure_requires (by simp) ?_ requires
      clear requires schedule
      intro requires
      let range (f l s : Int) : Lynx.Term := .map [
        (.atom "step", .integer s), (.atom "last", .integer l),
        (.atom "first", .integer f), (.atom "__struct__", .atom "Elixir.Range")]
      let count (f l s : Int) := if (0 < s ∧ l < f) ∨ (s < 0 ∧ f < l) then 0
        else (l - f).tdiv s + 1
      have keys (f l s : Int) : Lynx.Term.getMapKeys
          [.atom "__struct__", .atom "first", .atom "last", .atom "step"] (range f l s) =
          [.atom "Elixir.Range", .integer f, .integer l, .integer s] := by
        simp [range, Lynx.Term.getMapKeys, Lynx.Term.exactCompare_atoms]
      have sizeModel (f l s : Int) (nonzero : s ≠ 0) :
          Elixir.Range.«size/1» (range f l s) = .ok (.integer (count f l s)) := by
        rw [Elixir.Range.«size/1».eq_def]
        simp only [keys]
        by_cases pos : 0 < s <;> by_cases asc : f < l <;> by_cases desc : l < f <;>
          simp [count, Erlang.erlang.«>/2», Erlang.erlang.«</2»,
            Ordering.isGT_iff_eq_gt, Ordering.isLT_iff_eq_lt, Int.compare_eq_gt,
            Int.compare_eq_lt, Erlang.erlang.«=:=/2», Erlang.erlang.«div/2»,
            pos, asc, desc, nonzero, show (s < 0) ↔ ¬ 0 < s by omega]
      have newModel (f l s : Int) (nonzero : s ≠ 0) :
          Elixir.Range.«new/3» (.integer f) (.integer l) (.integer s) = .ok (range f l s) := by
        unfold Elixir.Range.«new/3»
        simp [range, Erlang.erlang.«is_integer/1», Erlang.erlang.«/=/2»,
          Erlang.erlang.«=:=/2», nonzero]
      have maxInt (a b : Int) : Erlang.erlang.«max/2» (.integer a) (.integer b) =
          .ok (.integer (max a b)) := by
        by_cases le : a ≤ b <;> by_cases ge : b ≤ a <;>
          simp [Erlang.erlang.«max/2», Int.isGE_compare,
            show max a b = (if b ≤ a then a else b) by omega, ge]
      have minInt (a b : Int) : Erlang.erlang.«min/2» (.integer a) (.integer b) =
          .ok (.integer (min a b)) := by
        by_cases le : a ≤ b <;>
          simp [Erlang.erlang.«min/2», Int.isLE_compare,
            show min a b = (if a ≤ b then a else b) by omega, le]
      let middle (f l s c : Int) := if 0 < s then max (min (f+s*(c-1)) l) (f-s)
        else min (max (f+s*(c-1)) l) (f-s)
      have splitFour (f l s c : Int) (nz : s ≠ 0) :
          Elixir.Range.«split/4» (.integer f) (.integer l) (.integer s) (.integer c) =
          .ok (if (0<s ∧ f≤l) ∨ (s<0 ∧ l≤f) then
            .tuple #[range f (middle f l s c) s, range (middle f l s c+s) l s]
            else .tuple #[range f (f-s) s, range (l+s) l s]) := by
        unfold Elixir.Range.«split/4»
        by_cases pos : 0<s <;> by_cases asc : f<l <;> by_cases equal : f=l <;>
          simp [middle, Erlang.erlang.«>/2», Erlang.erlang.«</2», Erlang.erlang.«==/2»,
            Erlang.erlang.«=:=/2», Ordering.isGT_iff_eq_gt, Ordering.isLT_iff_eq_lt,
            Int.compare_eq_gt, Int.compare_eq_lt, maxInt, minInt, newModel _ _ _ nz,
            pos, asc, equal, show (s<0) ↔ ¬0<s by omega,
            show (f≤l) ↔ (f<l ∨ f=l) by omega,
            show (l≤f) ↔ ¬f<l by omega]
      have splitTwo (f l s c : Int) (nz : s ≠ 0) :
          Elixir.Range.«split/2» (range f l s) (.integer c) =
            Elixir.Range.«split/4» (.integer f) (.integer l) (.integer s)
              (.integer (if c<0 then count f l s+c else c)) := by
        unfold Elixir.Range.«split/2»
        by_cases neg : c<0 <;>
          simp [keys, sizeModel _ _ _ nz, Erlang.erlang.«>=/2»,
            Int.isGE_compare, neg, show (0≤c) ↔ ¬c<0 by omega]
      have positivePartition (f l s c : Int) (pos : 0 < s) (ordered : f ≤ l) :
          let n := count f l s
          let k := max 0 (min c n)
          let m := max (min (f + s * (c - 1)) l) (f - s)
          count f m s = k ∧ count (m+s) l s = n-k ∧ (k < n → m+s=f+k*s) := by
        have nz : s ≠ 0 := by omega
        have ss : ¬ s < 0 := by omega
        have qLo := Int.ediv_mul_le (l-f) nz
        have qHi := Int.lt_ediv_mul (l-f) pos
        have quot := Int.tdiv_eq_ediv_of_nonneg (show 0 ≤ l-f by omega) (b := s)
        have nModel : count f l s = (l-f)/s+1 := by simp [count, pos, ss, show ¬ l<f by omega, quot]
        have nPos : 0 < count f l s := by rw [nModel]; have := Int.ediv_nonneg (show 0≤l-f by omega) (show 0≤s by omega); omega
        dsimp only
        by_cases low : c ≤ 0
        · have mul := Int.mul_le_mul_of_nonneg_left (show c-1 ≤ -1 by omega) (show 0≤s by omega)
          have mid : max (min (f+s*(c-1)) l) (f-s) = f-s := by
            have bound : f+s*(c-1) ≤ f-s := by grind only
            omega
          simp only [mid, show max 0 (min c (count f l s)) = 0 by omega, Int.sub_zero, Int.zero_mul, Int.add_zero]
          have left : count f (f-s) s = 0 := by simp [count, pos, show f-s<f by omega]
          have right : f-s+s=f := by omega
          simp [left, right]
        · by_cases high : count f l s < c
          · have mul := Int.mul_le_mul_of_nonneg_left (show (l-f)/s+1 ≤ c-1 by rw [nModel] at high; omega) (show 0≤s by omega)
            have cand : l ≤ f+s*(c-1) := by grind only
            have mid : max (min (f+s*(c-1)) l) (f-s) = l := by omega
            simp only [mid, show max 0 (min c (count f l s)) = count f l s by omega, Int.sub_self, Int.lt_irrefl, false_implies, and_true]
            simp [count, pos, show l<l+s by omega]
          · have cLo : 1 ≤ c := by omega
            have cHi : c ≤ (l-f)/s+1 := by rw [nModel] at high; omega
            have mul := Int.mul_le_mul_of_nonneg_left (show c-1 ≤ (l-f)/s by omega) (show 0≤s by omega)
            have mulLo := Int.mul_nonneg (show 0≤s by omega) (show 0≤c-1 by omega)
            have cand : f+s*(c-1) ≤ l := by grind only
            have mid : max (min (f+s*(c-1)) l) (f-s) = f+s*(c-1) := by
              omega
            simp only [mid, show max 0 (min c (count f l s)) = c by omega]
            have left : count f (f+s*(c-1)) s = c := by
              have nonnegative : 0 ≤ f+s*(c-1)-f := by omega
              simp only [count, show ¬ (0<s ∧ f+s*(c-1)<f ∨ s<0 ∧ f<f+s*(c-1)) by omega, ↓reduceIte,
                Int.tdiv_eq_ediv_of_nonneg nonnegative]
              rw [show f+s*(c-1)-f = (c-1)*s by grind only, Int.mul_ediv_cancel _ nz]
              omega
            have offset : f+s*(c-1)+s=f+c*s := by grind only
            refine ⟨left, ?_, fun _ => offset⟩
            by_cases empty : l < f+s*(c-1)+s
            · have eqn : count f l s = c := by
                by_cases same : c=(l-f)/s+1
                · omega
                · have small : c ≤ (l-f)/s := by omega
                  have bound := Int.mul_le_mul_of_nonneg_left small (show 0≤s by omega)
                  have impossible : f+s*(c-1)+s ≤ l := by grind only
                  omega
              rw [eqn]
              simp [count, pos, empty]
            · have nonnegative : 0 ≤ l-(f+s*(c-1)+s) := by omega
              rw [nModel]
              simp only [count, show ¬ (0<s ∧ l<f+s*(c-1)+s ∨ s<0 ∧ f+s*(c-1)+s<l) by omega, ↓reduceIte,
                Int.tdiv_eq_ediv_of_nonneg nonnegative]
              rw [show l-(f+s*(c-1)+s) = (l-f)-c*s by grind only, Int.sub_mul_ediv_right _ _ nz]
              omega

      have reflection (f l s : Int) : count (-f) (-l) (-s) = count f l s := by
        unfold count
        rw [show -l - -f = -(l-f) by omega, Int.neg_tdiv_neg]
        have equiv : (0 < -s ∧ -l < -f ∨ -s < 0 ∧ -f < -l) ↔ (0<s ∧ l<f ∨ s<0 ∧ f<l) := by omega
        simp only [equiv]

      have negativePartition (f l s c : Int) (neg : s < 0) (ordered : l ≤ f) :
          let n := count f l s
          let k := max 0 (min c n)
          let m := min (max (f + s * (c - 1)) l) (f - s)
          count f m s = k ∧ count (m+s) l s = n-k ∧ (k < n → m+s=f+k*s) := by
        have positive := positivePartition (-f) (-l) (-s) c (by omega) (by omega)
        dsimp only at positive ⊢
        have mid : max (min (-f + -s*(c-1)) (-l)) (-f - -s) =
            -(min (max (f+s*(c-1)) l) (f-s)) := by
          have eq : -f + -s*(c-1) = -(f+s*(c-1)) := by grind only
          rw [eq]
          omega
        simp only [reflection, mid] at positive
        obtain ⟨left, right, offset⟩ := positive
        refine ⟨by simpa only [reflection] using left, ?_, ?_⟩
        · simpa only [← Int.neg_add, reflection] using right
        · intro inside
          have := offset inside
          grind only
      have keys3 (f l s : Int) : Lynx.Term.getMapKeys
          [.atom "__struct__", .atom "first", .atom "step"] (range f l s) =
          [.atom "Elixir.Range", .integer f, .integer s] := by
        simp [range, Lynx.Term.getMapKeys, Lynx.Term.exactCompare_atoms]
      have finish (f l s c i m rf n k : Int) (nz : s ≠ 0)
          (returned : Elixir.Range.«split/2» (range f l s) (.integer c) =
            .ok (.tuple #[range f m s, range rf l s]))
          (nEq : count f l s = n)
          (kEq : max 0 (min (if c<0 then n+c else c) n) = k)
          (left : count f m s = k) (right : count rf l s = n-k)
          (offset : k<n → rf=f+k*s) :
          «split_contract/5» (.integer f) (.integer l) (.integer s) (.integer c) (.integer i) =
            .ok Lynx.Term.true := by
        have sizes := sizeModel
        have fields := keys3
        dsimp only [range] at returned sizes fields
        by_cases idx : i<n
        · by_cases pre : i<k
          · by_cases neg : c<0 <;> simp only [neg, ↓reduceIte] at kEq <;>
              simp [«split_contract/5», returned, fields, sizes _ _ _ nz, nEq,
                maxInt, minInt, kEq, left, right, Erlang.erlang.«</2»,
                Ordering.isLT_iff_eq_lt, Int.compare_eq_lt, Erlang.erlang.«=:=/2», neg, idx, pre]
          · have equation : rf+(i-k)*s=f+i*s := by have := offset (by omega); grind only
            by_cases neg : c<0 <;> simp only [neg, ↓reduceIte] at kEq <;>
              simp [«split_contract/5», returned, fields, sizes _ _ _ nz, nEq,
                maxInt, minInt, kEq, left, right, Erlang.erlang.«</2»,
                Ordering.isLT_iff_eq_lt, Int.compare_eq_lt, Erlang.erlang.«=:=/2», neg, idx, pre, equation]
        · by_cases neg : c<0 <;> simp only [neg, ↓reduceIte] at kEq <;>
            simp [«split_contract/5», returned, fields, sizes _ _ _ nz, nEq,
              maxInt, minInt, kEq, left, right, Erlang.erlang.«</2»,
              Ordering.isLT_iff_eq_lt, Int.compare_eq_lt, Erlang.erlang.«=:=/2», neg, idx]
      cases first <;> simp [«split_preserves_ordered_partition:requires/5»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i f
      cases last <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i l
      cases step <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i s
      by_cases nonzero : s = 0 <;> simp [Erlang.erlang.«/=/2», Erlang.erlang.«==/2», nonzero] at requires
      cases cut <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i c
      cases index <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i i
      change «split_contract/5» (.integer f) (.integer l) (.integer s) (.integer c) (.integer i) = .ok Lynx.Term.true
      let n := count f l s
      let q := if c<0 then n+c else c
      let k := max 0 (min q n)
      have returned := (splitTwo f l s c nonzero).trans (splitFour f l s q nonzero)
      by_cases valid : (0<s ∧ f≤l) ∨ (s<0 ∧ l≤f)
      · rw [if_pos valid] at returned
        have facts : count f (middle f l s q) s = k ∧
            count (middle f l s q+s) l s = n-k ∧
            (k<n → middle f l s q+s=f+k*s) := by
          by_cases pos : 0<s
          · have ordered : f≤l := by omega
            simpa only [middle, if_pos pos] using positivePartition f l s q pos ordered
          · have neg : s<0 := by omega
            have ordered : l≤f := by omega
            simpa only [middle, if_neg pos] using negativePartition f l s q neg ordered
        exact finish f l s c i (middle f l s q) (middle f l s q+s) n k nonzero
          returned rfl rfl facts.1 facts.2.1 facts.2.2
      · rw [if_neg valid] at returned
        have empty : (0<s ∧ l<f) ∨ (s<0 ∧ f<l) := by omega
        have nZero : n=0 := by simp [n, count, empty]
        have kZero : k=0 := by dsimp [k]; omega
        have left : count f (f-s) s = 0 := by
          have empty : (0<s ∧ f-s<f) ∨ (s<0 ∧ f<f-s) := by omega
          simp [count, empty]
        have right : count (l+s) l s = 0 := by
          have empty : (0<s ∧ l<l+s) ∨ (s<0 ∧ l+s<l) := by omega
          simp [count, empty]
        apply finish f l s c i (f-s) (l+s) n k nonzero returned rfl rfl
        · simpa only [kZero] using left
        · simpa only [nZero, kZero, Int.sub_self] using right
        · intro impossible; omega
      """
  end

  def shift_contract(first, last, step, left, right, point) do
    input = %Range{first: first, last: last, step: step}

    %Range{first: shifted_first, last: shifted_last, step: shifted_step} =
      shifted = Range.shift(input, left)

    Range.shift(shifted, right) === Range.shift(input, left + right) and
      Range.shift(shifted, -left) === input and shifted_step === step and
      Range.size(shifted) === Range.size(input) and
      member?(shifted_first, shifted_last, shifted_step, point + left * step) ===
        member?(first, last, step, point)
  end

  laws "Range shift" do
    cutoff &Kernel.inspect/1
    cutoff &ArgumentError.exception/1
    termination_suffix &Range.size/1, @range_size_fixpoint

    law shift_obeys_translation_laws(first, last, step, left, right, point),
      max_heartbeats: 1_000_000,
      requires:
        valid_range(first, last, step) and is_integer(left) and is_integer(right) and
          is_integer(point),
      expects: shift_contract(first, last, step, left, right, point),
      proof: ~LEAN"""
      let range (f l s : Int) : Lynx.Term := .map [
        (.atom "step",.integer s),(.atom "last",.integer l),
        (.atom "first",.integer f),(.atom "__struct__",.atom "Elixir.Range")]
      let count (f l s : Int) := if (0<s ∧ l<f) ∨ (s<0 ∧ f<l) then 0 else (l-f).tdiv s+1
      have keys (f l s : Int) : Lynx.Term.getMapKeys
          [.atom "__struct__",.atom "first",.atom "last",.atom "step"] (range f l s) =
          [.atom "Elixir.Range",.integer f,.integer l,.integer s] := by
        simp [range,Lynx.Term.getMapKeys,Lynx.Term.exactCompare_atoms]
      have key (f l s : Int) : Lynx.Term.getMapKeys [.atom "__struct__"] (range f l s) =
          [.atom "Elixir.Range"] := by
        simp [range,Lynx.Term.getMapKeys,Lynx.Term.exactCompare_atoms]
      have newModel (f l s : Int) (nz : s≠0) :
          Elixir.Range.«new/3» (.integer f) (.integer l) (.integer s) = .ok (range f l s) := by
        unfold Elixir.Range.«new/3»
        simp [range,Erlang.erlang.«is_integer/1»,Erlang.erlang.«/=/2»,Erlang.erlang.«=:=/2»,nz]
      have sizeModel (f l s : Int) (nz : s≠0) :
          Elixir.Range.«size/1» (range f l s) = .ok (.integer (count f l s)) := by
        rw [Elixir.Range.«size/1».eq_def]
        simp only [keys]
        by_cases pos : 0<s <;> by_cases asc : f<l <;> by_cases desc : l<f <;>
          simp [count,Erlang.erlang.«>/2»,Erlang.erlang.«</2»,Erlang.erlang.«=:=/2»,
            Erlang.erlang.«div/2»,Ordering.isGT_iff_eq_gt,Ordering.isLT_iff_eq_lt,
            Int.compare_eq_gt,Int.compare_eq_lt,pos,asc,desc,nz,show (s<0) ↔ ¬0<s by omega]
      have sizeShift (f l s delta : Int) : count (f+delta) (l+delta) s=count f l s := by
        simp only [count,show (l+delta<f+delta) ↔ l<f by omega,
          show (f+delta<l+delta) ↔ f<l by omega,show l+delta-(f+delta)=l-f by omega]
      have memberShift (f l s delta z : Int) :
          «member?/4» (.integer (f+delta)) (.integer (l+delta)) (.integer s) (.integer (z+delta)) =
            «member?/4» (.integer f) (.integer l) (.integer s) (.integer z) := by
        simp [«member?/4»,Erlang.erlang.«>/2»,Erlang.erlang.«=</2»,
          Ordering.isGT_iff_eq_gt,Int.compare_eq_gt,Int.isLE_compare,
          show (l+delta≤z+delta) ↔ l≤z by omega,show (z+delta≤f+delta) ↔ z≤f by omega,
          show (f+delta≤z+delta) ↔ f≤z by omega,show (z+delta≤l+delta) ↔ z≤l by omega,
          show z+delta-(f+delta)=z-f by omega]
      have memberReturns (f l s z : Int) (nz : s≠0) :
          ∃ value,«member?/4» (.integer f) (.integer l) (.integer s) (.integer z)=.ok value := by
        by_cases pos : 0<s <;> by_cases lo : f≤z <;> by_cases hi : z≤l <;>
          by_cases otherLo : l≤z <;> by_cases otherHi : z≤f <;>
          simp [«member?/4»,Erlang.erlang.«>/2»,Erlang.erlang.«=</2»,
            Ordering.isGT_iff_eq_gt,Int.compare_eq_gt,Int.isLE_compare,
            Erlang.erlang.«rem/2»,Erlang.erlang.«=:=/2»,nz,pos,lo,hi,otherLo,otherHi]
      have shiftModel (f l s n : Int) (nz : s≠0) :
          Elixir.Range.«shift/2» (range f l s) (.integer n) =
            .ok (range (f+n*s) (l+n*s) s) := by
        unfold Elixir.Range.«shift/2»
        by_cases zero : n=0
        · subst n
          simp [key]
        · simp [key,keys,newModel _ _ _ nz,zero,Erlang.erlang.«is_integer/1»]
      cases first <;> simp [«shift_obeys_translation_laws:requires/6»,«valid_range/3»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i f
      cases last <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i l
      cases step <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i s
      by_cases nz : s=0 <;> simp [Erlang.erlang.«/=/2»,Erlang.erlang.«==/2»,nz] at requires
      cases left <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      cases right <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i b
      cases point <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i z
      obtain ⟨member,returned⟩ := memberReturns f l s z nz
      have shifts := shiftModel
      have sizes := sizeModel
      have fields := keys
      dsimp only [range] at shifts sizes fields
      simp [«shift_obeys_translation_laws:ensures/6»,«shift_contract/6»,shifts _ _ _ _ nz,
        fields,sizes _ _ _ nz,sizeShift,memberShift,returned,Erlang.erlang.«-/1»,Erlang.erlang.«=:=/2»,
        Int.add_mul,Int.add_assoc,Int.neg_mul,Int.add_right_neg]
      """
  end
end
