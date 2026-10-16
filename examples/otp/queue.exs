# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/queue.exs
# Prove the installed OTP queue module, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1, ERTS 17.1.1).
# These proofs depend on implementation details; rerun after OTP upgrades.
ExUnit.start()

defmodule QueueProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp proper_list([]), do: true
  defp proper_list([_ | tail]), do: proper_list(tail)
  defp proper_list(_), do: false

  defp valid_queue({rear, front}), do: proper_list(rear) and proper_list(front)
  defp valid_queue(_), do: false

  def split_contract(index, queue) do
    {left, right} = :queue.split(index, queue)

    :queue.len(left) === index and
      :queue.to_list(left) ++ :queue.to_list(right) === :queue.to_list(queue)
  end

  laws "queue split" do
    law split_preserves_ordered_partition(index, queue),
      requires:
        is_integer(index) and index >= 0 and valid_queue(queue) and index <= :queue.len(queue),
      expects: split_contract(index, queue),
      proof: ~LEAN"""
      let encode (xs : List Lynx.Term) : Lynx.Term := xs.foldr Lynx.Term.cons .nil
      let pack (r f : List Lynx.Term) : Lynx.Term := .tuple ⟨[encode r, encode f]⟩
      have encNil : encode [] = Lynx.Term.nil := rfl
      have encCons (x : Lynx.Term) (xs : List Lynx.Term) :
          encode (x :: xs) = .cons x (encode xs) := rfl
      have shape (xs : List Lynx.Term) :
          Erlang.erlang.«is_list/1» (encode xs) = .ok Lynx.Term.true := by
        cases xs <;> rfl
      have shapeCons (x t : Lynx.Term) :
          Erlang.erlang.«is_list/1» (.cons x t) = .ok Lynx.Term.true := rfl
      have shapeNil : Erlang.erlang.«is_list/1» .nil = .ok Lynx.Term.true := rfl
      have lengthModel (xs : List Lynx.Term) :
          Erlang.erlang.«length/1» (encode xs) = .ok (.integer xs.length) := by
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [encode, Erlang.erlang.«length/1», ih, Int.natCast_add]
      have lengthCons (x : Lynx.Term) (xs : List Lynx.Term) :
          Erlang.erlang.«length/1» (.cons x (encode xs)) = .ok (.integer (↑(xs.length+1 : Nat))) := by
        simpa only [encCons, List.length_cons] using lengthModel (x :: xs)
      have appendModel (xs ys : List Lynx.Term) :
          Erlang.erlang.«++/2» (encode xs) (encode ys) = .ok (encode (xs ++ ys)) := by
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [encode, Erlang.erlang.«++/2», ih]
      have reverseModel (xs ys : List Lynx.Term) :
          Erlang.lists.«reverse/2» (encode xs) (encode ys) =
            .ok (encode (xs.reverse ++ ys)) := by
        induction xs generalizing ys with
        | nil => rfl
        | cons x xs ih =>
          simpa [encode, Erlang.lists.«reverse/2», List.reverse_cons, List.append_assoc] using
            ih (x :: ys)
      have reverseNil (xs : List Lynx.Term) :
          Erlang.lists.«reverse/2» (encode xs) .nil = .ok (encode xs.reverse) := by
        simpa only [encNil, List.append_nil] using reverseModel xs []
      have lenModel (r f : List Lynx.Term) :
          Erlang.queue.«len/1» (pack r f) = .ok (.integer (r.length + f.length)) := by
        simp [Erlang.queue.«len/1», pack, shape, lengthModel, Erlang.erlang.«and/2»]
      have toListModel (r f : List Lynx.Term) :
          Erlang.queue.«to_list/1» (pack r f) = .ok (encode (f ++ r.reverse)) := by
        simp [Erlang.queue.«to_list/1», pack, shape, reverseNil, appendModel,
          Erlang.erlang.«and/2»]

      have listSplit (n : Nat) (xs acc : List Lynx.Term) (bound : n ≤ xs.length) :
          Erlang.lists.«split/3» (.integer n) (encode xs) (encode acc) =
            .ok (.tuple #[encode (acc.reverse ++ xs.take n), encode (xs.drop n)]) := by
        induction n generalizing xs acc with
        | zero => simp [Erlang.lists.«split/3», reverseNil]
        | succ n ih =>
          cases xs with
          | nil => simp at bound
          | cons x xs =>
            have step := ih xs (x :: acc) (by simpa using bound)
            rw [Erlang.lists.«split/3».eq_def]
            simp only [encCons]
            simpa [encCons, encNil, List.reverse_cons, List.append_assoc,
              show (↑(n+1) : Int) - 1 = n by omega] using step
      have listSplitPublic (n : Nat) (xs : List Lynx.Term) (bound : n ≤ xs.length) :
          Erlang.lists.«split/2» (.integer n) (encode xs) =
            .ok (.tuple #[encode (xs.take n), encode (xs.drop n)]) := by
        have returned := listSplit n xs [] bound
        simp only [encNil, List.reverse_nil, List.nil_append] at returned
        simp [Erlang.lists.«split/2», shape, returned, Erlang.erlang.«and/2»]

      have frontWorker (n : Nat) (r f ar af : List Lynx.Term) (bound : n ≤ f.length) :
          Erlang.queue.«split_f1_to_r2/5» (.integer n) (encode r) (encode f) (encode ar) (encode af) =
            .ok (.tuple #[pack ((f.take n).reverse ++ ar) af, pack r (f.drop n)]) := by
        induction n generalizing f ar with
        | zero => simp [Erlang.queue.«split_f1_to_r2/5», pack]
        | succ n ih =>
          cases f with
          | nil => simp at bound
          | cons x f =>
            have step := ih f (x :: ar) (by simpa using bound)
            rw [Erlang.queue.«split_f1_to_r2/5».eq_def]
            simp only [encCons]
            simpa [encCons, encNil, pack, List.reverse_cons, List.append_assoc,
              show (↑(n+1) : Int) - 1 = n by omega] using step
      have rearWorker (n : Nat) (r f ar af : List Lynx.Term) (bound : n ≤ r.length) :
          Erlang.queue.«split_r1_to_f2/5» (.integer n) (encode r) (encode f) (encode ar) (encode af) =
            .ok (.tuple #[pack (r.drop n) f, pack ar ((r.take n).reverse ++ af)]) := by
        induction n generalizing r af with
        | zero => simp [Erlang.queue.«split_r1_to_f2/5», pack]
        | succ n ih =>
          cases r with
          | nil => simp at bound
          | cons x r =>
            have step := ih r (x :: af) (by simpa using bound)
            rw [Erlang.queue.«split_r1_to_f2/5».eq_def]
            simp only [encCons]
            simpa [encCons, encNil, pack, List.reverse_cons, List.append_assoc,
              show (↑(n+1) : Int) - 1 = n by omega] using step
      -- These are the two normalizations inlined by OTP at the split boundary.

      let front : Lynx.Term → Lynx.Result := fun input => match input with
        | .nil => .ok (pack [] [])
        | .cons x .nil => .ok (pack [x] [])
        | .cons x (.cons y .nil) => .ok (pack [y] [x])
        | xs => do
          let count ← Erlang.erlang.«length/1» xs
          let half ← Erlang.erlang.«div/2» count (.integer 2)
          let pair ← Erlang.lists.«split/2» half xs
          match pair with
          | .tuple ⟨[ff, rr]⟩ => do
            let rear ← Erlang.lists.«reverse/2» rr .nil
            .ok (.tuple #[rear, ff])
          | other => .error (.error (.tuple #[.atom "badmatch", other]))
      let rear : Lynx.Term → Lynx.Result := fun input => match input with
        | .nil => .ok (pack [] [])
        | .cons x .nil => .ok (pack [] [x])
        | .cons y (.cons x .nil) => .ok (pack [y] [x])
        | xs => do
          let count ← Erlang.erlang.«length/1» xs
          let half ← Erlang.erlang.«div/2» count (.integer 2)
          let pair ← Erlang.lists.«split/2» half xs
          match pair with
          | .tuple ⟨[rr, ff]⟩ => do
            let forward ← Erlang.lists.«reverse/2» ff .nil
            .ok (.tuple #[rr, forward])
          | other => .error (.error (.tuple #[.atom "badmatch", other]))

      have frontModel (xs : List Lynx.Term) : ∃ r f : List Lynx.Term,
          front (encode xs) = .ok (pack r f) ∧
            r.length + f.length = xs.length ∧ f ++ r.reverse = xs := by
        match xs with
        | [] => exact ⟨[], [], rfl, rfl, rfl⟩
        | [x] => exact ⟨[x], [], rfl, rfl, rfl⟩
        | [x, y] => exact ⟨[y], [x], rfl, rfl, rfl⟩
        | x :: y :: z :: tail =>
          let xs := x :: y :: z :: tail
          let half := xs.length / 2
          have divided : Erlang.erlang.«div/2» (.integer xs.length) (.integer 2) =
              .ok (.integer half) := rfl
          refine ⟨(xs.drop half).reverse, xs.take half, ?_, ?_, ?_⟩
          · change (show Lynx.Result from do
              let count ← Erlang.erlang.«length/1» (encode xs)
              let half ← Erlang.erlang.«div/2» count (.integer 2)
              let pair ← Erlang.lists.«split/2» half (encode xs)
              match pair with
              | .tuple ⟨[ff, rr]⟩ => do
                let rear ← Erlang.lists.«reverse/2» rr .nil
                .ok (.tuple #[rear, ff])
              | other => .error (.error (.tuple #[.atom "badmatch", other]))) = _
            simp only [lengthModel, divided,
              listSplitPublic half xs (Nat.div_le_self xs.length 2),
              reverseNil, Lynx.Result.ok_bind] <;> rfl
          · change _ = xs.length
            simp only [List.length_reverse, List.length_drop, List.length_take]
            omega
          · simp only [List.reverse_reverse, List.take_append_drop]
            rfl
      have rearModel (xs : List Lynx.Term) : ∃ r f : List Lynx.Term,
          rear (encode xs) = .ok (pack r f) ∧
            r.length + f.length = xs.length ∧ f ++ r.reverse = xs.reverse := by
        match xs with
        | [] => exact ⟨[], [], rfl, rfl, rfl⟩
        | [x] => exact ⟨[], [x], rfl, rfl, rfl⟩
        | [y, x] => exact ⟨[y], [x], rfl, rfl, rfl⟩
        | x :: y :: z :: tail =>
          let xs := x :: y :: z :: tail
          let half := xs.length / 2
          have divided : Erlang.erlang.«div/2» (.integer xs.length) (.integer 2) =
              .ok (.integer half) := rfl
          refine ⟨xs.take half, (xs.drop half).reverse, ?_, ?_, ?_⟩
          · change (show Lynx.Result from do
              let count ← Erlang.erlang.«length/1» (encode xs)
              let half ← Erlang.erlang.«div/2» count (.integer 2)
              let pair ← Erlang.lists.«split/2» half (encode xs)
              match pair with
              | .tuple ⟨[rr, ff]⟩ => do
                let forward ← Erlang.lists.«reverse/2» ff .nil
                .ok (.tuple #[rr, forward])
              | other => .error (.error (.tuple #[.atom "badmatch", other]))) = _
            simp only [lengthModel, divided,
              listSplitPublic half xs (Nat.div_le_self xs.length 2),
              reverseNil, Lynx.Result.ok_bind] <;> rfl
          · change _ = xs.length
            simp only [List.length_reverse, List.length_drop, List.length_take]
            omega
          · rw [← List.reverse_append, List.take_append_drop]
      have greaterModel (a b : Int) : Erlang.erlang.«>/2» (.integer a) (.integer b) =
          .ok (if b < a then Lynx.Term.true else Lynx.Term.false) := by
        simp [Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, Int.compare_eq_gt]

      -- Reduce guards before their shared fallthroughs so simplification does
      -- not duplicate the inlined normalizations into every alternative.
      have splitModel (n : Nat) (r f : List Lynx.Term) (bound : n ≤ r.length + f.length) :
          ∃ lr lf rr rf : List Lynx.Term,
            Erlang.queue.«split/2» (.integer n) (pack r f) =
              .ok (.tuple #[pack lr lf, pack rr rf]) ∧
            lr.length + lf.length = n ∧
            (lf ++ lr.reverse) ++ (rf ++ rr.reverse) = f ++ r.reverse := by
        cases n with
        | zero =>
          refine ⟨[], [], r, f, ?_, rfl, by simp⟩
          dsimp only [Erlang.queue.«split/2», pack]
          simp only [Int.cast_ofNat_Int, shape, Lynx.Result.ok_bind, Erlang.erlang.«and/2»,
            Lynx.Term.true, Lynx.Result.tryWith_ok, pack, encNil] <;> rfl
        | succ n =>
          have positive : (1 : Int) ≤ ↑(n+1) := by omega
          have nonzero : (↑(n+1) : Int) ≠ 0 := by omega
          by_cases before : n+1 < f.length
          · cases f with
            | nil => simp at before
            | cons x f =>
              have inside : n ≤ f.length := by simp only [List.length_cons] at before; omega
              refine ⟨(f.take n).reverse, [x], r, f.drop n, ?_, ?_, ?_⟩
              · have returned := frontWorker n r f [] [x] inside
                have beforeInt : (↑(n+1) : Int) < ↑(f.length+1 : Nat) := by
                  simp only [List.length_cons] at before
                  omega
                dsimp only [Erlang.queue.«split/2», pack]
                simpa only [Lynx.Term.atom.injEq, String.reduceEq, imp_self, Int.cast_ofNat_Int, Int.reduceLT,
                  Int.reduceLE, Int.reduceEq, List.length_cons, lengthCons, List.append_nil, Lynx.Term.true,
                  Lynx.Term.false, shapeCons, shapeNil, if_true, if_false, Lynx.Result.ok_bind,
                  Lynx.Result.tryWith_ok, Lynx.Result.pure_eq_ok, Erlang.erlang.«>=/2_integers»,
                  Erlang.erlang.«</2_integers», greaterModel, Erlang.erlang.«-/2_integers», if_pos, if_neg, encNil,
                  pack, shape, lengthModel, encCons,
                  Erlang.erlang.«and/2»,
                  positive, nonzero,
                  beforeInt,
                  List.append_nil, show (↑(n+1) : Int)-1 = n by omega, encode, List.foldr_cons, List.foldr_nil] using
                    returned
              · simp only [List.length_reverse, List.length_take, List.length_singleton]
                omega
              · simp only [List.reverse_reverse, List.singleton_append, List.cons_append, List.nil_append]
                rw [← List.append_assoc, List.take_append_drop]
          · by_cases after : f.length < n+1
            · let remaining := r.length - ((n+1) - f.length)
              have remainingEq : (↑r.length : Int) - (↑(n+1) - ↑f.length) = remaining := by
                dsimp only [remaining, List.length_cons]
                omega
              by_cases empty : remaining = 0
              · refine ⟨r, f, [], [], ?_, by dsimp only [remaining, List.length_cons] at empty; omega, by simp⟩
                dsimp only [Erlang.queue.«split/2», pack]
                simp only [Lynx.Term.atom.injEq, String.reduceEq, imp_self, Int.cast_ofNat_Int, Int.reduceLT,
                  Int.reduceLE, Int.reduceEq, List.length_cons, lengthCons, List.append_nil, Lynx.Term.true,
                  Lynx.Term.false, shapeCons, shapeNil, if_true, if_false, Lynx.Result.ok_bind,
                  Lynx.Result.tryWith_ok, Lynx.Result.pure_eq_ok, Erlang.erlang.«>=/2_integers»,
                  Erlang.erlang.«</2_integers», greaterModel, Erlang.erlang.«-/2_integers», if_pos, if_neg, encNil,
                  shape, lengthModel,
                  Erlang.erlang.«and/2»,
                  positive, nonzero,
                  show ¬ (↑(n+1) : Int) < ↑f.length by omega,
                  show (↑f.length : Int) < ↑(n+1) by omega,
                  remainingEq, empty]
              · cases r with
                | nil => simp at bound; omega
                | cons x r =>
                  have inRear : remaining - 1 ≤ r.length := by dsimp only [remaining, List.length_cons]; omega
                  refine ⟨r.drop (remaining-1), f, [x], (r.take (remaining-1)).reverse, ?_, ?_, ?_⟩
                  · have returned := rearWorker (remaining-1) r f [x] [] inRear
                    have remainingEq' : (↑(r.length+1 : Nat) : Int) -
                        (↑(n+1) - ↑f.length) = remaining := by
                      simpa only [List.length_cons] using remainingEq
                    dsimp only [Erlang.queue.«split/2», pack]
                    simpa only [Lynx.Term.atom.injEq, String.reduceEq, imp_self, Int.cast_ofNat_Int, Int.reduceLT,
                      Int.reduceLE, Int.reduceEq, List.length_cons, lengthCons, List.append_nil, Lynx.Term.true,
                      Lynx.Term.false, shapeCons, shapeNil, if_true, if_false, Lynx.Result.ok_bind,
                      Lynx.Result.tryWith_ok, Lynx.Result.pure_eq_ok, Erlang.erlang.«>=/2_integers»,
                      Erlang.erlang.«</2_integers», greaterModel, Erlang.erlang.«-/2_integers», if_pos, if_neg,
                      encNil, pack, shape, lengthModel, encCons,
                      Erlang.erlang.«and/2»,
                      positive, nonzero,
                      show ¬ (↑(n+1) : Int) < ↑f.length by omega,
                      show (↑f.length : Int) < ↑(n+1) by omega,
                      remainingEq', show ¬ (↑remaining : Int) < 0 by omega,
                      show (0 : Int) < ↑remaining by omega,
                      show (↑remaining : Int)-1 = ↑(remaining-1) by omega, encode, List.foldr_cons, List.foldr_nil]
                        using returned
                  · simp only [List.length_drop]
                    dsimp only [remaining, List.length_cons] at empty inRear remainingEq ⊢
                    omega
                  · have restored : (r.drop (remaining-1)).reverse ++
                        (r.take (remaining-1)).reverse = r.reverse := by
                      rw [← List.reverse_append, List.take_append_drop]
                    simpa only [List.append_assoc, List.reverse_cons, List.reverse_singleton,
                      List.reverse_nil, List.append_nil, List.nil_append] using
                      congrArg (fun xs => f ++ (xs ++ [x])) restored
            · have boundary : n+1 = f.length := by omega
              obtain ⟨lr, lf, left, leftLength, leftOrder⟩ := frontModel f
              obtain ⟨rr, rf, right, _, rightOrder⟩ := rearModel r
              refine ⟨lr, lf, rr, rf, ?_, by omega, by rw [leftOrder, rightOrder]⟩
              have normalized : Erlang.queue.«split/2» (.integer (↑(n+1 : Nat))) (pack r f) =
                  (do let left ← front (encode f)
                      let right ← rear (encode r)
                      .ok (.tuple #[left, right])) := by
                dsimp only [Erlang.queue.«split/2», pack]
                simp only [Lynx.Term.atom.injEq, String.reduceEq, imp_self, Int.cast_ofNat_Int, Int.reduceLT,
                  Int.reduceLE, Int.reduceEq, List.length_cons, lengthCons, List.append_nil, Lynx.Term.true,
                  Lynx.Term.false, shapeCons, shapeNil, if_true, if_false, Lynx.Result.ok_bind,
                  Lynx.Result.tryWith_ok, Lynx.Result.pure_eq_ok, Erlang.erlang.«>=/2_integers»,
                  Erlang.erlang.«</2_integers», greaterModel, Erlang.erlang.«-/2_integers», if_pos, if_neg, encNil,
                  shape, lengthModel,
                  Erlang.erlang.«and/2»,
                  positive, nonzero,
                  show ¬ (↑(n+1) : Int) < ↑f.length by omega,
                  show ¬ (↑f.length : Int) < ↑(n+1) by omega, front, rear]
                all_goals rcases f with _ | ⟨x, _ | ⟨y, _ | ⟨z, tail⟩⟩⟩
                all_goals rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
                all_goals simp only [pack, encCons, encNil] <;> rfl
              rw [normalized, left]
              simp [right]

      have properModel (t : Lynx.Term) (proper : «proper_list/1» t = .ok Lynx.Term.true) :
          ∃ xs : List Lynx.Term, encode xs = t := by
        induction t using «proper_list/1».induct with
        | case1 => exact ⟨[], rfl⟩
        | case2 x t ih =>
          obtain ⟨xs, rfl⟩ := ih (by simpa [«proper_list/1»] using proper)
          exact ⟨x :: xs, rfl⟩
        | case3 t notNil notCons => simp_all [«proper_list/1»]
      have properBool (t : Lynx.Term) :
          «proper_list/1» t = .ok Lynx.Term.true ∨ «proper_list/1» t = .ok Lynx.Term.false := by
        induction t using «proper_list/1».induct with
        | case1 => exact Or.inl rfl
        | case2 _ _ ih => simpa [«proper_list/1»] using ih
        | case3 t notNil notCons => simp_all [«proper_list/1»]

      cases index <;> simp [«split_preserves_ordered_partition:requires/2»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i k
      have nonnegative : 0 ≤ k := by
        by_cases h : 0 ≤ k <;> simp [h] at requires <;> omega
      simp [nonnegative] at requires
      cases queue <;> simp [«valid_queue/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [«valid_queue/1»] at requires
      | [rTerm, fTerm] =>
        rcases properBool rTerm with rProper | rInvalid
        · rcases properBool fTerm with fProper | fInvalid
          · obtain ⟨r, rfl⟩ := properModel rTerm rProper
            obtain ⟨f, rfl⟩ := properModel fTerm fProper
            simp [«valid_queue/1», rProper, fProper] at requires
            change (do let total ← Erlang.queue.«len/1» (pack r f)
                       Erlang.erlang.«=</2» (.integer k) total) = .ok Lynx.Term.true at requires
            rw [lenModel] at requires
            simp only [Lynx.Result.ok_bind, Erlang.erlang.«=</2_integers»] at requires
            have maxIndex : k ≤ (↑r.length : Int) + ↑f.length := by
              by_cases h : k ≤ (↑r.length : Int) + ↑f.length <;> simp_all
            have bound : k.toNat ≤ r.length + f.length := by omega
            obtain ⟨lr, lf, rr, rf, returned, leftLength, order⟩ := splitModel k.toNat r f bound
            have indexEq := Int.toNat_of_nonneg nonnegative
            simp only [indexEq] at returned
            have leftSize : (↑lr.length : Int) + ↑lf.length = k := by omega
            change «split_contract/2» (.integer k) (pack r f) = .ok Lynx.Term.true
            unfold «split_contract/2»
            rw [returned]
            simp [lenModel, toListModel, appendModel, leftSize, order,
              Erlang.erlang.«=:=/2»]
          · simp [«valid_queue/1», rProper, fInvalid] at requires
        · simp [«valid_queue/1», rInvalid] at requires
      """
  end

  laws "queue" do
    law reverse_involution(queue),
      requires: :queue.is_queue(queue),
      expects: :queue.reverse(:queue.reverse(queue)) === queue,
      proof: ~LEAN"""
      cases queue <;> simp [«reverse_involution:requires/1», Erlang.queue.«is_queue/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [Erlang.queue.«is_queue/1»] at requires
      | [rear, front] =>
        cases rear <;> simp [«reverse_involution:requires/1», Erlang.queue.«is_queue/1»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»] at requires
        all_goals cases front <;> simp [Erlang.erlang.«is_list/1»] at requires
        all_goals simp [«reverse_involution:ensures/1», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«and/2», Erlang.queue.«reverse/1», Erlang.erlang.«=:=/2»]
      """

    law reverse_exchanges_ends(value, queue),
      requires: :queue.is_queue(queue),
      expects:
        :queue.reverse(:queue.in(value, queue)) === :queue.in_r(value, :queue.reverse(queue)),
      proof: ~LEAN"""
      cases queue <;> simp [«reverse_exchanges_ends:requires/2», Erlang.queue.«is_queue/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [Erlang.queue.«is_queue/1»] at requires
      | [rear, front] =>
        cases rear <;> simp [«reverse_exchanges_ends:requires/2», Erlang.queue.«is_queue/1»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»] at requires
        all_goals cases front <;> simp [Erlang.erlang.«is_list/1»] at requires
        all_goals simp [«reverse_exchanges_ends:ensures/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«and/2», Erlang.queue.«reverse/1», Erlang.queue.«in/2»,
          Erlang.queue.«in_r/2», Erlang.erlang.«=:=/2»]
        all_goals split <;> simp_all [Erlang.queue.«reverse/1», Erlang.queue.«in_r/2»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»,
          Erlang.erlang.«=:=/2»]
      """

    law front_insert_peek(value, queue),
      requires: :queue.is_queue(queue),
      expects: :queue.peek(:queue.in_r(value, queue)) === {:value, value},
      proof: ~LEAN"""
      cases queue <;> simp [«front_insert_peek:requires/2», Erlang.queue.«is_queue/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [Erlang.queue.«is_queue/1»] at requires
      | [rear, front] =>
        cases rear <;> simp [«front_insert_peek:requires/2», Erlang.queue.«is_queue/1»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»] at requires
        all_goals cases front <;> simp [Erlang.erlang.«is_list/1»] at requires
        all_goals simp [«front_insert_peek:ensures/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«and/2», Erlang.queue.«in_r/2», Erlang.queue.«peek/1», Erlang.erlang.«=:=/2»]
        all_goals split <;> simp_all [Erlang.queue.«in_r/2»,
          Erlang.queue.«peek/1», Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»,
          Erlang.erlang.«=:=/2»]
      """
  end
end
