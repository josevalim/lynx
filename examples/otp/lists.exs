# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/lists.exs
# Prove the installed OTP implementation, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1).
# These proofs depend on implementation details; rerun after OTP upgrades.
ExUnit.start()

defmodule ListsProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  # The endpoint may be one step behind the start, producing an empty sequence.
  # A zero step is legal only for equal endpoints and produces a singleton.
  def sequence_contract(first, last, step, index) do
    values = :lists.seq(first, last, step)
    count = if step == 0, do: 1, else: div(last - first + step, step)

    length(values) === count and
      (index >= count or :lists.nth(index + 1, values) === first + index * step)
  end

  defp proper_list([]), do: true
  defp proper_list([_ | tail]), do: proper_list(tail)
  defp proper_list(_), do: false

  defp sorted([]), do: true
  defp sorted([_]), do: true
  defp sorted([left, right | tail]), do: left <= right and sorted([right | tail])

  defp multiplicity([], _value), do: 0

  defp multiplicity([head | tail], value),
    do: if(head === value, do: 1, else: 0) + multiplicity(tail, value)

  def sort_contract(list, value) do
    result = :lists.sort(list)

    sorted(result) and multiplicity(result, value) === multiplicity(list, value) and
      :lists.sort(result) === result
  end

  def enum_sort_contract(list, value) do
    result = Enum.sort(list)

    sorted(result) and multiplicity(result, value) === multiplicity(list, value) and
      Enum.sort(result) === result
  end

  @merge_fixpoint ~LEAN"""
  partial_fixpoint
  """

  laws "sort preserves multiplicities and is idempotent" do
    # The list-only law never enters Enum's general enumerable implementation.
    cutoff &Enum.sort/2
    termination_suffix &:lists.mergel/2, @merge_fixpoint
    termination_suffix &:lists.rmergel/2, @merge_fixpoint

    law sort_contract_holds(list, value),
      requires: proper_list(list),
      expects: sort_contract(list, value) and enum_sort_contract(list, value),
      proof: ~LEAN"""
      let encode (xs : List Lynx.Term) : Lynx.Term := xs.foldr Lynx.Term.cons .nil
      -- Reverse merging prefers the right run on ties. Sortedness uses a
      -- non-strict relation in both directions; element identity is preserved.
      let select (descending : Bool) (left right : Lynx.Term) : Bool :=
        if descending then (Lynx.Term.compare left right).isGT else (Lynx.Term.compare left right).isLE
      let first (descending : Bool) :=
        if descending then Erlang.lists.«rmerge2_1/4» else Erlang.lists.«merge2_1/4»
      let second (descending : Bool) :=
        if descending then Erlang.lists.«rmerge2_2/5» else Erlang.lists.«merge2_2/5»
      have reverseModel (xs ys : List Lynx.Term) :
          Erlang.lists.«reverse/2» (encode xs) (encode ys) = .ok (encode (xs.reverse ++ ys)) := by
        induction xs generalizing ys with
        | nil => rfl
        | cons x xs ih =>
          simpa [encode, Erlang.lists.«reverse/2», List.reverse_cons, List.append_assoc] using ih (x :: ys)
      have firstNil (descending : Bool) (head : Lynx.Term) (ys acc : List Lynx.Term) :
          first descending (encode []) head (encode ys) (encode acc) =
            .ok (encode ((head :: ys).reverse ++ acc)) := by
        cases descending <;> simp only [first, Bool.false_eq_true, if_false, if_true]
        all_goals first | rw [Erlang.lists.«merge2_1/4».eq_def] | rw [Erlang.lists.«rmerge2_1/4».eq_def]
        all_goals simpa [encode, List.reverse_cons, List.append_assoc] using reverseModel ys (head :: acc)
      have secondNil (descending : Bool) (head previous : Lynx.Term) (xs acc : List Lynx.Term) :
          second descending (encode xs) previous (encode []) (encode acc) head =
            .ok (encode ((head :: xs).reverse ++ previous :: acc)) := by
        cases descending <;> simp only [second, Bool.false_eq_true, if_false, if_true]
        all_goals first | rw [Erlang.lists.«merge2_2/5».eq_def] | rw [Erlang.lists.«rmerge2_2/5».eq_def]
        all_goals simpa [encode, List.reverse_cons, List.append_assoc] using reverseModel xs (head :: previous :: acc)
      have firstStep (descending : Bool) (x head : Lynx.Term) (xs ys acc : List Lynx.Term) :
          first descending (encode (x :: xs)) head (encode ys) (encode acc) =
            if select descending x head then
              first descending (encode xs) head (encode ys) (encode (x :: acc))
            else second descending (encode xs) head (encode ys) (encode acc) x := by
        cases descending
        · simp only [first, second, select, Bool.false_eq_true, if_false, if_true]
          rw [Erlang.lists.«merge2_1/4».eq_def]
          cases comparison : Lynx.Term.compare x head <;>
            simp [encode, Erlang.erlang.«=</2», comparison]
        · simp only [first, second, select, Bool.false_eq_true, if_false, if_true]
          rw [Erlang.lists.«rmerge2_1/4».eq_def]
          cases comparison : Lynx.Term.compare x head <;>
            simp [encode, Erlang.erlang.«=</2», comparison]
      have secondStep (descending : Bool) (head previous y : Lynx.Term) (xs ys acc : List Lynx.Term) :
          second descending (encode xs) previous (encode (y :: ys)) (encode acc) head =
            if select descending head y then
              first descending (encode xs) y (encode ys) (encode (head :: previous :: acc))
            else second descending (encode xs) y (encode ys) (encode (previous :: acc)) head := by
        cases descending
        · simp only [first, second, select, Bool.false_eq_true, if_false, if_true]
          rw [Erlang.lists.«merge2_2/5».eq_def]
          cases comparison : Lynx.Term.compare head y <;>
            simp [encode, Erlang.erlang.«=</2», comparison]
        · simp only [first, second, select, Bool.false_eq_true, if_false, if_true]
          rw [Erlang.lists.«rmerge2_2/5».eq_def]
          cases comparison : Lynx.Term.compare head y <;>
            simp [encode, Erlang.erlang.«=</2», comparison]
      -- The two worker states implement an ordinary merge into a reversed accumulator.
      have merge2Model (descending : Bool) (n : Nat) (xs ys : List Lynx.Term)
          (length : xs.length + ys.length = n) :
          (∀ head acc, first descending (encode xs) head (encode ys) (encode acc) =
            .ok (encode ((List.merge xs (head :: ys) (select descending)).reverse ++ acc))) ∧
          (∀ previous head acc,
            second descending (encode xs) previous (encode ys) (encode acc) head =
              .ok (encode ((List.merge (head :: xs) ys (select descending)).reverse ++ previous :: acc))) := by
        induction n using Nat.strongRecOn generalizing xs ys with
        | ind n ih =>
          constructor
          · intro head acc
            cases xs with
            | nil => simpa using firstNil descending head ys acc
            | cons x xs =>
              have smaller : xs.length + ys.length < n := by simp at length; omega
              rw [firstStep]
              by_cases choice : select descending x head
              · have returned := (ih _ smaller xs ys rfl).1 head (x :: acc)
                simpa [choice, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using returned
              · have returned := (ih _ smaller xs ys rfl).2 head x acc
                simpa [choice, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using returned
          · intro previous head acc
            cases ys with
            | nil => simpa using secondNil descending head previous xs acc
            | cons y ys =>
              have smaller : xs.length + ys.length < n := by simp at length; omega
              rw [secondStep]
              by_cases choice : select descending head y
              · have returned := (ih _ smaller xs ys rfl).1 y (head :: previous :: acc)
                simpa [choice, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using returned
              · have returned := (ih _ smaller xs ys rfl).2 y head (previous :: acc)
                simpa [choice, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using returned
      let f1 (descending : Bool) (xs acc : List Lynx.Term) (h2 : Lynx.Term) (ys : List Lynx.Term)
          (h3 : Lynx.Term) (zs : List Lynx.Term) : Except Lynx.Exception Lynx.Term :=
        (if descending then Erlang.lists.«rmerge3_1/6» else Erlang.lists.«merge3_1/6»)
          (encode xs) (encode acc) h2 (encode ys) h3 (encode zs)
      let f2 (descending : Bool) (xs : List Lynx.Term) (h1 : Lynx.Term) (acc ys : List Lynx.Term)
          (h3 : Lynx.Term) (zs : List Lynx.Term) : Except Lynx.Exception Lynx.Term :=
        (if descending then Erlang.lists.«rmerge3_2/6» else Erlang.lists.«merge3_2/6»)
          (encode xs) h1 (encode acc) (encode ys) h3 (encode zs)
      let f12 (descending : Bool) (xs : List Lynx.Term) (h1 h2 : Lynx.Term) (ys acc zs : List Lynx.Term) :
          Except Lynx.Exception Lynx.Term :=
        (if descending then Erlang.lists.«rmerge3_21_3/6» else Erlang.lists.«merge3_12_3/6»)
          (encode xs) h1 h2 (encode ys) (encode acc) (encode zs)
      let f21 (descending : Bool) (xs : List Lynx.Term) (h1 h2 : Lynx.Term) (ys acc zs : List Lynx.Term) :
          Except Lynx.Exception Lynx.Term :=
        (if descending then Erlang.lists.«rmerge3_12_3/6» else Erlang.lists.«merge3_21_3/6»)
          (encode xs) h1 h2 (encode ys) (encode acc) (encode zs)
      have f1Nil (descending : Bool) (acc ys zs : List Lynx.Term) (h2 h3 : Lynx.Term) :
          f1 descending [] acc h2 ys h3 zs =
            first descending (encode (h2 :: ys)) h3 (encode zs) (encode acc) := by
        cases descending <;> simp only [f1, first, Bool.false_eq_true, if_false, if_true]
        · conv => lhs; rw [Erlang.lists.«merge3_1/6».eq_def]
          conv => rhs; rw [Erlang.lists.«merge2_1/4».eq_def]
          simp [encode]
        · conv => lhs; rw [Erlang.lists.«rmerge3_1/6».eq_def]
          conv => rhs; rw [Erlang.lists.«rmerge2_1/4».eq_def]
          simp [encode]
      have f2Nil (descending : Bool) (xs acc zs : List Lynx.Term) (h1 h3 : Lynx.Term) :
          f2 descending xs h1 acc [] h3 zs =
            first descending (encode (h1 :: xs)) h3 (encode zs) (encode acc) := by
        cases descending <;> simp only [f2, first, Bool.false_eq_true, if_false, if_true]
        · conv => lhs; rw [Erlang.lists.«merge3_2/6».eq_def]
          conv => rhs; rw [Erlang.lists.«merge2_1/4».eq_def]
          simp [encode]
        · conv => lhs; rw [Erlang.lists.«rmerge3_2/6».eq_def]
          conv => rhs; rw [Erlang.lists.«rmerge2_1/4».eq_def]
          simp [encode]
      have f12Nil (descending : Bool) (xs ys acc : List Lynx.Term) (h1 h2 : Lynx.Term) :
          f12 descending xs h1 h2 ys acc [] =
            first descending (encode xs) h2 (encode ys) (encode (h1 :: acc)) := by
        cases descending <;> simp only [f12, first, Bool.false_eq_true, if_false, if_true]
        · rw [Erlang.lists.«merge3_12_3/6».eq_def]
          rfl
        · rw [Erlang.lists.«rmerge3_21_3/6».eq_def]
          rfl
      have f21Nil (descending : Bool) (xs ys acc : List Lynx.Term) (h1 h2 : Lynx.Term) :
          f21 descending xs h1 h2 ys acc [] =
            second descending (encode xs) h2 (encode ys) (encode acc) h1 := by
        cases descending <;> simp only [f21, second, Bool.false_eq_true, if_false, if_true]
        · rw [Erlang.lists.«merge3_21_3/6».eq_def]
          rfl
        · rw [Erlang.lists.«rmerge3_12_3/6».eq_def]
          rfl
      have f1Step (descending : Bool) (x h2 h3 : Lynx.Term) (xs acc ys zs : List Lynx.Term) :
          f1 descending (x :: xs) acc h2 ys h3 zs =
            if select descending x h2 then
              if select descending x h3 then f1 descending xs (x :: acc) h2 ys h3 zs
              else f12 descending xs x h2 ys (h3 :: acc) zs
            else
              if select descending h2 h3 then f2 descending xs x (h2 :: acc) ys h3 zs
              else f21 descending xs x h2 ys (h3 :: acc) zs := by
        cases descending <;> simp only [f1, f2, f12, f21, select, Bool.false_eq_true, if_false, if_true]
        all_goals first | rw [Erlang.lists.«merge3_1/6».eq_def] | rw [Erlang.lists.«rmerge3_1/6».eq_def]
        all_goals cases a : Lynx.Term.compare x h2 <;> cases b : Lynx.Term.compare x h3 <;>
          cases c : Lynx.Term.compare h2 h3 <;> simp [encode, Erlang.erlang.«=</2», a, b, c]
      have f2Step (descending : Bool) (h1 h2 h3 : Lynx.Term) (xs acc ys zs : List Lynx.Term) :
          f2 descending xs h1 acc (h2 :: ys) h3 zs =
            f1 descending (h1 :: xs) acc h2 ys h3 zs := by
        cases descending <;> simp only [f1, f2, Bool.false_eq_true, if_false, if_true]
        · conv => lhs; rw [Erlang.lists.«merge3_2/6».eq_def]
          conv => rhs; rw [Erlang.lists.«merge3_1/6».eq_def]
          simp [encode]
        · conv => lhs; rw [Erlang.lists.«rmerge3_2/6».eq_def]
          conv => rhs; rw [Erlang.lists.«rmerge3_1/6».eq_def]
          simp [encode]
      have f12Step (descending : Bool) (h1 h2 h3 : Lynx.Term) (xs ys acc zs : List Lynx.Term) :
          f12 descending xs h1 h2 ys acc (h3 :: zs) =
            if select descending h1 h3 then f1 descending xs (h1 :: acc) h2 ys h3 zs
            else f12 descending xs h1 h2 ys (h3 :: acc) zs := by
        cases descending <;> simp only [f1, f12, select, Bool.false_eq_true, if_false, if_true]
        all_goals first | rw [Erlang.lists.«merge3_12_3/6».eq_def] | rw [Erlang.lists.«rmerge3_21_3/6».eq_def]
        all_goals cases comparison : Lynx.Term.compare h1 h3 <;> simp [encode, Erlang.erlang.«=</2», comparison]
      have f21Step (descending : Bool) (h1 h2 h3 : Lynx.Term) (xs ys acc zs : List Lynx.Term) :
          f21 descending xs h1 h2 ys acc (h3 :: zs) =
            if select descending h2 h3 then f2 descending xs h1 (h2 :: acc) ys h3 zs
            else f21 descending xs h1 h2 ys (h3 :: acc) zs := by
        cases descending <;> simp only [f2, f21, select, Bool.false_eq_true, if_false, if_true]
        all_goals first | rw [Erlang.lists.«merge3_21_3/6».eq_def] | rw [Erlang.lists.«rmerge3_12_3/6».eq_def]
        all_goals cases comparison : Lynx.Term.compare h2 h3 <;> simp [encode, Erlang.erlang.«=</2», comparison]
      let merged (descending : Bool) (xs ys zs : List Lynx.Term) :=
        List.merge (List.merge xs ys (select descending)) zs (select descending)
      -- OTP caches the minimum of the first two heads before reading the third run.
      -- A left-associated pair of merges models all four cached-head states.
      have threeModel (descending : Bool) (n : Nat) :
          (∀ xs ys zs : List Lynx.Term, xs.length+ys.length+zs.length = n → ∀ h2 h3 acc,
            f1 descending xs acc h2 ys h3 zs =
              .ok (encode ((merged descending xs (h2 :: ys) (h3 :: zs)).reverse ++ acc))) ∧
          (∀ xs ys zs : List Lynx.Term, xs.length+ys.length+zs.length = n → ∀ h1 h3 acc,
            f2 descending xs h1 acc ys h3 zs =
              .ok (encode ((merged descending (h1 :: xs) ys (h3 :: zs)).reverse ++ acc))) ∧
          (∀ xs ys zs : List Lynx.Term, xs.length+ys.length+zs.length = n → ∀ h1 h2 acc,
            select descending h1 h2 → f12 descending xs h1 h2 ys acc zs =
              .ok (encode ((merged descending (h1 :: xs) (h2 :: ys) zs).reverse ++ acc))) ∧
          (∀ xs ys zs : List Lynx.Term, xs.length+ys.length+zs.length = n → ∀ h1 h2 acc,
            ¬ select descending h1 h2 → f21 descending xs h1 h2 ys acc zs =
              .ok (encode ((merged descending (h1 :: xs) (h2 :: ys) zs).reverse ++ acc))) := by
        induction n using Nat.strongRecOn with
        | ind n ih =>
          have firstModel (xs ys zs : List Lynx.Term) (length : xs.length+ys.length+zs.length = n)
              (h2 h3 : Lynx.Term) (acc : List Lynx.Term) :
              f1 descending xs acc h2 ys h3 zs =
                .ok (encode ((merged descending xs (h2 :: ys) (h3 :: zs)).reverse ++ acc)) := by
            cases xs with
            | nil =>
              rw [f1Nil]
              simpa [merged] using (merge2Model descending _ (h2 :: ys) zs rfl).1 h3 acc
            | cons x xs =>
              have smaller : xs.length+ys.length+zs.length < n := by simp at length; omega
              have previous := ih _ smaller
              rw [f1Step]
              by_cases xy : select descending x h2 <;>
                by_cases xz : select descending x h3 <;>
                by_cases yz : select descending h2 h3
              all_goals first
                | simpa [xy, xz, yz, merged, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using
                    previous.1 xs ys zs rfl h2 h3 (x :: acc)
                | simpa [xy, xz, yz, merged, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using
                    previous.2.2.1 xs ys zs rfl x h2 (h3 :: acc) xy
                | simpa [xy, xz, yz, merged, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using
                    previous.2.1 xs ys zs rfl x h3 (h2 :: acc)
                | simpa [xy, xz, yz, merged, List.cons_merge_cons, List.reverse_cons, List.append_assoc] using
                    previous.2.2.2 xs ys zs rfl x h2 (h3 :: acc) xy
          refine ⟨firstModel, ?_, ?_, ?_⟩
          · intro xs ys zs length h1 h3 acc
            cases ys with
            | nil =>
              rw [f2Nil]
              simpa [merged] using (merge2Model descending _ (h1 :: xs) zs rfl).1 h3 acc
            | cons h2 ys =>
              rw [f2Step]
              exact firstModel (h1 :: xs) ys zs (by simp at length ⊢; omega) h2 h3 acc
          · intro xs ys zs length h1 h2 acc selected
            cases zs with
            | nil =>
              rw [f12Nil]
              simpa [merged, List.cons_merge_cons, selected, List.reverse_cons, List.append_assoc] using
                (merge2Model descending _ xs ys rfl).1 h2 (h1 :: acc)
            | cons h3 zs =>
              have smaller : xs.length+ys.length+zs.length < n := by simp at length; omega
              have previous := ih _ smaller
              rw [f12Step]
              by_cases choice : select descending h1 h3
              · simpa [merged, List.cons_merge_cons, selected, choice, List.reverse_cons, List.append_assoc] using
                  previous.1 xs ys zs rfl h2 h3 (h1 :: acc)
              · simpa [merged, List.cons_merge_cons, selected, choice, List.reverse_cons, List.append_assoc] using
                  previous.2.2.1 xs ys zs rfl h1 h2 (h3 :: acc) selected
          · intro xs ys zs length h1 h2 acc selected
            cases zs with
            | nil =>
              rw [f21Nil]
              simpa [merged, List.cons_merge_cons, selected, List.reverse_cons, List.append_assoc] using
                (merge2Model descending _ xs ys rfl).2 h2 h1 acc
            | cons h3 zs =>
              have smaller : xs.length+ys.length+zs.length < n := by simp at length; omega
              have previous := ih _ smaller
              rw [f21Step]
              by_cases choice : select descending h2 h3
              · simpa [merged, List.cons_merge_cons, selected, choice, List.reverse_cons, List.append_assoc] using
                  previous.2.1 xs ys zs rfl h1 h3 (h2 :: acc)
              · simpa [merged, List.cons_merge_cons, selected, choice, List.reverse_cons, List.append_assoc] using
                  previous.2.2.2 xs ys zs rfl h1 h2 (h3 :: acc) selected
      let order (descending : Bool) (left right : Lynx.Term) : Bool :=
        if descending then (Lynx.Term.compare right left).isLE else (Lynx.Term.compare left right).isLE
      -- Quantifying over weights proves multiplicity preservation for every term.
      let mass (weight : Lynx.Term → Nat) (xs : List Lynx.Term) := (xs.map weight).sum
      have massNil (weight : Lynx.Term → Nat) : mass weight [] = 0 := rfl
      have massCons (weight : Lynx.Term → Nat) (x : Lynx.Term) (xs : List Lynx.Term) :
          mass weight (x :: xs) = weight x + mass weight xs := rfl
      have massAppend (weight : Lynx.Term → Nat) (xs ys : List Lynx.Term) :
          mass weight (xs ++ ys) = mass weight xs + mass weight ys := by simp [mass]
      have massReverse (weight : Lynx.Term → Nat) (xs : List Lynx.Term) :
          mass weight xs.reverse = mass weight xs := by simp [mass]
      have massMerge (descending : Bool) (weight : Lynx.Term → Nat) (xs ys : List Lynx.Term) :
          mass weight (List.merge xs ys (select descending)) = mass weight xs + mass weight ys := by
        have sums (as bs : List Lynx.Term) (permutation : as.Perm bs) : mass weight as = mass weight bs := by
          induction permutation with
          | nil => rfl
          | cons x _ ih => simp only [massCons, ih]
          | swap x y rest => simp only [massCons]; omega
          | trans _ _ ihl ihr => exact ihl.trans ihr
        simpa only [massAppend] using sums _ _ (List.merge_perm_append (le := select descending))
      have orderTrans (descending : Bool) (a b c : Lynx.Term)
          (ab : order descending a b) (bc : order descending b c) : order descending a c := by
        cases descending
        · exact Std.TransCmp.isLE_trans ab bc
        · exact Std.TransCmp.isLE_trans bc ab
      have selectedOrder (descending : Bool) (a b : Lynx.Term) :
          (select descending a b → order descending a b) ∧
          (¬ select descending a b → order descending b a) := by
        have swapped : Lynx.Term.compare b a = (Lynx.Term.compare a b).swap := Std.OrientedCmp.eq_swap
        cases descending <;> cases comparison : Lynx.Term.compare a b <;>
          simp [order, select, swapped, comparison]
      have mergeSorted (descending : Bool) (xs ys : List Lynx.Term)
          (left : xs.Pairwise (fun a b => order descending a b))
          (right : ys.Pairwise (fun a b => order descending a b)) :
          (List.merge xs ys (select descending)).Pairwise (fun a b => order descending a b) := by
        induction xs generalizing ys with
        | nil => simpa using right
        | cons x xs ih =>
          induction ys with
          | nil => simpa using left
          | cons y ys ihy =>
            rw [List.cons_merge_cons]
            by_cases selected : select descending x y
            · rw [if_pos selected]
              apply List.pairwise_cons.mpr
              refine ⟨?_, ih (y :: ys) (List.pairwise_cons.mp left).2 right⟩
              intro z member
              rcases List.mem_merge.mp member with member | member
              · exact (List.pairwise_cons.mp left).1 z member
              · rcases List.mem_cons.mp member with rfl | member
                · exact (selectedOrder descending x z).1 selected
                · exact orderTrans descending x y z ((selectedOrder descending x y).1 selected)
                    ((List.pairwise_cons.mp right).1 z member)
            · rw [if_neg selected]
              apply List.pairwise_cons.mpr
              refine ⟨?_, ihy (List.pairwise_cons.mp right).2⟩
              intro z member
              rcases List.mem_merge.mp member with member | member
              · rcases List.mem_cons.mp member with rfl | member
                · exact (selectedOrder descending z y).2 selected
                · exact orderTrans descending y x z ((selectedOrder descending x y).2 selected)
                    ((List.pairwise_cons.mp left).1 z member)
              · exact (List.pairwise_cons.mp right).1 z member
      have reversedOrder (descending : Bool) (xs : List Lynx.Term)
          (sorted : xs.Pairwise (fun a b => order descending a b)) :
          xs.reverse.Pairwise (fun a b => order (!descending) a b) := by
        cases descending <;> simpa only [List.pairwise_reverse, order, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, if_false, if_true] using sorted
      let combine (descending : Bool) (xs ys zs : List Lynx.Term) := (merged descending xs ys zs).reverse
      have combineMass (descending : Bool) (weight : Lynx.Term → Nat) (xs ys zs : List Lynx.Term) :
          mass weight (combine descending xs ys zs) = mass weight xs + mass weight ys + mass weight zs := by
        simp only [combine, merged, massReverse, massMerge]
      have combineSorted (descending : Bool) (xs ys zs : List Lynx.Term)
          (sx : xs.Pairwise (fun a b => order descending a b))
          (sy : ys.Pairwise (fun a b => order descending a b))
          (sz : zs.Pairwise (fun a b => order descending a b)) :
          (combine descending xs ys zs).Pairwise (fun a b => order (!descending) a b) :=
        reversedOrder descending _ (mergeSorted descending _ _ (mergeSorted descending _ _ sx sy) sz)
      have combineNonempty (descending : Bool) (xs ys zs : List Lynx.Term)
          (nonempty : 0 < xs.length+ys.length+zs.length) : combine descending xs ys zs ≠ [] := by
        intro empty
        have length := congrArg List.length empty
        simp only [combine, merged, List.length_reverse, List.length_merge, List.length_nil] at length
        omega
      let pack (runs : List (List Lynx.Term)) : Lynx.Term := encode (runs.map encode)
      let schedule (descending : Bool) (runs acc : List (List Lynx.Term)) :
          Except Lynx.Exception Lynx.Term :=
        (if descending then Erlang.lists.«rmergel/2» else Erlang.lists.«mergel/2») (pack runs) (pack acc)
      let runsGood (descending : Bool) (runs : List (List Lynx.Term)) : Prop :=
        ∀ run ∈ runs, run ≠ [] ∧ run.Pairwise (fun a b => order descending a b)
      let good (input : List Lynx.Term) (computation : Except Lynx.Exception Lynx.Term) : Prop :=
        ∃ output : List Lynx.Term, computation = .ok (encode output) ∧
          output.Pairwise (fun a b => order false a b) ∧
          ∀ weight, mass weight output = mass weight input
      have goodTransfer (original next : List Lynx.Term) (computation : Except Lynx.Exception Lynx.Term)
          (checked : good next computation)
          (same : ∀ weight, mass weight next = mass weight original) : good original computation := by
        obtain ⟨output, returned, sorted, equal⟩ := checked
        exact ⟨output, returned, sorted, fun weight => (equal weight).trans (same weight)⟩
      have mergeTwoEval (descending : Bool) (xs ys : List Lynx.Term) (head : Lynx.Term) :
          first descending (encode xs) head (encode ys) (encode []) =
            .ok (encode (combine descending xs (head :: ys) [])) := by
        simpa [combine, merged] using (merge2Model descending _ xs ys rfl).1 head []
      have mergeThreeEval (descending : Bool) (xs ys zs : List Lynx.Term) (h2 h3 : Lynx.Term) :
          f1 descending xs [] h2 ys h3 zs =
            .ok (encode (combine descending xs (h2 :: ys) (h3 :: zs))) := by
        simpa [combine] using (threeModel descending _).1 xs ys zs rfl h2 h3 []
      have ascendingEmpty : schedule false [] [] = .ok (encode []) := by
        simp only [schedule, Bool.false_eq_true, if_false]
        rw [Erlang.lists.«mergel/2».eq_def]
        rfl
      have ascendingLeaf (x : Lynx.Term) (xs : List Lynx.Term) :
          schedule false [x :: xs] [] = .ok (encode (x :: xs)) := by
        simp only [schedule, Bool.false_eq_true, if_false]
        rw [Erlang.lists.«mergel/2».eq_def]
        rfl
      have ascendingBoundary (run : List Lynx.Term) (acc : List (List Lynx.Term)) :
          schedule false [] (run :: acc) = schedule true (run :: acc) [] := by
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«mergel/2».eq_def]
        rfl
      have descendingBoundary (acc : List (List Lynx.Term)) :
          schedule true [] acc = schedule false acc [] := by
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«rmergel/2».eq_def]
        rfl
      have ascendingOne (x : Lynx.Term) (xs run : List Lynx.Term) (acc : List (List Lynx.Term)) :
          schedule false [x :: xs] (run :: acc) =
            schedule true ((x :: xs).reverse :: run :: acc) [] := by
        have returned := reverseModel (x :: xs) []
        simp only [encode, List.foldr_cons, List.foldr_nil, List.append_nil] at returned
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«mergel/2».eq_def]
        simp [pack, encode, returned]
      have descendingOne (run : List Lynx.Term) (acc : List (List Lynx.Term)) :
          schedule true [run] acc = schedule false (run.reverse :: acc) [] := by
        have returned := reverseModel run []
        simp only [encode, List.foldr_nil, List.append_nil] at returned
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«rmergel/2».eq_def]
        simp [pack, encode, returned]
      have ascendingTwo (x y : Lynx.Term) (xs ys : List Lynx.Term) (acc : List (List Lynx.Term)) :
          schedule false [x :: xs, y :: ys] acc =
            schedule true (combine false (x :: xs) (y :: ys) [] :: acc) [] := by
        have returned := mergeTwoEval false (x :: xs) ys y
        simp only [first, Bool.false_eq_true, if_false, encode, List.foldr_cons, List.foldr_nil] at returned
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«mergel/2».eq_def]
        simp [pack, encode, returned]
      have descendingTwo (x y : Lynx.Term) (xs ys : List Lynx.Term) (acc : List (List Lynx.Term)) :
          schedule true [x :: xs, y :: ys] acc =
            schedule false (combine true (y :: ys) (x :: xs) [] :: acc) [] := by
        have returned := mergeTwoEval true (y :: ys) xs x
        simp only [first, if_true, encode, List.foldr_cons, List.foldr_nil] at returned
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«rmergel/2».eq_def]
        simp [pack, encode, returned]
      have ascendingThree (x y z : Lynx.Term) (xs ys zs : List Lynx.Term) (runs acc : List (List Lynx.Term)) :
          schedule false ((x :: xs) :: (y :: ys) :: (z :: zs) :: runs) acc =
            schedule false runs (combine false (x :: xs) (y :: ys) (z :: zs) :: acc) := by
        have returned := mergeThreeEval false (x :: xs) ys zs y z
        simp only [f1, Bool.false_eq_true, if_false, encode, List.foldr_cons, List.foldr_nil] at returned
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«mergel/2».eq_def]
        simp [pack, encode, returned]
      have descendingThree (x y z : Lynx.Term) (xs ys zs : List Lynx.Term) (runs acc : List (List Lynx.Term)) :
          schedule true ((x :: xs) :: (y :: ys) :: (z :: zs) :: runs) acc =
            schedule true runs (combine true (z :: zs) (y :: ys) (x :: xs) :: acc) := by
        have returned := mergeThreeEval true (z :: zs) ys xs y x
        simp only [f1, if_true, encode, List.foldr_cons, List.foldr_nil] at returned
        simp only [schedule, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«rmergel/2».eq_def]
        simp [pack, encode, returned]
      have runsNil (descending : Bool) : runsGood descending [] := by simp [runsGood]
      have runsCons (descending : Bool) (run : List Lynx.Term) (runs : List (List Lynx.Term)) :
          runsGood descending (run :: runs) ↔
            (run ≠ [] ∧ run.Pairwise (fun a b => order descending a b)) ∧ runsGood descending runs := by
        simp [runsGood]
      have reversedValid (descending : Bool) (run : List Lynx.Term)
          (valid : run ≠ [] ∧ run.Pairwise (fun a b => order descending a b)) :
          run.reverse ≠ [] ∧ run.reverse.Pairwise (fun a b => order (!descending) a b) :=
        ⟨by simpa using valid.1, reversedOrder descending run valid.2⟩
      let measure (descending : Bool) (runs acc : List (List Lynx.Term)) : Nat :=
        4*(runs.length+acc.length) + (if acc.isEmpty then 0 else 2) + (if descending then 1 else 0)
      -- Every valid scheduler state terminates, including boundaries between passes.
      -- The native measure counts runs and distinguishes the direction and accumulator.
      have scheduler (n : Nat) (descending : Bool) (runs acc : List (List Lynx.Term))
          (size : measure descending runs acc = n)
          (valid : runsGood descending runs) (saved : runsGood (!descending) acc) :
          good (runs.flatten ++ acc.flatten) (schedule descending runs acc) := by
        induction n using Nat.strongRecOn generalizing descending runs acc with
        | ind n ih =>
          have advance (direction : Bool) (nextRuns nextAcc : List (List Lynx.Term))
              (smaller : measure direction nextRuns nextAcc < n)
              (nextValid : runsGood direction nextRuns) (nextSaved : runsGood (!direction) nextAcc) :
              good (nextRuns.flatten ++ nextAcc.flatten) (schedule direction nextRuns nextAcc) :=
            ih _ smaller direction nextRuns nextAcc rfl nextValid nextSaved
          cases descending
          · cases runs with
            | nil =>
              cases acc with
              | nil => exact ⟨[], ascendingEmpty, by simp, fun _ => rfl⟩
              | cons run acc =>
                rw [ascendingBoundary]
                have child := advance true (run :: acc) [] (by simp [measure] at size ⊢; omega)
                  saved (runsNil false)
                simpa only [List.flatten_nil, List.nil_append, List.append_nil] using child
            | cons xs runs =>
              obtain ⟨xValid, restValid1⟩ := (runsCons false xs runs).mp valid
              obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil xValid.1
              cases runs with
              | nil =>
                cases acc with
                | nil =>
                  refine ⟨x :: xs, ascendingLeaf x xs, xValid.2, ?_⟩
                  intro weight
                  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
                | cons run acc =>
                  rw [ascendingOne]
                  have child := advance true ((x :: xs).reverse :: run :: acc) []
                    (by simp [measure] at size ⊢; omega)
                    ((runsCons true _ _).mpr ⟨reversedValid false _ xValid, saved⟩) (runsNil false)
                  refine goodTransfer _ _ _ child ?_
                  intro weight
                  simp only [List.flatten_cons, List.flatten_nil, massAppend, massReverse, massNil]
                  omega
              | cons ys runs =>
                obtain ⟨yValid, restValid2⟩ := (runsCons false ys runs).mp restValid1
                obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil yValid.1
                cases runs with
                | nil =>
                  rw [ascendingTwo]
                  have combined := (runsCons true _ acc).mpr
                    ⟨⟨combineNonempty false _ _ [] (by simp; omega),
                        combineSorted false _ _ [] xValid.2 yValid.2 (by simp)⟩, saved⟩
                  have child := advance true (combine false (x :: xs) (y :: ys) [] :: acc) []
                    (by simp [measure] at size ⊢; omega) combined (runsNil false)
                  refine goodTransfer _ _ _ child ?_
                  intro weight
                  simp only [List.flatten_cons, List.flatten_nil, massAppend, combineMass, massNil]
                  omega
                | cons zs runs =>
                  obtain ⟨zValid, restValid3⟩ := (runsCons false zs runs).mp restValid2
                  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil zValid.1
                  rw [ascendingThree]
                  have combined := (runsCons true _ acc).mpr
                    ⟨⟨combineNonempty false _ _ _ (by simp; omega),
                        combineSorted false _ _ _ xValid.2 yValid.2 zValid.2⟩, saved⟩
                  have child := advance false runs (combine false (x :: xs) (y :: ys) (z :: zs) :: acc)
                    (by simp [measure] at size ⊢; omega) restValid3 combined
                  refine goodTransfer _ _ _ child ?_
                  intro weight
                  simp only [List.flatten_cons, massAppend, combineMass]
                  omega
          · cases runs with
            | nil =>
              rw [descendingBoundary]
              have child := advance false acc [] (by simp [measure] at size ⊢; omega) saved (runsNil true)
              simpa only [List.flatten_nil, List.nil_append, List.append_nil] using child
            | cons xs runs =>
              obtain ⟨xValid, restValid1⟩ := (runsCons true xs runs).mp valid
              obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil xValid.1
              cases runs with
              | nil =>
                rw [descendingOne]
                have child := advance false ((x :: xs).reverse :: acc) []
                  (by simp [measure] at size ⊢; omega)
                  ((runsCons false _ acc).mpr ⟨reversedValid true _ xValid, saved⟩) (runsNil true)
                refine goodTransfer _ _ _ child ?_
                intro weight
                simp only [List.flatten_cons, List.flatten_nil, massAppend, massReverse, massNil]
                omega
              | cons ys runs =>
                obtain ⟨yValid, restValid2⟩ := (runsCons true ys runs).mp restValid1
                obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil yValid.1
                cases runs with
                | nil =>
                  rw [descendingTwo]
                  have combined := (runsCons false _ acc).mpr
                    ⟨⟨combineNonempty true _ _ [] (by simp; omega),
                        combineSorted true _ _ [] yValid.2 xValid.2 (by simp)⟩, saved⟩
                  have child := advance false (combine true (y :: ys) (x :: xs) [] :: acc) []
                    (by simp [measure] at size ⊢; omega) combined (runsNil true)
                  refine goodTransfer _ _ _ child ?_
                  intro weight
                  simp only [List.flatten_cons, List.flatten_nil, massAppend, combineMass, massNil]
                  omega
                | cons zs runs =>
                  obtain ⟨zValid, restValid3⟩ := (runsCons true zs runs).mp restValid2
                  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil zValid.1
                  rw [descendingThree]
                  have combined := (runsCons false _ acc).mpr
                    ⟨⟨combineNonempty true _ _ _ (by simp; omega),
                        combineSorted true _ _ _ zValid.2 yValid.2 xValid.2⟩, saved⟩
                  have child := advance true runs (combine true (z :: zs) (y :: ys) (x :: xs) :: acc)
                    (by simp [measure] at size ⊢; omega) restValid3 combined
                  refine goodTransfer _ _ _ child ?_
                  intro weight
                  simp only [List.flatten_cons, massAppend, combineMass]
                  omega
      have geFlip (left right : Lynx.Term) :
          (Lynx.Term.compare left right).isGE = (Lynx.Term.compare right left).isLE := by
        have swapped : Lynx.Term.compare left right = (Lynx.Term.compare right left).swap := Std.OrientedCmp.eq_swap
        rw [swapped]
        cases Lynx.Term.compare right left <;> rfl
      have reversePack (runs tail : List (List Lynx.Term)) :
          Erlang.lists.«reverse/2» (pack runs) (pack tail) = .ok (pack (runs.reverse ++ tail)) := by
        simpa [pack, List.map_reverse, List.map_append] using reverseModel (runs.map encode) (tail.map encode)
      let start (descending : Bool) (x y : Lynx.Term) (xs r : List Lynx.Term) (runs : List (List Lynx.Term)) :=
        (if descending then Erlang.lists.«split_2/5» else Erlang.lists.«split_1/5»)
          x y (encode xs) (encode r) (pack runs)
      let pending (descending : Bool) (x y : Lynx.Term) (xs r : List Lynx.Term) (runs : List (List Lynx.Term)) (s : Lynx.Term) :=
        (if descending then Erlang.lists.«split_2_1/6» else Erlang.lists.«split_1_1/6»)
          x y (encode xs) (encode r) (pack runs) s
      have startNil (descending : Bool) (x y : Lynx.Term) (r : List Lynx.Term) (runs : List (List Lynx.Term)) :
          start descending x y [] r runs =
            if descending then schedule false (runs.reverse ++ [y :: x :: r]) []
            else schedule true ((y :: x :: r) :: runs) [] := by
        cases descending <;> simp only [start, schedule, Bool.false_eq_true, if_false, if_true]
        · rw [Erlang.lists.«split_1/5».eq_def]
          rfl
        · have returned := reversePack runs [y :: x :: r]
          simp only [pack, encode, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at returned
          rw [Erlang.lists.«split_2/5».eq_def]
          simp [pack, encode, returned]
      have pendingNil (descending : Bool) (x y saved : Lynx.Term) (r : List Lynx.Term) (runs : List (List Lynx.Term)) :
          pending descending x y [] r runs saved =
            if descending then schedule false (runs.reverse ++ [y :: x :: r, [saved]]) []
            else schedule true ([saved] :: (y :: x :: r) :: runs) [] := by
        cases descending <;> simp only [pending, schedule, Bool.false_eq_true, if_false, if_true]
        · rw [Erlang.lists.«split_1_1/6».eq_def]
          rfl
        · have returned := reversePack runs [y :: x :: r, [saved]]
          simp only [pack, encode, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at returned
          rw [Erlang.lists.«split_2_1/6».eq_def]
          simp [pack, encode, returned]
      have startStep (descending : Bool) (x y z : Lynx.Term) (xs r : List Lynx.Term) (runs : List (List Lynx.Term)) :
          start descending x y (z :: xs) r runs =
            if select descending y z then start descending y z xs (x :: r) runs
            else if select descending x z then start descending z y xs (x :: r) runs
            else if r.isEmpty then start descending x y xs [z] runs
            else pending descending x y xs r runs z := by
        cases descending <;> cases r <;>
          simp only [start, pending, select, Bool.false_eq_true, if_false, if_true]
        all_goals first | rw [Erlang.lists.«split_1/5».eq_def] | rw [Erlang.lists.«split_2/5».eq_def]
        all_goals cases a : Lynx.Term.compare y z <;> cases b : Lynx.Term.compare x z <;>
          simp [encode, Erlang.erlang.«>=/2», Erlang.erlang.«>/2», geFlip, a, b]
      have pendingStep (descending : Bool) (x y z saved : Lynx.Term) (xs r : List Lynx.Term) (runs : List (List Lynx.Term)) :
          pending descending x y (z :: xs) r runs saved =
            if select descending y z then pending descending y z xs (x :: r) runs saved
            else if select descending x z then pending descending z y xs (x :: r) runs saved
            else if select descending saved z then start descending saved z xs [] ((y :: x :: r) :: runs)
            else start descending z saved xs [] ((y :: x :: r) :: runs) := by
        cases descending <;> simp only [start, pending, select, Bool.false_eq_true, if_false, if_true]
        all_goals first | rw [Erlang.lists.«split_1_1/6».eq_def] | rw [Erlang.lists.«split_2_1/6».eq_def]
        all_goals cases a : Lynx.Term.compare y z <;> cases b : Lynx.Term.compare x z <;>
          cases c : Lynx.Term.compare saved z <;>
          simp [encode, pack, Erlang.erlang.«>=/2», Erlang.erlang.«>/2», geFlip, a, b, c]
      have flipped (descending : Bool) (left right : Lynx.Term) :
          order (!descending) left right = order descending right left := by cases descending <;> rfl
      have chainStep (descending : Bool) (a b : Lynx.Term) (tail : List Lynx.Term) :
          ((a :: b :: tail).Pairwise (fun a b => order descending a b)) ↔
            order descending a b ∧ (b :: tail).Pairwise (fun a b => order descending a b) := by
        constructor
        · intro sorted
          exact ⟨(List.pairwise_cons.mp sorted).1 b (by simp), (List.pairwise_cons.mp sorted).2⟩
        · rintro ⟨first, rest⟩
          apply List.pairwise_cons.mpr
          refine ⟨?_, rest⟩
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact orderTrans descending a b item first ((List.pairwise_cons.mp rest).1 item member)
      have prependRun (descending : Bool) (a b : Lynx.Term) (tail : List Lynx.Term)
          (first : order descending a b)
          (rest : (b :: tail).Pairwise (fun a b => order descending a b)) :
          (a :: b :: tail).Pairwise (fun a b => order descending a b) :=
        (chainStep descending a b tail).mpr ⟨first, rest⟩
      have runsAppend (descending : Bool) (left right : List (List Lynx.Term)) :
          runsGood descending (left ++ right) ↔ runsGood descending left ∧ runsGood descending right := by
        constructor
        · intro valid
          exact ⟨fun run member => valid run (List.mem_append_left right member),
            fun run member => valid run (List.mem_append_right left member)⟩
        · rintro ⟨leftGood, rightGood⟩ run member
          rcases List.mem_append.mp member with member | member
          · exact leftGood run member
          · exact rightGood run member
      have runsReverse (descending : Bool) (runs : List (List Lynx.Term)) :
          runsGood descending runs.reverse ↔ runsGood descending runs := by simp [runsGood]
      have massRunsReverse (weight : Lynx.Term → Nat) (runs : List (List Lynx.Term)) :
          mass weight runs.reverse.flatten = mass weight runs.flatten := by
        induction runs with
        | nil => rfl
        | cons run runs ih =>
          simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
            massAppend, massNil, ih]
          omega
      have startFinish (descending : Bool) (x y : Lynx.Term) (r : List Lynx.Term) (runs : List (List Lynx.Term))
          (partialSorted : (y :: x :: r).Pairwise (fun a b => order (!descending) a b))
          (saved : runsGood (!descending) runs) :
          good ([x, y] ++ r ++ runs.flatten) (start descending x y [] r runs) := by
        rw [startNil]
        cases descending <;> simp only [Bool.false_eq_true, if_false, if_true]
        · have valid := (runsCons true _ runs).mpr ⟨⟨by simp, partialSorted⟩, saved⟩
          have checked := scheduler _ true ((y :: x :: r) :: runs) [] rfl valid (runsNil false)
          refine goodTransfer _ _ _ checked ?_
          intro weight
          simp only [List.flatten_cons, List.flatten_nil, massAppend, massCons, massNil]
          omega
        · have valid := (runsAppend false _ _).mpr
            ⟨(runsReverse false runs).mpr saved,
              (runsCons false _ []).mpr ⟨⟨by simp, partialSorted⟩, runsNil false⟩⟩
          have checked := scheduler _ false (runs.reverse ++ [y :: x :: r]) [] rfl valid (runsNil true)
          refine goodTransfer _ _ _ checked ?_
          intro weight
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            massAppend, massCons, massNil, massRunsReverse]
          omega
      have pendingFinish (descending : Bool) (x y s : Lynx.Term) (r : List Lynx.Term) (runs : List (List Lynx.Term))
          (partialSorted : (y :: x :: r).Pairwise (fun a b => order (!descending) a b))
          (saved : runsGood (!descending) runs) :
          good ([s, x, y] ++ r ++ runs.flatten) (pending descending x y [] r runs s) := by
        rw [pendingNil]
        cases descending <;> simp only [Bool.false_eq_true, if_false, if_true]
        · have valid := (runsCons true [s] ((y :: x :: r) :: runs)).mpr ⟨⟨by simp, by simp⟩,
            (runsCons true _ runs).mpr ⟨⟨by simp, partialSorted⟩, saved⟩⟩
          have checked := scheduler _ true ([s] :: (y :: x :: r) :: runs) [] rfl valid (runsNil false)
          refine goodTransfer _ _ _ checked ?_
          intro weight
          simp only [List.flatten_cons, List.flatten_nil, massAppend, massCons, massNil]
          omega
        · have valid := (runsAppend false _ _).mpr
            ⟨(runsReverse false runs).mpr saved,
              (runsCons false _ _).mpr ⟨⟨by simp, partialSorted⟩,
                (runsCons false [s] []).mpr ⟨⟨by simp, by simp⟩, runsNil false⟩⟩⟩
          have checked := scheduler _ false (runs.reverse ++ [y :: x :: r, [s]]) [] rfl valid (runsNil true)
          refine goodTransfer _ _ _ checked ?_
          intro weight
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            massAppend, massCons, massNil, massRunsReverse]
          omega
      -- Run building preserves a sorted partial run and already completed runs.
      -- The second state holds one outlier aside while scanning the remaining input.
      have splitModel (descending : Bool) (n : Nat) (xs : List Lynx.Term) (length : xs.length = n) :
          (∀ x y r runs, (y :: x :: r).Pairwise (fun a b => order (!descending) a b) →
            runsGood (!descending) runs →
            good ([x, y] ++ xs ++ r ++ runs.flatten) (start descending x y xs r runs)) ∧
          (∀ x y r runs s, (y :: x :: r).Pairwise (fun a b => order (!descending) a b) →
            runsGood (!descending) runs →
            good ([s, x, y] ++ xs ++ r ++ runs.flatten) (pending descending x y xs r runs s)) := by
        induction n using Nat.strongRecOn generalizing xs with
        | ind n ih =>
          cases xs with
          | nil =>
            exact ⟨fun x y r runs sorted saved => startFinish descending x y r runs sorted saved,
              fun x y r runs s sorted saved => pendingFinish descending x y s r runs sorted saved⟩
          | cons z xs =>
            have smaller : xs.length < n := by simp at length; omega
            have previous := ih _ smaller xs rfl
            constructor
            · intro x y r runs sorted saved
              rw [startStep]
              by_cases yz : select descending y z
              · rw [if_pos yz]
                have newSorted := prependRun (!descending) z y (x :: r)
                  (by simpa only [flipped] using (selectedOrder descending y z).1 yz) sorted
                have child := previous.1 y z (x :: r) runs newSorted saved
                refine goodTransfer _ _ _ child ?_
                intro weight
                simp only [massAppend, massCons, massNil]
                omega
              · rw [if_neg yz]
                by_cases xz : select descending x z
                · rw [if_pos xz]
                  have zx := prependRun (!descending) z x r
                    (by simpa only [flipped] using (selectedOrder descending x z).1 xz)
                    (List.pairwise_cons.mp sorted).2
                  have newSorted := prependRun (!descending) y z (x :: r)
                    (by simpa only [flipped] using (selectedOrder descending y z).2 yz) zx
                  have child := previous.1 z y (x :: r) runs newSorted saved
                  refine goodTransfer _ _ _ child ?_
                  intro weight
                  simp only [massAppend, massCons, massNil]
                  omega
                · rw [if_neg xz]
                  cases r with
                  | nil =>
                    rw [if_pos (by rfl)]
                    have xzSorted := prependRun (!descending) x z []
                      (by simpa only [flipped] using (selectedOrder descending x z).2 xz) (by simp)
                    have newSorted := prependRun (!descending) y x [z]
                      ((chainStep (!descending) y x []).mp sorted).1 xzSorted
                    have child := previous.1 x y [z] runs newSorted saved
                    refine goodTransfer _ _ _ child ?_
                    intro weight
                    simp only [massAppend, massCons, massNil]
                    omega
                  | cons a r =>
                    rw [if_neg (by simp)]
                    have child := previous.2 x y (a :: r) runs z sorted saved
                    refine goodTransfer _ _ _ child ?_
                    intro weight
                    simp only [massAppend, massCons, massNil]
                    omega
            · intro x y r runs s sorted saved
              rw [pendingStep]
              by_cases yz : select descending y z
              · rw [if_pos yz]
                have newSorted := prependRun (!descending) z y (x :: r)
                  (by simpa only [flipped] using (selectedOrder descending y z).1 yz) sorted
                have child := previous.2 y z (x :: r) runs s newSorted saved
                refine goodTransfer _ _ _ child ?_
                intro weight
                simp only [massAppend, massCons, massNil]
                omega
              · rw [if_neg yz]
                by_cases xz : select descending x z
                · rw [if_pos xz]
                  have zx := prependRun (!descending) z x r
                    (by simpa only [flipped] using (selectedOrder descending x z).1 xz)
                    (List.pairwise_cons.mp sorted).2
                  have newSorted := prependRun (!descending) y z (x :: r)
                    (by simpa only [flipped] using (selectedOrder descending y z).2 yz) zx
                  have child := previous.2 z y (x :: r) runs s newSorted saved
                  refine goodTransfer _ _ _ child ?_
                  intro weight
                  simp only [massAppend, massCons, massNil]
                  omega
                · rw [if_neg xz]
                  have savedRun := (runsCons (!descending) _ runs).mpr ⟨⟨by simp, sorted⟩, saved⟩
                  by_cases sz : select descending s z
                  · rw [if_pos sz]
                    have newSorted := prependRun (!descending) z s []
                      (by simpa only [flipped] using (selectedOrder descending s z).1 sz) (by simp)
                    have child := previous.1 s z [] ((y :: x :: r) :: runs) newSorted savedRun
                    refine goodTransfer _ _ _ child ?_
                    intro weight
                    simp only [List.flatten_cons, massAppend, massCons, massNil]
                    omega
                  · rw [if_neg sz]
                    have newSorted := prependRun (!descending) s z []
                      (by simpa only [flipped] using (selectedOrder descending s z).2 sz) (by simp)
                    have child := previous.1 z s [] ((y :: x :: r) :: runs) newSorted savedRun
                    refine goodTransfer _ _ _ child ?_
                    intro weight
                    simp only [List.flatten_cons, massAppend, massCons, massNil]
                    omega
      let initial (x : Lynx.Term) (xs r : List Lynx.Term) := Erlang.lists.«sort_1/3» x (encode xs) (encode r)
      have initialNil (x : Lynx.Term) (r : List Lynx.Term) :
          initial x [] r = .ok (encode (r.reverse ++ [x])) := by
        have returned := reverseModel r [x]
        simp only [encode, List.foldr_cons, List.foldr_nil] at returned
        simp only [initial]
        rw [Erlang.lists.«sort_1/3».eq_def]
        simpa [encode] using returned
      have initialStep (x y : Lynx.Term) (xs r : List Lynx.Term) :
          initial x (y :: xs) r = match Lynx.Term.compare x y with
            | .eq => initial y xs (x :: r)
            | .lt => start false x y xs r []
            | .gt => start true x y xs [] [r.reverse] := by
        have returned := reverseModel r []
        simp only [encode, List.foldr_nil, List.append_nil] at returned
        simp only [initial, start, Bool.false_eq_true, if_false, if_true]
        rw [Erlang.lists.«sort_1/3».eq_def]
        cases comparison : Lynx.Term.compare x y <;>
          simp [encode, pack, Erlang.erlang.«==/2», Erlang.erlang.«</2», comparison, returned]
      have initialModel (n : Nat) (xs : List Lynx.Term) (length : xs.length = n) :
          ∀ x r, r ≠ [] → (x :: r).Pairwise (fun a b => order true a b) →
            good ((x :: xs) ++ r) (initial x xs r) := by
        induction n using Nat.strongRecOn generalizing xs with
        | ind n ih =>
          cases xs with
          | nil =>
            intro x r nonempty sorted
            refine ⟨r.reverse ++ [x], initialNil x r, ?_, ?_⟩
            · simpa only [List.reverse_cons, Bool.not_true] using reversedOrder true (x :: r) sorted
            · intro weight
              simp only [massAppend, massCons, massReverse, massNil]
              omega
          | cons y xs =>
            intro x r nonempty sorted
            have smaller : xs.length < n := by simp at length; omega
            rw [initialStep]
            cases comparison : Lynx.Term.compare x y with
            | eq =>
              have prefixSorted := prependRun true y x r (by simp [order, comparison]) sorted
              have child := ih _ smaller xs rfl y (x :: r) (by simp) prefixSorted
              refine goodTransfer _ _ _ child ?_
              intro weight
              simp only [massAppend, massCons]
              omega
            | lt =>
              have prefixSorted := prependRun true y x r (by simp [order, comparison]) sorted
              have child := (splitModel false _ xs rfl).1 x y r [] prefixSorted (runsNil true)
              refine goodTransfer _ _ _ child ?_
              intro weight
              simp only [List.flatten_nil, massAppend, massCons, massNil]
              omega
            | gt =>
              have backwards : Lynx.Term.compare y x = .lt := Std.OrientedCmp.lt_of_gt comparison
              have prefixSorted := prependRun false y x [] (by simp [order, backwards]) (by simp)
              have saved := (runsCons false r.reverse []).mpr
                ⟨reversedValid true r ⟨nonempty, (List.pairwise_cons.mp sorted).2⟩, runsNil false⟩
              have child := (splitModel true _ xs rfl).1 x y [] [r.reverse] prefixSorted saved
              refine goodTransfer _ _ _ child ?_
              intro weight
              simp only [List.flatten_cons, List.flatten_nil, massAppend, massCons, massReverse, massNil]
              omega
      let small (x y z : Lynx.Term) : List Lynx.Term :=
        if select false x y then
          if select false y z then [x, y, z]
          else if select false x z then [x, z, y] else [z, x, y]
        else if select false x z then [y, x, z]
        else if select false y z then [y, z, x] else [z, y, x]
      have smallSorted (x y z : Lynx.Term) : (small x y z).Pairwise (fun a b => order false a b) := by
        by_cases xy : select false x y <;> by_cases yz : select false y z <;> by_cases xz : select false x z
        all_goals simp only [small, xy, yz, xz, Bool.false_eq_true, if_true, if_false, chainStep, List.pairwise_singleton]
        all_goals repeat' constructor
        all_goals first
          | exact (selectedOrder false x y).1 xy
          | exact (selectedOrder false x y).2 xy
          | exact (selectedOrder false y z).1 yz
          | exact (selectedOrder false y z).2 yz
          | exact (selectedOrder false x z).1 xz
          | exact (selectedOrder false x z).2 xz
      have smallMass (weight : Lynx.Term → Nat) (x y z : Lynx.Term) : mass weight (small x y z) = mass weight [x,y,z] := by
        by_cases xy : select false x y <;> by_cases yz : select false y z <;> by_cases xz : select false x z <;>
          simp only [small, xy, yz, xz, Bool.false_eq_true, if_true, if_false, massCons, massNil] <;> omega
      have sortTwo (x y : Lynx.Term) : Erlang.lists.«sort/1» (encode [x,y]) =
          .ok (encode (if select false x y then [x,y] else [y,x])) := by
        rw [Erlang.lists.«sort/1».eq_def]
        cases comparison : Lynx.Term.compare x y <;> simp [encode, select, Erlang.erlang.«=</2», comparison]
      have sortThree (x y z : Lynx.Term) : Erlang.lists.«sort/1» (encode [x,y,z]) = .ok (encode (small x y z)) := by
        rw [Erlang.lists.«sort/1».eq_def]
        cases a : Lynx.Term.compare x y <;> cases b : Lynx.Term.compare y z <;> cases c : Lynx.Term.compare x z <;>
          simp [encode, small, select, Erlang.erlang.«=</2», a, b, c]
      have sortMany (x y z w : Lynx.Term) (xs : List Lynx.Term) :
          Erlang.lists.«sort/1» (encode (x :: y :: z :: w :: xs)) =
            if select false x y then
              if Lynx.Term.compare x y = .eq then initial y (z :: w :: xs) [x]
              else start false x y (z :: w :: xs) [] []
            else start true x y (z :: w :: xs) [] [] := by
        rw [Erlang.lists.«sort/1».eq_def]
        cases comparison : Lynx.Term.compare x y <;>
          simp [encode, select, initial, start, pack, Erlang.erlang.«=</2», Erlang.erlang.«==/2», comparison]
      have sortModel (xs : List Lynx.Term) : good xs (Erlang.lists.«sort/1» (encode xs)) := by
        match xs with
        | [] =>
          refine ⟨[], ?_, by simp, fun _ => rfl⟩
          rw [Erlang.lists.«sort/1».eq_def]
          rfl
        | [x] =>
          refine ⟨[x], ?_, by simp, fun _ => rfl⟩
          rw [Erlang.lists.«sort/1».eq_def]
          rfl
        | [x,y] =>
          by_cases choice : select false x y
          · refine ⟨[x,y], by simpa [choice] using sortTwo x y, ?_, fun _ => rfl⟩
            exact prependRun false x y [] ((selectedOrder false x y).1 choice) (by simp)
          · refine ⟨[y,x], by simpa [choice] using sortTwo x y, ?_, ?_⟩
            · exact prependRun false y x [] ((selectedOrder false x y).2 choice) (by simp)
            · intro weight
              simp only [massCons, massNil]
              omega
        | [x,y,z] => exact ⟨small x y z, sortThree x y z, smallSorted x y z, fun weight => smallMass weight x y z⟩
        | x :: y :: z :: w :: xs =>
          rw [sortMany]
          by_cases choice : select false x y
          · rw [if_pos choice]
            by_cases same : Lynx.Term.compare x y = .eq
            · rw [if_pos same]
              have prefixSorted := prependRun true y x [] (by simp [order, same]) (by simp)
              have child := initialModel _ (z :: w :: xs) rfl y [x] (by simp) prefixSorted
              refine goodTransfer _ _ _ child ?_
              intro weight
              simp only [massAppend, massCons, massNil]
              omega
            · rw [if_neg same]
              have prefixSorted := prependRun true y x [] (by exact choice) (by simp)
              have child := (splitModel false _ (z :: w :: xs) rfl).1 x y [] [] prefixSorted (runsNil true)
              refine goodTransfer _ _ _ child ?_
              intro weight
              simp only [List.flatten_nil, massAppend, massCons, massNil]
              omega
          · rw [if_neg choice]
            have prefixSorted := prependRun false y x [] ((selectedOrder false x y).2 choice) (by simp)
            have child := (splitModel true _ (z :: w :: xs) rfl).1 x y [] [] prefixSorted (runsNil false)
            refine goodTransfer _ _ _ child ?_
            intro weight
            simp only [List.flatten_nil, massAppend, massCons, massNil]
            omega
      have ascendingAny (run : List Lynx.Term) (nonempty : run ≠ []) :
          schedule false [run] [] = .ok (encode run) := by
        cases run with
        | nil => simp at nonempty
        | cons x xs => exact ascendingLeaf x xs
      have descendingAny (run : List Lynx.Term) (nonempty : run ≠ []) :
          schedule true [run] [] = .ok (encode run.reverse) := by
        rw [descendingOne]
        exact ascendingAny run.reverse (by simpa using nonempty)
      have startSorted (xs : List Lynx.Term) (x y : Lynx.Term) (r : List Lynx.Term)
          (sorted : (y :: xs).Pairwise (fun a b => order false a b)) :
          start false x y xs r [] = .ok (encode (r.reverse ++ [x,y] ++ xs)) := by
        induction xs generalizing x y r with
        | nil =>
          rw [startNil]
          simp only [Bool.false_eq_true, if_false]
          simpa only [List.reverse_cons, List.reverse_singleton, List.singleton_append,
            List.append_nil, List.append_assoc] using descendingAny (y :: x :: r) (by simp)
        | cons z xs ih =>
          have ordered : select false y z := (List.pairwise_cons.mp sorted).1 z (by simp)
          rw [startStep, if_pos ordered]
          simpa only [List.reverse_cons, List.reverse_singleton, List.append_assoc,
            List.singleton_append, List.cons_append, List.nil_append] using
            ih y z (x :: r) (List.pairwise_cons.mp sorted).2
      have initialSorted (xs : List Lynx.Term) (x : Lynx.Term) (r : List Lynx.Term)
          (sorted : (x :: xs).Pairwise (fun a b => order false a b)) :
          initial x xs r = .ok (encode (r.reverse ++ x :: xs)) := by
        induction xs generalizing x r with
        | nil => exact initialNil x r
        | cons y xs ih =>
          rw [initialStep]
          cases comparison : Lynx.Term.compare x y with
          | eq =>
            simpa only [List.reverse_cons, List.reverse_singleton, List.singleton_append, List.append_assoc] using
              ih y (x :: r) (List.pairwise_cons.mp sorted).2
          | lt => simpa only [List.append_assoc, List.cons_append, List.nil_append] using
              startSorted xs x y r (List.pairwise_cons.mp sorted).2
          | gt =>
            have ordered := (List.pairwise_cons.mp sorted).1 y (by simp)
            simp [order, comparison] at ordered
      -- A sorted input follows a single run, retaining even distinct equal-order values.
      have sortSorted (xs : List Lynx.Term) (sorted : xs.Pairwise (fun a b => order false a b)) :
          Erlang.lists.«sort/1» (encode xs) = .ok (encode xs) := by
        match xs with
        | [] => rw [Erlang.lists.«sort/1».eq_def]; rfl
        | [x] => rw [Erlang.lists.«sort/1».eq_def]; rfl
        | [x,y] =>
          have ordered : select false x y := (List.pairwise_cons.mp sorted).1 y (by simp)
          simpa only [ordered, if_true] using sortTwo x y
        | [x,y,z] =>
          have xy : select false x y := (List.pairwise_cons.mp sorted).1 y (by simp)
          have yz : select false y z := (List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1 z (by simp)
          simpa only [small, xy, yz, if_true] using sortThree x y z
        | x :: y :: z :: w :: xs =>
          have ordered : select false x y := (List.pairwise_cons.mp sorted).1 y (by simp)
          rw [sortMany, if_pos ordered]
          by_cases same : Lynx.Term.compare x y = .eq
          · rw [if_pos same]
            simpa using initialSorted (z :: w :: xs) y [x] (List.pairwise_cons.mp sorted).2
          · rw [if_neg same]
            simpa using startSorted (z :: w :: xs) x y [] (List.pairwise_cons.mp sorted).2
      have properModel (input : Lynx.Term) (accepted : «proper_list/1» input = .ok Lynx.Term.true) :
          ∃ xs : List Lynx.Term, encode xs = input := by
        induction input using «proper_list/1».induct with
        | case1 => exact ⟨[], rfl⟩
        | case2 head tail ih =>
          obtain ⟨xs, rfl⟩ := ih (by simpa [«proper_list/1»] using accepted)
          exact ⟨head :: xs, rfl⟩
        | case3 input notNil notCons =>
          cases input <;> simp [«proper_list/1»] at accepted
          · exact False.elim (notNil rfl)
          · exact False.elim (notCons _ _ rfl)
      have sortedCheck (xs : List Lynx.Term) (sorted : xs.Pairwise (fun a b => order false a b)) :
          «sorted/1» (encode xs) = .ok Lynx.Term.true := by
        induction xs with
        | nil => rw [«sorted/1».eq_def]; rfl
        | cons x xs ih =>
          cases xs with
          | nil => rw [«sorted/1».eq_def]; rfl
          | cons y xs =>
            have ordered : (Lynx.Term.compare x y).isLE := (List.pairwise_cons.mp sorted).1 y (by simp)
            have returned := ih (List.pairwise_cons.mp sorted).2
            simp only [encode, List.foldr_cons] at returned
            rw [«sorted/1».eq_def]
            simp [encode, Erlang.erlang.«=</2», ordered, returned]
      have multiplicityModel (xs : List Lynx.Term) (value : Lynx.Term) :
          «multiplicity/2» (encode xs) value =
            .ok (.integer (mass (fun head => if Lynx.Term.exactCompare head value = .eq then 1 else 0) xs)) := by
        induction xs with
        | nil => rfl
        | cons head tail ih =>
          by_cases equal : Lynx.Term.exactCompare head value = .eq <;>
            simp [«multiplicity/2», encode, Erlang.erlang.«=:=/2», equal, ih,
              massCons, Int.natCast_add]
      have enumSort (xs : List Lynx.Term) :
          Elixir.Enum.«sort/1» (encode xs) = Erlang.lists.«sort/1» (encode xs) := by
        have isList : Erlang.erlang.«is_list/1» (encode xs) = .ok Lynx.Term.true := by
          cases xs <;> rfl
        simp [Elixir.Enum.«sort/1», isList]
      have accepted : «proper_list/1» list = .ok Lynx.Term.true := by
        simpa only [«sort_contract_holds:requires/2»] using requires
      obtain ⟨xs, rfl⟩ := properModel list accepted
      obtain ⟨output, returned, sorted, masses⟩ := sortModel xs
      have countEqual := masses (fun head => if Lynx.Term.exactCompare head value = .eq then 1 else 0)
      simp [«sort_contract_holds:ensures/2», «sort_contract/2», «enum_sort_contract/2», enumSort, returned,
        sortedCheck output sorted, multiplicityModel, countEqual, sortSorted output sorted,
        Erlang.erlang.«=:=/2»]
      """
  end

  laws "sequence length and elements" do
    termination_suffix &:lists.seq_loop/4, ~LEAN"""
    partial_fixpoint
    """

    law sequence_formula(first, last, step, index),
      requires:
        is_integer(first) and is_integer(last) and is_integer(step) and
          is_integer(index) and index >= 0 and
          ((step > 0 and first - step <= last) or
             (step < 0 and first - step >= last) or (step == 0 and first == last)),
      expects: sequence_contract(first, last, step, index),
      proof: ~LEAN"""
      let encode (xs : List Int) : Lynx.Term :=
        xs.foldr (fun x tail => .cons (.integer x) tail) .nil
      let series (n : Nat) (a d : Int) := (List.range n).map (fun (i : Nat) => a + (i : Int) * d)
      have seriesZero (a d : Int) : series 0 a d = [] := rfl
      have seriesStep (n : Nat) (a d : Int) :
          series (n+1) a d = series n a d ++ [a + (n : Int) * d] := by
        simp [series, List.range_succ, List.map_append]
      have worker (n : Nat) (a d : Int) (tail : List Int) :
          Erlang.lists.«seq_loop/4» (.integer n) (.integer (a + ((n : Int)-1)*d))
            (.integer d) (encode tail) = .ok (encode (series n a d ++ tail)) := by
        induction n using Nat.strongRecOn generalizing tail with
        | ind n ih =>
          rw [Erlang.lists.«seq_loop/4».eq_def]
          by_cases four : 4 ≤ n
          · have returned :=  ih (n-4) (by omega)
                ([a + ((n : Int)-4)*d, a + ((n : Int)-3)*d,
                  a + ((n : Int)-2)*d, a + ((n : Int)-1)*d] ++ tail)
            have nEq : n = (n-4)+1+1+1+1 := by omega
            have arith (k : Int) : a + k*d-d = a + (k-1)*d := by simp only [Int.sub_mul, Int.one_mul]; omega
            simp only [Erlang.erlang.«>=/2_integers», Erlang.erlang.«-/2_integers»,
              show (4 : Int) ≤ n by omega, if_true, Lynx.Except.tryWith_ok,
              Lynx.Except.ok_bind]
            simp only [arith]
            have expanded : series n a d = series (n-4) a d ++
                [a + ((n : Int)-4)*d, a + ((n : Int)-3)*d,
                 a + ((n : Int)-2)*d, a + ((n : Int)-1)*d] := by
              conv => lhs; rw [nEq]
              simp only [seriesStep, Int.natCast_add, Int.natCast_sub four,
                Int.cast_ofNat_Int, List.append_assoc,
                List.singleton_append, List.cons_append, List.nil_append]
              congr 10 <;> omega
            simpa [encode, expanded, Int.natCast_sub four, Int.sub_sub,
              List.append_assoc] using returned
          · by_cases two : 2 ≤ n
            · have returned :=  ih (n-2) (by omega)
                  ([a + ((n : Int)-2)*d, a + ((n : Int)-1)*d] ++ tail)
              have nEq : n = (n-2)+1+1 := by omega
              have arith (k : Int) : a + k*d-d = a + (k-1)*d := by simp only [Int.sub_mul, Int.one_mul]; omega
              simp only [Erlang.erlang.«>=/2_integers», Erlang.erlang.«-/2_integers»,
                show ¬ (4 : Int) ≤ n by omega, show (2 : Int) ≤ n by omega,
                if_true, if_false, Lynx.Except.tryWith_ok,
                Lynx.Except.ok_bind]
              simp only [arith]
              have expanded : series n a d = series (n-2) a d ++
                  [a + ((n : Int)-2)*d, a + ((n : Int)-1)*d] := by
                conv => lhs; rw [nEq]
                simp only [seriesStep, Int.natCast_add, Int.natCast_sub two,
                  Int.cast_ofNat_Int, List.append_assoc,
                  List.singleton_append, List.cons_append, List.nil_append]
                congr 10 <;> omega
              simpa [encode, expanded, Int.natCast_sub two, Int.sub_sub,
                List.append_assoc] using returned
            · have small : n = 0 ∨ n = 1 := by omega
              rcases small with rfl | rfl <;>
                simp [Erlang.erlang.«>=/2_integers», series, encode]
      have lengthModel (xs : List Int) :
          Erlang.erlang.«length/1» (encode xs) = .ok (.integer xs.length) := by
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [encode, Erlang.erlang.«length/1», ih, Int.natCast_add]
      have nthWorker (xs : List Int) (i : Nat) (bound : i < xs.length) :
          Erlang.lists.«nth_1/2» (.integer (i+1)) (encode xs) = .ok (.integer xs[i]) := by
        induction i generalizing xs with
        | zero =>
          cases xs with
          | nil => simp at bound
          | cons x xs => rfl
        | succ i ih =>
          cases xs with
          | nil => simp at bound
          | cons x xs =>
            have returned := ih xs (by simpa using bound)
            rw [Erlang.lists.«nth_1/2».eq_def]
            simp only [encode, List.foldr_cons]
            split <;> simp_all [Erlang.erlang.«-/2_integers», encode,
              show (↑(i+1)+1 : Int)-1 = ↑i+1 by omega]
            omega
      have nthModel (xs : List Int) (i : Nat) (bound : i < xs.length) :
          Erlang.lists.«nth/2» (.integer (i+1)) (encode xs) = .ok (.integer xs[i]) := by
        cases xs with
        | nil => simp at bound
        | cons x xs =>
          cases i with
          | zero => rfl
          | succ i =>
            have returned := nthWorker (x :: xs) (i+1) bound
            rw [Erlang.lists.«nth/2».eq_def]
            simp only [encode, List.foldr_cons]
            split <;> simp_all [encode, Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt, Erlang.erlang.«and/2»,
              show (1 : Int) < ↑i+1+1 by omega]
            omega
      cases first <;> simp [«sequence_formula:requires/4», Erlang.erlang.«is_integer/1»] at requires
      rename_i a
      cases last <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i b
      cases step <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i d
      cases index <;> simp [Erlang.erlang.«is_integer/1»] at requires
      rename_i i
      have nonnegative : 0 ≤ i := by
        by_cases h : 0 ≤ i <;> simp [h] at requires <;> omega
      have domain : (0 < d ∧ a-d ≤ b) ∨ (d < 0 ∧ b ≤ a-d) ∨ (d = 0 ∧ a = b) := by
        by_cases pos : 0 < d
        · by_cases lo : a-d ≤ b
          · exact .inl ⟨pos, lo⟩
          · simp [pos, lo, show ¬ d < 0 by omega, show d ≠ 0 by omega,
              nonnegative, Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
              Int.compare_eq_gt, Erlang.erlang.«==/2»] at requires
        · by_cases neg : d < 0
          · by_cases hi : b ≤ a-d
            · exact .inr (.inl ⟨neg, hi⟩)
            · simp [pos, neg, hi, show d ≠ 0 by omega,
                nonnegative, Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
                Int.compare_eq_gt, Erlang.erlang.«==/2»] at requires
          · have zero : d = 0 := by omega
            have same : a = b := by
              by_cases same : a = b
              · exact same
              · simp [pos, neg, zero, same, nonnegative, Erlang.erlang.«>/2»,
                  Ordering.isGT_iff_eq_gt, Int.compare_eq_gt,
                  Erlang.erlang.«==/2»] at requires
            exact .inr (.inr ⟨zero, same⟩)
      let count : Int := if d = 0 then 1 else (b-a+d).tdiv d
      have result : ∃ n : Nat, (n : Int) = count ∧
          Erlang.lists.«seq/3» (.integer a) (.integer b) (.integer d) =
            .ok (encode (series n a d)) := by
        by_cases zero : d = 0
        · have same : a = b := by omega
          subst d
          subst b
          refine ⟨1, rfl, ?_⟩
          simp [Erlang.lists.«seq/3», Erlang.erlang.«>/2»,
            Erlang.erlang.«and/2», Erlang.erlang.«is_integer/1»,
            Erlang.erlang.«=:=/2», series, encode]
        · have nonneg : 0 ≤ (b-a+d).tdiv d := by
            rcases domain with pos | neg | bad
            · exact Int.tdiv_nonneg (by omega) (by omega)
            · exact Int.tdiv_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
            · omega
          let n := ((b-a+d).tdiv d).toNat
          have cast : (n : Int) = (b-a+d).tdiv d := Int.toNat_of_nonneg nonneg
          refine ⟨n, by simp [count, zero, cast], ?_⟩
          have returned := worker n a d []
          simp only [List.append_nil, show encode [] = .nil from rfl, cast] at returned
          rw [Int.mul_comm ((b-a+d).tdiv d - 1) d]
            at returned
          rcases domain with pos | neg | bad
          · simp [Erlang.lists.«seq/3», Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt,
              Erlang.erlang.«and/2», Erlang.erlang.«is_integer/1»,
              Erlang.erlang.«=:=/2», Erlang.erlang.«div/2», zero, pos.1, pos.2,
              show d * ((b-a+d).tdiv d-1) + a =
                a + d * ((b-a+d).tdiv d-1) by omega, returned]
          · simp [Erlang.lists.«seq/3», Erlang.erlang.«>/2»,
              Ordering.isGT_iff_eq_gt, Int.compare_eq_gt,
              Erlang.erlang.«and/2», Erlang.erlang.«is_integer/1»,
              Erlang.erlang.«=:=/2», Erlang.erlang.«div/2», zero, neg.1, neg.2,
              show ¬ 0 < d by omega,
              show d * ((b-a+d).tdiv d-1) + a =
                a + d * ((b-a+d).tdiv d-1) by omega, returned]
          · omega
      obtain ⟨n, size, returned⟩ := result
      have len : (series n a d).length = n := by simp [series]
      have counted : (if d = 0 then (1 : Int) else (b-a+d).tdiv d) = n := by
        simpa only [count] using size.symm
      simp only [«sequence_formula:ensures/4», «sequence_contract/4», returned,
        Lynx.Except.ok_bind]
      by_cases zero : d = 0
      · have one : n = 1 := by simp only [zero, if_true] at counted; omega
        subst n
        subst d
        clear counted size count worker seriesStep nthWorker nthModel lengthModel len
        have either : i = 0 ∨ 1 ≤ i := by omega
        rcases either with rfl | outside <;>
          simp_all [Erlang.erlang.«==/2», Erlang.erlang.«=:=/2»,
            series, encode, Erlang.lists.«nth/2»,
            Erlang.erlang.«length/1»]
      · simp only [zero, if_false] at counted
        by_cases outside : (n : Int) ≤ i
        · simp [lengthModel, len, Erlang.erlang.«==/2», Erlang.erlang.«div/2»,
            Erlang.erlang.«=:=/2», counted, outside, zero]
        · have bound : i.toNat < (series n a d).length := by omega
          have indexed := nthModel (series n a d) i.toNat bound
          have value : (series n a d)[i.toNat] = a + i*d := by
            simp [series, Int.toNat_of_nonneg nonnegative]
          simp only [Int.toNat_of_nonneg nonnegative, value] at indexed
          simp [lengthModel, len, Erlang.erlang.«==/2», Erlang.erlang.«div/2»,
            Erlang.erlang.«=:=/2», counted, outside, indexed, zero]
      """
  end
end
