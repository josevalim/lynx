# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/otp/rand.exs
# Prove the installed OTP rand module, translated from its BEAM debug information.
# Verified against Erlang/OTP 29.1.2 (stdlib 8.1.1, ERTS 17.1.1).
# The proofs depend on shuffle_s/2's implementation; rerun them after OTP upgrades.
ExUnit.start()

defmodule RandProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  defp multiplicity([], _value), do: 0

  defp multiplicity([head | tail], value),
    do: if(head === value, do: 1, else: 0) + multiplicity(tail, value)

  # Seeding selects a handler whose `next` is one of rand's own generators.
  def shuffle_returns(list, alg, seed),
    do: match?({_, _}, :rand.shuffle_s(list, :rand.seed_s(alg, seed)))

  defp at_most_one([]), do: true
  defp at_most_one([_]), do: true
  defp at_most_one(_), do: false

  def shuffle_unchanged(list, alg, seed) do
    state = :rand.seed_s(alg, seed)
    :rand.shuffle_s(list, state) === {list, state}
  end

  def shuffle_contract(list, alg, seed, value) do
    {handler, _} = state = :rand.seed_s(alg, seed)
    {shuffled, {kept, _}} = :rand.shuffle_s(list, state)
    multiplicity(shuffled, value) === multiplicity(list, value) and kept === handler
  end

  # rand:shuffle_s/2 returns once its generator has produced bits that order
  # every element. Whether it does depends on the bits: it never returns for a
  # generator whose bits are constant, such as the all-zero exsss state that
  # rand:seed_s/1 accepts. These laws therefore hold whenever it returns, for
  # every algorithm and seed rand:seed_s/2 accepts, whatever bits the generator
  # produces. They do not state that the permutation is uniform.
  laws "shuffle" do
    # The shuffle retries until its generator yields bits that split the list, which
    # depends on the bits. These loops are fixed points.
    termination_suffix &:rand.shuffle_r/4, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.shuffle_r/8, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.shuffle_r_2/5, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.shuffle_r_3/6, ~LEAN"partial_fixpoint"

    # Seeding translates the handlers of every algorithm. Their loops retrying for
    # usable values, and their jump functions, are fixed points too.
    termination_suffix &:rand.uniform_range/7, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.uniform_range/4, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exsss_uniform/2, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exsp_uniform/2, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exrop_uniform/2, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exro928ss_uniform/2, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exro928ss_next/1, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exs1024_next/1, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exs1024_gen1024/3, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exs1024_jump/6, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exsplus_jump/4, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.exrop_jump/5, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.polyjump/4, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.polyjump/5, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.xorzip_sr/3, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.seed_s/2, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.seed_nz/4, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.seed58/1, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.seed58/2, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.seed64/1, ~LEAN"partial_fixpoint"
    termination_suffix &:rand.seed64/2, ~LEAN"partial_fixpoint"
    termination_suffix &:lists.duplicate/3, ~LEAN"partial_fixpoint"

    prelude ~LEAN"""
    module
    public import Lynx
    public section

    namespace ShuffleProof
    open Lynx

    /-- Prepend elements onto a term, as the shuffle prepends onto its accumulator. -/
    @[expose] def onto : List Term → Term → Term
      | [], acc => acc
      | x :: xs, acc => .cons x (onto xs acc)

    @[simp] theorem onto_nil (acc : Term) : onto [] acc = acc := rfl
    @[simp] theorem onto_cons (x : Term) (xs : List Term) (acc : Term) :
        onto (x :: xs) acc = .cons x (onto xs acc) := rfl
    @[simp] theorem onto_list (xs : List Term) : onto xs .nil = Term.list xs := by
      induction xs <;> simp_all

    theorem onto_append (xs ys : List Term) (acc : Term) :
        onto (xs ++ ys) acc = onto xs (onto ys acc) := by
      induction xs <;> simp_all

    -- Postconditions on successful returns are admissible for fixed point induction.
    theorem post4 (R : Term → Term → Term → Term → Term → Prop) :
        Lean.Order.admissible (fun f : Term → Term → Term → Term → Except Exception Term =>
          ∀ a0 a1 a2 a3 v, f a0 a1 a2 a3 = .ok v → R a0 a1 a2 a3 v) := by
      apply Lean.Order.admissible_pi_apply
        (fun a0 (g : Term → Term → Term → Except Exception Term) =>
          ∀ a1 a2 a3 v, g a1 a2 a3 = .ok v → R a0 a1 a2 a3 v)
      intro a0
      apply Lean.Order.admissible_pi_apply
        (fun a1 (g : Term → Term → Except Exception Term) =>
          ∀ a2 a3 v, g a2 a3 = .ok v → R a0 a1 a2 a3 v)
      intro a1
      apply Lean.Order.admissible_pi_apply
        (fun a2 (g : Term → Except Exception Term) =>
          ∀ a3 v, g a3 = .ok v → R a0 a1 a2 a3 v)
      intro a2
      apply Lean.Order.admissible_pi_apply
        (fun a3 (g : Except Exception Term) =>
          ∀ v, g = .ok v → R a0 a1 a2 a3 v)
      intro a3
      exact Lynx.Except.admissible_success _

    theorem post5 (R : Term → Term → Term → Term → Term → Term → Prop) :
        Lean.Order.admissible (fun f : Term → Term → Term → Term → Term → Except Exception Term =>
          ∀ a0 a1 a2 a3 a4 v, f a0 a1 a2 a3 a4 = .ok v → R a0 a1 a2 a3 a4 v) := by
      apply Lean.Order.admissible_pi_apply
        (fun a0 (g : Term → Term → Term → Term → Except Exception Term) =>
          ∀ a1 a2 a3 a4 v, g a1 a2 a3 a4 = .ok v → R a0 a1 a2 a3 a4 v)
      intro a0
      apply Lean.Order.admissible_pi_apply
        (fun a1 (g : Term → Term → Term → Except Exception Term) =>
          ∀ a2 a3 a4 v, g a2 a3 a4 = .ok v → R a0 a1 a2 a3 a4 v)
      intro a1
      apply Lean.Order.admissible_pi_apply
        (fun a2 (g : Term → Term → Except Exception Term) =>
          ∀ a3 a4 v, g a3 a4 = .ok v → R a0 a1 a2 a3 a4 v)
      intro a2
      apply Lean.Order.admissible_pi_apply
        (fun a3 (g : Term → Except Exception Term) =>
          ∀ a4 v, g a4 = .ok v → R a0 a1 a2 a3 a4 v)
      intro a3
      apply Lean.Order.admissible_pi_apply
        (fun a4 (g : Except Exception Term) =>
          ∀ v, g = .ok v → R a0 a1 a2 a3 a4 v)
      intro a4
      exact Lynx.Except.admissible_success _

    theorem post6 (R : Term → Term → Term → Term → Term → Term → Term → Prop) :
        Lean.Order.admissible (fun f : Term → Term → Term → Term → Term → Term →
            Except Exception Term =>
          ∀ a0 a1 a2 a3 a4 a5 v, f a0 a1 a2 a3 a4 a5 = .ok v → R a0 a1 a2 a3 a4 a5 v) := by
      apply Lean.Order.admissible_pi_apply
        (fun a0 (g : Term → Term → Term → Term → Term → Except Exception Term) =>
          ∀ a1 a2 a3 a4 a5 v, g a1 a2 a3 a4 a5 = .ok v → R a0 a1 a2 a3 a4 a5 v)
      intro a0
      apply Lean.Order.admissible_pi_apply
        (fun a1 (g : Term → Term → Term → Term → Except Exception Term) =>
          ∀ a2 a3 a4 a5 v, g a2 a3 a4 a5 = .ok v → R a0 a1 a2 a3 a4 a5 v)
      intro a1
      apply Lean.Order.admissible_pi_apply
        (fun a2 (g : Term → Term → Term → Except Exception Term) =>
          ∀ a3 a4 a5 v, g a3 a4 a5 = .ok v → R a0 a1 a2 a3 a4 a5 v)
      intro a2
      apply Lean.Order.admissible_pi_apply
        (fun a3 (g : Term → Term → Except Exception Term) =>
          ∀ a4 a5 v, g a4 a5 = .ok v → R a0 a1 a2 a3 a4 a5 v)
      intro a3
      apply Lean.Order.admissible_pi_apply
        (fun a4 (g : Term → Except Exception Term) =>
          ∀ a5 v, g a5 = .ok v → R a0 a1 a2 a3 a4 a5 v)
      intro a4
      apply Lean.Order.admissible_pi_apply
        (fun a5 (g : Except Exception Term) =>
          ∀ v, g = .ok v → R a0 a1 a2 a3 a4 a5 v)
      intro a5
      exact Lynx.Except.admissible_success _

    -- Instances for functions of eight arguments nest deeply.
    set_option synthInstance.maxSize 2048 in
    theorem post8 (R : Term → Term → Term → Term → Term → Term → Term → Term → Term → Prop) :
        Lean.Order.admissible (fun f : Term → Term → Term → Term → Term → Term → Term → Term →
            Except Exception Term =>
          ∀ a0 a1 a2 a3 a4 a5 a6 a7 v, f a0 a1 a2 a3 a4 a5 a6 a7 = .ok v →
            R a0 a1 a2 a3 a4 a5 a6 a7 v) := by
      apply Lean.Order.admissible_pi_apply
        (fun a0 (g : Term → Term → Term → Term → Term → Term → Term → Except Exception Term) =>
          ∀ a1 a2 a3 a4 a5 a6 a7 v, g a1 a2 a3 a4 a5 a6 a7 = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a0
      apply Lean.Order.admissible_pi_apply
        (fun a1 (g : Term → Term → Term → Term → Term → Term → Except Exception Term) =>
          ∀ a2 a3 a4 a5 a6 a7 v, g a2 a3 a4 a5 a6 a7 = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a1
      apply Lean.Order.admissible_pi_apply
        (fun a2 (g : Term → Term → Term → Term → Term → Except Exception Term) =>
          ∀ a3 a4 a5 a6 a7 v, g a3 a4 a5 a6 a7 = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a2
      apply Lean.Order.admissible_pi_apply
        (fun a3 (g : Term → Term → Term → Term → Except Exception Term) =>
          ∀ a4 a5 a6 a7 v, g a4 a5 a6 a7 = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a3
      apply Lean.Order.admissible_pi_apply
        (fun a4 (g : Term → Term → Term → Except Exception Term) =>
          ∀ a5 a6 a7 v, g a5 a6 a7 = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a4
      apply Lean.Order.admissible_pi_apply
        (fun a5 (g : Term → Term → Except Exception Term) =>
          ∀ a6 a7 v, g a6 a7 = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a5
      apply Lean.Order.admissible_pi_apply
        (fun a6 (g : Term → Except Exception Term) =>
          ∀ a7 v, g a7 = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a6
      apply Lean.Order.admissible_pi_apply
        (fun a7 (g : Except Exception Term) =>
          ∀ v, g = .ok v → R a0 a1 a2 a3 a4 a5 a6 a7 v)
      intro a7
      exact Lynx.Except.admissible_success _

    /-- Split a successful return into the paths that produce it, discarding those
    that raise. The values bound along the way are split the same way. -/
    syntax "peel " ident : tactic
    macro_rules
      | `(tactic| peel $h:ident) => `(tactic| repeat' (first
        | contradiction
        | (subst $h:ident)
        | (simp only [Lynx.Except.tryWith, Lynx.Except.bind_eq_ok, Lynx.Except.pure_eq_ok,
            Except.ok.injEq] at $h:ident)
        | (obtain ⟨_, bound, $h:ident⟩ := $h:ident; peel bound)
        | (split at $h:ident)))

    /-- The shuffle of three elements returns one of their orders. -/
    theorem perm3 (x y z : Term) :
        [z, y, x].Perm [x, y, z] ∧ [y, z, x].Perm [x, y, z] ∧ [z, x, y].Perm [x, y, z] ∧
          [x, z, y].Perm [x, y, z] ∧ [y, x, z].Perm [x, y, z] := by
      have yzx : [y, z, x].Perm [x, y, z] :=
        ((List.Perm.swap x z []).cons y).trans (List.Perm.swap x y [z])
      have xzy : [x, z, y].Perm [x, y, z] := (List.Perm.swap y z []).cons x
      exact ⟨(List.Perm.swap y z [x]).trans yzx, yzx, (List.Perm.swap x z [y]).trans xzy, xzy,
        List.Perm.swap x y [z]⟩

    theorem nil_eq_list {l : List Term} (same : Term.nil = Term.list l) : l = [] := by
      cases l <;> simp_all

    theorem cons_eq_list {x tail : Term} {l : List Term} (same : Term.cons x tail = Term.list l) :
        ∃ rest, l = x :: rest ∧ tail = Term.list rest := by
      cases l <;> simp_all

    /-- An element moved from a bucket to the front keeps the permutation. -/
    theorem move (xs before after : List Term) (x : Term) :
        (xs ++ before ++ x :: after).Perm (x :: xs ++ before ++ after) := by
      simpa only [List.append_assoc, List.cons_append] using
        (List.perm_middle (a := x) (l₁ := xs ++ before) (l₂ := after))

    /-- Shuffling the buckets in turn prepends a permutation of all of them. -/
    theorem buckets {y0 y1 y2 y3 a b c k : List Term} (p0 : y0.Perm a) (p1 : y1.Perm b)
        (p2 : y2.Perm c) (p3 : y3.Perm k) :
        (y3 ++ (y2 ++ (y1 ++ y0))).Perm ([] ++ a ++ b ++ c ++ k) := by
      have reversed : (y3 ++ (y2 ++ (y1 ++ y0))).Perm (y0 ++ y1 ++ y2 ++ y3) :=
        List.perm_append_comm.trans (List.Perm.append (List.perm_append_comm.trans
          (List.Perm.append List.perm_append_comm (List.Perm.refl y2))) (List.Perm.refl y3))
      simpa only [List.nil_append] using
        reversed.trans (((p0.append p1).append p2).append p3)

    end ShuffleProof
    """

    law shuffle_permutes(list, alg, seed, value),
      requires: shuffle_returns(list, alg, seed),
      expects: shuffle_contract(list, alg, seed, value),
      proof: ~LEAN"""
      open ShuffleProof in
      have two : ∀ (d : Lynx.Dispatcher) X acc P S Y r,
          Erlang.rand.«shuffle_r_2/5» d X acc P S Y = .ok r →
          ∃ ys P' S', r = .tuple #[onto ys acc, P', S'] ∧ ys.Perm [X, Y] := by
        intro d
        apply Erlang.rand.«shuffle_r_2/5».fixpoint_induct d
          (motive := fun f => ∀ X acc P S Y r, f X acc P S Y = .ok r →
            ∃ ys P' S', r = .tuple #[onto ys acc, P', S'] ∧ ys.Perm [X, Y])
        · exact post5 _
        · intro f ih X acc P S Y r h
          simp only [Lynx.Except.guard_eq] at h
          peel h
          all_goals first
            | exact ih _ _ _ _ _ _ h
            | exact ⟨[Y, X], _, _, rfl, List.Perm.swap _ _ _⟩
            | exact ⟨[X, Y], _, _, rfl, List.Perm.refl _⟩
      have three : ∀ (d : Lynx.Dispatcher) X acc P S Y Z r,
          Erlang.rand.«shuffle_r_3/6» d X acc P S Y Z = .ok r →
          ∃ ys P' S', r = .tuple #[onto ys acc, P', S'] ∧ ys.Perm [X, Y, Z] := by
        intro d
        apply Erlang.rand.«shuffle_r_3/6».fixpoint_induct d
          (motive := fun f => ∀ X acc P S Y Z r, f X acc P S Y Z = .ok r →
            ∃ ys P' S', r = .tuple #[onto ys acc, P', S'] ∧ ys.Perm [X, Y, Z])
        · exact post6 _
        · intro f ih X acc P S Y Z r h
          simp only [Lynx.Except.guard_eq] at h
          peel h
          all_goals first
            | exact ih _ _ _ _ _ _ _ h
            | exact ⟨[Z, Y, X], _, _, rfl, (perm3 X Y Z).1⟩
            | exact ⟨[Y, Z, X], _, _, rfl, (perm3 X Y Z).2.1⟩
            | exact ⟨[Z, X, Y], _, _, rfl, (perm3 X Y Z).2.2.1⟩
            | exact ⟨[X, Z, Y], _, _, rfl, (perm3 X Y Z).2.2.2.1⟩
            | exact ⟨[Y, X, Z], _, _, rfl, (perm3 X Y Z).2.2.2.2⟩
            | exact ⟨[X, Y, Z], _, _, rfl, List.Perm.refl _⟩
      have split : ∀ (d : Lynx.Dispatcher) L acc P S r,
          Erlang.rand.«shuffle_r/4» d L acc P S = .ok r →
          ∃ xs ys P' S', L = Lynx.Term.list xs ∧ ys.Perm xs ∧
            r = .tuple #[onto ys acc, P', S'] := by
        intro d
        apply Erlang.rand.«shuffle_r/4».fixpoint_induct d
          (motive_1 := fun f => ∀ L acc P S r, f L acc P S = .ok r →
            ∃ xs ys P' S', L = Lynx.Term.list xs ∧ ys.Perm xs ∧ r = .tuple #[onto ys acc, P', S'])
          (motive_2 := fun g => ∀ L acc P S z o t e r, g L acc P S z o t e = .ok r →
            ∃ xs a b c k ys P' S', L = Lynx.Term.list xs ∧ z = Lynx.Term.list a ∧
              o = Lynx.Term.list b ∧ t = Lynx.Term.list c ∧ e = Lynx.Term.list k ∧
              ys.Perm (xs ++ a ++ b ++ c ++ k) ∧ r = .tuple #[onto ys acc, P', S'])
        · exact post4 _
        · exact post8 _
        · intro g ihg L acc P S r h
          peel h
          all_goals first
            | exact ⟨[], [], _, _, rfl, .refl _, rfl⟩
            | exact ⟨[_], [_], _, _, rfl, .refl _, rfl⟩
            | (obtain ⟨ys, P', S', rfl, perm⟩ := two d _ _ _ _ _ _ h
               exact ⟨[_, _], ys, P', S', rfl, perm, rfl⟩)
            | (obtain ⟨ys, P', S', rfl, perm⟩ := three d _ _ _ _ _ _ _ h
               exact ⟨[_, _, _], ys, P', S', rfl, perm, rfl⟩)
            | (obtain ⟨xs, a, b, c, k, ys, P', S', hL, ha, hb, hc, hk, perm, rfl⟩ :=
                 ihg _ _ _ _ _ _ _ _ _ h
               rw [nil_eq_list ha, nil_eq_list hb, nil_eq_list hc, nil_eq_list hk] at perm
               exact ⟨xs, ys, P', S', hL, by simpa using perm, rfl⟩)
        · intro f g ihf ihg L acc P S z o t e r h
          simp only [Lynx.Except.guard_eq] at h
          peel h
          all_goals first
            | exact ihg _ _ _ _ _ _ _ _ _ h
            | (rename_i _ a1 p1 s1 h1 _ a2 p2 s2 h2 _ a3 p3 s3 h3
               obtain ⟨za, y0, q0, w0, hz, perm0, e0⟩ := ihf _ _ _ _ _ h1
               obtain ⟨ob, y1, q1, w1, ho, perm1, e1⟩ := ihf _ _ _ _ _ h2
               obtain ⟨tc, y2, q2, w2, ht, perm2, e2⟩ := ihf _ _ _ _ _ h3
               obtain ⟨ek, y3, q3, w3, he, perm3, rfl⟩ := ihf _ _ _ _ _ h
               simp only [Lynx.Term.tuple.injEq, Array.mk.injEq, List.cons.injEq,
                 and_true] at e0 e1 e2
               obtain ⟨rfl, rfl, rfl⟩ := e0
               obtain ⟨rfl, rfl, rfl⟩ := e1
               obtain ⟨rfl, rfl, rfl⟩ := e2
               exact ⟨[], za, ob, tc, ek, y3 ++ (y2 ++ (y1 ++ y0)), q3, w3, rfl, hz, ho, ht, he,
                 buckets perm0 perm1 perm2 perm3, by simp [onto_append]⟩)
            | (obtain ⟨xs, a, b, c, k, ys, P', S', hL, ha, hb, hc, hk, perm, rfl⟩ :=
                 ihg _ _ _ _ _ _ _ _ _ h
               first
                 | (obtain ⟨b', rfl, hb'⟩ := cons_eq_list hb
                    exact ⟨_ :: xs, a, b', c, k, ys, P', S', by rw [hL], ha, hb', hc, hk,
                      perm.trans (by simpa only [List.append_assoc, List.cons_append,
                        List.nil_append] using move xs a (b' ++ c ++ k) _), rfl⟩)
                 | (obtain ⟨c', rfl, hc'⟩ := cons_eq_list hc
                    exact ⟨_ :: xs, a, b, c', k, ys, P', S', by rw [hL], ha, hb, hc', hk,
                      perm.trans (by simpa only [List.append_assoc, List.cons_append,
                        List.nil_append] using move xs (a ++ b) (c' ++ k) _), rfl⟩)
                 | (obtain ⟨k', rfl, hk'⟩ := cons_eq_list hk
                    exact ⟨_ :: xs, a, b, c, k', ys, P', S', by rw [hL], ha, hb, hc, hk',
                      perm.trans (by simpa only [List.append_assoc, List.cons_append,
                        List.nil_append] using move xs (a ++ b ++ c) k' _), rfl⟩)
                 | (obtain ⟨a', rfl, ha'⟩ := cons_eq_list ha
                    exact ⟨_ :: xs, a', b, c, k, ys, P', S', by rw [hL], ha', hb, hc, hk,
                      perm.trans (by simpa only [List.append_assoc, List.cons_append,
                        List.nil_append] using move xs [] (a' ++ b ++ c ++ k) _), rfl⟩))
      have shuffles : ∀ (d : Lynx.Dispatcher) L state r,
          Erlang.rand.«shuffle_s/2» d L state = .ok r →
          ∃ xs ys handler R0 R1, L = Lynx.Term.list xs ∧ ys.Perm xs ∧
            state = .tuple #[handler, R0] ∧
            r = .tuple #[Lynx.Term.list ys, .tuple #[handler, R1]] := by
        intro d L state r h
        unfold Erlang.rand.«shuffle_s/2» at h
        simp only [Lynx.Except.guard_eq] at h
        peel h
        rename_i returned
        obtain ⟨xs, ys, P', S', rfl, perm, same⟩ := split d _ _ _ _ _ returned
        simp only [Lynx.Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at same
        obtain ⟨rfl, -, -⟩ := same
        exact ⟨xs, ys, _, _, _, rfl, perm, rfl, by rw [onto_list]⟩
      -- The multiplicity of a value counts the elements exactly equal to it.
      have counts : ∀ (xs : List Lynx.Term) (v : Lynx.Term),
          «multiplicity/2» (Lynx.Term.list xs) v =
            .ok (.integer (xs.filter (fun x => Lynx.Term.exactCompare x v == .eq)).length) := by
        intro xs v
        induction xs with
        | nil => simp [«multiplicity/2»]
        | cons x xs ih =>
          unfold «multiplicity/2»
          by_cases same : Lynx.Term.exactCompare x v = .eq <;>
            simp [Erlang.erlang.«=:=/2», same, ih, List.filter_cons] <;> omega
      simp only [Lynx.apply_eq, «shuffle_permutes:requires/4», «shuffle_returns/3»,
        Lynx.Except.bind_eq_ok] at requires
      obtain ⟨state, seeded, r, returned, -⟩ := requires
      obtain ⟨xs, ys, handler, R0, R1, rfl, perm, rfl, rfl⟩ := shuffles _ _ _ _ returned
      simp [«shuffle_permutes:ensures/4», «shuffle_contract/4», seeded, returned, counts,
        (perm.filter _).length_eq, Erlang.erlang.«=:=/2»]
      """

    law shuffle_short_consumes_nothing(list, alg, seed),
      requires: shuffle_returns(list, alg, seed) and at_most_one(list),
      expects: shuffle_unchanged(list, alg, seed),
      proof: ~LEAN"""
      open ShuffleProof in
      have init : ∀ R alg v, Erlang.rand.«shuffle_init_bitstream/2» R alg = .ok v →
          ∃ P W, v = .cons P (.cons R W) := by
        intro R alg v h
        unfold Erlang.rand.«shuffle_init_bitstream/2» at h
        peel h
        all_goals
          unfold Erlang.rand.«shuffle_init_bitstream/4» at h
          peel h
          exact ⟨_, _, rfl⟩
      simp only [Lynx.apply_eq, «shuffle_short_consumes_nothing:requires/3», «shuffle_returns/3»,
        Lynx.Except.bind_eq_ok] at requires
      obtain ⟨tested, ⟨state, seeded, r, returned, paired⟩, short⟩ := requires
      have result := returned
      unfold Erlang.rand.«shuffle_s/2» at result
      simp only [Lynx.Except.guard_eq] at result
      peel result
      rename_i initialized _ _ _ _ _ shuffled
      obtain ⟨P, W, bits⟩ := init _ _ _ initialized
      simp only [Lynx.Term.cons.injEq] at bits
      obtain ⟨rfl, rfl⟩ := bits
      simp only [Lynx.Except.pure_eq_ok, Except.ok.injEq] at paired
      subst paired
      simp only [Lynx.Term.true] at short
      rcases list with _ | _ | _ | _ | _ | _ | _ | _ | _ |
          ⟨head, _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _⟩ | _⟩ | _ <;>
        simp [«at_most_one/1»] at short
      all_goals
        rw [Erlang.rand.«shuffle_r/4».eq_def] at shuffled
        simp only [Lynx.Except.pure_eq_ok, Except.ok.injEq, Lynx.Term.tuple.injEq, Array.mk.injEq,
          List.cons.injEq, Lynx.Term.cons.injEq, and_true] at shuffled
        obtain ⟨rfl, rfl, rfl, rfl⟩ := shuffled
        simp [«shuffle_short_consumes_nothing:ensures/3», «shuffle_unchanged/3», seeded, returned,
          Erlang.erlang.«=:=/2»]
      """
  end
end
