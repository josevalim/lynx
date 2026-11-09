# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/stt/descr.exs
# Prove the set operations of Elixir's type system. The empty type law covers every type,
# and the negation laws cover bitmaps, atoms, functions, lists, tuples, and maps, both for
# the plain operations and for the optimized ones the type checker uses: a type does not
# meet its negation, and a type united with its negation is the top type. De Morgan's law
# holds for the plain operations: the negation of a union is the intersection of negations.
# Checked against Elixir 1.21.0-dev (9f3dcabcb), Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/module/types/descr.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule STTDescrProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  @moduletag timeout: :infinity
  alias Module.Types.Descr

  # Static types of bitmaps and atoms in normal form: bitmaps are non-empty,
  # and so are unions of atoms.
  def valid?(descr) when is_map(descr), do: valid_fields?(:maps.to_list(descr))
  def valid?(_descr), do: false

  defp valid_fields?([{:bitmap, bits} | fields]),
    do: is_integer(bits) and bits >= 1 and bits <= 255 and valid_fields?(fields)

  defp valid_fields?([{:atom, {:union, set}} | fields]),
    do: atoms?(set) and map_size(set) > 0 and valid_fields?(fields)

  defp valid_fields?([{:atom, {:negation, set}} | fields]),
    do: atoms?(set) and valid_fields?(fields)

  defp valid_fields?([]), do: true
  defp valid_fields?(_fields), do: false

  # Version 2 sets are maps from their elements to [].
  defp atoms?(set) when is_map(set), do: atom_keys?(:maps.to_list(set))
  defp atoms?(_set), do: false

  defp atom_keys?([{atom, []} | rest]), do: is_atom(atom) and atom_keys?(rest)
  defp atom_keys?([]), do: true
  defp atom_keys?(_rest), do: false

  # Types of bitmaps, atoms, functions, lists, tuples, and maps. Function types are
  # unions or negations of maps from arities to BDDs, whose literals are not inspected.
  def negatable?(descr) when is_map(descr), do: negatable_fields?(:maps.to_list(descr))
  def negatable?(_descr), do: false

  defp negatable_fields?([field | fields]), do: negatable_field?(field) and negatable_fields?(fields)
  defp negatable_fields?([]), do: true

  defp negatable_field?({:fun, {tag, arities}}) when tag in [:union, :negation],
    do: is_map(arities) and arity_bdds?(:maps.to_list(arities))

  defp negatable_field?({:list, bdd}), do: list_bdd?(bdd)
  defp negatable_field?({:tuple, bdd}), do: tuple_bdd?(bdd)
  defp negatable_field?({:map, bdd}), do: map_bdd?(bdd)
  defp negatable_field?(field), do: valid_fields?([field])

  defp arity_bdds?([{_arity, bdd} | arities]), do: any_bdd?(bdd, :bottom) and arity_bdds?(arities)
  defp arity_bdds?([]), do: true

  # BDDs ordered by Erlang's term order, whose literals may hold anything.
  defp any_bdd?(:bdd_top, _lower), do: true
  defp any_bdd?(:bdd_bot, _lower), do: true
  defp any_bdd?({key, _, _} = leaf, lower), do: is_integer(key) and leaf > lower

  defp any_bdd?({hash, {key, _, _} = lit, c, u, d}, lower),
    do:
      is_integer(hash) and is_integer(key) and lit > lower and any_bdd?(c, lit) and any_bdd?(u, lit) and
        any_bdd?(d, lit)

  defp any_bdd?(_bdd, _lower), do: false

  # List types are all non-empty lists, or BDDs of other list literals ordered
  # by Erlang's term order. Atoms precede the tuples of literals.
  defp list_bdd?({key, :term, :term}), do: is_integer(key)
  defp list_bdd?(bdd), do: ordered_bdd?(bdd, :bottom)

  defp ordered_bdd?(:bdd_top, _lower), do: true
  defp ordered_bdd?(:bdd_bot, _lower), do: true
  defp ordered_bdd?({_, _, _} = leaf, lower), do: list_literal?(leaf, lower)

  defp ordered_bdd?({hash, lit, c, u, d}, lower),
    do:
      is_integer(hash) and list_literal?(lit, lower) and ordered_bdd?(c, lit) and
        ordered_bdd?(u, lit) and ordered_bdd?(d, lit)

  defp ordered_bdd?(_bdd, _lower), do: false

  defp list_literal?({key, list, last} = lit, lower),
    do: is_integer(key) and lit > lower and not (list == :term and last == :term)

  defp list_literal?(_lit, _lower), do: false

  # Tuple types are all tuples, or BDDs of other tuple literals ordered by
  # Erlang's term order. Their elements are the top type or valid types of
  # bitmaps and atoms.
  defp tuple_bdd?({key, :open, []}), do: is_integer(key)
  defp tuple_bdd?(bdd), do: ordered_tuple_bdd?(bdd, :bottom)

  defp ordered_tuple_bdd?(:bdd_top, _lower), do: true
  defp ordered_tuple_bdd?(:bdd_bot, _lower), do: true
  defp ordered_tuple_bdd?({_, _, _} = leaf, lower), do: tuple_literal?(leaf, lower)

  defp ordered_tuple_bdd?({hash, lit, c, u, d}, lower),
    do:
      is_integer(hash) and tuple_literal?(lit, lower) and ordered_tuple_bdd?(c, lit) and
        ordered_tuple_bdd?(u, lit) and ordered_tuple_bdd?(d, lit)

  defp ordered_tuple_bdd?(_bdd, _lower), do: false

  defp tuple_literal?({key, tag, elements} = lit, lower) when tag in [:open, :closed],
    do: is_integer(key) and lit > lower and not (tag == :open and elements == []) and elements?(elements)

  defp tuple_literal?(_lit, _lower), do: false

  defp elements?([element | elements]), do: element?(element) and elements?(elements)
  defp elements?([]), do: true
  defp elements?(_elements), do: false

  defp element?(:term), do: true
  defp element?(element), do: valid?(element)

  # Map types are all maps, or BDDs of other map literals ordered by Erlang's
  # term order. Their literals are open or closed maps whose fields hold valid
  # types of bitmaps and atoms, or the top type.
  defp map_bdd?({key, :open, []}), do: is_integer(key)
  defp map_bdd?(bdd), do: ordered_map_bdd?(bdd, :bottom)

  defp ordered_map_bdd?(:bdd_top, _lower), do: true
  defp ordered_map_bdd?(:bdd_bot, _lower), do: true
  defp ordered_map_bdd?({_, _, _} = leaf, lower), do: map_literal?(leaf, lower)

  defp ordered_map_bdd?({hash, lit, c, u, d}, lower),
    do:
      is_integer(hash) and map_literal?(lit, lower) and ordered_map_bdd?(c, lit) and
        ordered_map_bdd?(u, lit) and ordered_map_bdd?(d, lit)

  defp ordered_map_bdd?(_bdd, _lower), do: false

  defp map_literal?({key, tag, fields} = lit, lower) when tag in [:open, :closed],
    do: is_integer(key) and lit > lower and not (tag == :open and fields == []) and map_fields?(fields)

  defp map_literal?(_lit, _lower), do: false

  defp map_fields?([{_key, {type, optional?}} | fields]),
    do: is_boolean(optional?) and field_type?(type) and map_fields?(fields)

  defp map_fields?([]), do: true
  defp map_fields?(_fields), do: false

  defp field_type?(:term), do: true
  defp field_type?(type), do: valid?(type)

  # Any type: the top type or a map of fields, whose dynamic part, if any,
  # is the top type or a map. The fields may hold anything.
  def descr?(:term), do: true
  def descr?(%{dynamic: dynamic}), do: dynamic == :term or is_map(dynamic)
  def descr?(descr), do: is_map(descr)

  laws "static" do
    # Elixir's default map field access falls back to a remote call on non-maps.
    cutoff &:elixir_erl_pass.no_parens_remote/2

    # Lines with negative tuple or map literals are not modeled, so their
    # emptiness is cut off.

    # Map literals with domain keys are not modeled.
    cutoff &Descr.map_domain_intersection/3
    cutoff &Descr.fields_merge_with_defaults/5
    # Lists are empty without lines, so their line checks are cut off.
    cutoff &Descr.list_line_empty?/4
    cutoff &Descr.non_empty_list_literals_intersection/2
    # Tuples are only padded to longer sizes, which never raises.
    cutoff &ArgumentError.exception/1

    # Descr only uses version 2 sets, which are maps.
    cutoff &:sets.get_slot/2
    cutoff &:sets.get_bucket/2
    cutoff &:sets.fold_set/3
    cutoff &:sets.filter_set/2
    cutoff &:sets.maybe_expand/1
    cutoff &:sets.maybe_contract/2
    cutoff &:sets.mk_seg/1

    # Recursive types are unfolded on demand, so descr's recursion is partial.
    termination_suffix &Descr.unfold/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_seen?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_union/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_difference/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_intersection/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_difference/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_map_difference_strategy/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:orddict.merge/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.duplicate/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_map_union_strategy/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_tuple_fuse_elements/4, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_tuple_union_leaf/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_difference_subtype?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.iterator_empty_difference_subtype?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fun_line_empty?/3, ~LEAN"partial_fixpoint", recur: true

    # Valid types hold a non-empty bitmap and atom types of version 2 sets.
    postlude ~LEAN"""
    namespace Elixir.STTDescrProofsTest
    open Lynx Lynx.Term

    /-! Valid types: every field is a non-empty bitmap or an atom type. -/

    /-- Atom types are unions (true) or negations (false) of version 2 sets of atoms. -/
    abbrev AtomField (w : Term) : Prop :=
      ∃ (pos : Bool) (S : List (Term × Term)),
        w = .tuple #[.atom (if pos then "union" else "negation"), .map S] ∧
          Erlang.sets.elements? (.map S) = some S

    /-- What `valid?/1` checks of a type. -/
    structure Valid (X : List (Term × Term)) : Prop where
      keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom"
      bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
      atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
      atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []

    /-- Atom sets hold [] for each element, so they are version 2 sets. -/
    theorem atom_keys_set (S : List (Term × Term))
        (atoms : «atom_keys?/1» (Term.list ((mapEntries S).map fun e => .tuple #[e.1, e.2])) =
          .ok Term.true) : Erlang.sets.elements? (.map S) = some S := by
      have empty : ∀ es : List (Term × Term),
          «atom_keys?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true →
          es.all (fun entry => entry.2 matches .nil) := by
        intro es
        induction es with
        | nil => intro _; rfl
        | cons e rest ih =>
          intro valid
          obtain ⟨k₀, w₀⟩ := e
          rw [«atom_keys?/1».eq_def] at valid
          split at valid
          · rename_i atom tail heq
            simp at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            simp [Lynx.Except.andAlso_eq_true] at valid
            simp [ih valid.2]
          · rename_i heq; simp at heq
          · simp at valid
      simp only [Erlang.sets.elements?]
      exact ite_eq_left (empty _ atoms)

    /-- Every field of a valid type is a bitmap or an atom field. -/
    theorem valid_fields (es : List (Term × Term))
        (valid : «valid_fields?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
        ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
          (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) := by
      induction es with
      | nil => simp
      | cons e rest ih =>
        obtain ⟨k, w⟩ := e
        have head : ((k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
            (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ [])) ∧
            «valid_fields?/1» (Term.list (rest.map fun e => .tuple #[e.1, e.2])) = .ok Term.true := by
          rw [«valid_fields?/1».eq_def] at valid
          split at valid
          · rename_i bits fields heq
            simp at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            simp [Lynx.Except.andAlso_eq_true] at valid
            cases w <;> simp [Erlang.erlang.«is_integer/1»] at valid
            rename_i n
            obtain ⟨⟨low, high⟩, tail⟩ := valid
            exact ⟨Or.inl ⟨rfl, n.toNat, by rw [Int.toNat_of_nonneg (by omega)], by omega, by omega⟩, tail⟩
          · rename_i set fields heq
            simp at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            simp [Lynx.Except.andAlso_eq_true] at valid
            cases set <;> simp [«atoms?/1»] at valid
            rename_i S
            refine ⟨Or.inr ⟨rfl, ⟨true, S, rfl, atom_keys_set S valid.1.1⟩, fun S' e => ?_⟩, valid.2⟩
            simp at e
            subst e
            rintro rfl
            simp [Erlang.erlang.«map_size/1»] at valid
          · rename_i set fields heq
            simp at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            simp [Lynx.Except.andAlso_eq_true] at valid
            cases set <;> simp [«atoms?/1»] at valid
            rename_i S
            exact ⟨Or.inr ⟨rfl, ⟨false, S, rfl, atom_keys_set S valid.1⟩, fun S' e => by simp at e⟩, valid.2⟩
          · rename_i heq
            simp at heq
          · simp at valid
        intro p member
        rcases List.mem_cons.mp member with rfl | member
        · exact head.1
        · exact ih head.2 p member

    theorem lookup_found (E : List (Term × Term)) (q w : Term) (lookup : mapLookup E q = some w) :
        ∃ p ∈ E, exactCompare q p.1 = .eq ∧ p.2 = w := by
      simp only [mapLookup, Option.map_eq_some_iff] at lookup
      obtain ⟨p, hp, rfl⟩ := lookup
      exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, rfl⟩

    theorem valid_of (X : List (Term × Term)) (valid : «valid?/1» (.map X) = .ok Term.true) : Valid X := by
      simp only [«valid?/1», Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at valid
      have each := valid_fields (mapEntries X) valid
      have entry (q w : Term) (lookup : mapLookup X q = some w) :
          ∃ p ∈ mapEntries X, exactCompare q p.1 = .eq ∧ p.2 = w :=
        lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
      refine ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?_⟩
      · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
        obtain ⟨p, mp, qp, -⟩ := entry q w lookup
        rcases each p mp with ⟨key, -⟩ | ⟨key, -⟩ <;> rw [key] at qp <;> simp at qp <;> simp [qp]
      · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
        rcases each p mp with ⟨key, field⟩ | ⟨key, -⟩
        · exact field
        · rw [key] at qp; simp at qp
      · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
        rcases each p mp with ⟨key, -⟩ | ⟨key, field, -⟩
        · rw [key] at qp; simp at qp
        · exact field
      · obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
        rcases each p mp with ⟨key, -⟩ | ⟨key, -, union⟩
        · rw [key] at qp; simp at qp
        · exact union S e

    theorem valid_map (descr : Term) (valid : «valid?/1» descr = .ok Term.true) :
        ∃ X, descr = .map X ∧ Valid X := by
      cases descr <;> simp [«valid?/1»] at valid
      exact ⟨_, rfl, valid_of _ (by simpa [«valid?/1»] using valid)⟩
    """

    # Unions merge fields with maps:merge_with/3.
    postlude ~LEAN"""
    /-! Map fields. -/

    /-- Atom keys are found exactly. -/
    theorem find_atom (X : List (Term × Term)) (name : String) :
        (mapEntries X).find? (fun p => decide (exactCompare (.atom name) p.1 = .eq)) =
          (mapLookup X (.atom name)).map fun v => (.atom name, v) := by
      rw [← mapLookup_mapEntries]
      simp only [mapLookup]
      cases hit : (mapEntries X).find? (fun p => decide (exactCompare (.atom name) p.1 = .eq)) with
      | none => rfl
      | some p =>
        have same : exactCompare (.atom name) p.1 = .eq := by simpa using List.find?_some hit
        have key : p.1 = .atom name := (exactCompare_eq_atom _ _).mp (Std.OrientedCmp.eq_symm same)
        obtain ⟨k₀, v₀⟩ := p
        simp only at key
        subst key
        rfl

    /-! Unions. -/

    /-- The union of two atom types holds the atoms of either. -/
    theorem atom_union (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
        (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
        (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
        ∃ (p : Bool) (E : List (Term × Term)),
          Elixir.Module.Types.Descr.«atom_union/2»
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
            .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
          Erlang.sets.elements? (.map E) = some E ∧
          ∀ q, (p == (mapLookup E q).isSome) =
            ((p₁ == (mapLookup S₁ q).isSome) || (p₂ == (mapLookup S₂ q).isSome)) := by
      cases p₁ <;> cases p₂
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
        refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
        refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
        refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
        refine ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl

    /-! Laws compare memberships as Booleans. -/

    """

    # Intersections intersect fields with maps:intersect_with/3 and drop empty ones.
    postlude ~LEAN"""
    /-! Intersections. -/

    /-- Unions of atoms are dropped when empty. -/
    theorem union_or_empty (E : List (Term × Term)) :
        (∃ s : Nat, s ≠ 0 ∧ Erlang.sets.«size/1» (.map E) = .ok (.integer s)) ∨
          (Erlang.sets.«size/1» (.map E) = .ok (.integer 0) ∧ ∀ q, mapLookup E q = none) := by
      cases h : ((E.map Prod.fst).eraseDupsBy (fun a b => exactCompare a b == .eq)).length with
      | zero =>
        have empty : Erlang.sets.«size/1» (.map E) = .ok (.integer 0) := by simp [Erlang.sets.«size/1», h]
        exact Or.inr ⟨empty, fun q => Erlang.sets.size_empty E q empty⟩
      | succ s => exact Or.inl ⟨s + 1, by omega, by simp [Erlang.sets.«size/1», h]⟩

    /-- The intersection of two atom types holds the atoms of both, and is `0` when empty. -/
    theorem atom_intersection (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
        (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
        (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
        (∃ (p : Bool) (E : List (Term × Term)),
          Elixir.Module.Types.Descr.«atom_intersection/2»
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
            .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
          Erlang.sets.elements? (.map E) = some E ∧
          -- Intersections are unions unless both types are negations, and are not empty.
          p = (p₁ || p₂) ∧ (p = Bool.true → E ≠ []) ∧
          ∀ q, (p == (mapLookup E q).isSome) =
            ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome))) ∨
        (Elixir.Module.Types.Descr.«atom_intersection/2»
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .ok (.integer 0) ∧
          ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) := by
      cases p₁ <;> cases p₂
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
        refine Or.inl ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE,
          Erlang.erlang.«==/2»], setE, rfl, fun negated => Bool.noConfusion negated, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
            subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
          rw [m]
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
        · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
            Erlang.erlang.«==/2»], fun q => ?_⟩
          have := m q
          rw [empty q] at this
          revert this
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
            subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
          rw [m]
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
        · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
            Erlang.erlang.«==/2»], fun q => ?_⟩
          have := m q
          rw [empty q] at this
          revert this
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
            subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
          rw [m]
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
        · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
            Erlang.erlang.«==/2»], fun q => ?_⟩
          have := m q
          rw [empty q] at this
          revert this
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp

    /-- The intersection keeps the fields that are neither `0` nor `bdd_bot`. -/
    def kept (entry : Term × Term) : Bool :=
      !decide (exactCompare entry.2 (.integer 0) = .eq) &&
        !decide (exactCompare entry.2 (.atom "bdd_bot") = .eq)

    theorem keep_field (key value : Term) :
        Elixir.Module.Types.Descr.«-symmetrical_intersection/3-fun-0-/2» key value =
          .ok (if kept (key, value) then Term.true else Term.false) := by
      by_cases zero : exactCompare value (.integer 0) = .eq <;>
        by_cases bot : exactCompare value (.atom "bdd_bot") = .eq <;>
        simp [Elixir.Module.Types.Descr.«-symmetrical_intersection/3-fun-0-/2», kept, Erlang.erlang.«=:=/2»,
          Erlang.erlang.«=/=/2», zero, bot, Term.true, Term.false]

    """

    # Differences fold over the fields of the right type and drop empty ones.
    postlude ~LEAN"""
    /-! Differences. -/

    /-- The difference updates the fields of the left type that the right type also has,
    dropping them when they become `0` or `bdd_bot`. -/
    def differenceStep (g : Term → Term → Term → Term) (acc : List (Term × Term)) (entry : Term × Term) :
        List (Term × Term) :=
      match mapLookup acc entry.1 with
      | some v₁ =>
        if kept (entry.1, g entry.1 v₁ entry.2) then (entry.1, g entry.1 v₁ entry.2) :: acc
        else acc.filter fun e => exactCompare entry.1 e.1 != .eq
      | none => acc

    theorem member_dropped (key w : Term) :
        isMember w [.integer 0, .atom "bdd_bot"] = if kept (key, w) then .atom "false" else .atom "true" := by
      by_cases zero : exactCompare w (.integer 0) = .eq <;>
        by_cases bot : exactCompare w (.atom "bdd_bot") = .eq <;>
        simp [isMember, kept, zero, bot]

    theorem difference_step (depth : Nat) (fn : Term) (g : Term → Term → Term → Term) (acc : List (Term × Term))
        (key v₂ : Term)
        (calls : ∀ v₁, mapLookup acc key = some v₁ →
          Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[key, v₁, v₂] =
            .ok (g key v₁ v₂)) :
        Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            fn key v₂ (.map acc) = .ok (.map (differenceStep g acc (key, v₂))) := by
      unfold Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4»
      cases found : mapLookup acc key with
      | none => simp [getMapKeys_single, found, differenceStep]
      | some v₁ =>
        simp only [getMapKeys_single, found, Option.toList_some,
          calls v₁ found, Lynx.Except.ok_bind, member_dropped key, differenceStep]
        obtain ⟨e, member, same⟩ := (mapLookup_isSome acc key).mp (by simp [found])
        by_cases keep : kept (key, g key v₁ v₂) <;> simp [keep, Erlang.erlang.«is_map/1», Erlang.maps.«update/3»,
          Erlang.maps.«remove/2»]
        exact ⟨e.1, ⟨e.2, member⟩, same⟩

    theorem step_other (g : Term → Term → Term → Term) (acc : List (Term × Term)) (e : Term × Term) (q : Term)
        (other : exactCompare q e.1 ≠ .eq) : mapLookup (differenceStep g acc e) q = mapLookup acc q := by
      unfold differenceStep
      cases mapLookup acc e.1 with
      | none => rfl
      | some v₁ =>
        by_cases keep : kept (e.1, g e.1 v₁ e.2)
        · simp [keep, mapLookup, other]
        · simp only [keep, Bool.false_eq_true, ite_false]
          rw [mapLookup_filter]
          simp [other]

    theorem step_same (g : Term → Term → Term → Term) (acc : List (Term × Term)) (e : Term × Term) (q : Term)
        (same : exactCompare q e.1 = .eq) :
        mapLookup (differenceStep g acc e) q = (mapLookup acc e.1).bind fun v₁ =>
          if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none := by
      unfold differenceStep
      cases found : mapLookup acc e.1 with
      | none => simp only [Option.bind_none]; rw [mapLookup_congr same, found]
      | some v₁ =>
        by_cases keep : kept (e.1, g e.1 v₁ e.2)
        · simp [keep, mapLookup, same]
        · simp only [keep, Bool.false_eq_true, ite_false, Option.bind_some]
          rw [mapLookup_filter]
          simp [same]

    /-- Folding the difference over the entries of the right type. -/
    theorem difference_fold (depth : Nat) (fn : Term) (g : Term → Term → Term → Term) (es acc : List (Term × Term))
        (distinct : es.Pairwise (fun a b => exactCompare a.1 b.1 ≠ .eq))
        (calls : ∀ e ∈ es, ∀ v₁, mapLookup acc e.1 = some v₁ →
          Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[e.1, v₁, e.2] =
            .ok (g e.1 v₁ e.2)) :
        ∃ M, es.foldlM (fun acc entry =>
            (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
              (.function "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3
              #[fn]) #[entry.1, entry.2, acc] : Except Exception Term))
            (.map acc) = .ok (.map M) ∧
          ∀ q, mapLookup M q =
            match es.find? (fun e => decide (exactCompare q e.1 = .eq)) with
            | some e => (mapLookup acc e.1).bind fun v₁ =>
                if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none
            | none => mapLookup acc q := by
      induction es generalizing acc with
      | nil => exact ⟨acc, rfl, fun q => rfl⟩
      | cons e rest ih =>
        have apart := List.pairwise_cons.mp distinct
        have step : (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
            (.function "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3
              #[fn]) #[e.1, e.2, .map acc] : Except Exception Term) =
            .ok (.map (differenceStep g acc e)) := by
          rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-dynamic_difference/3-fun-0-/3».pure,
            difference_step depth fn g acc e.1 e.2 (calls e (List.mem_cons_self ..))]
        obtain ⟨M, run, look⟩ := ih (differenceStep g acc e) apart.2 (by
          intro e' member v₁ found
          rw [step_other g acc e e'.1 (fun same => apart.1 e' member (Std.OrientedCmp.eq_symm same))] at found
          exact calls e' (List.mem_cons_of_mem _ member) v₁ found)
        refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_⟩
        rw [look q]
        by_cases same : exactCompare q e.1 = .eq
        · have absent : rest.find? (fun p => decide (exactCompare q p.1 = .eq)) = none := by
            rw [List.find?_eq_none]
            intro p member hit
            exact apart.1 p member
              (Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm same) (of_decide_eq_true hit))
          simp only [absent, List.find?_cons, same, decide_true]
          exact step_same g acc e q same
        · simp only [List.find?_cons, same, decide_false]
          cases hit : rest.find? (fun p => decide (exactCompare q p.1 = .eq)) with
          | none => exact step_other g acc e q same
          | some e' =>
            have qe' : exactCompare q e'.1 = .eq := by simpa using List.find?_some hit
            have other : exactCompare e'.1 e.1 ≠ .eq := fun same' =>
              same (Std.TransCmp.eq_trans qe' same')
            simp only
            rw [step_other g acc e e'.1 other]

    /-! Bitmap differences remove the bits of the right bitmap. -/

    theorem add_eq_or (x y : Nat) (disjoint : x &&& y = 0) : x + y = x ||| y := by
      let w := x + y + 1
      have small (n : Nat) (h : n ≤ x + y) : n < 2 ^ w :=
        Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega))
      have bv : BitVec.ofNat w x &&& BitVec.ofNat w y = 0#w := by
        apply BitVec.eq_of_toNat_eq
        simp [Nat.mod_eq_of_lt (small x (by omega)), Nat.mod_eq_of_lt (small y (by omega)), disjoint]
      have := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ bv)
      simp only [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (small x (by omega)), Nat.mod_eq_of_lt (small y (by omega)),
        Nat.mod_eq_of_lt (small (x + y) (by omega))] at this
      exact this

    theorem testBit_sub_and (a b i : Nat) :
        (a - (a &&& b)).testBit i = (a.testBit i && !b.testBit i) := by
      have disjoint : (a ^^^ (a &&& b)) &&& (a &&& b) = 0 := Nat.eq_of_testBit_eq fun j => by
        simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
        cases a.testBit j <;> cases b.testBit j <;> rfl
      have whole : (a ^^^ (a &&& b)) ||| (a &&& b) = a := Nat.eq_of_testBit_eq fun j => by
        simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
        cases a.testBit j <;> cases b.testBit j <;> rfl
      have split := add_eq_or _ _ disjoint
      rw [whole] at split
      rw [show a - (a &&& b) = a ^^^ (a &&& b) by omega]
      simp only [Nat.testBit_xor, Nat.testBit_and]
      cases a.testBit i <;> cases b.testBit i <;> rfl

    /-- The difference of two atom types holds the atoms of the first only, and is `0` when empty. -/
    theorem atom_difference (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
        (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
        (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
        (∃ (p : Bool) (E : List (Term × Term)),
          Elixir.Module.Types.Descr.«atom_difference/2»
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
            .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
          Erlang.sets.elements? (.map E) = some E ∧
          -- Differences are unions unless a negation removes a union.
          p = (p₁ || !p₂) ∧ (p = Bool.true → E ≠ []) ∧
          ∀ q, (p == (mapLookup E q).isSome) =
            ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome))) ∨
        (Elixir.Module.Types.Descr.«atom_difference/2»
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .ok (.integer 0) ∧
          ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome)) = Bool.false) := by
      cases p₁ <;> cases p₂
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
            subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
          rw [m]
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
        · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2»], fun q => ?_⟩
          have := m q
          rw [empty q] at this
          revert this
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
        refine Or.inl ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE,
          Erlang.erlang.«==/2»], setE, rfl, fun negated => Bool.noConfusion negated, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
            subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
          rw [m]
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
        · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2»], fun q => ?_⟩
          have := m q
          rw [empty q] at this
          revert this
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
            subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
          rw [m]
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
        · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2»], fun q => ?_⟩
          have := m q
          rw [empty q] at this
          revert this
          cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp

    theorem unfold_map (d : Dispatcher) (entries : List (Term × Term)) :
        Elixir.Module.Types.Descr.«unfold/1» d (.map entries) = .ok (.map entries) := by
      rw [Elixir.Module.Types.Descr.«unfold/1».eq_def]; rfl

    theorem static_map {X : List (Term × Term)} (static : mapLookup X (.atom "dynamic") = none) :
        Erlang.erlang.«is_map_key/2» (.atom "dynamic") (.map X) = .ok (.atom "false") := by
      have absent : X.any (fun entry => exactCompare (.atom "dynamic") entry.1 == .eq) = Bool.false := by
        rw [Bool.eq_false_iff]
        intro present
        obtain ⟨entry, member, same⟩ := List.any_eq_true.mp present
        have := (mapLookup_isSome X (.atom "dynamic")).mpr ⟨entry, member, by simpa using same⟩
        rw [static] at this
        cases this
      simp [Erlang.erlang.«is_map_key/2», absent, Term.false]

    """

    # The empty type is the empty map, and intersecting with it empties a type.
    postlude ~LEAN"""
    /-- Maps without visible keys hold no entries. -/
    theorem nil_of_lookup_none (entries : List (Term × Term))
        (none : ∀ q, mapLookup entries q = Option.none) : entries = [] := by
      cases entries with
      | nil => rfl
      | cons entry rest =>
        have := none entry.1
        simp [mapLookup] at this

    /-- Intersecting a map of fields with the empty type keeps no field. -/
    theorem symmetrical_none (d : Dispatcher) (X : List (Term × Term)) :
        Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map X) (.map [])
          (.function "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) = .ok (.map []) := by
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup d "Elixir.Module.Types.Descr"
        "bare_intersection" #[] X [] (fun _ _ _ => .nil) (by intro e _ y hy; simp [mapLookup] at hy)
      obtain rfl : I = [] := nil_of_lookup_none I fun q => by
        rw [lookI]
        cases (mapEntries X).find? (fun e => decide (exactCompare q e.1 = .eq)) <;> simp [mapLookup]
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup d "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] [] kept (by intro e member; simp at member)
      obtain rfl : out = [] := nil_of_lookup_none out fun q => by rw [lookO]; simp
      unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
      simp [runI, runO]

    /-- The intersection of a static type with the empty type is empty, whatever its fields hold. -/
    theorem intersection_none_static (depth : Nat) (X : List (Term × Term))
        (static : mapLookup X (.atom "dynamic") = Option.none) :
        Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map X) (.map []) = .ok (.map []) := by
      have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»
      simp [getMapKeys_single, static, absent, symmetrical_none]

    /-- The intersection of a gradual type with the empty type is empty, when its dynamic
    part is the top type or a map of fields. -/
    theorem intersection_none_dynamic (depth : Nat) (X : List (Term × Term)) (Dy : Term)
        (dynamic : mapLookup X (.atom "dynamic") = some Dy)
        (inner : Dy = .atom "term" ∨ ∃ Y, Dy = .map Y) :
        Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map X) (.map []) = .ok (.map []) := by
      have part : Elixir.Module.Types.Descr.«bare_intersection/3»
          (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom "dynamic") Dy (.map []) =
            .ok (.integer 0) := by
        simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]
        unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»
        rcases inner with rfl | ⟨Y, rfl⟩
        · simp [Erlang.erlang.«==/2»]
        · simp [symmetrical_none, Erlang.erlang.«==/2»]
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "bare_intersection" #[] X [(.atom "dynamic", .map [])] (fun _ _ _ => .integer 0) (by
          intro e me y hy
          simp [mapLookup] at hy
          obtain ⟨key, rfl⟩ := hy
          have hx := mapLookup_of_mem_mapEntries me
          rw [key, dynamic] at hx
          cases hx
          rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, key, part])
      have zero : ∀ e ∈ mapEntries I, e.2 = .integer 0 := by
        intro e me
        have hx := mapLookup_of_mem_mapEntries me
        rw [lookI] at hx
        split at hx
        · simp at hx
          exact hx.2.symm
        · cases hx
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] I kept (by
          intro e _
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
      obtain rfl : out = [] := nil_of_lookup_none out fun q => by
        rw [lookO]
        cases found : (mapEntries I).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | none => rfl
        | some e => simp [kept, zero e (List.mem_of_find?_eq_some found)]
      have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»
      simp [getMapKeys_single, dynamic, absent, Erlang.maps.«put/3»]
      unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
      simp [runI, runO]

    /-- The empty type is empty. -/
    theorem empty_none (d : Dispatcher) :
        Elixir.Module.Types.Descr.«empty?/1» d (.map []) = .ok Term.true := by
      simp only [Elixir.Module.Types.Descr.«empty?/1»]
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
      simp [getMapKeys_single, mapLookup, Erlang.erlang.«==/2», Term.true]

    """

    # A function type and its negation hold the same BDDs for each arity, whose
    # differences are bottom, so their intersection drops every arity.
    postlude ~LEAN"""
    /-- Function types are unions (true) or negations (false) of maps from arities to BDDs. -/
    abbrev FunField (w : Term) : Prop :=
      ∃ (pos : Bool) (R : List (Term × Term)), w = .tuple #[.atom (if pos then "union" else "negation"), .map R]

    /-- A BDD without its own copy is bottom. -/
    theorem bdd_difference_self (b : Term) :
        Elixir.Module.Types.Descr.«bdd_difference/2» b b = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Erlang.erlang.«=:=/2»]

    /-- Each step of `fun_repr_difference/2` removes an arity whose BDD the accumulator holds as is. -/
    theorem repr_step (acc : List (Term × Term)) (key bdd : Term)
        (same : ∀ v, mapLookup acc key = some v → v = bdd) :
        ∃ next, Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3» key bdd (.map acc) = .ok (.map next) ∧
          (∀ q, exactCompare q key ≠ .eq → mapLookup next q = mapLookup acc q) ∧
          (∀ q, exactCompare q key = .eq → mapLookup next q = Option.none) := by
      unfold Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3»
      cases found : mapLookup acc key with
      | none =>
        refine ⟨acc, by simp [getMapKeys_single, found], fun q _ => rfl, fun q eq => ?_⟩
        rw [mapLookup_congr eq]; exact found
      | some v =>
        obtain rfl := same v found
        refine ⟨acc.filter fun e => exactCompare key e.1 != .eq, ?_, fun q ne => ?_, fun q eq => ?_⟩
        · simp [getMapKeys_single, found, bdd_difference_self, isMember, Erlang.maps.«remove/2»]
        · rw [mapLookup_filter]; simp [ne]
        · rw [mapLookup_filter]; simp [eq]

    /-- Folding `fun_repr_difference/2` over arities whose BDDs the accumulator holds as is
    removes them. -/
    theorem repr_fold (n : Nat) (es acc : List (Term × Term))
        (distinct : es.Pairwise (fun a b => exactCompare a.1 b.1 ≠ .eq))
        (same : ∀ e ∈ es, ∀ v, mapLookup acc e.1 = some v → v = e.2) :
        ∃ M, es.foldlM (fun acc entry =>
            (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table n)
              (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
              #[entry.1, entry.2, acc] : Except Exception Term)) (.map acc) = .ok (.map M) ∧
          ∀ q, mapLookup M q =
            match es.find? (fun e => decide (exactCompare q e.1 = .eq)) with
            | some _ => Option.none
            | none => mapLookup acc q := by
      induction es generalizing acc with
      | nil => exact ⟨acc, rfl, fun q => rfl⟩
      | cons e rest ih =>
        have apart := List.pairwise_cons.mp distinct
        obtain ⟨next, run₁, other, gone⟩ := repr_step acc e.1 e.2 (same e (List.mem_cons_self ..))
        have step : (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table n)
            (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
            #[e.1, e.2, .map acc] : Except Exception Term) = .ok (.map next) := by
          rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_difference/2-fun-0-/3».pure, run₁]
        obtain ⟨M, run, look⟩ := ih next apart.2 (by
          intro e' member v found
          rw [other e'.1 (fun s => apart.1 e' member (Std.OrientedCmp.eq_symm s))] at found
          exact same e' (List.mem_cons_of_mem _ member) v found)
        refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_⟩
        rw [look q]
        by_cases s : exactCompare q e.1 = .eq
        · have absent : rest.find? (fun p => decide (exactCompare q p.1 = .eq)) = Option.none := by
            rw [List.find?_eq_none]
            intro p member hit
            exact apart.1 p member
              (Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm s) (of_decide_eq_true hit))
          simp only [absent, List.find?_cons, s, decide_true]
          exact gone q s
        · simp only [List.find?_cons, s, decide_false]
          cases rest.find? (fun p => decide (exactCompare q p.1 = .eq)) with
          | none => exact other q s
          | some _ => rfl

    /-- The difference of a map of arities to BDDs with a map of the same lookups is empty. -/
    theorem repr_cancel (n : Nat) (R M : List (Term × Term)) (lookups : ∀ q, mapLookup M q = mapLookup R q) :
        Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
          (.map R) (.map M) = .ok (.map []) := by
      obtain ⟨D, run, look⟩ := repr_fold n (mapEntries M) R (mapEntries_distinct M) (by
        intro e member v found
        rw [← lookups, mapLookup_of_mem_mapEntries member] at found
        exact (Option.some.inj found).symm)
      obtain rfl : D = [] := nil_of_lookup_none D fun q => by
        rw [look q]
        cases hit : (mapEntries M).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | some _ => rfl
        | none =>
          have : mapLookup (mapEntries M) q = Option.none := by simp [mapLookup, hit]
          rw [mapLookup_mapEntries, lookups] at this
          exact this
      simp only [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
      simpa using run

    /-- A function type does not intersect its negation. -/
    theorem fun_negation (n : Nat) (w : Term) (field : FunField w) :
        ∃ y, Elixir.Module.Types.Descr.«fun_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
            (.tuple #[.atom "negation", .map []]) w = .ok y ∧
          (y = .integer 0 ∨ ∀ m, Elixir.Module.Types.Descr.«fun_intersection/2»
            (Dispatcher.ofTable Erlang.program.fun_table m) w y = .ok (.integer 0)) := by
      obtain ⟨pos, R, rfl⟩ := field
      cases pos with
      | true =>
        obtain ⟨out, merge, look⟩ := Erlang.maps.merge_with_lookup (Dispatcher.ofTable Erlang.program.fun_table n)
          "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] R (fun _ _ _ => .nil)
          (by intro e _ v found; simp [mapLookup] at found)
        have same : ∀ q, mapLookup out q = mapLookup R q := by
          intro q
          rw [look q, ← mapLookup_mapEntries R]
          simp only [mapLookup]
          cases (mapEntries R).find? (fun e => decide (exactCompare q e.1 = .eq)) <;> simp
        refine ⟨.tuple #[.atom "negation", .map out], ?_, Or.inr fun m => ?_⟩
        · simp [Elixir.Module.Types.Descr.«fun_difference/2», Elixir.Module.Types.Descr.«fun_repr_union/2»,
            Elixir.Module.Types.Descr.«symmetrical_merge/3», merge, Erlang.erlang.«==/2», Lynx.Except.andAlso]
        · simp [Elixir.Module.Types.Descr.«fun_intersection/2», repr_cancel m R out same, Erlang.erlang.«==/2»,
            Erlang.erlang.«map_size/1», Lynx.Except.andAlso]
      | false =>
        have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
            (.map R) (.map []) = .ok (.map R) := by
          simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
        by_cases empty : ((R.map Prod.fst).eraseDupsBy (fun a b => exactCompare a b == .eq)).length = 0
        · refine ⟨.integer 0, ?_, Or.inl rfl⟩
          simp [Elixir.Module.Types.Descr.«fun_difference/2», keep, Erlang.erlang.«==/2»,
            Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
        · refine ⟨.tuple #[.atom "union", .map R], ?_, Or.inr fun m => ?_⟩
          · simp [Elixir.Module.Types.Descr.«fun_difference/2», keep, Erlang.erlang.«==/2»,
              Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
          · simp [Elixir.Module.Types.Descr.«fun_intersection/2», repr_cancel m R R (fun _ => rfl),
              Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]
    """

    # Lazy BDDs ordered by their literals: unions, removals, intersections,
    # negations, and differences terminate and compute the propositional
    # connectives, so a BDD that no assignment of its literals satisfies has no line.
    postlude ~LEAN"""
    namespace BddProofs

    /-- BDD literals are leaves: triples with an integer key. -/
    def IsLeaf (t : Term) : Prop := ∃ (k : Int) (x y : Term), t = .tuple #[.integer k, x, y]

    /-- Ordered BDDs whose literals satisfy `ok`. -/
    def Bdd (ok : Term → Prop) : Term → Prop
      | .atom "bdd_top" => True
      | .atom "bdd_bot" => True
      | .tuple ⟨[.integer _, lit, c, u, d]⟩ => IsLeaf lit ∧ ok lit ∧
          Bdd (fun t => ok t ∧ compare lit t = .lt) c ∧ Bdd (fun t => ok t ∧ compare lit t = .lt) u ∧
          Bdd (fun t => ok t ∧ compare lit t = .lt) d
      | .tuple ⟨[.integer k, x, y]⟩ => ok (.tuple #[.integer k, x, y])
      | _ => False

    /-- The propositional semantics of a BDD, given the truth of each literal. -/
    def eval (ρ : Term → Bool) : Term → Bool
      | .atom "bdd_top" => true
      | .tuple ⟨[_, lit, c, u, d]⟩ => (ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)
      | .tuple ⟨[k, x, y]⟩ => ρ (.tuple #[k, x, y])
      | _ => false

    theorem Bdd.shape {ok : Term → Prop} {b : Term} (wf : Bdd ok b) :
        b = .atom "bdd_top" ∨ b = .atom "bdd_bot" ∨ (∃ (k : Int) (x y : Term), b = .tuple #[.integer k, x, y]) ∨
          ∃ (h : Int) (lit c u d : Term), b = .tuple #[.integer h, lit, c, u, d] := by
      unfold Bdd at wf
      split at wf <;> simp_all

    def bandI : Int → Int → Int
      | .ofNat x, .ofNat y => .ofNat (x &&& y)
      | .ofNat x, .negSucc y => .ofNat (x ^^^ (x &&& y))
      | .negSucc x, .ofNat y => .ofNat (y ^^^ (y &&& x))
      | .negSucc x, .negSucc y => .negSucc (x ||| y)

    def bxorI : Int → Int → Int
      | .ofNat x, .ofNat y => .ofNat (x ^^^ y)
      | .ofNat x, .negSucc y => .negSucc (x ^^^ y)
      | .negSucc x, .ofNat y => .negSucc (x ^^^ y)
      | .negSucc x, .negSucc y => .ofNat (x ^^^ y)

    @[simp] theorem band_int (x y : Int) : Erlang.erlang.«band/2» (.integer x) (.integer y) = .ok (.integer (bandI x y)) := by
      cases x <;> cases y <;> rfl
    @[simp] theorem bxor_int (x y : Int) : Erlang.erlang.«bxor/2» (.integer x) (.integer y) = .ok (.integer (bxorI x y)) := by
      cases x <;> cases y <;> rfl
    @[simp] theorem bsl_six (x : Int) : Erlang.erlang.«bsl/2» (.integer x) (.integer 6) = .ok (.integer (x <<< 6)) := rfl
    @[simp] theorem bsr_two (x : Int) : Erlang.erlang.«bsr/2» (.integer x) (.integer 2) = .ok (.integer (x >>> 2)) := rfl

    /-- Computations that return an integer. -/
    def IntOk (e : Except Exception Term) : Prop := ∃ z : Int, e = .ok (.integer z)

    theorem IntOk.bind {m : Except Exception Term} {f : Term → Except Exception Term} (hm : IntOk m)
        (hf : ∀ a : Int, IntOk (f (.integer a))) : IntOk (m >>= f) := by
      obtain ⟨a, rfl⟩ := hm
      exact hf a

    theorem hash_ok {ok : Term → Prop} {b : Term} (wf : Bdd ok b) {e : Except Exception Term}
        (top : b = .atom "bdd_top" → IntOk e) (bot : b = .atom "bdd_bot" → IntOk e)
        (leaf : ∀ (k : Int) (x y : Term), b = .tuple #[.integer k, x, y] → IntOk e)
        (node : ∀ (h : Int) (lit c u d : Term), b = .tuple #[.integer h, lit, c, u, d] → IntOk e) : IntOk e := by
      rcases wf.shape with h | h | ⟨k, x, y, h⟩ | ⟨n, lit, c, u, d, h⟩
      · exact top h
      · exact bot h
      · exact leaf k x y h
      · exact node n lit c u d h

    macro "int_ok" : tactic => `(tactic| (apply Exists.intro; simp only [Erlang.erlang.«+/2_integers», bsl_six,
      bsr_two, bxor_int, band_int, Lynx.Except.ok_bind, pure, Except.pure]; try rfl))

    theorem node_new {okc oku okd : Term → Prop} (lit c u d : Term) (leaf : IsLeaf lit) (hc : Bdd okc c) (hu : Bdd oku u) (hd : Bdd okd d) :
        ∃ h : Int, Elixir.Module.Types.Descr.«bdd_node_new/4» lit c u d = .ok (.tuple #[.integer h, lit, c, u, d]) := by
      obtain ⟨k, x, y, rfl⟩ := leaf
      have hash : IntOk (Elixir.Module.Types.Descr.«bdd_compute_hash/4» (.tuple #[.integer k, x, y]) c u d) := by
        unfold Elixir.Module.Types.Descr.«bdd_compute_hash/4»
        refine IntOk.bind ?_ fun _ => ?_
        · int_ok
        refine IntOk.bind ?_ fun _ => ?_
        · refine hash_ok hc ?_ ?_ ?_ ?_ <;> (intros; subst_vars; int_ok)
        refine IntOk.bind ?_ fun _ => ?_
        · int_ok
        refine IntOk.bind ?_ fun _ => ?_
        · refine hash_ok hu ?_ ?_ ?_ ?_ <;> (intros; subst_vars; int_ok)
        refine IntOk.bind ?_ fun _ => ?_
        · int_ok
        refine IntOk.bind ?_ fun _ => ?_
        · refine hash_ok hd ?_ ?_ ?_ ?_ <;> (intros; subst_vars; int_ok)
        refine IntOk.bind ?_ fun _ => ?_
        · int_ok
        int_ok
      obtain ⟨h, run⟩ := hash
      exact ⟨h, by simp [Elixir.Module.Types.Descr.«bdd_node_new/4», run]⟩

    /-- The literals of a node's children are above the node's literal. -/
    abbrev Above (ok : Term → Prop) (lit : Term) : Term → Prop := fun t => ok t ∧ Term.compare lit t = .lt

    theorem Bdd.node_iff {ok : Term → Prop} {h : Int} {lit c u d : Term} :
        Bdd ok (.tuple #[.integer h, lit, c, u, d]) ↔
          IsLeaf lit ∧ ok lit ∧ Bdd (Above ok lit) c ∧ Bdd (Above ok lit) u ∧ Bdd (Above ok lit) d := by
      simp [Bdd, Above]

    theorem Bdd.leaf_iff {ok : Term → Prop} {k : Int} {x y : Term} :
        Bdd ok (.tuple #[.integer k, x, y]) ↔ ok (.tuple #[.integer k, x, y]) := by
      simp [Bdd]

    theorem sizeOf_children (h lit c u d : Term) :
        sizeOf c < sizeOf (Term.tuple #[h, lit, c, u, d]) ∧ sizeOf u < sizeOf (Term.tuple #[h, lit, c, u, d]) ∧
          sizeOf d < sizeOf (Term.tuple #[h, lit, c, u, d]) := by
      simp only [Term.tuple.sizeOf_spec, List.size_toArray, Array.mk.sizeOf_spec, List.cons.sizeOf_spec,
        List.nil.sizeOf_spec]
      omega

    /-- Induction over ordered BDDs. -/
    theorem Bdd.induction {P : (Term → Prop) → Term → Prop}
        (top : ∀ ok, P ok (.atom "bdd_top")) (bot : ∀ ok, P ok (.atom "bdd_bot"))
        (leaf : ∀ ok (k : Int) x y, ok (.tuple #[.integer k, x, y]) → P ok (.tuple #[.integer k, x, y]))
        (node : ∀ ok (h : Int) lit c u d, IsLeaf lit → ok lit →
          Bdd (Above ok lit) c → Bdd (Above ok lit) u → Bdd (Above ok lit) d →
          P (Above ok lit) c → P (Above ok lit) u → P (Above ok lit) d →
          P ok (.tuple #[.integer h, lit, c, u, d])) :
        ∀ (ok : Term → Prop) (b : Term), Bdd ok b → P ok b := by
      suffices all : ∀ n, ∀ (ok : Term → Prop) (b : Term), sizeOf b ≤ n → Bdd ok b → P ok b from
        fun ok b => all _ ok b (Nat.le_refl _)
      intro n
      induction n with
      | zero => intro ok b size; cases b <;> simp at size <;> omega
      | succ n ih =>
        intro ok b size wf
        rcases wf.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
        · exact top ok
        · exact bot ok
        · exact leaf ok k x y (Bdd.leaf_iff.mp wf)
        · obtain ⟨isLeaf, okLit, hc, hu, hd⟩ := Bdd.node_iff.mp wf
          obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h) lit c u d
          exact node ok h lit c u d isLeaf okLit hc hu hd (ih _ c (by omega) hc) (ih _ u (by omega) hu)
            (ih _ d (by omega) hd)

    theorem Bdd.mono {ok ok' : Term → Prop} (h : ∀ t, ok t → ok' t) {b : Term} (wf : Bdd ok b) : Bdd ok' b := by
      revert ok'
      refine Bdd.induction (P := fun ok b => ∀ {ok'}, (∀ t, ok t → ok' t) → Bdd ok' b) ?_ ?_ ?_ ?_ ok b wf
      · intro ok ok' _; simp [Bdd]
      · intro ok ok' _; simp [Bdd]
      · intro ok k x y okb ok' h; exact Bdd.leaf_iff.mpr (h _ okb)
      · intro ok n lit c u d isLeaf okLit _ _ _ ihc ihu ihd ok' h
        have lift : ∀ t, Above ok lit t → Above ok' lit t := fun t ht => ⟨h t ht.1, ht.2⟩
        exact Bdd.node_iff.mpr ⟨isLeaf, h _ okLit, ihc lift, ihu lift, ihd lift⟩

    /-- A BDD whose head is above `m` has all its literals above `m`. -/
    def head : Term → Option Term
      | .tuple ⟨[_, lit, _, _, _]⟩ => some lit
      | .tuple ⟨[k, x, y]⟩ => some (.tuple #[k, x, y])
      | _ => none

    theorem Bdd.raise {ok : Term → Prop} {b m : Term} (wf : Bdd ok b)
        (above : ∀ l, head b = some l → compare m l = .lt) : Bdd (Above ok m) b := by
      rcases wf.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · simp [Bdd]
      · simp [Bdd]
      · exact Bdd.leaf_iff.mpr ⟨Bdd.leaf_iff.mp wf, above _ (by simp [head])⟩
      · obtain ⟨isLeaf, okLit, hc, hu, hd⟩ := Bdd.node_iff.mp wf
        have ml : compare m lit = .lt := above lit (by simp [head])
        have lift : ∀ t, Above ok lit t → Above (Above ok m) lit t :=
          fun t ht => ⟨⟨ht.1, Std.TransCmp.lt_trans ml ht.2⟩, ht.2⟩
        exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okLit, ml⟩, hc.mono lift, hu.mono lift, hd.mono lift⟩

    /-- A non-trivial BDD seen as a node: leaves `l` are `(l and top) or bot or (not l and bot)`. -/
    def Split (a lit c u d : Term) : Prop :=
      (∃ h : Int, a = .tuple #[.integer h, lit, c, u, d]) ∨
        (a = lit ∧ IsLeaf lit ∧ c = .atom "bdd_top" ∧ u = .atom "bdd_bot" ∧ d = .atom "bdd_bot")

    theorem head_some {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) :
        (∃ (k : Int) (x y : Term), a = .tuple #[.integer k, x, y] ∧ l = a) ∨
          ∃ (h : Int) (c u d : Term), a = .tuple #[.integer h, l, c, u, d] := by
      rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · simp [head] at ha
      · simp [head] at ha
      · simp [head] at ha; exact Or.inl ⟨k, x, y, rfl, ha.symm⟩
      · simp [head] at ha; subst ha; exact Or.inr ⟨h, c, u, d, rfl⟩

    theorem head_shape {a l : Term} (ha : head a = some l) :
        (∃ x y z : Term, a = .tuple #[x, y, z] ∧ l = a) ∨ ∃ h c u d : Term, a = .tuple #[h, l, c, u, d] := by
      unfold head at ha
      split at ha
      · cases ha; exact Or.inr ⟨_, _, _, _, rfl⟩
      · cases ha; exact Or.inl ⟨_, _, _, rfl, rfl⟩
      · cases ha

    theorem compare_lt {ok : Term → Prop} {a b la lb : Term} (wa : Bdd ok a) (ha : head a = some la)
        (hb : head b = some lb) (lt : compare la lb = .lt) :
        ∃ (h : Int) (c u d : Term), Elixir.Module.Types.Descr.«bdd_compare/2» a b =
          .ok (.tuple #[.atom "lt", .tuple #[.integer h, la, c, u, d], b]) ∧ Split a la c u d := by
      have top : Bdd (fun _ => True) (.atom "bdd_top") := by simp [Bdd]
      have bot : Bdd (fun _ => True) (.atom "bdd_bot") := by simp [Bdd]
      unfold Elixir.Module.Types.Descr.«bdd_compare/2»
      rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨n, c, u, d, rfl⟩
      · obtain ⟨h, run⟩ := node_new (.tuple #[.integer k, x, y]) _ _ _ ⟨k, x, y, rfl⟩ top bot bot
        refine ⟨h, _, _, _, ?_, Or.inr ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩⟩
        rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
          simp [Erlang.erlang.«</2», lt, Lynx.Except.guard, run]
      · refine ⟨n, c, u, d, ?_, Or.inl ⟨n, rfl⟩⟩
        rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
          simp [Erlang.erlang.«</2», lt, Lynx.Except.guard]

    theorem compare_gt {ok : Term → Prop} {a b la lb : Term} (wb : Bdd ok b) (ha : head a = some la)
        (hb : head b = some lb) (gt : compare la lb = .gt) :
        ∃ (h : Int) (c u d : Term), Elixir.Module.Types.Descr.«bdd_compare/2» a b =
          .ok (.tuple #[.atom "gt", a, .tuple #[.integer h, lb, c, u, d]]) ∧ Split b lb c u d := by
      have top : Bdd (fun _ => True) (.atom "bdd_top") := by simp [Bdd]
      have bot : Bdd (fun _ => True) (.atom "bdd_bot") := by simp [Bdd]
      unfold Elixir.Module.Types.Descr.«bdd_compare/2»
      rcases head_some wb hb with ⟨k, x, y, rfl, rfl⟩ | ⟨n, c, u, d, rfl⟩
      · obtain ⟨h, run⟩ := node_new (.tuple #[.integer k, x, y]) _ _ _ ⟨k, x, y, rfl⟩ top bot bot
        refine ⟨h, _, _, _, ?_, Or.inr ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩⟩
        rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
          simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», gt, Lynx.Except.guard, run]
      · refine ⟨n, c, u, d, ?_, Or.inl ⟨n, rfl⟩⟩
        rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
          simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», gt, Lynx.Except.guard]

    /-- The literal `bdd_compare/2` reads of a BDD. -/
    theorem compare_eq {a b la lb : Term} (ha : head a = some la) (hb : head b = some lb)
        (eq : compare la lb = .eq) :
        Elixir.Module.Types.Descr.«bdd_compare/2» a b = .ok (.tuple #[.atom "eq", a, b]) := by
      unfold Elixir.Module.Types.Descr.«bdd_compare/2»
      rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
        rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
        simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», eq, Lynx.Except.guard]

    /-! Semantics. -/

    /-- Valuations give equal literals the same truth. -/
    def Resp (ρ : Term → Bool) : Prop := ∀ a b, compare a b = .eq → ρ a = ρ b

    @[simp] theorem eval_top (ρ : Term → Bool) : eval ρ (.atom "bdd_top") = Bool.true := by simp [eval]
    @[simp] theorem eval_bot (ρ : Term → Bool) : eval ρ (.atom "bdd_bot") = Bool.false := by simp [eval]
    @[simp] theorem eval_node (ρ : Term → Bool) (h lit c u d : Term) :
        eval ρ (.tuple #[h, lit, c, u, d]) = ((ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)) := by
      simp [eval]
    @[simp] theorem eval_leaf (ρ : Term → Bool) (k x y : Term) :
        eval ρ (.tuple #[k, x, y]) = ρ (.tuple #[k, x, y]) := by
      simp [eval]

    theorem Split.eval {a lit c u d : Term} (split : Split a lit c u d) (ρ : Term → Bool) :
        eval ρ a = ((ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)) := by
      rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩
      · simp
      · cases h : ρ (.tuple #[.integer k, x, y]) <;> simp [h]

    theorem tuple3_exact {a₀ a₁ a₂ b : Term} (e : exactCompare (.tuple #[a₀, a₁, a₂]) b = .eq) :
        ∃ b₀ b₁ b₂, b = .tuple #[b₀, b₁, b₂] ∧ exactCompare a₀ b₀ = .eq ∧ exactCompare a₁ b₁ = .eq ∧
          exactCompare a₂ b₂ = .eq := by
      rw [exactCompare_eq_step] at e
      cases b <;> simp [Compare.compareStep] at e
      rename_i ys
      obtain ⟨ys⟩ := ys
      rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, rest⟩⟩⟩⟩ <;>
        simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
          List.compareLex_nil_cons] at e
      · exact ⟨b₀, b₁, b₂, rfl, e.1, e.2.1, e.2.2⟩

    theorem tuple5_exact {a₀ a₁ a₂ a₃ a₄ b : Term} (e : exactCompare (.tuple #[a₀, a₁, a₂, a₃, a₄]) b = .eq) :
        ∃ b₀ b₁ b₂ b₃ b₄, b = .tuple #[b₀, b₁, b₂, b₃, b₄] ∧ exactCompare a₁ b₁ = .eq ∧
          exactCompare a₂ b₂ = .eq ∧ exactCompare a₃ b₃ = .eq ∧ exactCompare a₄ b₄ = .eq := by
      rw [exactCompare_eq_step] at e
      cases b <;> simp [Compare.compareStep] at e
      rename_i ys
      obtain ⟨ys⟩ := ys
      rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, rest⟩⟩⟩⟩⟩⟩ <;>
        simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
          List.compareLex_nil_cons] at e
      · exact ⟨b₀, b₁, b₂, b₃, b₄, rfl, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2⟩

    /-- Exactly equal BDDs have the same semantics. -/
    theorem eval_congr {ok : Term → Prop} {a : Term} (wa : Bdd ok a) {ρ : Term → Bool} (resp : Resp ρ) :
        ∀ {b}, exactCompare a b = .eq → eval ρ a = eval ρ b := by
      refine Bdd.induction (P := fun _ a => ∀ {b}, exactCompare a b = .eq → eval ρ a = eval ρ b)
        ?_ ?_ ?_ ?_ ok a wa
      · intro _ b e
        obtain rfl := (exactCompare_eq_atom b "bdd_top").mp (Std.OrientedCmp.eq_symm e)
        rfl
      · intro _ b e
        obtain rfl := (exactCompare_eq_atom b "bdd_bot").mp (Std.OrientedCmp.eq_symm e)
        rfl
      · intro _ k x y _ b e
        obtain ⟨b₀, b₁, b₂, rfl, -, -, -⟩ := tuple3_exact e
        simp only [eval_leaf]
        exact resp _ _ (compare_eq_of_exactCompare_eq _ _ e)
      · intro _ h lit c u d _ _ _ _ _ ihc ihu ihd b e
        obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl, el, ec, eu, ed⟩ := tuple5_exact e
        simp only [eval_node]
        rw [resp _ _ (compare_eq_of_exactCompare_eq _ _ el), ihc ec, ihu eu, ihd ed]

    theorem head_ok {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) : ok l := by
      rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨h, c, u, d, rfl⟩
      · exact Bdd.leaf_iff.mp wa
      · exact (Bdd.node_iff.mp wa).2.1

    theorem head_leaf {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) : IsLeaf l := by
      rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨h, c, u, d, rfl⟩
      · exact ⟨k, x, y, rfl⟩
      · exact (Bdd.node_iff.mp wa).1

    /-- The children of a split BDD hold literals above its head. -/
    theorem Split.children {ok : Term → Prop} {a lit c u d : Term} (split : Split a lit c u d) (wa : Bdd ok a) :
        Bdd (Above ok lit) c ∧ Bdd (Above ok lit) u ∧ Bdd (Above ok lit) d := by
      rcases split with ⟨h, rfl⟩ | ⟨rfl, _, rfl, rfl, rfl⟩
      · exact (Bdd.node_iff.mp wa).2.2
      · simp [Bdd]

    /-! Termination: each recursive call raises the smallest literal of its arguments. -/

    /-- All literals of `b` are above `m`. -/
    abbrev High (m : Term) : Term → Prop := Bdd (fun t => Term.compare m t = .lt)

    open Classical in
    /-- The literals of the universe that some argument does not exceed. -/
    noncomputable def μ (U : List Term) (a b : Term) : Nat :=
      (U.filter fun m => !decide (High m a ∧ High m b)).length

    theorem filter_le {α} (U : List α) (p q : α → Bool) (h : ∀ x ∈ U, p x → q x) :
        (U.filter p).length ≤ (U.filter q).length := by
      induction U with
      | nil => simp
      | cons x xs ih =>
        have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
        by_cases px : p x <;> by_cases qx : q x <;> simp [List.filter_cons, px, qx] <;>
          first | omega | (have := h x List.mem_cons_self px; simp_all)

    theorem filter_lt {α} (U : List α) (p q : α → Bool) (h : ∀ x ∈ U, p x → q x) {l : α} (hl : l ∈ U)
        (hp : p l = Bool.false) (hq : q l = Bool.true) : (U.filter p).length < (U.filter q).length := by
      induction U with
      | nil => simp at hl
      | cons x xs ih =>
        have le := filter_le xs p q (fun y hy => h y (List.mem_cons_of_mem _ hy))
        rcases List.mem_cons.mp hl with rfl | hl
        · simp [List.filter_cons, hp, hq]; omega
        · have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hl
          by_cases px : p x <;> by_cases qx : q x <;> simp [List.filter_cons, px, qx] <;>
            first | omega | (have := h x List.mem_cons_self px; simp_all)

    theorem μ_le {U : List Term} {a b a' b' : Term}
        (mono : ∀ m, High m a → High m b → High m a' ∧ High m b') : μ U a' b' ≤ μ U a b := by
      unfold μ
      apply filter_le
      intro m _ hm
      simp at hm ⊢
      intro ha hb
      exact hm (mono m ha hb).1 (mono m ha hb).2

    theorem μ_lt {U : List Term} {a b a' b' l : Term}
        (mono : ∀ m, High m a → High m b → High m a' ∧ High m b') (hl : l ∈ U)
        (old : ¬(High l a ∧ High l b)) (new : High l a' ∧ High l b') : μ U a' b' < μ U a b := by
      unfold μ
      refine filter_lt _ _ _ ?_ hl ?_ ?_
      · intro m _ hm
        simp at hm ⊢
        intro ha hb
        exact hm (mono m ha hb).1 (mono m ha hb).2
      · simp [new]
      · simp
        exact fun ha hb => old ⟨ha, hb⟩

    /-- A BDD is never above its own head. -/
    theorem not_high_head {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) : ¬High l a :=
      fun high => by have := head_ok high ha; simp at this

    /-! BDDs without leaves, whose literals all sit in nodes. -/

    def NoLeaf : Term → Prop
      | .atom "bdd_top" => True
      | .atom "bdd_bot" => True
      | .tuple ⟨[_, _, c, u, d]⟩ => NoLeaf c ∧ NoLeaf u ∧ NoLeaf d
      | _ => False

    theorem NoLeaf.top : NoLeaf (.atom "bdd_top") := by simp [NoLeaf]
    theorem NoLeaf.bot : NoLeaf (.atom "bdd_bot") := by simp [NoLeaf]

    theorem NoLeaf.node {h lit c u d : Term} : NoLeaf (.tuple #[h, lit, c, u, d]) ↔ NoLeaf c ∧ NoLeaf u ∧ NoLeaf d := by
      simp [NoLeaf]

    theorem NoLeaf.leaf {k x y : Term} (n : NoLeaf (.tuple #[k, x, y])) : False := by
      simp [NoLeaf] at n

    theorem Split.noLeaf {a lit c u d : Term} (split : Split a lit c u d) (n : NoLeaf a) :
        NoLeaf c ∧ NoLeaf u ∧ NoLeaf d := by
      rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, -⟩
      · exact NoLeaf.node.mp n
      · exact n.leaf.elim

    /-! Unions. -/

    def UnionOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_union/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a || eval ρ b)

    def RemoveOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_remove/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)

    /-- What unions and removals guarantee, including that they keep BDDs without leaves. -/
    def UnionOkN (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_union/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → eval ρ r = (eval ρ a || eval ρ b)) ∧
          (NoLeaf a → NoLeaf b → NoLeaf r)

    def RemoveOkN (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_remove/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)) ∧
          (NoLeaf a → NoLeaf b → NoLeaf r)

    def RemoveBddOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_remove_bdd/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)) ∧
          (NoLeaf a → NoLeaf b → NoLeaf r)

    /-- Every pair of BDDs over the universe below the measure `n` unites and removes. -/
    def Below (U : List Term) (n : Nat) : Prop :=
      ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → UnionOkN a b ∧ RemoveOkN a b ∧ RemoveBddOk a b

    theorem Bdd.top {ok : Term → Prop} : Bdd ok (.atom "bdd_top") := by simp [Bdd]
    theorem Bdd.bot {ok : Term → Prop} : Bdd ok (.atom "bdd_bot") := by simp [Bdd]

    theorem nontrivial_head {ok : Term → Prop} {a : Term} (wa : Bdd ok a) (t : a ≠ .atom "bdd_top")
        (f : a ≠ .atom "bdd_bot") : ∃ l, head a = some l := by
      rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · exact absurd rfl t
      · exact absurd rfl f
      · exact ⟨.tuple #[.integer k, x, y], by simp [head]⟩
      · exact ⟨lit, by simp [head]⟩

    /-- Arguments above `m` keep the result above `m`. -/
    theorem High.split {ok : Term → Prop} {a lit c u d m : Term} (split : Split a lit c u d) (wa : Bdd ok a)
        (high : High m a) : High m c ∧ High m u ∧ High m d := by
      obtain ⟨hc, hu, hd⟩ := split.children high
      exact ⟨hc.mono fun _ h => h.1, hu.mono fun _ h => h.1, hd.mono fun _ h => h.1⟩

    theorem Split.high {ok : Term → Prop} {a lit c u d : Term} (split : Split a lit c u d) (wa : Bdd ok a) :
        High lit c ∧ High lit u ∧ High lit d := by
      obtain ⟨hc, hu, hd⟩ := split.children wa
      exact ⟨hc.mono fun _ h => h.2, hu.mono fun _ h => h.2, hd.mono fun _ h => h.2⟩

    theorem Split.head {a lit c u d : Term} (split : Split a lit c u d) : head a = some lit := by
      rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, -⟩ <;> simp [BddProofs.head]

    theorem Bdd.within {ok : Term → Prop} {b : Term} (wb : Bdd ok b) : Bdd (fun _ => True) b :=
      wb.mono fun _ _ => trivial

    theorem Bdd.congr {ok : Term → Prop} {x la lb : Term} (e : Term.compare la lb = .eq)
        (w : Bdd (Above ok lb) x) : Bdd (Above ok la) x :=
      w.mono fun t h => ⟨h.1, by rw [Std.TransCmp.congr_left e]; exact h.2⟩

    theorem High.congr {x la lb : Term} (e : Term.compare la lb = .eq) (w : High lb x) : High la x :=
      w.mono fun t h => by rw [Std.TransCmp.congr_left e]; exact h

    theorem union_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
        (ih : Below U (μ U a b)) : UnionOkN a b := by
      by_cases same : exactCompare b a = .eq
      · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_, fun na _ => na⟩
        · unfold Elixir.Module.Types.Descr.«bdd_union/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [← eval_congr wb resp same]; simp
      by_cases ta : a = .atom "bdd_top"
      · subst ta
        refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp, fun _ _ => NoLeaf.top⟩
        unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases tb : b = .atom "bdd_top"
      · subst tb
        refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp, fun _ _ => NoLeaf.top⟩
        unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fa : a = .atom "bdd_bot"
      · subst fa
        refine ⟨b, ?_, fun ok _ wb => wb, fun ρ _ => by simp, fun _ nb => nb⟩
        unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fb : b = .atom "bdd_bot"
      · subst fb
        refine ⟨a, ?_, fun ok wa _ => wa, fun ρ _ => by simp, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
      obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
      have lU : la ∈ U := head_ok wa ha
      have lbU : lb ∈ U := head_ok wb hb
      have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
          High la a' ∧ High la b' → μ U a' b' < μ U a b :=
        fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
      rcases order : Term.compare la lb
      · -- lt
        obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
        have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
          fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
        obtain ⟨hc, hu, hd⟩ := split.children wa
        obtain ⟨Hc, Hu, Hd⟩ := split.high wa
        have HB : High la b := (raiseB wb).mono fun _ h => h.2
        obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ b (hc.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)).2.1
        obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ b (hu.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)).1
        obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ b (hd.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)).2.1
        obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc (raiseB wb))
          (keep₂ _ hu (raiseB wb)) (keep₃ _ hd (raiseB wb))
        have body : Elixir.Module.Types.Descr.«bdd_union/2» a b =
            if exactCompare r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
            else .ok (.tuple #[.integer h₁, la, r₁, r₂, r₃]) := by
          conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
          simp [run, run₁, run₂, run₃, node]
          by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
        by_cases post : exactCompare r₃ r₁ = .eq
        · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wb)
            (keep₂ _ (hu.mono fun _ h => h.1) wb)
            (lower (fun m ha' hb' => ⟨keep₁ _ (High.split split wa ha').1 hb', keep₂ _ (High.split split wa ha').2.1 hb'⟩)
              ⟨keep₁ _ Hc HB, keep₂ _ Hu HB⟩)).1
          refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_,
            fun na nb => nlr (nl₁ (split.noLeaf na).1 nb) (nl₂ (split.noLeaf na).2.1 nb)⟩
          · obtain ⟨oc, ou, -⟩ := split.children oka
            exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) okb) (keep₂ ok (ou.mono fun _ h => h.1) okb)
          · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wb) resp post
            have s₁ := sem₁ ρ resp
            have s₂ := sem₂ ρ resp
            have s₃ := sem₃ ρ resp
            rw [semr ρ resp, split.eval ρ, s₂]
            rw [← e₃] at s₁
            cases hB : eval ρ b <;> cases hl : ρ la <;> simp_all [Bool.or_comm, Bool.or_left_comm]
        · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_,
            fun na nb => NoLeaf.node.mpr ⟨nl₁ (split.noLeaf na).1 nb, nl₂ (split.noLeaf na).2.1 nb,
              nl₃ (split.noLeaf na).2.2 nb⟩⟩
          · obtain ⟨oc, ou, od⟩ := split.children oka
            exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc (raiseB okb),
              keep₂ _ ou (raiseB okb), keep₃ _ od (raiseB okb)⟩
          · have s₁ := sem₁ ρ resp
            have s₂ := sem₂ ρ resp
            have s₃ := sem₃ ρ resp
            rw [eval_node, split.eval ρ, s₂]
            cases hB : eval ρ b <;> cases hl : ρ la <;> simp_all [Bool.or_comm, Bool.or_left_comm]
      · -- eq
        have run := compare_eq ha hb order
        have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
            High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
          fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
        have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
        rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
          rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
        · -- two leaves
          refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
          · unfold Elixir.Module.Types.Descr.«bdd_union/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run]
          · simp [sameLit ρ resp]
        · -- a leaf below a node
          obtain ⟨-, -, hc, hu, hd⟩ := Bdd.node_iff.mp wb
          have Hu : High lb u₂ := hu.mono fun _ h => h.2
          have Hd : High lb d₂ := hd.mono fun _ h => h.2
          obtain ⟨h₃, node⟩ := node_new lb (.atom "bdd_top") u₂ d₂ (head_leaf wb hb) (Bdd.top (ok := fun _ => True)) hu hd
          have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k₁, x₁, y₁])
              (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
              if exactCompare d₂ (.atom "bdd_top") = .eq then
                Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_top") u₂
              else .ok (.tuple #[.integer h₃, lb, .atom "bdd_top", u₂, d₂]) := by
            conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, node]
            by_cases post : exactCompare d₂ (.atom "bdd_top") = .eq <;> simp [post]
          by_cases post : exactCompare d₂ (.atom "bdd_top") = .eq
          · obtain rfl := (exactCompare_eq_atom _ _).mp post
            obtain ⟨r, runr, keepr, semr, -⟩ := (ih (.atom "bdd_top") u₂ Bdd.top (hu.mono fun _ h => h.1)
              (lowerB (fun m _ hb' => ⟨Bdd.top, (High.split (Or.inl ⟨h₂, rfl⟩) wb hb').2.1⟩) ⟨Bdd.top, Hu⟩)).1
            refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok _ okb => ?_,
              fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
            · exact keepr ok Bdd.top ((Bdd.node_iff.mp okb).2.2.2.1.mono fun _ h => h.1)
            · rw [semr ρ resp]
              cases hl : ρ lb <;> simp [hl, sameLit ρ resp]
          · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok _ okb => ?_,
              fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
            · obtain ⟨leaf, okl, -, ou, od⟩ := Bdd.node_iff.mp okb
              exact Bdd.node_iff.mpr ⟨leaf, okl, Bdd.top, ou, od⟩
            · cases hl : ρ lb <;> simp [hl, sameLit ρ resp]
        · -- a node above a leaf
          obtain ⟨-, -, hc, hu, hd⟩ := Bdd.node_iff.mp wa
          have Hu : High la u₁ := hu.mono fun _ h => h.2
          obtain ⟨h₃, node⟩ := node_new la (.atom "bdd_top") u₁ d₁ (head_leaf wa ha) (Bdd.top (ok := fun _ => True)) hu hd
          have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer h₁, la, c₁, u₁, d₁])
              (.tuple #[.integer k₂, x₂, y₂]) =
              if exactCompare d₁ (.atom "bdd_top") = .eq then
                Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_top") u₁
              else .ok (.tuple #[.integer h₃, la, .atom "bdd_top", u₁, d₁]) := by
            conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, node]
            by_cases post : exactCompare d₁ (.atom "bdd_top") = .eq <;> simp [post]
          by_cases post : exactCompare d₁ (.atom "bdd_top") = .eq
          · obtain rfl := (exactCompare_eq_atom _ _).mp post
            obtain ⟨r, runr, keepr, semr, -⟩ := (ih (.atom "bdd_top") u₁ Bdd.top (hu.mono fun _ h => h.1)
              (lower (fun m ha' _ => ⟨Bdd.top, (High.split (Or.inl ⟨h₁, rfl⟩) wa ha').2.1⟩) ⟨Bdd.top, Hu⟩)).1
            refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka _ => ?_,
              fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
            · exact keepr ok Bdd.top ((Bdd.node_iff.mp oka).2.2.2.1.mono fun _ h => h.1)
            · rw [semr ρ resp]
              cases hl : ρ la <;> simp [hl, ← sameLit ρ resp]
          · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka _ => ?_,
              fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
            · obtain ⟨leaf, okl, -, ou, od⟩ := Bdd.node_iff.mp oka
              exact Bdd.node_iff.mpr ⟨leaf, okl, Bdd.top, ou, od⟩
            · cases hl : ρ la <;> simp [hl, ← sameLit ρ resp]
        · -- two nodes
          have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
          have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
          obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
          obtain ⟨hc₂, hu₂, hd₂⟩ := splitB.children wb
          obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
          obtain ⟨Hc₂, Hu₂, Hd₂⟩ := splitB.high wb
          obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
            (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
              ⟨Hc₁, Hc₂.congr order⟩)).1
          obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ u₂ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1)
            (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, (High.split splitB wb hb').2.1⟩)
              ⟨Hu₁, Hu₂.congr order⟩)).1
          obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
            (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, (High.split splitB wb hb').2.2⟩)
              ⟨Hd₁, Hd₂.congr order⟩)).1
          obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc₁ (hc₂.congr order))
            (keep₂ _ hu₁ (hu₂.congr order)) (keep₃ _ hd₁ (hd₂.congr order))
          have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer h₁, la, c₁, u₁, d₁])
              (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
              if exactCompare r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
              else .ok (.tuple #[.integer h₃, la, r₁, r₂, r₃]) := by
            conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
            by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
          by_cases post : exactCompare r₃ r₁ = .eq
          · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
              (keep₂ _ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1))
              (lower (fun m ha' hb' => ⟨keep₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
                keep₂ _ (High.split splitA wa ha').2.1 (High.split splitB wb hb').2.1⟩)
                ⟨keep₁ _ Hc₁ (Hc₂.congr order), keep₂ _ Hu₁ (Hu₂.congr order)⟩)).1
            refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_,
              fun ρ resp => ?_, fun na nb => nlr (nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1)
                (nl₂ (NoLeaf.node.mp na).2.1 (NoLeaf.node.mp nb).2.1)⟩
            · obtain ⟨oc₁, ou₁, -⟩ := splitA.children oka
              obtain ⟨oc₂, ou₂, -⟩ := splitB.children okb
              exact keepr ok (keep₁ ok (oc₁.mono fun _ h => h.1) (oc₂.mono fun _ h => h.1))
                (keep₂ ok (ou₁.mono fun _ h => h.1) (ou₂.mono fun _ h => h.1))
            · have e₃ := eval_congr (keep₃ _ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)) resp post
              have s₁ := sem₁ ρ resp
              have s₂ := sem₂ ρ resp
              have s₃ := sem₃ ρ resp
              rw [semr ρ resp, eval_node, eval_node, s₁, s₂, ← sameLit ρ resp]
              rw [e₃, s₁] at s₃
              revert s₃
              generalize ρ la = L
              generalize eval ρ c₁ = C₁
              generalize eval ρ c₂ = C₂
              generalize eval ρ d₁ = D₁
              generalize eval ρ d₂ = D₂
              generalize eval ρ u₁ = U₁
              generalize eval ρ u₂ = U₂
              revert L C₁ C₂ D₁ D₂ U₁ U₂
              decide
          · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_,
              fun ρ resp => ?_, fun na nb => NoLeaf.node.mpr ⟨nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1,
                nl₂ (NoLeaf.node.mp na).2.1 (NoLeaf.node.mp nb).2.1, nl₃ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2⟩⟩
            · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
              obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
              exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc₁ (oc₂.congr order),
                keep₂ _ ou₁ (ou₂.congr order), keep₃ _ od₁ (od₂.congr order)⟩
            · rw [eval_node, eval_node, eval_node, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, ← sameLit ρ resp]
              cases ρ la <;> simp [Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
      · -- gt
        have order' : Term.compare lb la = .lt := Std.OrientedCmp.lt_of_gt order
        obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
        have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
            High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
          fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
        have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
          fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
        obtain ⟨hc, hu, hd⟩ := split.children wb
        obtain ⟨Hc, Hu, Hd⟩ := split.high wb
        have HA : High lb a := (raiseA wa).mono fun _ h => h.2
        obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₂ a (hc.mono fun _ h => h.1) wa
          (lowerB (fun m ha' hb' => ⟨(High.split split wb hb').1, ha'⟩) ⟨Hc, HA⟩)).2.1
        obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih a u₂ wa (hu.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)).1
        obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₂ a (hd.mono fun _ h => h.1) wa
          (lowerB (fun m ha' hb' => ⟨(High.split split wb hb').2.2, ha'⟩) ⟨Hd, HA⟩)).2.1
        obtain ⟨h₁, node⟩ := node_new lb r₁ r₂ r₃ (head_leaf wb hb) (keep₁ _ hc (raiseA wa))
          (keep₂ _ (raiseA wa) hu) (keep₃ _ hd (raiseA wa))
        have body : Elixir.Module.Types.Descr.«bdd_union/2» a b =
            if exactCompare r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
            else .ok (.tuple #[.integer h₁, lb, r₁, r₂, r₃]) := by
          conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
          simp [run, run₁, run₂, run₃, node]
          by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
        by_cases post : exactCompare r₃ r₁ = .eq
        · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wa)
            (keep₂ _ wa (hu.mono fun _ h => h.1))
            (lowerB (fun m ha' hb' => ⟨keep₁ _ (High.split split wb hb').1 ha', keep₂ _ ha' (High.split split wb hb').2.1⟩)
              ⟨keep₁ _ Hc HA, keep₂ _ HA Hu⟩)).1
          refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_,
            fun na nb => nlr (nl₁ (split.noLeaf nb).1 na) (nl₂ na (split.noLeaf nb).2.1)⟩
          · obtain ⟨oc, ou, -⟩ := split.children okb
            exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) oka) (keep₂ ok oka (ou.mono fun _ h => h.1))
          · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wa) resp post
            have s₁ := sem₁ ρ resp
            have s₂ := sem₂ ρ resp
            have s₃ := sem₃ ρ resp
            rw [semr ρ resp, split.eval ρ, s₂]
            rw [← e₃] at s₁
            cases hA : eval ρ a <;> cases hl : ρ lb <;> simp_all [Bool.or_comm, Bool.or_left_comm]
        · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_,
            fun na nb => NoLeaf.node.mpr ⟨nl₁ (split.noLeaf nb).1 na, nl₂ na (split.noLeaf nb).2.1,
              nl₃ (split.noLeaf nb).2.2 na⟩⟩
          · obtain ⟨oc, ou, od⟩ := split.children okb
            exact Bdd.node_iff.mpr ⟨head_leaf wb hb, head_ok okb hb, keep₁ _ oc (raiseA oka),
              keep₂ _ (raiseA oka) ou, keep₃ _ od (raiseA oka)⟩
          · have s₁ := sem₁ ρ resp
            have s₂ := sem₂ ρ resp
            have s₃ := sem₃ ρ resp
            rw [eval_node, split.eval ρ, s₂]
            cases hA : eval ρ a <;> cases hl : ρ lb <;> simp_all [Bool.or_comm, Bool.or_left_comm]

    theorem Below.mono {U : List Term} {n m : Nat} (le : m ≤ n) (below : Below U n) : Below U m :=
      fun a b wa wb lt => below a b wa wb (by omega)

    /-- Removing a BDD from another one that is not a node above it. -/
    theorem remove_bdd_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
        (ih : Below U (μ U a b)) : RemoveBddOk a b := by
      by_cases same : exactCompare b a = .eq
      · refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ resp => ?_, fun _ _ => NoLeaf.bot⟩
        · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [eval_congr wb resp same]; simp
      rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₁, la, c₁, u₁, d₁, rfl⟩
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      have ha : head (.tuple #[.integer h₁, la, c₁, u₁, d₁]) = some la := by simp [head]
      have hb : head (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) = some lb := by simp [head]
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      have lU : la ∈ U := head_ok wa ha
      have lbU : lb ∈ U := head_ok wb hb
      have lower : ∀ {a' b'}, (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) → High m a' ∧ High m b') →
          High la a' ∧ High la b' → μ U a' b' < μ U (.tuple #[.integer h₁, la, c₁, u₁, d₁]) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
        fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
      have lowerB : ∀ {a' b'}, (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) → High m a' ∧ High m b') →
          High lb a' ∧ High lb b' → μ U a' b' < μ U (.tuple #[.integer h₁, la, c₁, u₁, d₁]) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
        fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
      obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
      obtain ⟨hc₂, hu₂, hd₂⟩ := splitB.children wb
      obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
      obtain ⟨Hc₂, Hu₂, Hd₂⟩ := splitB.high wb
      rcases order : Term.compare la lb
      · -- lt: remove the right BDD from each branch
        have raiseB : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
            Bdd (Above ok la) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
          fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
        have HB := (raiseB wb).mono fun _ h => h.2
        obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ _ (hc₁.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, hb'⟩) ⟨Hc₁, HB⟩)).2.2
        obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ _ (hu₁.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, hb'⟩) ⟨Hu₁, HB⟩)).2.2
        obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ _ (hd₁.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, hb'⟩) ⟨Hd₁, HB⟩)).2.2
        obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc₁ (raiseB wb))
          (keep₂ _ hu₁ (raiseB wb)) (keep₃ _ hd₁ (raiseB wb))
        refine ⟨.tuple #[.integer h₃, la, r₁, r₂, r₃], ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
          fun na nb => NoLeaf.node.mpr ⟨nl₁ (NoLeaf.node.mp na).1 nb, nl₂ (NoLeaf.node.mp na).2.1 nb,
            nl₃ (NoLeaf.node.mp na).2.2 nb⟩⟩
        · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», order, run₁, run₂, run₃, node]
        · obtain ⟨oc, ou, od⟩ := splitA.children oka
          exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc (raiseB okb),
            keep₂ _ ou (raiseB okb), keep₃ _ od (raiseB okb)⟩
        · have s₁ := sem₁ ρ resp
          have s₂ := sem₂ ρ resp
          have s₃ := sem₃ ρ resp
          simp only [eval_node] at s₁ s₂ s₃ ⊢
          revert s₁ s₂ s₃
          generalize ρ la = L
          generalize ρ lb = L'
          generalize eval ρ c₂ = C₂
          generalize eval ρ u₂ = U₂
          generalize eval ρ d₂ = D₂
          generalize eval ρ c₁ = C₁
          generalize eval ρ u₁ = U₁
          generalize eval ρ d₁ = D₁
          generalize eval ρ r₁ = R₁
          generalize eval ρ r₂ = R₂
          generalize eval ρ r₃ = R₃
          revert L L' C₂ U₂ D₂ C₁ U₁ D₁ R₁ R₂ R₃
          decide
      · -- eq: remove each branch, and the union branch of the right BDD
        obtain ⟨x₁, runx₁, keepx₁, semx₁, nlx₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
            ⟨Hc₁, Hc₂.congr order⟩)).2.1
        obtain ⟨x₂, runx₂, keepx₂, semx₂, nlx₂⟩ := (ih x₁ u₂ (keepx₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
          (hu₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨keepx₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
            (High.split splitB wb hb').2.1⟩) ⟨keepx₁ _ Hc₁ (Hc₂.congr order), Hu₂.congr order⟩)).2.1
        obtain ⟨y₁, runy₁, keepy₁, semy₁, nly₁⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, (High.split splitB wb hb').2.2⟩)
            ⟨Hd₁, Hd₂.congr order⟩)).2.1
        obtain ⟨y₂, runy₂, keepy₂, semy₂, nly₂⟩ := (ih y₁ u₂ (keepy₁ _ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1))
          (hu₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨keepy₁ _ (High.split splitA wa ha').2.2 (High.split splitB wb hb').2.2,
            (High.split splitB wb hb').2.1⟩) ⟨keepy₁ _ Hd₁ (Hd₂.congr order), Hu₂.congr order⟩)).2.1
        have bx := keepx₂ _ (keepx₁ _ hc₁ (hc₂.congr order)) (hu₂.congr order)
        have byy := keepy₂ _ (keepy₁ _ hd₁ (hd₂.congr order)) (hu₂.congr order)
        obtain ⟨h₃, node⟩ := node_new la x₂ u₁ y₂ (head_leaf wa ha) bx hu₁ byy
        refine ⟨.tuple #[.integer h₃, la, x₂, u₁, y₂], ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
          fun na nb => NoLeaf.node.mpr ⟨nlx₂ (nlx₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1) (NoLeaf.node.mp nb).2.1,
            (NoLeaf.node.mp na).2.1, nly₂ (nly₁ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2) (NoLeaf.node.mp nb).2.1⟩⟩
        · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», Erlang.erlang.«>/2», order,
            runx₁, runx₂, runy₁, runy₂, node]
        · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
          exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha,
            keepx₂ _ (keepx₁ _ oc₁ (oc₂.congr order)) (ou₂.congr order), ou₁,
            keepy₂ _ (keepy₁ _ od₁ (od₂.congr order)) (ou₂.congr order)⟩
        · have s₁ := semx₁ ρ resp
          have s₂ := semx₂ ρ resp
          have s₃ := semy₁ ρ resp
          have s₄ := semy₂ ρ resp
          have l := resp _ _ order
          simp only [eval_node]
          revert s₁ s₂ s₃ s₄ l
          generalize ρ la = L
          generalize ρ lb = L'
          generalize eval ρ c₂ = C₂
          generalize eval ρ u₂ = U₂
          generalize eval ρ d₂ = D₂
          generalize eval ρ c₁ = C₁
          generalize eval ρ u₁ = U₁
          generalize eval ρ d₁ = D₁
          generalize eval ρ x₁ = X₁
          generalize eval ρ x₂ = X₂
          generalize eval ρ y₁ = Y₁
          generalize eval ρ y₂ = Y₂
          revert L L' C₂ U₂ D₂ C₁ U₁ D₁ X₁ X₂ Y₁ Y₂
          decide
      · -- gt: what the right BDD always removes
        have order' : Term.compare lb la = .lt := Std.OrientedCmp.lt_of_gt order
        have raiseA : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h₁, la, c₁, u₁, d₁]) →
            Bdd (Above ok lb) (.tuple #[.integer h₁, la, c₁, u₁, d₁]) :=
          fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
        have HA := (raiseA wa).mono fun _ h => h.2
        obtain ⟨r, run, keep, sem, nl⟩ := (ih _ u₂ wa (hu₂.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split splitB wb hb').2.1⟩) ⟨HA, Hu₂⟩)).2.1
        refine ⟨r, ?_, fun ok oka okb => keep ok oka ((splitB.children okb).2.1.mono fun _ h => h.1),
          fun ρ resp => ?_, fun na nb => nl na (NoLeaf.node.mp nb).2.1⟩
        · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
          have notLt : Term.compare la lb ≠ .lt := by rw [order]; decide
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», Erlang.erlang.«>/2», order, run]
        · have s := sem ρ resp
          rw [eval_node]
          revert s
          generalize eval ρ (.tuple #[.integer h₁, la, c₁, u₁, d₁]) = A
          generalize ρ lb = L
          generalize eval ρ c₂ = C₂
          generalize eval ρ u₂ = U₂
          generalize eval ρ d₂ = D₂
          generalize eval ρ r = R
          revert A L C₂ U₂ D₂ R
          decide

    /-- Removing a BDD from another one. -/
    theorem remove_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
        (ih : Below U (μ U a b)) : RemoveOkN a b := by
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
        simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
      · refine ⟨a, ?_, fun _ oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
      · -- removing a leaf
        have leafRun : Elixir.Module.Types.Descr.«bdd_remove/2» a (.tuple #[.integer k, x, y]) =
            Elixir.Module.Types.Descr.«bdd_remove_leaf/2» a (.tuple #[.integer k, x, y]) := by
          simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
        have fallback : ¬(∃ (h : Int) (la c u d : Term), a = .tuple #[.integer h, la, c, u, d] ∧
            exactCompare (.tuple #[.integer k, x, y]) la = .eq) → RemoveOkN a (.tuple #[.integer k, x, y]) := by
          intro notFirst
          have run : Elixir.Module.Types.Descr.«bdd_remove_leaf/2» a (.tuple #[.integer k, x, y]) =
              if exactCompare (.tuple #[.integer k, x, y]) a = .eq then .ok (.atom "bdd_bot") else .ok a := by
            unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
            rcases wa.shape with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨h, la, c, u, d, rfl⟩
            · by_cases same : exactCompare (.tuple #[.integer k, x, y]) (.atom "bdd_top") = .eq <;>
                simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
            · by_cases same : exactCompare (.tuple #[.integer k, x, y]) (.atom "bdd_bot") = .eq <;>
                simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
            · rename_i k' x' y'
              by_cases same : exactCompare (.tuple #[.integer k, x, y]) (.tuple #[.integer k', x', y']) = .eq <;>
                simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
            · have ne : ¬exactCompare (.tuple #[.integer k, x, y]) la = .eq := fun e => notFirst ⟨h, la, c, u, d, rfl, e⟩
              by_cases same : exactCompare (.tuple #[.integer k, x, y]) (.tuple #[.integer h, la, c, u, d]) = .eq <;>
                simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, ne]
          by_cases same : exactCompare (.tuple #[.integer k, x, y]) a = .eq
          · refine ⟨.atom "bdd_bot", by rw [leafRun, run, if_pos same], fun _ _ _ => Bdd.bot, fun ρ resp => ?_,
              fun _ _ => NoLeaf.bot⟩
            rw [eval_congr wb resp same]; simp
          · exact ⟨a, by rw [leafRun, run, if_neg same], fun _ oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
        by_cases first : ∃ (h : Int) (la c u d : Term), a = .tuple #[.integer h, la, c, u, d] ∧
            exactCompare (.tuple #[.integer k, x, y]) la = .eq
        · obtain ⟨h, la, c, u, d, rfl, e⟩ := first
          have ha : head (.tuple #[.integer h, la, c, u, d]) = some la := by simp [head]
          have splitA : Split _ la c u d := Or.inl ⟨h, rfl⟩
          obtain ⟨hc, hu, hd⟩ := splitA.children wa
          have wl : Bdd (· ∈ U) la := by
            obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
            exact Bdd.leaf_iff.mpr (head_ok wa ha)
          have highLit : ∀ {m}, High m (.tuple #[.integer h, la, c, u, d]) → High m la := fun high => by
            obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
            exact Bdd.leaf_iff.mpr (head_ok high ha)
          have okLit : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h, la, c, u, d]) → Bdd ok la := fun w => by
            obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
            exact Bdd.leaf_iff.mpr (head_ok w ha)
          obtain ⟨r₁, run₁, keep₁, sem₁, -⟩ := union_step U la u wl (hu.mono fun _ h => h.1)
            (ih.mono (μ_le fun m ha' _ => ⟨highLit ha', (High.split splitA wa ha').2.1⟩))
          have wr₁ := keep₁ _ wl (hu.mono fun _ h => h.1)
          obtain ⟨r₂, run₂, keep₂, sem₂, -⟩ := union_step U r₁ d wr₁ (hd.mono fun _ h => h.1)
            (ih.mono (μ_le fun m ha' _ =>
              ⟨keep₁ _ (highLit ha') (High.split splitA wa ha').2.1, (High.split splitA wa ha').2.2⟩))
          refine ⟨r₂, ?_, fun ok oka _ => ?_, fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
          · rw [leafRun]
            unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», e, run₁, run₂]
          · obtain ⟨-, ou, od⟩ := splitA.children oka
            exact keep₂ ok (keep₁ ok (okLit oka) (ou.mono fun _ h => h.1)) (od.mono fun _ h => h.1)
          · have l : ρ (.tuple #[.integer k, x, y]) = ρ la := resp _ _ (compare_eq_of_exactCompare_eq _ _ e)
            rw [sem₂ ρ resp, sem₁ ρ resp]
            obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
            simp only [eval_node, eval_leaf, l]
            cases ρ (.tuple #[.integer k', x', y']) <;> simp [Bool.or_comm, Bool.or_left_comm]
        · exact fallback first
      · have run : Elixir.Module.Types.Descr.«bdd_remove/2» a (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
            Elixir.Module.Types.Descr.«bdd_remove_bdd/2» a (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) := by
          simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
        obtain ⟨r, runr, keep, sem, nl⟩ := remove_bdd_step U a _ wa wb ih
        exact ⟨r, by rw [run, runr], keep, sem, nl⟩

    /-- Every pair of BDDs over a universe unites and removes. -/
    theorem below_all (U : List Term) : ∀ n, Below U n := by
      intro n
      induction n with
      | zero => intro a b _ _ lt; omega
      | succ n ih =>
        intro a b wa wb lt
        have ih' : Below U (μ U a b) := ih.mono (by omega)
        exact ⟨union_step U a b wa wb ih', remove_step U a b wa wb ih', remove_bdd_step U a b wa wb ih'⟩

    theorem Bdd.and {p q : Term → Prop} {b : Term} (hp : Bdd p b) (hq : Bdd q b) :
        Bdd (fun t => p t ∧ q t) b := by
      revert hq
      refine Bdd.induction (P := fun p b => ∀ {q}, Bdd q b → Bdd (fun t => p t ∧ q t) b) ?_ ?_ ?_ ?_ p b hp
      · intro _ _ _; exact Bdd.top
      · intro _ _ _; exact Bdd.bot
      · intro _ k x y okp q hq; exact Bdd.leaf_iff.mpr ⟨okp, Bdd.leaf_iff.mp hq⟩
      · intro p h lit c u d leaf okp _ _ _ ic iu id q hq
        obtain ⟨-, okq, qc, qu, qd⟩ := Bdd.node_iff.mp hq
        refine Bdd.node_iff.mpr ⟨leaf, ⟨okp, okq⟩, ?_, ?_, ?_⟩
        · exact (ic qc).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩
        · exact (iu qu).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩
        · exact (id qd).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩

    /-- The literals of a BDD. -/
    def lits : Term → List Term
      | .tuple ⟨[_, lit, c, u, d]⟩ => lit :: (lits c ++ lits u ++ lits d)
      | .tuple ⟨[k, x, y]⟩ => [.tuple #[k, x, y]]
      | _ => []

    theorem Bdd.lits {ok : Term → Prop} {a : Term} (wa : Bdd ok a) : Bdd (· ∈ BddProofs.lits a) a := by
      refine Bdd.induction (P := fun _ a => Bdd (· ∈ BddProofs.lits a) a) ?_ ?_ ?_ ?_ ok a wa
      · intro _; exact Bdd.top
      · intro _; exact Bdd.bot
      · intro _ k x y _; exact Bdd.leaf_iff.mpr (by simp [BddProofs.lits])
      · intro _ h lit c u d leaf _ hc hu hd ic iu id
        refine Bdd.node_iff.mpr ⟨leaf, by simp [BddProofs.lits], ?_, ?_, ?_⟩
        · exact (Bdd.and ic hc).mono fun t ht => ⟨by simp [BddProofs.lits, ht.1], ht.2.2⟩
        · exact (Bdd.and iu hu).mono fun t ht => ⟨by simp [BddProofs.lits, ht.1], ht.2.2⟩
        · exact (Bdd.and id hd).mono fun t ht => ⟨by simp [BddProofs.lits, ht.1], ht.2.2⟩

    theorem union_okN {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : UnionOkN a b :=
      let U := lits a ++ lits b
      (below_all U _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
        (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)).1

    theorem union_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : UnionOk a b :=
      let ⟨r, run, keep, sem, _⟩ := union_okN wa wb
      ⟨r, run, keep, sem⟩

    theorem remove_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : RemoveOk a b :=
      let U := lits a ++ lits b
      let ⟨r, run, keep, sem, _⟩ := (below_all U _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
        (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)).2.1
      ⟨r, run, keep, sem⟩

    /-! Intersections. -/

    /-- Nodes whose constrained and dual branches are equal collapse into a union. -/
    theorem post_spec (lit r₁ r₂ r₃ : Term) (h : Int) {okU : Term → Prop}
        (w₁ : Bdd okU r₁) (w₂ : Bdd okU r₂) (w₃ : Bdd okU r₃) :
        ∃ r, (if exactCompare r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
            else .ok (.tuple #[.integer h, lit, r₁, r₂, r₃])) = .ok r ∧
          (∀ ok : Term → Prop, IsLeaf lit → ok lit → Bdd (Above ok lit) r₁ → Bdd (Above ok lit) r₂ →
            Bdd (Above ok lit) r₃ → Bdd ok r) ∧
          (∀ ρ, Resp ρ → eval ρ r = ((ρ lit && eval ρ r₁) || eval ρ r₂ || (!ρ lit && eval ρ r₃))) ∧
          (NoLeaf r₁ → NoLeaf r₂ → NoLeaf r₃ → NoLeaf r) := by
      by_cases post : exactCompare r₃ r₁ = .eq
      · obtain ⟨r, run, keep, sem, nl⟩ := union_okN w₁ w₂
        refine ⟨r, by rw [ite_eq_left_of_eq_true _ _ (eq_true post), run], fun ok _ _ o₁ o₂ _ =>
          keep ok (o₁.mono fun _ h => h.1) (o₂.mono fun _ h => h.1), fun ρ resp => ?_, fun n₁ n₂ _ => nl n₁ n₂⟩
        rw [sem ρ resp, eval_congr w₃ resp post]
        cases ρ lit <;> cases eval ρ r₁ <;> simp
      · exact ⟨_, ite_eq_right_of_eq_false _ _ (eq_false post), fun ok leaf okl o₁ o₂ o₃ =>
          Bdd.node_iff.mpr ⟨leaf, okl, o₁, o₂, o₃⟩, fun ρ _ => eval_node ρ _ _ _ _ _,
          fun n₁ n₂ n₃ => NoLeaf.node.mpr ⟨n₁, n₂, n₃⟩⟩

    theorem same_lit_bool (x y : Term) :
        Elixir.Module.Types.Descr.«same_lit?/2» x y = .ok (.atom "true") ∨
          Elixir.Module.Types.Descr.«same_lit?/2» x y = .ok (.atom "false") := by
      unfold Elixir.Module.Types.Descr.«same_lit?/2»
      split
      · simp only [Lynx.Except.guard, Erlang.erlang.«=:=/2», Lynx.Except.tryWith]
        split <;> simp
      · simp

    theorem orElse_bool {x y : Except Exception Term}
        (hx : x = .ok (.atom "true") ∨ x = .ok (.atom "false")) (hy : y = .ok (.atom "true") ∨ y = .ok (.atom "false")) :
        Lynx.Except.orElse x y Bool.true = .ok (.atom "true") ∨ Lynx.Except.orElse x y Bool.true = .ok (.atom "false") := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [Lynx.Except.orElse]

    def InterOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a && eval ρ b)

    def InterOkN (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → eval ρ r = (eval ρ a && eval ρ b)) ∧
          (NoLeaf a → NoLeaf b → NoLeaf r)

    theorem inter_eq_spec {okU : Term → Prop} (cd₁ cd₂ u₁ u₂ : Term) (w₁ : Bdd okU cd₁) (w₂ : Bdd okU cd₂)
        (w₃ : Bdd okU u₁) (w₄ : Bdd okU u₂) (i₁ : InterOkN cd₁ cd₂) (i₂ : InterOkN cd₁ u₂) (i₃ : InterOkN u₁ cd₂) :
        ∃ r, Elixir.Module.Types.Descr.«bdd_intersection_eq/4» cd₁ cd₂ u₁ u₂ = .ok r ∧
          (∀ ok, Bdd ok cd₁ → Bdd ok cd₂ → Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
          (∀ ρ, Resp ρ → eval ρ r = ((eval ρ cd₁ && eval ρ cd₂) || (eval ρ cd₁ && eval ρ u₂) ||
            (eval ρ u₁ && eval ρ cd₂))) ∧ (NoLeaf cd₁ → NoLeaf cd₂ → NoLeaf u₁ → NoLeaf u₂ → NoLeaf r) := by
      obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := i₁
      obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := i₂
      obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := i₃
      by_cases top : r₁ = .atom "bdd_top"
      · subst top
        refine ⟨.atom "bdd_top", ?_, fun _ _ _ _ _ => Bdd.top, fun ρ resp => ?_, fun _ _ _ _ => NoLeaf.top⟩
        · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
          simp [run₁]
        · have := sem₁ ρ resp
          simp at this
          simp [this]
      · obtain ⟨r₄, run₄, keep₄, sem₄, nl₄⟩ := union_okN (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂)
        obtain ⟨r, runr, keepr, semr, nlr⟩ := union_okN (keep₁ _ w₁ w₂) (keep₄ _ (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂))
        refine ⟨r, ?_, fun ok o₁ o₂ o₃ o₄ => keepr ok (keep₁ ok o₁ o₂)
          (keep₄ ok (keep₂ ok o₁ o₄) (keep₃ ok o₃ o₂)), fun ρ resp => ?_,
          fun n₁ n₂ n₃ n₄ => nlr (nl₁ n₁ n₂) (nl₄ (nl₂ n₁ n₄) (nl₃ n₃ n₂))⟩
        · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
          simp only [run₁, Lynx.Except.ok_bind]
          simp [run₂, run₃, run₄, runr]
        · rw [semr ρ resp, sem₄ ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp]
          simp [Bool.or_assoc]

    def BelowI (U : List Term) (n : Nat) : Prop :=
      ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → InterOkN a b

    theorem inter_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
        (ih : BelowI U (μ U a b)) : InterOkN a b := by
      by_cases same : exactCompare b a = .eq
      · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_, fun na _ => na⟩
        · unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [← eval_congr wb resp same]; simp
      by_cases ta : a = .atom "bdd_top"
      · subst ta
        refine ⟨b, ?_, fun ok _ okb => okb, fun ρ _ => by simp, fun _ nb => nb⟩
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases tb : b = .atom "bdd_top"
      · subst tb
        refine ⟨a, ?_, fun ok oka _ => oka, fun ρ _ => by simp, fun na _ => na⟩
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fa : a = .atom "bdd_bot"
      · subst fa
        refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fb : b = .atom "bdd_bot"
      · subst fb
        refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
      obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
      have lU : la ∈ U := head_ok wa ha
      have lbU : lb ∈ U := head_ok wb hb
      have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
          High la a' ∧ High la b' → μ U a' b' < μ U a b :=
        fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
      have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
          High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
        fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
      rcases order : Term.compare la lb
      · -- lt
        obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
        have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
          fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
        obtain ⟨hc, hu, hd⟩ := split.children wa
        obtain ⟨Hc, Hu, Hd⟩ := split.high wa
        have HB : High la b := (raiseB wb).mono fun _ h => h.2
        obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := ih c₁ b (hc.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)
        obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := ih u₁ b (hu.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)
        obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := ih d₁ b (hd.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)
        have w₁ := keep₁ _ hc (raiseB wb)
        have w₂ := keep₂ _ hu (raiseB wb)
        have w₃ := keep₃ _ hd (raiseB wb)
        obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
        obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ r₂ r₃ h₁ w₁ w₂ w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
          fun na nb => nl (nl₁ (split.noLeaf na).1 nb) (nl₂ (split.noLeaf na).2.1 nb) (nl₃ (split.noLeaf na).2.2 nb)⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
          by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc, ou, od⟩ := split.children oka
          exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc (raiseB okb)) (keep₂ _ ou (raiseB okb))
            (keep₃ _ od (raiseB okb))
        · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
          cases ρ la <;> cases eval ρ b <;> simp
      · -- eq
        have run := compare_eq ha hb order
        have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
        rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
          rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
        · -- two leaves
          refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
          · unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run]
          · simp [sameLit ρ resp]
        · -- a leaf below a node
          have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
          obtain ⟨hc, hu, hd⟩ := splitB.children wb
          obtain ⟨r₁, run₁, keep₁, sem₁⟩ := union_ok hc hu
          have w₁ := keep₁ _ hc hu
          obtain ⟨h₃, node⟩ := node_new lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wb hb) w₁
            (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
          obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₁, node]
            by_cases post : exactCompare (.atom "bdd_bot") r₁ = .eq <;> simp [post]
          · obtain ⟨oc, ou, -⟩ := splitB.children okb
            exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ oc ou) Bdd.bot Bdd.bot
          · rw [sem ρ resp, sem₁ ρ resp]
            simp only [eval_node, eval_leaf, eval_bot, sameLit ρ resp]
            cases ρ lb <;> simp
        · -- a node above a leaf
          have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
          obtain ⟨hc, hu, hd⟩ := splitA.children wa
          obtain ⟨r₁, run₁, keep₁, sem₁⟩ := union_ok hc hu
          have w₁ := keep₁ _ hc hu
          obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wa ha) w₁
            (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
          obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₁, node]
            by_cases post : exactCompare (.atom "bdd_bot") r₁ = .eq <;> simp [post]
          · obtain ⟨oc, ou, -⟩ := splitA.children oka
            exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc ou) Bdd.bot Bdd.bot
          · rw [sem ρ resp, sem₁ ρ resp]
            simp only [eval_node, eval_leaf, eval_bot, ← sameLit ρ resp]
            cases ρ la <;> simp
        · -- two nodes
          have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
          have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
          obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
          obtain ⟨hc₂', hu₂', hd₂'⟩ := splitB.children wb
          have hc₂ := hc₂'.congr order
          have hu₂ := hu₂'.congr order
          have hd₂ := hd₂'.congr order
          obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
          have Hc₂ := (splitB.high wb).1.congr order
          have Hu₂ := (splitB.high wb).2.1.congr order
          have Hd₂ := (splitB.high wb).2.2.congr order
          have mA := fun m (ha' : High m _) => High.split splitA wa ha'
          have mB := fun m (hb' : High m _) => High.split splitB wb hb'
          have U' : ∀ {x : Term}, Bdd (Above (· ∈ U) la) x → Bdd (· ∈ U) x := fun w => w.mono fun _ h => h.1
          have pair : ∀ {x y : Term}, Bdd (Above (· ∈ U) la) x → Bdd (Above (· ∈ U) la) y → High la x → High la y →
              (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
                High m x ∧ High m y) → InterOkN x y :=
            fun wx wy hx hy mono => ih _ _ (U' wx) (U' wy) (lower mono ⟨hx, hy⟩)
          have bool : ∀ ρ, Resp ρ → ρ lb = ρ la := fun ρ resp => (sameLit ρ resp).symm
          by_cases su : exactCompare u₂ u₁ = .eq
          · obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
            obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
            have w₁ := keep₁ _ hc₁ hc₂
            have w₃ := keep₃ _ hd₁ hd₂
            obtain ⟨h₃, node⟩ := node_new la r₁ u₁ r₃ (head_leaf wa ha) w₁ hu₁ w₃
            obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ u₁ r₃ h₃ w₁ hu₁ w₃
            refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => nl
              (nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1) (NoLeaf.node.mp na).2.1
              (nl₃ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2)⟩
            · rw [← runr]
              unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
              simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, su, run₁, run₃, node]
              by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
            · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
              obtain ⟨oc₂, -, od₂⟩ := splitB.children okb
              exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc₁ (oc₂.congr order)) ou₁
                (keep₃ _ od₁ (od₂.congr order))
            · have eu := eval_congr (hu₂'.mono fun _ h => h.1) resp su
              rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp]
              simp only [eval_node, bool ρ resp, eu]
              generalize ρ la = L
              generalize eval ρ c₁ = C₁
              generalize eval ρ c₂ = C₂
              generalize eval ρ d₁ = D₁
              generalize eval ρ d₂ = D₂
              generalize eval ρ u₁ = U₁
              revert L C₁ C₂ D₁ D₂ U₁
              decide
          · rcases orElse_bool (same_lit_bool c₁ c₂) (same_lit_bool d₁ d₂) with so | so
            · -- equal literals below: intersect the branches with each other's unions
              obtain ⟨i₁, ri₁, ki₁, si₁, ni₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
              obtain ⟨i₂, ri₂, ki₂, si₂, ni₂⟩ := pair hc₁ hu₂ Hc₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').2.1⟩
              obtain ⟨i₃, ri₃, ki₃, si₃, ni₃⟩ := pair hu₁ hc₂ Hu₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').1⟩
              obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := inter_eq_spec c₁ c₂ u₁ u₂ hc₁ hc₂ hu₁ hu₂
                ⟨i₁, ri₁, ki₁, si₁, ni₁⟩ ⟨i₂, ri₂, ki₂, si₂, ni₂⟩ ⟨i₃, ri₃, ki₃, si₃, ni₃⟩
              obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := pair hu₁ hu₂ Hu₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.1⟩
              obtain ⟨j₁, rj₁, kj₁, sj₁, nj₁⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
              obtain ⟨j₂, rj₂, kj₂, sj₂, nj₂⟩ := pair hd₁ hu₂ Hd₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.1⟩
              obtain ⟨j₃, rj₃, kj₃, sj₃, nj₃⟩ := pair hu₁ hd₂ Hu₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.2⟩
              obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := inter_eq_spec d₁ d₂ u₁ u₂ hd₁ hd₂ hu₁ hu₂
                ⟨j₁, rj₁, kj₁, sj₁, nj₁⟩ ⟨j₂, rj₂, kj₂, sj₂, nj₂⟩ ⟨j₃, rj₃, kj₃, sj₃, nj₃⟩
              have w₁ := keep₁ _ hc₁ hc₂ hu₁ hu₂
              have w₂ := keep₂ _ hu₁ hu₂
              have w₃ := keep₃ _ hd₁ hd₂ hu₁ hu₂
              obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
              obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ r₂ r₃ h₃ w₁ w₂ w₃
              refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => by
                obtain ⟨c₁', u₁', d₁'⟩ := NoLeaf.node.mp na
                obtain ⟨c₂', u₂', d₂'⟩ := NoLeaf.node.mp nb
                exact nl (nl₁ c₁' c₂' u₁' u₂') (nl₂ u₁' u₂') (nl₃ d₁' d₂' u₁' u₂')⟩
              · rw [← runr]
                unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
                simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, su, so, isMember, run₁, run₂, run₃, node]
                by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
              · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
                obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
                exact keep ok (head_leaf wa ha) (head_ok oka ha)
                  (keep₁ _ oc₁ (oc₂.congr order) ou₁ (ou₂.congr order)) (keep₂ _ ou₁ (ou₂.congr order))
                  (keep₃ _ od₁ (od₂.congr order) ou₁ (ou₂.congr order))
              · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp]
                simp only [eval_node, bool ρ resp]
                generalize ρ la = L
                generalize eval ρ c₁ = C₁
                generalize eval ρ c₂ = C₂
                generalize eval ρ d₁ = D₁
                generalize eval ρ d₂ = D₂
                generalize eval ρ u₁ = U₁
                generalize eval ρ u₂ = U₂
                revert L C₁ C₂ D₁ D₂ U₁ U₂
                decide
            · -- intersect the unions of each side
              obtain ⟨x, rx, kx, sx, nx⟩ := union_okN hc₁ hu₁
              obtain ⟨y, ry, ky, sy, ny⟩ := union_okN hc₂ hu₂
              obtain ⟨x', rx', kx', sx', nx'⟩ := union_okN hd₁ hu₁
              obtain ⟨y', ry', ky', sy', ny'⟩ := union_okN hd₂ hu₂
              obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := pair (kx _ hc₁ hu₁) (ky _ hc₂ hu₂) (kx _ Hc₁ Hu₁) (ky _ Hc₂ Hu₂)
                fun m ha' hb' => ⟨kx _ (mA m ha').1 (mA m ha').2.1, ky _ (mB m hb').1 (mB m hb').2.1⟩
              obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := pair (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂) (kx' _ Hd₁ Hu₁) (ky' _ Hd₂ Hu₂)
                fun m ha' hb' => ⟨kx' _ (mA m ha').2.2 (mA m ha').2.1, ky' _ (mB m hb').2.2 (mB m hb').2.1⟩
              have w₁ := keep₁ _ (kx _ hc₁ hu₁) (ky _ hc₂ hu₂)
              have w₃ := keep₃ _ (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂)
              obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
                (Bdd.bot (ok := fun _ => True)) w₃
              obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
              refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => by
                obtain ⟨c₁', u₁', d₁'⟩ := NoLeaf.node.mp na
                obtain ⟨c₂', u₂', d₂'⟩ := NoLeaf.node.mp nb
                exact nl (nl₁ (nx c₁' u₁') (ny c₂' u₂')) NoLeaf.bot (nl₃ (nx' d₁' u₁') (ny' d₂' u₂'))⟩
              · rw [← runr]
                unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
                simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, su, so, isMember, rx, ry, rx', ry',
                  run₁, run₃, node]
                by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
              · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
                obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
                exact keep ok (head_leaf wa ha) (head_ok oka ha)
                  (keep₁ _ (kx _ oc₁ ou₁) (ky _ (oc₂.congr order) (ou₂.congr order))) Bdd.bot
                  (keep₃ _ (kx' _ od₁ ou₁) (ky' _ (od₂.congr order) (ou₂.congr order)))
              · rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp, sx ρ resp, sy ρ resp, sx' ρ resp, sy' ρ resp]
                simp only [eval_node, eval_bot, bool ρ resp]
                generalize ρ la = L
                generalize eval ρ c₁ = C₁
                generalize eval ρ c₂ = C₂
                generalize eval ρ d₁ = D₁
                generalize eval ρ d₂ = D₂
                generalize eval ρ u₁ = U₁
                generalize eval ρ u₂ = U₂
                revert L C₁ C₂ D₁ D₂ U₁ U₂
                decide
      · -- gt
        have order' : Term.compare lb la = .lt := Std.OrientedCmp.lt_of_gt order
        obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
        have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
          fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
        obtain ⟨hc, hu, hd⟩ := split.children wb
        obtain ⟨Hc, Hu, Hd⟩ := split.high wb
        have HA : High lb a := (raiseA wa).mono fun _ h => h.2
        obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := ih a c₂ wa (hc.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').1⟩) ⟨HA, Hc⟩)
        obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := ih a u₂ wa (hu.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)
        obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := ih a d₂ wa (hd.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.2⟩) ⟨HA, Hd⟩)
        have w₁ := keep₁ _ (raiseA wa) hc
        have w₂ := keep₂ _ (raiseA wa) hu
        have w₃ := keep₃ _ (raiseA wa) hd
        obtain ⟨h₁, node⟩ := node_new lb r₁ r₂ r₃ (head_leaf wb hb) w₁ w₂ w₃
        obtain ⟨r, runr, keep, sem, nl⟩ := post_spec lb r₁ r₂ r₃ h₁ w₁ w₂ w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
          fun na nb => nl (nl₁ na (split.noLeaf nb).1) (nl₂ na (split.noLeaf nb).2.1) (nl₃ na (split.noLeaf nb).2.2)⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
          by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc, ou, od⟩ := split.children okb
          exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ (raiseA oka) oc) (keep₂ _ (raiseA oka) ou)
            (keep₃ _ (raiseA oka) od)
        · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
          cases ρ lb <;> cases eval ρ a <;> simp

    theorem belowI_all (U : List Term) : ∀ n, BelowI U n := by
      intro n
      induction n with
      | zero => intro a b _ _ lt; omega
      | succ n ih =>
        intro a b wa wb lt
        exact inter_step U a b wa wb fun a' b' wa' wb' lt' => ih a' b' wa' wb' (by omega)

    theorem inter_okN {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : InterOkN a b :=
      belowI_all (lits a ++ lits b) _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
        (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)

    theorem inter_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : InterOk a b :=
      let ⟨r, run, keep, sem, _⟩ := inter_okN wa wb
      ⟨r, run, keep, sem⟩

    /-! Negations. -/

    def NegOk (b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok r ∧ (∀ ok, Bdd ok b → Bdd ok r) ∧
        ∀ ρ, Resp ρ → eval ρ r = !eval ρ b

    /-- Negations, which never have leaves. -/
    def NegOkN (b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok r ∧ (∀ ok, Bdd ok b → Bdd ok r) ∧
        (∀ ρ, Resp ρ → eval ρ r = !eval ρ b) ∧ NoLeaf r

    theorem neg_okN {ok₀ : Term → Prop} {b : Term} (wb : Bdd ok₀ b) : NegOkN b := by
      refine Bdd.induction (P := fun _ b => NegOkN b) ?_ ?_ ?_ ?_ ok₀ b wb
      · intro _
        exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.bot,
          fun ρ _ => by simp, NoLeaf.bot⟩
      · intro _
        exact ⟨.atom "bdd_top", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.top,
          fun ρ _ => by simp, NoLeaf.top⟩
      · intro ok k x y okl
        obtain ⟨h, node⟩ := node_new (.tuple #[.integer k, x, y]) (.atom "bdd_bot") (.atom "bdd_bot")
          (.atom "bdd_top") ⟨k, x, y, rfl⟩ (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
          (Bdd.top (ok := fun _ => True))
        refine ⟨.tuple #[.integer h, .tuple #[.integer k, x, y], .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"],
          by simp [Elixir.Module.Types.Descr.«bdd_negation/1», node], fun ok' w => ?_, fun ρ _ => ?_,
          NoLeaf.node.mpr ⟨NoLeaf.bot, NoLeaf.bot, NoLeaf.top⟩⟩
        · exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, Bdd.leaf_iff.mp w, Bdd.bot, Bdd.bot, Bdd.top⟩
        · cases ρ (.tuple #[.integer k, x, y]) <;> simp
      · intro ok h lit c u d leaf okl hc hu hd ⟨nc, runc, keepc, semc, nlc⟩ ⟨nu, runu, keepu, semu, nlu⟩
          ⟨nd, rund, keepd, semd, nld⟩
        have wnc := keepc _ hc
        have wnd := keepd _ hd
        obtain ⟨h₁, inner⟩ := node_new lit nc (.atom "bdd_bot") nd leaf wnc (Bdd.bot (ok := fun _ => True)) wnd
        have winner : Bdd ok (.tuple #[.integer h₁, lit, nc, .atom "bdd_bot", nd]) :=
          Bdd.node_iff.mpr ⟨leaf, okl, wnc, Bdd.bot, wnd⟩
        have wnu : Bdd ok nu := (keepu _ hu).mono fun _ h => h.1
        obtain ⟨i, runi, keepi, semi, nli⟩ := inter_okN winner wnu
        have wi := keepi _ winner wnu
        have ni : NoLeaf i := nli (NoLeaf.node.mpr ⟨nlc, NoLeaf.bot, nld⟩) nlu
        -- the result before and after the final simplification
        have final : ∃ r, (∀ ok', Bdd ok' (.tuple #[.integer h, lit, c, u, d]) → Bdd ok' r) ∧
            (∀ ρ, Resp ρ → eval ρ r = eval ρ i) ∧
            Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, lit, c, u, d]) = .ok r ∧ NoLeaf r := by
          have keepI : ∀ ok', Bdd ok' (.tuple #[.integer h, lit, c, u, d]) → Bdd ok' i := fun ok' w => by
            obtain ⟨-, okl', oc, ou, od⟩ := Bdd.node_iff.mp w
            exact keepi ok' (Bdd.node_iff.mpr ⟨leaf, okl', keepc _ oc, Bdd.bot, keepd _ od⟩)
              ((keepu _ ou).mono fun _ h => h.1)
          have base : Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, lit, c, u, d]) =
              (match i with
                | .tuple ⟨[_, _, c', u', d']⟩ =>
                  if exactCompare d' c' = .eq then Elixir.Module.Types.Descr.«bdd_union/2» u' c' else .ok i
                | _ => .ok i) := by
            conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
            simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
            rcases wi.shape with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, c', u', d', rfl⟩
            · rfl
            · rfl
            · rfl
            · by_cases e : exactCompare d' c' = .eq <;> simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», e]
          rcases wi.shape with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨hi, li, c', u', d', rfl⟩
          · exact ⟨_, keepI, fun _ _ => rfl, base, ni⟩
          · exact ⟨_, keepI, fun _ _ => rfl, base, ni⟩
          · exact ⟨_, keepI, fun _ _ => rfl, base, ni⟩
          · by_cases e : exactCompare d' c' = .eq
            · obtain ⟨-, -, wc', wu', wd'⟩ := Bdd.node_iff.mp wi
              obtain ⟨r, runr, keepr, semr, nlr⟩ := union_okN wu' wc'
              refine ⟨r, fun ok' w => ?_, fun ρ resp => ?_, by rw [base]; simp [e, runr],
                nlr (NoLeaf.node.mp ni).2.1 (NoLeaf.node.mp ni).1⟩
              · obtain ⟨-, -, oc', ou', -⟩ := Bdd.node_iff.mp (keepI ok' w)
                exact keepr ok' (ou'.mono fun _ h => h.1) (oc'.mono fun _ h => h.1)
              · rw [semr ρ resp, eval_node, eval_congr wd' resp e]
                cases ρ li <;> cases eval ρ c' <;> simp
            · exact ⟨_, keepI, fun _ _ => rfl, by rw [base]; simp [e], ni⟩
        obtain ⟨r, keepr, semr, runr, nlr⟩ := final
        refine ⟨r, runr, keepr, fun ρ resp => ?_, nlr⟩
        rw [semr ρ resp, semi ρ resp, eval_node, eval_node, semc ρ resp, semd ρ resp, semu ρ resp]
        cases ρ lit <;> cases eval ρ c <;> cases eval ρ u <;> cases eval ρ d <;> simp

    theorem neg_ok {ok₀ : Term → Prop} {b : Term} (wb : Bdd ok₀ b) : NegOk b :=
      let ⟨r, run, keep, sem, _⟩ := neg_okN wb
      ⟨r, run, keep, sem⟩

    /-! Differences. -/

    theorem tuple3_cmp {a₀ a₁ a₂ b : Term} (e : Term.compare (.tuple #[a₀, a₁, a₂]) b = .eq) :
        ∃ b₀ b₁ b₂, b = .tuple #[b₀, b₁, b₂] ∧ Term.compare a₀ b₀ = .eq ∧ Term.compare a₁ b₁ = .eq ∧
          Term.compare a₂ b₂ = .eq := by
      rw [compare_eq_step] at e
      cases b <;> simp [Compare.compareStep] at e
      rename_i ys
      obtain ⟨ys⟩ := ys
      rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, rest⟩⟩⟩⟩ <;>
        simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
          List.compareLex_nil_cons] at e
      · exact ⟨b₀, b₁, b₂, rfl, e.1, e.2.1, e.2.2⟩

    theorem tuple5_cmp {a₀ a₁ a₂ a₃ a₄ b : Term} (e : Term.compare (.tuple #[a₀, a₁, a₂, a₃, a₄]) b = .eq) :
        ∃ b₀ b₁ b₂ b₃ b₄, b = .tuple #[b₀, b₁, b₂, b₃, b₄] ∧ Term.compare a₁ b₁ = .eq ∧
          Term.compare a₂ b₂ = .eq ∧ Term.compare a₃ b₃ = .eq ∧ Term.compare a₄ b₄ = .eq := by
      rw [compare_eq_step] at e
      cases b <;> simp [Compare.compareStep] at e
      rename_i ys
      obtain ⟨ys⟩ := ys
      rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, rest⟩⟩⟩⟩⟩⟩ <;>
        simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
          List.compareLex_nil_cons] at e
      · exact ⟨b₀, b₁, b₂, b₃, b₄, rfl, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2⟩

    /-- Equal BDDs have the same semantics. -/
    theorem eval_congr_cmp {ok : Term → Prop} {a : Term} (wa : Bdd ok a) {ρ : Term → Bool} (resp : Resp ρ) :
        ∀ {b}, Term.compare a b = .eq → eval ρ a = eval ρ b := by
      refine Bdd.induction (P := fun _ a => ∀ {b}, Term.compare a b = .eq → eval ρ a = eval ρ b)
        ?_ ?_ ?_ ?_ ok a wa
      · intro _ b e
        obtain rfl := (compare_eq_atom b "bdd_top").mp (Std.OrientedCmp.eq_symm e)
        rfl
      · intro _ b e
        obtain rfl := (compare_eq_atom b "bdd_bot").mp (Std.OrientedCmp.eq_symm e)
        rfl
      · intro _ k x y _ b e
        obtain ⟨b₀, b₁, b₂, rfl, -, -, -⟩ := tuple3_cmp e
        simp only [eval_leaf]
        exact resp _ _ e
      · intro _ h lit c u d _ _ _ _ _ ihc ihu ihd b e
        obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl, el, ec, eu, ed⟩ := tuple5_cmp e
        simp only [eval_node]
        rw [resp _ _ el, ihc ec, ihu eu, ihd ed]

    def DiffOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_difference/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a && !eval ρ b)

    def BelowD (U : List Term) (n : Nat) : Prop :=
      ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → DiffOk a b

    theorem diff_union_spec {okU : Term → Prop} {i u₁ u₂ : Term} (wu₁ : Bdd okU u₁) (wu₂ : Bdd okU u₂)
        (diff : ∀ u, Elixir.Module.Types.Descr.«bdd_union/2» u₁ u₂ = .ok u → DiffOk i u) :
        ∃ r, Elixir.Module.Types.Descr.«bdd_difference_union/3» i u₁ u₂ = .ok r ∧
          (∀ ok, Bdd ok i → Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
          ∀ ρ, Resp ρ → eval ρ r = (eval ρ i && !(eval ρ u₁ || eval ρ u₂)) := by
      by_cases bot : i = .atom "bdd_bot"
      · subst bot
        exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«bdd_difference_union/3»; rfl,
          fun _ _ _ _ => Bdd.bot, fun _ _ => by simp⟩
      obtain ⟨u, runU, keepU, semU⟩ := union_ok wu₁ wu₂
      obtain ⟨r, run, keep, sem⟩ := diff u runU
      refine ⟨r, ?_, fun ok oi o₁ o₂ => keep ok oi (keepU ok o₁ o₂), fun ρ resp => by rw [sem ρ resp, semU ρ resp]⟩
      unfold Elixir.Module.Types.Descr.«bdd_difference_union/3»
      split
      · exact absurd rfl bot
      · simp [runU, run]

    theorem neg_union_spec {okU : Term → Prop} {u₁ u₂ : Term} (wu₁ : Bdd okU u₁) (wu₂ : Bdd okU u₂) :
        ∃ r, Elixir.Module.Types.Descr.«bdd_negation_union/2» u₁ u₂ = .ok r ∧
          (∀ ok, Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
          ∀ ρ, Resp ρ → eval ρ r = !(eval ρ u₁ || eval ρ u₂) := by
      obtain ⟨n₁, run₁, keep₁, sem₁⟩ := neg_ok wu₁
      obtain ⟨n₂, run₂, keep₂, sem₂⟩ := neg_ok wu₂
      obtain ⟨r, run, keep, sem⟩ := inter_ok (keep₁ _ wu₁) (keep₂ _ wu₂)
      refine ⟨r, by simp [Elixir.Module.Types.Descr.«bdd_negation_union/2», run₁, run₂, run],
        fun ok o₁ o₂ => keep ok (keep₁ ok o₁) (keep₂ ok o₂), fun ρ resp => ?_⟩
      rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp]
      cases eval ρ u₁ <;> cases eval ρ u₂ <;> rfl

    theorem diff_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
        (ih : BelowD U (μ U a b)) : DiffOk a b := by
      by_cases same : exactCompare b a = .eq
      · refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ resp => ?_⟩
        · unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [eval_congr wb resp same]; simp
      by_cases tb : b = .atom "bdd_top"
      · subst tb
        refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fa : a = .atom "bdd_bot"
      · subst fa
        refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fb : b = .atom "bdd_bot"
      · subst fb
        refine ⟨a, ?_, fun _ oka _ => oka, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases ta : a = .atom "bdd_top"
      · subst ta
        obtain ⟨r, run, keep, sem⟩ := neg_ok wb
        refine ⟨r, ?_, fun ok _ okb => keep ok okb, fun ρ resp => by simp [sem ρ resp]⟩
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run]
      obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
      obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
      have lU : la ∈ U := head_ok wa ha
      have lbU : lb ∈ U := head_ok wb hb
      have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
          High la a' ∧ High la b' → μ U a' b' < μ U a b :=
        fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
      have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
          High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
        fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
      rcases order : Term.compare la lb
      · -- lt
        obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
        have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
          fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
        obtain ⟨hc, hu, hd⟩ := split.children wa
        obtain ⟨Hc, Hu, Hd⟩ := split.high wa
        have HB : High la b := (raiseB wb).mono fun _ h => h.2
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := ih c₁ b (hc.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)
        obtain ⟨r₂, run₂, keep₂, sem₂⟩ := ih u₁ b (hu.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := ih d₁ b (hd.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)
        have w₁ := keep₁ _ hc (raiseB wb)
        have w₂ := keep₂ _ hu (raiseB wb)
        have w₃ := keep₃ _ hd (raiseB wb)
        obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
        obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ r₂ r₃ h₁ w₁ w₂ w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node, ta, tb, fa, fb]
          by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc, ou, od⟩ := split.children oka
          exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc (raiseB okb)) (keep₂ _ ou (raiseB okb))
            (keep₃ _ od (raiseB okb))
        · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
          cases ρ la <;> cases eval ρ b <;> simp
      · -- eq
        have run := compare_eq ha hb order
        have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
        rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
          rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
        · -- two leaves
          refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ resp => ?_⟩
          · unfold Elixir.Module.Types.Descr.«bdd_difference/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run]
          · simp [sameLit ρ resp]
        · -- a leaf below a node
          have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
          obtain ⟨hc, hu, hd⟩ := splitB.children wb
          obtain ⟨r₁, run₁, keep₁, sem₁⟩ := neg_union_spec hc hu
          have w₁ := keep₁ _ hc hu
          obtain ⟨h₃, node⟩ := node_new lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wb hb) w₁
            (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
          obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_difference/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₁, node]
            by_cases post : exactCompare (.atom "bdd_bot") r₁ = .eq <;> simp [post]
          · obtain ⟨oc, ou, -⟩ := splitB.children okb
            exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ oc ou) Bdd.bot Bdd.bot
          · rw [sem ρ resp, sem₁ ρ resp]
            simp only [eval_node, eval_leaf, eval_bot, sameLit ρ resp]
            cases ρ lb <;> simp
        · -- a node above a leaf
          have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
          obtain ⟨hc, hu, hd⟩ := splitA.children wa
          obtain ⟨r₃, run₃, keep₃, sem₃⟩ := union_ok hd hu
          have w₃ := keep₃ _ hd hu
          obtain ⟨h₃, node⟩ := node_new la (.atom "bdd_bot") (.atom "bdd_bot") r₃ (head_leaf wa ha)
            (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) w₃
          obtain ⟨r, runr, keep, sem, -⟩ := post_spec la (.atom "bdd_bot") (.atom "bdd_bot") r₃ h₃ Bdd.bot Bdd.bot w₃
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_difference/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, run₃, node]
            by_cases post : exactCompare r₃ (.atom "bdd_bot") = .eq <;> simp [post]
          · obtain ⟨-, ou, od⟩ := splitA.children oka
            exact keep ok (head_leaf wa ha) (head_ok oka ha) Bdd.bot Bdd.bot (keep₃ _ od ou)
          · rw [sem ρ resp, sem₃ ρ resp]
            simp only [eval_node, eval_leaf, eval_bot, ← sameLit ρ resp]
            cases ρ la <;> cases eval ρ u₁ <;> cases eval ρ d₁ <;> simp
        · -- two nodes
          have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
          have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
          obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
          obtain ⟨hc₂', hu₂', hd₂'⟩ := splitB.children wb
          have hc₂ := hc₂'.congr order
          have hu₂ := hu₂'.congr order
          have hd₂ := hd₂'.congr order
          obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
          have Hc₂ := (splitB.high wb).1.congr order
          have Hu₂ := (splitB.high wb).2.1.congr order
          have Hd₂ := (splitB.high wb).2.2.congr order
          have mA := fun m (ha' : High m _) => High.split splitA wa ha'
          have mB := fun m (hb' : High m _) => High.split splitB wb hb'
          have U' : ∀ {x : Term}, Bdd (Above (· ∈ U) la) x → Bdd (· ∈ U) x := fun w => w.mono fun _ h => h.1
          have pair : ∀ {x y : Term}, Bdd (Above (· ∈ U) la) x → Bdd (Above (· ∈ U) la) y → High la x → High la y →
              (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
                High m x ∧ High m y) → DiffOk x y :=
            fun wx wy hx hy mono => ih _ _ (U' wx) (U' wy) (lower mono ⟨hx, hy⟩)
          have bool : ∀ ρ, Resp ρ → ρ lb = ρ la := fun ρ resp => (sameLit ρ resp).symm
          by_cases cond : Term.compare u₁ (.atom "bdd_bot") = .eq ∨ Term.compare u₁ u₂ = .eq
          · obtain ⟨q₁, runQ₁, keepQ₁, semQ₁⟩ := union_ok hc₂ hu₂
            obtain ⟨q₃, runQ₃, keepQ₃, semQ₃⟩ := union_ok hd₂ hu₂
            obtain ⟨r₁, run₁, keep₁, sem₁⟩ := diff_union_spec (i := c₁) hc₂ hu₂ fun u ru => by
              rw [runQ₁] at ru; cases ru
              exact pair hc₁ (keepQ₁ _ hc₂ hu₂) Hc₁ (keepQ₁ _ Hc₂ Hu₂)
                fun m ha' hb' => ⟨(mA m ha').1, keepQ₁ _ (mB m hb').1 (mB m hb').2.1⟩
            obtain ⟨r₃, run₃, keep₃, sem₃⟩ := diff_union_spec (i := d₁) hd₂ hu₂ fun u ru => by
              rw [runQ₃] at ru; cases ru
              exact pair hd₁ (keepQ₃ _ hd₂ hu₂) Hd₁ (keepQ₃ _ Hd₂ Hu₂)
                fun m ha' hb' => ⟨(mA m ha').2.2, keepQ₃ _ (mB m hb').2.2 (mB m hb').2.1⟩
            have w₁ := keep₁ _ hc₁ hc₂ hu₂
            have w₃ := keep₃ _ hd₁ hd₂ hu₂
            obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
              (Bdd.bot (ok := fun _ => True)) w₃
            obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
            refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
            · rw [← runr]
              unfold Elixir.Module.Types.Descr.«bdd_difference/2»
              have yes : Lynx.Except.orElse (Erlang.erlang.«==/2» u₁ (.atom "bdd_bot")) (Erlang.erlang.«==/2» u₁ u₂) =
                  .ok (.atom "true") := by
                by_cases c₀ : Term.compare u₁ (.atom "bdd_bot") = .eq
                · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₀, Term.true, Term.false]
                · have c := cond.resolve_left c₀
                  simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₀, c, Term.true, Term.false]
              simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, yes, run₁, run₃, node]
              by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
            · obtain ⟨oc₁, -, od₁⟩ := splitA.children oka
              obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
              exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc₁ (oc₂.congr order) (ou₂.congr order)) Bdd.bot
                (keep₃ _ od₁ (od₂.congr order) (ou₂.congr order))
            · have hU : eval ρ u₁ = Bool.false ∨ eval ρ u₁ = eval ρ u₂ := by
                rcases cond with c | c
                · left; rw [(compare_eq_atom _ _).mp c]; simp
                · right; exact eval_congr_cmp (hu₁.mono fun _ h => h.1) resp c
              rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp]
              simp only [eval_node, eval_bot, bool ρ resp]
              revert hU
              generalize ρ la = L
              generalize eval ρ c₁ = C₁
              generalize eval ρ c₂ = C₂
              generalize eval ρ d₁ = D₁
              generalize eval ρ d₂ = D₂
              generalize eval ρ u₁ = U₁
              generalize eval ρ u₂ = U₂
              revert L C₁ C₂ D₁ D₂ U₁ U₂
              decide
          · obtain ⟨p₁, runP₁, keepP₁, semP₁⟩ := union_ok hc₁ hu₁
            obtain ⟨q₁, runQ₁, keepQ₁, semQ₁⟩ := union_ok hc₂ hu₂
            obtain ⟨p₃, runP₃, keepP₃, semP₃⟩ := union_ok hd₁ hu₁
            obtain ⟨q₃, runQ₃, keepQ₃, semQ₃⟩ := union_ok hd₂ hu₂
            obtain ⟨r₁', run₁, keep₁, sem₁⟩ := pair (keepP₁ _ hc₁ hu₁) (keepQ₁ _ hc₂ hu₂) (keepP₁ _ Hc₁ Hu₁)
              (keepQ₁ _ Hc₂ Hu₂) fun m ha' hb' => ⟨keepP₁ _ (mA m ha').1 (mA m ha').2.1, keepQ₁ _ (mB m hb').1 (mB m hb').2.1⟩
            obtain ⟨r₃', run₃, keep₃, sem₃⟩ := pair (keepP₃ _ hd₁ hu₁) (keepQ₃ _ hd₂ hu₂) (keepP₃ _ Hd₁ Hu₁)
              (keepQ₃ _ Hd₂ Hu₂) fun m ha' hb' => ⟨keepP₃ _ (mA m ha').2.2 (mA m ha').2.1,
                keepQ₃ _ (mB m hb').2.2 (mB m hb').2.1⟩
            obtain ⟨r₁, wr₁, s₁, def₁⟩ : ∃ r₁, (∀ ok, Bdd (Above ok la) c₁ → Bdd (Above ok la) c₂ →
                Bdd (Above ok la) u₁ → Bdd (Above ok la) u₂ → Bdd (Above ok la) r₁) ∧
                (∀ ρ, Resp ρ → eval ρ r₁ = ((eval ρ c₁ || eval ρ u₁) && !(eval ρ c₂ || eval ρ u₂))) ∧
                ((c₂ = .atom "bdd_top" ∧ r₁ = .atom "bdd_bot") ∨ (¬c₂ = .atom "bdd_top" ∧ r₁ = r₁')) := by
              by_cases ct : c₂ = .atom "bdd_top"
              · exact ⟨.atom "bdd_bot", fun _ _ _ _ _ => Bdd.bot, fun ρ _ => by simp [ct], Or.inl ⟨ct, rfl⟩⟩
              · exact ⟨r₁', fun ok o₁ o₂ o₃ o₄ => keep₁ _ (keepP₁ _ o₁ o₃) (keepQ₁ _ o₂ o₄),
                  fun ρ resp => by rw [sem₁ ρ resp, semP₁ ρ resp, semQ₁ ρ resp], Or.inr ⟨ct, rfl⟩⟩
            obtain ⟨r₃, wr₃, s₃, def₃⟩ : ∃ r₃, (∀ ok, Bdd (Above ok la) d₁ → Bdd (Above ok la) d₂ →
                Bdd (Above ok la) u₁ → Bdd (Above ok la) u₂ → Bdd (Above ok la) r₃) ∧
                (∀ ρ, Resp ρ → eval ρ r₃ = ((eval ρ d₁ || eval ρ u₁) && !(eval ρ d₂ || eval ρ u₂))) ∧
                ((d₂ = .atom "bdd_top" ∧ r₃ = .atom "bdd_bot") ∨ (¬d₂ = .atom "bdd_top" ∧ r₃ = r₃')) := by
              by_cases dt : d₂ = .atom "bdd_top"
              · exact ⟨.atom "bdd_bot", fun _ _ _ _ _ => Bdd.bot, fun ρ _ => by simp [dt], Or.inl ⟨dt, rfl⟩⟩
              · exact ⟨r₃', fun ok o₁ o₂ o₃ o₄ => keep₃ _ (keepP₃ _ o₁ o₃) (keepQ₃ _ o₂ o₄),
                  fun ρ resp => by rw [sem₃ ρ resp, semP₃ ρ resp, semQ₃ ρ resp], Or.inr ⟨dt, rfl⟩⟩
            have w₁ := wr₁ _ hc₁ hc₂ hu₁ hu₂
            have w₃ := wr₃ _ hd₁ hd₂ hu₁ hu₂
            obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
              (Bdd.bot (ok := fun _ => True)) w₃
            obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
            refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
            · rw [← runr]
              unfold Elixir.Module.Types.Descr.«bdd_difference/2»
              have no : Lynx.Except.orElse (Erlang.erlang.«==/2» u₁ (.atom "bdd_bot")) (Erlang.erlang.«==/2» u₁ u₂) =
                  .ok (.atom "false") := by
                simp only [not_or] at cond
                simp [Erlang.erlang.«==/2», Lynx.Except.orElse, cond.1, cond.2, Term.true, Term.false]
              simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, no]
              clear keep sem s₁ s₃ wr₁ wr₃ w₁ w₃ pair lower lowerB ih mA mB
              rcases def₁ with ⟨ct, rfl⟩ | ⟨ct, rfl⟩ <;> rcases def₃ with ⟨dt, rfl⟩ | ⟨dt, rfl⟩ <;>
                simp [Erlang.erlang.«==/2», ct, dt, Term.true, Term.false, runP₁, runQ₁, run₁, runP₃, runQ₃, run₃, node] <;>
                split <;> simp_all
            · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
              obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
              exact keep ok (head_leaf wa ha) (head_ok oka ha)
                (wr₁ _ oc₁ (oc₂.congr order) ou₁ (ou₂.congr order)) Bdd.bot
                (wr₃ _ od₁ (od₂.congr order) ou₁ (ou₂.congr order))
            · rw [sem ρ resp, s₁ ρ resp, s₃ ρ resp]
              simp only [eval_node, eval_bot, bool ρ resp]
              generalize ρ la = L
              generalize eval ρ c₁ = C₁
              generalize eval ρ c₂ = C₂
              generalize eval ρ d₁ = D₁
              generalize eval ρ d₂ = D₂
              generalize eval ρ u₁ = U₁
              generalize eval ρ u₂ = U₂
              revert L C₁ C₂ D₁ D₂ U₁ U₂
              decide
      · -- gt
        have order' : Term.compare lb la = .lt := Std.OrientedCmp.lt_of_gt order
        obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
        have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
          fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
        obtain ⟨hc, hu, hd⟩ := split.children wb
        obtain ⟨Hc, Hu, Hd⟩ := split.high wb
        have HA : High lb a := (raiseA wa).mono fun _ h => h.2
        obtain ⟨m, runM, keepM, semM⟩ := ih a u₂ wa (hu.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)
        have wm := keepM _ (raiseA wa) hu
        have Hm : High lb m := keepM _ HA Hu
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := ih m c₂ (wm.mono fun _ h => h.1) (hc.mono fun _ h => h.1)
          (lowerB (fun m' ha' hb' => ⟨keepM _ ha' (High.split split wb hb').2.1, (High.split split wb hb').1⟩) ⟨Hm, Hc⟩)
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := ih m d₂ (wm.mono fun _ h => h.1) (hd.mono fun _ h => h.1)
          (lowerB (fun m' ha' hb' => ⟨keepM _ ha' (High.split split wb hb').2.1, (High.split split wb hb').2.2⟩) ⟨Hm, Hd⟩)
        have w₁ := keep₁ _ wm hc
        have w₃ := keep₃ _ wm hd
        obtain ⟨h₁, node⟩ := node_new lb r₁ (.atom "bdd_bot") r₃ (head_leaf wb hb) w₁ (Bdd.bot (ok := fun _ => True)) w₃
        obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") r₃ h₁ w₁ Bdd.bot w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, runM, run₁, run₃, node, ta, tb, fa, fb]
          by_cases post : exactCompare r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc, ou, od⟩ := split.children okb
          have om := keepM _ (raiseA oka) ou
          exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ om oc) Bdd.bot (keep₃ _ om od)
        · rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp, semM ρ resp, split.eval ρ]
          cases ρ lb <;> cases eval ρ a <;> cases eval ρ u₂ <;> simp

    theorem belowD_all (U : List Term) : ∀ n, BelowD U n := by
      intro n
      induction n with
      | zero => intro a b _ _ lt; omega
      | succ n ih =>
        intro a b wa wb lt
        exact diff_step U a b wa wb fun a' b' wa' wb' lt' => ih a' b' wa' wb' (by omega)

    theorem diff_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : DiffOk a b :=
      belowD_all (lits a ++ lits b) _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
        (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)

    /-! Unsatisfiable ordered BDDs have no lines. -/

    /-- Valuations agreeing on the literals of a BDD agree on the BDD. -/
    theorem eval_ext {ok : Term → Prop} {x : Term} (wx : Bdd ok x) {ρ ρ' : Term → Bool}
        (agree : ∀ t, ok t → ρ' t = ρ t) : eval ρ' x = eval ρ x := by
      revert agree
      refine Bdd.induction (P := fun ok x => (∀ t, ok t → ρ' t = ρ t) → eval ρ' x = eval ρ x)
        ?_ ?_ ?_ ?_ ok x wx
      · intro _ _; simp
      · intro _ _; simp
      · intro _ k x y okl agree; simp [agree _ okl]
      · intro ok h lit c u d _ okl _ _ _ ic iu id agree
        have below : ∀ t, Above ok lit t → ρ' t = ρ t := fun t ht => agree t ht.1
        simp [agree _ okl, ic below, iu below, id below]

    /-- Setting the truth of a literal. -/
    def flip (ρ : Term → Bool) (l : Term) (v : Bool) : Term → Bool :=
      fun t => if Term.compare t l = .eq then v else ρ t

    theorem Resp.flip {ρ : Term → Bool} (resp : Resp ρ) (l : Term) (v : Bool) : Resp (flip ρ l v) := by
      intro a b e
      simp only [BddProofs.flip]
      by_cases ha : Term.compare a l = .eq
      · have hb : Term.compare b l = .eq := Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm e) ha
        simp [ha, hb]
      · have hb : ¬Term.compare b l = .eq := fun hb => ha (Std.TransCmp.eq_trans e hb)
        simp [ha, hb, resp a b e]

    def Unsat (r : Term) : Prop := ∀ ρ, Resp ρ → eval ρ r = Bool.false

    theorem resp_const (v : Bool) : Resp (fun _ => v) := fun _ _ _ => rfl

    theorem dnf_unsat {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (unsat : Unsat r) :
        ∀ acc pos neg, Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc pos neg r = .ok acc := by
      revert unsat
      refine Bdd.induction (P := fun _ r => Unsat r → ∀ acc pos neg,
        Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc pos neg r = .ok acc) ?_ ?_ ?_ ?_ ok r wr
      · intro _ unsat; have := unsat _ (resp_const Bool.true); simp at this
      · intro _ _ acc pos neg; simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»]
      · intro _ k x y _ unsat; have := unsat _ (resp_const Bool.true); simp at this
      · intro ok h lit c u d _ _ hc hu hd ic iu id unsat acc pos neg
        have above : ∀ v ρ t, Above ok lit t → flip ρ lit v t = ρ t := fun v ρ t ht => by
          have : Term.compare t lit ≠ .eq := fun e => by
            have := ht.2; rw [Std.OrientedCmp.eq_symm e] at this; cases this
          simp [BddProofs.flip, this]
        have parts : ∀ ρ, Resp ρ → eval ρ c = Bool.false ∧ eval ρ u = Bool.false ∧ eval ρ d = Bool.false := by
          intro ρ resp
          have t := unsat _ (resp.flip lit Bool.true)
          have f := unsat _ (resp.flip lit Bool.false)
          simp only [eval_node, eval_ext hc (above Bool.true ρ), eval_ext hu (above Bool.true ρ),
            eval_ext hd (above Bool.true ρ)] at t
          simp only [eval_node, eval_ext hc (above Bool.false ρ), eval_ext hu (above Bool.false ρ),
            eval_ext hd (above Bool.false ρ)] at f
          simp [BddProofs.flip] at t f
          exact ⟨t.1, t.2, f.2⟩
        simp only [Elixir.Module.Types.Descr.«bdd_to_dnf/4»]
        rw [iu (fun ρ resp => (parts ρ resp).2.1), Lynx.Except.ok_bind, ic (fun ρ resp => (parts ρ resp).1),
          Lynx.Except.ok_bind, id (fun ρ resp => (parts ρ resp).2.2)]

    /-- Unsatisfiable list BDDs are empty. -/
    theorem list_empty_unsat (dsp : Dispatcher) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (unsat : Unsat r)
        (S : List (Term × Term)) :
        Elixir.Module.Types.Descr.«list_empty?/2» dsp r (.map S) = .ok (.atom "true") := by
      have dnf := dnf_unsat wr unsat .nil .nil .nil
      unfold Elixir.Module.Types.Descr.«list_empty?/2»
      split
      · have := unsat _ (resp_const Bool.true); simp at this
      · simp only [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf,
          Lynx.Except.ok_bind]
        by_cases seen : S.any (fun e => Term.exactCompare (.cons (.atom "list") r) e.1 == .eq) = Bool.true
        · simp [Erlang.erlang.«is_map_key/2», seen, Term.true]
        · simp [Erlang.erlang.«is_map_key/2», seen, Term.true, Term.false, Erlang.maps.«put/3»,
            Erlang.lists.«all/2», Lynx.Except.guard, Erlang.erlang.«is_function/2»]

    end BddProofs
    """

    # Tuple types are the top tuple literal or ordered BDDs of other tuple literals,
    # whose elements are types of bitmaps, atoms, tuples, and lists. Lines of
    # tuples intersect these elements, which stay such types, and what remains
    # of a tuple type and its negation has no line, except for the empty tuple,
    # whose negation holds tuples of other sizes.
    postlude ~LEAN"""
    open BddProofs

    /-- Element types of tuples: valid types of bitmaps and atoms. -/
    abbrev Elem (X : List (Term × Term)) : Prop := Valid X

    def ElemTerm (e : Term) : Prop := e = .atom "term" ∨ ∃ X, e = .map X ∧ Elem X

    theorem Elem.static {X : List (Term × Term)} (valid : Elem X) : mapLookup X (.atom "dynamic") = Option.none := by
      cases h : mapLookup X (.atom "dynamic") with
      | none => rfl
      | some w =>
        rcases valid.keys _ (by rw [h]; rfl) with bad | bad <;> simp only [Term.atom.injEq] at bad <;>
          exact absurd bad (by decide)

    /-- The shape of a field of an element type. -/
    def ElemField (q w : Term) : Prop :=
      (q = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
        (q = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ [])

    theorem Elem.field {X : List (Term × Term)} (valid : Elem X) {q w : Term} (h : mapLookup X q = some w) :
        ElemField q w := by
      rcases valid.keys q (by simp [h]) with rfl | rfl
      · exact Or.inl ⟨rfl, valid.bitmap w h⟩
      · exact Or.inr ⟨rfl, valid.atom w h, fun S e => valid.atomUnion S (e ▸ h)⟩

    /-- Element types intersect into element types with fewer fields. -/
    theorem elem_inter_map (depth : Nat) (L R : List (Term × Term)) (vL : Elem L) (vR : Elem R) :
        ∃ out, Elixir.Module.Types.Descr.«bare_intersection/2»
            (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map out) ∧
          Elem out ∧ ∀ q w, mapLookup out q = some w → ∃ x, mapLookup L q = some x := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            q x y = .ok (g q x y) ∧ (kept (q, g q x y) = Bool.true → ElemField q (g q x y)) := by
        intro q x y hx hy
        rcases vL.field hx with ⟨rfl, b₁, rfl, -, le₁⟩ | ⟨rfl, ax, -⟩
        · obtain ⟨b₂, rfl, -, -⟩ := vR.bitmap y hy
          have run : Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
              (.atom "bitmap") (.integer b₁) (.integer b₂) = .ok (.integer ↑(b₁ &&& b₂)) := by
            simp [Elixir.Module.Types.Descr.«bare_intersection/3», bandI]
          refine ⟨by simp only [g, run], fun k => ?_⟩
          simp only [g, run] at k ⊢
          have le : b₁ &&& b₂ ≤ b₁ := Nat.and_le_left
          refine Or.inl ⟨rfl, _, rfl, ?_, by omega⟩
          by_cases zero : b₁ &&& b₂ = 0
          · simp [kept, zero] at k
          · omega
        · obtain ⟨p₁, S₁, rfl, set₁⟩ := ax
          obtain ⟨p₂, S₂, rfl, set₂⟩ := vR.atom y hy
          rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -, nonempty, -⟩ | ⟨hE, -⟩
          · exact ⟨by simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE], fun _ => by
              simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE]
              refine Or.inr ⟨rfl, ⟨p, E, rfl, setE⟩, fun S e => ?_⟩
              cases p
              · simp at e
              · simp at e; subst e; exact nonempty rfl⟩
          · exact ⟨by simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE], fun k => by
              simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE, kept] at k⟩
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "bare_intersection" #[] L R g (by
          intro e member y hy
          rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure,
            (common e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy).1])
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] I kept (by
          intro e _
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
      have field : ∀ q w, mapLookup out q = some w → ElemField q w ∧ ∃ x, mapLookup L q = some x := by
        intro q w hw
        rw [lookO q] at hw
        cases hit : (mapEntries I).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | none => simp [hit] at hw
        | some e =>
          rw [hit] at hw
          have qe : exactCompare q e.1 = .eq := by simpa using List.find?_some hit
          have inI : mapLookup I e.1 = some e.2 := mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hit)
          rw [lookI e.1] at inI
          cases hL : (mapEntries L).find? (fun f => decide (exactCompare e.1 f.1 = .eq)) with
          | none => simp [hL] at inI
          | some f =>
            rw [hL] at inI
            obtain ⟨y, hy, value⟩ := Option.map_eq_some_iff.mp inI
            have hx := mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hL)
            have ef : exactCompare e.1 f.1 = .eq := by simpa using List.find?_some hL
            have keep : kept e = kept (f.1, g f.1 f.2 y) := by rw [value]; rfl
            by_cases k : kept e = Bool.true
            · simp [k] at hw
              subst hw
              have shape := (common f.1 f.2 y hx hy).2 (by rw [← keep]; exact k)
              have qf := Std.TransCmp.eq_trans qe ef
              have inL : ∃ x, mapLookup L q = some x := ⟨f.2, by rw [mapLookup_congr qf]; exact hx⟩
              refine ⟨?_, inL⟩
              rw [value] at shape
              rcases shape with ⟨key, s⟩ | ⟨key, s⟩ <;> rw [key] at qf <;>
                simp only [exactCompare_eq_atom] at qf <;> subst qf
              · exact Or.inl ⟨rfl, s⟩
              · exact Or.inr ⟨rfl, s⟩
            · simp [k] at hw
      refine ⟨out, ?_, ⟨fun q some => ?_, fun w h => ?_, fun w h => ?_, fun S h => ?_⟩, fun q w h => (field q w h).2⟩
      · have absent : mapLookup R (.atom "dynamic") = Option.none := vR.static
        unfold Elixir.Module.Types.Descr.«bare_intersection/2»
        simp [getMapKeys_single, vL.static, absent]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runO]
      · obtain ⟨w, h⟩ := Option.isSome_iff_exists.mp some
        rcases (field q w h).1 with ⟨k, -⟩ | ⟨k, -⟩ <;> simp [k]
      · rcases (field _ w h).1 with ⟨k, s⟩ | ⟨k, -⟩
        · exact s
        · simp at k
      · rcases (field _ w h).1 with ⟨k, -⟩ | ⟨k, s, -⟩
        · simp at k
        · exact s
      · rcases (field _ _ h).1 with ⟨k, -⟩ | ⟨k, -, s⟩
        · simp at k
        · exact s S rfl

    theorem elem_inter (depth : Nat) {a b : Term} (ha : ElemTerm a) (hb : ElemTerm b) :
        ∃ e, Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) a b = .ok e ∧ ElemTerm e := by
      rcases ha with rfl | ⟨L, rfl, vL⟩
      · exact ⟨b, by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl, hb⟩
      rcases hb with rfl | ⟨R, rfl, vR⟩
      · exact ⟨.map L, by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl, Or.inr ⟨L, rfl, vL⟩⟩
      obtain ⟨out, run, vo, -⟩ := elem_inter_map depth L R vL vR
      exact ⟨.map out, run, Or.inr ⟨out, rfl, vo⟩⟩

    /-- Lists of element types. -/
    def AllElem (xs : Term) : Prop := ∃ l : List Term, xs = Term.list l ∧ ∀ e ∈ l, ElemTerm e

    theorem reverse_elems (l : List Term) (hl : ∀ e ∈ l, ElemTerm e) :
        ∀ tail, AllElem tail → ∃ r, Erlang.lists.«reverse/2» (Term.list l) tail = .ok r ∧ AllElem r := by
      induction l with
      | nil => intro tail ht; exact ⟨tail, by simp [Term.list, Erlang.lists.«reverse/2»], ht⟩
      | cons h t ih =>
        rintro tail ⟨lt, rfl, hlt⟩
        obtain ⟨r, run, hr⟩ := ih (fun e me => hl e (List.mem_cons_of_mem _ me)) (Term.list (h :: lt))
          ⟨h :: lt, rfl, fun e me => by
            rcases List.mem_cons.mp me with rfl | me
            · exact hl e List.mem_cons_self
            · exact hlt e me⟩
        exact ⟨r, by simpa [Term.list, Erlang.lists.«reverse/2»] using run, hr⟩

    theorem zip_elems (depth : Nat) (l₁ : List Term) (h₁ : ∀ e ∈ l₁, ElemTerm e) :
        ∀ (l₂ : List Term), (∀ e ∈ l₂, ElemTerm e) → ∀ acc, AllElem acc →
        ∃ r, Elixir.Module.Types.Descr.«zip_intersection/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
          (Term.list l₁) (Term.list l₂) acc (.function "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]) =
            .ok r ∧ AllElem r := by
      induction l₁ with
      | nil =>
        rintro l₂ h₂ acc ⟨la, rfl, hla⟩
        obtain ⟨r, run, hr⟩ := reverse_elems la hla (Term.list l₂) ⟨l₂, rfl, h₂⟩
        exact ⟨r, by unfold Elixir.Module.Types.Descr.«zip_intersection/4»; exact run, hr⟩
      | cons x xs ih =>
        rintro l₂ h₂ acc ⟨la, rfl, hla⟩
        cases l₂ with
        | nil =>
          obtain ⟨r, run, hr⟩ := reverse_elems la hla (Term.list (x :: xs)) ⟨_, rfl, h₁⟩
          exact ⟨r, by unfold Elixir.Module.Types.Descr.«zip_intersection/4»; exact run, hr⟩
        | cons y ys =>
          obtain ⟨e, run, he⟩ := elem_inter depth (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
          obtain ⟨r, runr, hr⟩ := ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys
            (fun e me => h₂ e (List.mem_cons_of_mem _ me)) (Term.list (e :: la))
            ⟨e :: la, rfl, fun e' me => by
              rcases List.mem_cons.mp me with rfl | me
              · exact he
              · exact hla e' me⟩
          refine ⟨r, ?_, hr⟩
          unfold Elixir.Module.Types.Descr.«zip_intersection/4»
          simp only [Term.list, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure, run,
            Lynx.Except.ok_bind]
          exact runr

    theorem length_list (l : List Term) : Erlang.erlang.«length/1» (Term.list l) = .ok (.integer l.length) := by
      induction l with
      | nil => rfl
      | cons h t ih => simp [Term.list, Erlang.erlang.«length/1»] at ih ⊢; simp [ih]

    /-- Lines of tuples: a tag and element types. -/
    def TuplePos (p : Term) : Prop :=
      ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ (tag = "open" ∨ tag = "closed") ∧
        ∀ e ∈ l, ElemTerm e

    /-- Tuple literals: a key, a tag, and element types. -/
    def TupleLit (t : Term) : Prop :=
      ∃ (k : Int) (tag : String) (l : List Term), t = .tuple #[.integer k, .atom tag, Term.list l] ∧
        (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, ElemTerm e

    theorem sizes_ok (t₁ t₂ : String) (h₁ : t₁ = "open" ∨ t₁ = "closed") (h₂ : t₂ = "open" ∨ t₂ = "closed")
        (n₁ n₂ : Int) : ∃ v, Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» (.atom t₁) (.integer n₁) (.atom t₂)
          (.integer n₂) = .ok v := by
      unfold Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
        simp [Lynx.Except.guard, Erlang.erlang.«/=/2», Erlang.erlang.«==/2»]
      all_goals (repeat (first | exact ⟨_, rfl⟩ | split))

    theorem line_ok (depth : Nat) {p t : Term} (hp : TuplePos p) (ht : TupleLit t) :
        Elixir.Module.Types.Descr.«tuple_line_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
            p t = .ok (.atom "empty") ∨
          ∃ p', Elixir.Module.Types.Descr.«tuple_line_intersection/2»
            (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) p t = .ok p' ∧ TuplePos p' := by
      obtain ⟨t₁, l₁, rfl, g₁, e₁⟩ := hp
      obtain ⟨k, t₂, l₂, rfl, g₂, e₂⟩ := ht
      obtain ⟨v, strategy⟩ := sizes_ok t₁ t₂ g₁ g₂ l₁.length l₂.length
      obtain ⟨r, zip, ⟨lr, rfl, hr⟩⟩ := zip_elems depth l₁ e₁ l₂ e₂ .nil ⟨[], rfl, by simp⟩
      unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
      simp only [length_list, Lynx.Except.ok_bind, strategy]
      split
      · exact Or.inl rfl
      · right
        rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
          simp [Erlang.erlang.«==/2», Lynx.Except.andAlso, zip] <;>
          exact ⟨_, lr, rfl, by simp, hr⟩

    /-- The branches of an unsatisfiable node are unsatisfiable. -/
    theorem unsat_children {ok : Term → Prop} {h : Int} {lit c u d : Term}
        (hc : Bdd (Above ok lit) c) (hu : Bdd (Above ok lit) u) (hd : Bdd (Above ok lit) d)
        (unsat : Unsat (.tuple #[.integer h, lit, c, u, d])) : Unsat c ∧ Unsat u ∧ Unsat d := by
      have above : ∀ v ρ t, Above ok lit t → flip ρ lit v t = ρ t := fun v ρ t ht => by
        have : Term.compare t lit ≠ .eq := fun e => by
          have := ht.2; rw [Std.OrientedCmp.eq_symm e] at this; cases this
        simp [BddProofs.flip, this]
      have parts : ∀ ρ, Resp ρ → eval ρ c = Bool.false ∧ eval ρ u = Bool.false ∧ eval ρ d = Bool.false := by
        intro ρ resp
        have t := unsat _ (resp.flip lit Bool.true)
        have f := unsat _ (resp.flip lit Bool.false)
        simp only [eval_node, eval_ext hc (above Bool.true ρ), eval_ext hu (above Bool.true ρ),
          eval_ext hd (above Bool.true ρ)] at t
        simp only [eval_node, eval_ext hc (above Bool.false ρ), eval_ext hu (above Bool.false ρ),
          eval_ext hd (above Bool.false ρ)] at f
        simp [BddProofs.flip] at t f
        exact ⟨t.1, t.2, f.2⟩
      exact ⟨fun ρ r => (parts ρ r).1, fun ρ r => (parts ρ r).2.1, fun ρ r => (parts ρ r).2.2⟩

    /-- Unsatisfiable tuple BDDs have no line, whatever the elements of their literals. -/
    theorem tuple_bdd_empty_unsat (depth : Nat) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
        (lits : ∀ t, ok t → TupleLit t) (unsat : Unsat r) :
        ∀ pos negs seen, TuplePos pos →
          Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
            pos negs r seen = .ok (.atom "true") := by
      revert lits unsat
      refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleLit t) → Unsat r → ∀ pos negs seen, TuplePos pos →
          Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
            pos negs r seen = .ok (.atom "true")) ?_ ?_ ?_ ?_ ok r wr
      · intro _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
      · intro _ _ _ pos negs seen _
        unfold Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
        rfl
      · intro _ k x y _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
      · intro ok h lit c u d _ okl hc hu hd ic iu id lits unsat pos negs seen hp
        obtain ⟨uc, uu, ud⟩ := unsat_children hc hu hd unsat
        have lits' : ∀ t, Above ok lit t → TupleLit t := fun t ht => lits t ht.1
        have dTrue := id lits' ud pos (.cons lit negs) seen hp
        have uTrue := iu lits' uu pos negs seen hp
        unfold Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
        simp only [dTrue, uTrue, Lynx.Except.andAlso_eq_true, Lynx.Except.andAlso]
        rcases line_ok depth hp (lits lit okl) with line | ⟨p', line, hp'⟩
        · simp [line]
        · have cTrue := ic lits' uc p' negs seen hp'
          obtain ⟨tg, l, rfl, -, -⟩ := hp'
          simp [line, cTrue]

    /-! Reading the tuple specification. -/

    theorem any_bdd_spec : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n → «any_bdd?/2» b lower = .ok Term.true →
        Bdd (fun t => Term.compare lower t = .lt) b := by
      intro n
      induction n with
      | zero => intro b _ size; cases b <;> simp at size <;> omega
      | succ n ih =>
        intro b lower size h
        unfold «any_bdd?/2» at h
        split at h
        · exact Bdd.top
        · exact Bdd.bot
        · rename_i key _ _
          simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
          cases key <;> simp [Erlang.erlang.«is_integer/1»] at h
          exact Bdd.leaf_iff.mpr (Std.OrientedCmp.lt_of_gt (by simpa [Erlang.erlang.«>/2»] using h))
        · rename_i hash key x y c u d
          simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
          obtain ⟨⟨⟨⟨⟨ih₁, ik⟩, gt⟩, hc⟩, hu⟩, hd⟩ := h
          cases hash <;> simp [Erlang.erlang.«is_integer/1»] at ih₁
          cases key <;> simp [Erlang.erlang.«is_integer/1»] at ik
          rename_i h' k
          have lt : Term.compare lower (.tuple #[.integer k, x, y]) = .lt :=
            Std.OrientedCmp.lt_of_gt (by simpa [Erlang.erlang.«>/2»] using gt)
          obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
          have lift : ∀ t, Term.compare (.tuple #[.integer k, x, y]) t = .lt →
              Above (fun t => Term.compare lower t = .lt) (.tuple #[.integer k, x, y]) t :=
            fun t ht => ⟨Std.TransCmp.lt_trans lt ht, ht⟩
          exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, lt,
            (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
            (ih d _ (by simp at size; omega) hd).mono lift⟩
        · simp [Term.true] at h

    theorem element_spec {e : Term} (h : «element?/1» e = .ok Term.true) : ElemTerm e := by
      unfold «element?/1» at h
      split at h
      · exact Or.inl rfl
      · obtain ⟨X, rfl, valid⟩ := valid_map e h
        exact Or.inr ⟨X, rfl, valid⟩

    theorem elements_spec : ∀ {xs : Term}, «elements?/1» xs = .ok Term.true → AllElem xs
      | .nil, _ => ⟨[], rfl, by simp⟩
      | .cons x xs, h => by
        simp only [«elements?/1», Term.true, Lynx.Except.andAlso_eq_true] at h
        obtain ⟨l, rfl, hl⟩ := elements_spec h.2
        exact ⟨x :: l, rfl, fun e me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact element_spec h.1
          · exact hl e me⟩
      | .atom _, h | .integer _, h | .float _, h | .reference _, h | .function _ _ _ _, h | .pid _, h
      | .tuple _, h | .map _, h | .bitstring _ _ _, h => by simp [«elements?/1», Term.true] at h

    /-- The top tuple literal `{_, open, []}`, which tuple operations treat as the top type. -/
    def IsTop (t : Term) : Prop := ∃ k : Term, t = .tuple #[k, .atom "open", .nil]

    def TupleOk (t : Term) : Prop := TupleLit t ∧ ¬IsTop t

    theorem tuple_literal_spec {lit lower : Term} (h : «tuple_literal?/2» lit lower = .ok Term.true) :
        IsLeaf lit ∧ Term.compare lower lit = .lt ∧ TupleOk lit := by
      unfold «tuple_literal?/2» at h
      simp only at h
      split at h
      · rename_i key tag elements
        simp only [Lynx.Except.guard, Lynx.Except.tryWith] at h
        split at h
        · next member =>
          have tags : tag = .atom "open" ∨ tag = .atom "closed" := by
            by_cases o : tag = .atom "open"
            · exact Or.inl o
            · by_cases c : tag = .atom "closed"
              · exact Or.inr c
              · simp [isMember, o, c] at member
          cases key <;> simp [Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true] at h
          rename_i k
          by_cases gt : (Term.compare (.tuple #[.integer k, tag, elements]) lower).isGT = Bool.true
          · have lt : Term.compare lower (.tuple #[.integer k, tag, elements]) = .lt :=
              Std.OrientedCmp.lt_of_gt (by simpa [Ordering.isGT_iff_eq_gt] using gt)
            rcases tags with rfl | rfl
            · by_cases en : elements = .nil
              · subst en
                simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2»] at h
              · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», en] at h
                obtain ⟨l, rfl, hl⟩ := elements_spec h
                refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "open", l, rfl, Or.inl rfl, hl⟩, ?_⟩
                rintro ⟨_, e⟩
                simp at e
                exact en e.2
            · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2»] at h
              obtain ⟨l, rfl, hl⟩ := elements_spec h
              refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "closed", l, rfl, Or.inr rfl, hl⟩, ?_⟩
              rintro ⟨_, e⟩
              simp at e
          · simp [Erlang.erlang.«>/2», gt] at h
        · simp [Term.true] at h
      · simp [Term.true] at h

    theorem ordered_tuple_spec : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
        «ordered_tuple_bdd?/2» b lower = .ok Term.true → Bdd (fun t => Term.compare lower t = .lt ∧ TupleOk t) b := by
      intro n
      induction n with
      | zero => intro b _ size; cases b <;> simp at size <;> omega
      | succ n ih =>
        intro b lower size h
        unfold «ordered_tuple_bdd?/2» at h
        split at h
        · exact Bdd.top
        · exact Bdd.bot
        · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := tuple_literal_spec h
          simp at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
        · rename_i hash lit c u d
          simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
          obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
          obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := tuple_literal_spec hl
          cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
          rename_i h'
          obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
          have lift : ∀ t, (Term.compare (.tuple #[.integer k, x, y]) t = .lt ∧ TupleOk t) →
              Above (fun t => Term.compare lower t = .lt ∧ TupleOk t) (.tuple #[.integer k, x, y]) t :=
            fun t ht => ⟨⟨Std.TransCmp.lt_trans lt ht.1, ht.2⟩, ht.1⟩
          exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
            (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
            (ih d _ (by simp at size; omega) hd).mono lift⟩
        · simp [Term.true] at h

    /-- Tuple types are the top tuple literal or ordered BDDs of other tuple literals. -/
    abbrev TupleField (w : Term) : Prop :=
      (∃ k : Int, w = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd TupleOk w

    theorem tuple_bdd_spec {w : Term} (h : «tuple_bdd?/1» w = .ok Term.true) : TupleField w := by
      unfold «tuple_bdd?/1» at h
      split at h
      · rename_i key
        cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
        exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ((ordered_tuple_spec _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)

    /-! Differences of two leaves. -/

    @[simp] theorem atom_exactCompare_eq (name : String) (t : Term) :
        exactCompare (.atom name) t = .eq ↔ t = .atom name :=
      ⟨fun e => (exactCompare_eq_atom _ _).mp (Std.OrientedCmp.eq_symm e),
        fun e => by subst e; exact exactCompare_self _⟩

    theorem diff_top_leaf (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_difference/2» (.atom "bdd_top") (.tuple #[k, x, y]) =
          Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[k, x, y]) := by
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem diff_bot_leaf (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_difference/2» (.atom "bdd_bot") (.tuple #[k, x, y]) = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem diff_leaf_bot (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_difference/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.tuple #[k, x, y]) := by
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem diff_leaf_top (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_difference/2» (.tuple #[k, x, y]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    /-- The difference of two leaves is a node or bottom. -/
    theorem leaf_difference {ok : Term → Prop} {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (oka : ok a) (okb : ok b) :
        ∃ r, Elixir.Module.Types.Descr.«bdd_difference/2» a b = .ok r ∧ Bdd ok r ∧
          (∀ ρ, Resp ρ → eval ρ r = (ρ a && !ρ b)) ∧ ∀ k x y, r ≠ .tuple #[k, x, y] := by
      have wa : Bdd ok a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr oka
      have wb : Bdd ok b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr okb
      have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
      have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
      have ea : ∀ ρ, eval ρ a = ρ a := fun ρ => by obtain ⟨_, _, _, rfl⟩ := la; simp
      have eb : ∀ ρ, eval ρ b = ρ b := fun ρ => by obtain ⟨_, _, _, rfl⟩ := lb; simp
      by_cases same : exactCompare b a = .eq
      · refine ⟨.atom "bdd_bot", ?_, Bdd.bot, fun ρ resp => ?_, fun _ _ _ => by simp⟩
        · obtain ⟨_, _, _, rfl⟩ := la
          obtain ⟨_, _, _, rfl⟩ := lb
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [resp _ _ (compare_eq_of_exactCompare_eq _ _ same)]; simp
      rcases order : Term.compare a b
      · -- lt: a and not b
        obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt wa ha hb order
        rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
        · obtain ⟨_, _, _, rfl⟩ := la; simp at e
        obtain ⟨nb, rnb, knb, snb⟩ := neg_ok wb
        have wnb : Bdd (Above ok a) nb := knb _ (wb.raise fun l hl => by simp [hb] at hl; subst hl; exact order)
        obtain ⟨h₁, node⟩ := node_new a nb (.atom "bdd_bot") (.atom "bdd_bot") la wnb
          (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
        refine ⟨.tuple #[.integer h₁, a, nb, .atom "bdd_bot", .atom "bdd_bot"], ?_,
          Bdd.node_iff.mpr ⟨la, oka, wnb, Bdd.bot, Bdd.bot⟩, fun ρ resp => ?_, fun _ _ _ => by simp⟩
        · have post : ¬exactCompare (.atom "bdd_bot") nb = .eq := by
            intro e
            have := snb (fun _ => Bool.false) (resp_const _)
            rw [(atom_exactCompare_eq _ _).mp e, eb] at this
            simp at this
          obtain ⟨_, _, _, rfl⟩ := la
          obtain ⟨_, _, _, rfl⟩ := lb
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, diff_top_leaf, rnb, diff_bot_leaf, node, post]
        · simp [snb ρ resp, eb]
      · -- eq: nothing is left
        refine ⟨.atom "bdd_bot", ?_, Bdd.bot, fun ρ resp => ?_, fun _ _ _ => by simp⟩
        · have eqr := compare_eq ha hb order
          obtain ⟨_, _, _, rfl⟩ := la
          obtain ⟨_, _, _, rfl⟩ := lb
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, eqr]
        · rw [resp _ _ order]; simp
      · -- gt: not b and a
        have order' : Term.compare b a = .lt := Std.OrientedCmp.lt_of_gt order
        obtain ⟨h₀, c, u, d, run, split⟩ := compare_gt wb ha hb order
        rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
        · obtain ⟨_, _, _, rfl⟩ := lb; simp at e
        have wa' : Bdd (Above ok b) a := wa.raise fun l hl => by simp [ha] at hl; subst hl; exact order'
        obtain ⟨h₁, node⟩ := node_new b (.atom "bdd_bot") (.atom "bdd_bot") a lb
          (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) wa'
        refine ⟨.tuple #[.integer h₁, b, .atom "bdd_bot", .atom "bdd_bot", a], ?_,
          Bdd.node_iff.mpr ⟨lb, okb, Bdd.bot, Bdd.bot, wa'⟩, fun ρ resp => ?_, fun _ _ _ => by simp⟩
        · obtain ⟨_, _, _, rfl⟩ := la
          obtain ⟨_, _, _, rfl⟩ := lb
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, diff_leaf_bot, diff_leaf_top, node]
        · simp [ea]; cases ρ a <;> cases ρ b <;> rfl

    /-! The empty tuple and its negation. -/

    def EmptyTuple (r : Term) : Prop :=
      ∀ n S, Elixir.Module.Types.Descr.«tuple_empty?/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) r
        (.map S) = .ok (.atom "true")

    theorem tuple_empty_of {r : Term} (run : ∀ n S, Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
        (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) (.tuple #[.atom "open", .nil]) .nil r (.map S) =
          .ok (.atom "true")) : EmptyTuple r := by
      intro n S
      unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
      by_cases seen : S.any (fun e => Term.exactCompare (.cons (.atom "tuple") r) e.1 == .eq) = Bool.true
      · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
      · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true,
          Term.false, Erlang.maps.«put/3», run]

    theorem tuple_empty_unsat {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (lits : ∀ t, ok t → TupleLit t)
        (unsat : Unsat r) : EmptyTuple r :=
      tuple_empty_of fun n S => tuple_bdd_empty_unsat n wr lits unsat _ _ _ ⟨"open", [], rfl, Or.inl rfl, by simp⟩

    theorem inter_top_leaf (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_top") (.tuple #[k, x, y]) = .ok (.tuple #[k, x, y]) := by
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem inter_bot_leaf (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_bot") (.tuple #[k, x, y]) = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem inter_leaf_top (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[k, x, y]) (.atom "bdd_top") = .ok (.tuple #[k, x, y]) := by
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem inter_leaf_bot (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    /-- Two distinct leaves intersect into a node of the smaller one. -/
    theorem leaf_intersection {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (same : ¬exactCompare b a = .eq)
        (order : Term.compare a b ≠ .eq) :
        ∃ h : Int, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok (.tuple #[.integer h, a, b, .atom "bdd_bot", .atom "bdd_bot"]) ∨
          Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok (.tuple #[.integer h, b, a, .atom "bdd_bot", .atom "bdd_bot"]) := by
      have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
      have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
      have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
      have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
      rcases cmp : Term.compare a b
      · obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt wa ha hb cmp
        rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
        · obtain ⟨_, _, _, rfl⟩ := la; simp at e
        obtain ⟨h₁, node⟩ := node_new a b (.atom "bdd_bot") (.atom "bdd_bot") la wb
          (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
        refine ⟨h₁, Or.inl ?_⟩
        obtain ⟨_, _, _, rfl⟩ := la
        obtain ⟨_, _, _, rfl⟩ := lb
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, inter_top_leaf, inter_bot_leaf, node]
      · exact absurd cmp order
      · obtain ⟨h₀, c, u, d, run, split⟩ := compare_gt wb ha hb cmp
        rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
        · obtain ⟨_, _, _, rfl⟩ := lb; simp at e
        obtain ⟨h₁, node⟩ := node_new b a (.atom "bdd_bot") (.atom "bdd_bot") lb wa
          (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
        refine ⟨h₁, Or.inr ?_⟩
        obtain ⟨_, _, _, rfl⟩ := la
        obtain ⟨_, _, _, rfl⟩ := lb
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, inter_leaf_top, inter_leaf_bot, node]

    theorem empty_tuple_cancel (k key : Int) :
        ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[.integer k, .atom "closed", .nil])
          (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) = .ok r ∧ EmptyTuple r := by
      have same : ¬exactCompare (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]])
          (.tuple #[.integer k, .atom "closed", .nil]) = .eq := by
        intro e
        obtain ⟨_, _, _, e', -, t, -⟩ := tuple3_exact e
        simp at e'
        obtain ⟨rfl, rfl, rfl⟩ := e'
        simp at t
      have order : Term.compare (.tuple #[.integer k, .atom "closed", .nil])
          (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) ≠ .eq := by
        rw [compare_tuple]
        simp [List.compareLex_cons_cons]
      obtain ⟨h, run | run⟩ := leaf_intersection ⟨k, _, _, rfl⟩ ⟨key, _, _, rfl⟩ same order
      · refine ⟨_, run, tuple_empty_of fun n S => ?_⟩
        simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
          Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Lynx.Except.guard,
          Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
          Erlang.lists.«reverse/2»]
      · refine ⟨_, run, tuple_empty_of fun n S => ?_⟩
        simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
          Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Lynx.Except.guard,
          Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
          Erlang.lists.«reverse/2»]

    /-- What survives of a tuple type and its negation is empty. -/
    def TupleCancel (x nb : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«tuple_intersection/2» x nb = .ok r ∧ (kept (.atom "tuple", r) = Bool.true → EmptyTuple r)

    theorem TupleOk.lit {t : Term} (h : TupleOk t) : TupleLit t := h.1

    theorem tuple_top_lit : TupleLit (.tuple #[.integer 61102469, .atom "open", .nil]) :=
      ⟨61102469, "open", [], rfl, Or.inl rfl, by simp⟩

    /-- Intersections of tuple BDDs that are not the top literal themselves. -/
    theorem tuple_intersection_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
        (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
        Elixir.Module.Types.Descr.«tuple_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
      split
      · exact (hx _ rfl).elim
      · exact (hy _ rfl).elim
      · rfl

    theorem not_top_of_ok {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (okNot : ∀ t, ok t → ¬IsTop t) :
        ∀ k, x ≠ .tuple #[k, .atom "open", .nil] := by
      intro k e
      subst e
      rcases wx.shape with h | h | ⟨k', x', y', h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact okNot _ (Bdd.leaf_iff.mp wx) ⟨_, rfl⟩

    theorem tuple_cancel (x : Term) (field : TupleField x) :
        ∃ nb, Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok nb ∧
          (kept (.atom "tuple", nb) = Bool.true → TupleCancel x nb) := by
      rcases field with ⟨k, rfl⟩ | wx
      · exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«tuple_difference/2»], fun k => by simp [kept] at k⟩
      have notTop := not_top_of_ok wx fun t h => h.2
      rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [diff_leaf_top]
      · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun _ => ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [diff_leaf_bot]
        · unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
          rfl
      · obtain ⟨⟨k', tag, ls, e, tags, elems⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
        simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        by_cases special : tag = "closed" ∧ ls = []
        · obtain ⟨rfl, rfl⟩ := special
          obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
          refine ⟨.tuple #[.integer ((1 <<< 27) + hash), .atom "open", Term.list [.atom "term"]], ?_, fun _ => ?_⟩
          · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
              Elixir.Module.Types.Descr.«bdd_leaf_key/2», Lynx.Except.guard, Erlang.erlang.«is_list/1»,
              Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»]
            rfl
          · obtain ⟨r, run, empty⟩ := empty_tuple_cancel k ((1 <<< 27) + hash)
            refine ⟨r, ?_, fun _ => empty⟩
            rw [tuple_intersection_bdd notTop (by intro k e; simp at e)]
            exact run
        · have notSpecial : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠
              .tuple #[k₁, .atom "closed", .nil] := by
            intro k₁ e
            simp at e
            apply special
            refine ⟨e.2.1, ?_⟩
            cases ls <;> simp_all [Term.list]
          obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
          have wnb := keep _ wx
          refine ⟨nb, ?_, fun _ => ?_⟩
          · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            split
            · next _ _ e =>
              exfalso
              simp at e
              obtain ⟨-, rfl, hl⟩ := e
              exact notTopX ⟨_, by rw [hl]⟩
            · next _ _ e => exact (notSpecial _ e).elim
            · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact run
            · next h₁ => exact (h₁ _ _ rfl rfl).elim
          · have wl : Bdd TupleLit (.tuple #[.integer k, .atom tag, Term.list ls]) := wx.mono fun _ h => h.1
            obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
            refine ⟨r, ?_, fun _ => tuple_empty_unsat (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h) fun ρ resp => ?_⟩
            · rw [tuple_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
              exact rr
            · rw [sr ρ resp, sem ρ resp]
              cases eval ρ (.tuple #[.integer k, .atom tag, Term.list ls]) <;> rfl
      · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
        have wnb := keep _ wx
        refine ⟨nb, ?_, fun _ => ?_⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [run]
        · have wl : Bdd TupleLit (.tuple #[.integer h, lit, c, u, d]) := wx.mono fun _ h => h.1
          obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
          refine ⟨r, ?_, fun _ => tuple_empty_unsat (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h) fun ρ resp => ?_⟩
          · rw [tuple_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
            exact rr
          · rw [sr ρ resp, sem ρ resp]
            cases eval ρ (.tuple #[.integer h, lit, c, u, d]) <;> rfl
    """

    # Map types are the top map literal or ordered BDDs of other map literals,
    # open or closed maps whose fields hold types of bitmaps and atoms. Lines of
    # maps intersect these fields, whose emptiness is immediate, and what remains
    # of a map type and its negation has no line.
    postlude ~LEAN"""
    open BddProofs

    /-- Field types of maps: the top type or types of bitmaps and atoms. -/
    def Flat (X : List (Term × Term)) : Prop :=
      Elem X ∧ ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom"

    def FlatTerm (t : Term) : Prop := t = .atom "term" ∨ ∃ X, t = .map X ∧ Flat X

    theorem flat_inter (depth : Nat) {a b : Term} (ha : FlatTerm a) (hb : FlatTerm b) :
        ∃ e, Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) a b = .ok e ∧ FlatTerm e := by
      rcases ha with rfl | ⟨L, rfl, vL⟩
      · exact ⟨b, by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl, hb⟩
      rcases hb with rfl | ⟨R, rfl, vR⟩
      · exact ⟨.map L, by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl, Or.inr ⟨L, rfl, vL⟩⟩
      obtain ⟨out, run, vo, fromL⟩ := elem_inter_map depth L R vL.1 vR.1
      refine ⟨.map out, run, Or.inr ⟨out, rfl, vo, fun q some => ?_⟩⟩
      obtain ⟨w, h⟩ := Option.isSome_iff_exists.mp some
      obtain ⟨x, hx⟩ := fromL q w h
      exact vL.2 q (by simp [hx])

    /-- The emptiness of flat types is decided without recursion. -/
    theorem flat_empty (d : Dispatcher) {t : Term} (ht : FlatTerm t) (S : List (Term × Term)) :
        Elixir.Module.Types.Descr.«empty_seen?/2» d t (.map S) = .ok (.atom "true") ∨
          Elixir.Module.Types.Descr.«empty_seen?/2» d t (.map S) = .ok (.atom "false") := by
      rcases ht with rfl | ⟨X, rfl, flat⟩
      · right
        rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
        rfl
      have absent : ∀ name, name ≠ "bitmap" → name ≠ "atom" → mapLookup X (.atom name) = Option.none := by
        intro name nb na
        cases h : mapLookup X (.atom name) with
        | none => rfl
        | some w =>
          rcases flat.2 (.atom name) (by rw [h]; rfl) with e | e
          · cases e; exact absurd rfl nb
          · cases e; exact absurd rfl na
      have anyKey : ∀ name, (X.any fun e => exactCompare (.atom name) e.1 == .eq) =
          (mapLookup X (.atom name)).isSome := by
        intro name
        rw [Bool.eq_iff_iff, mapLookup_isSome]
        simp
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
      simp [getMapKeys_single, absent "dynamic" (by decide) (by decide), Erlang.erlang.«==/2»,
        Erlang.erlang.«is_map_key/2», anyKey, absent "tuple" (by decide) (by decide), absent "map" (by decide) (by decide),
        absent "list" (by decide) (by decide), absent "fun" (by decide) (by decide), Term.true, Term.false]
      by_cases empty : X = []
      · simp [empty]
      simp only [empty, if_false]
      cases ha : mapLookup X (.atom "atom") <;> cases hb : mapLookup X (.atom "bitmap") <;>
        simp [Erlang.erlang.«not/1», Lynx.Except.andAlso]

    /-! Map literals. -/

    /-- Results of literal intersections, which throw `:empty` when a required field is empty. -/
    def Throws (e : Except Exception Term) (P : Term → Prop) : Prop :=
      (∃ v, e = .ok v ∧ P v) ∨ e = .error (Exception.throw (.atom "empty"))

    def boolAtom (o : Bool) : Term := .atom (if o then "true" else "false")

    /-- Map fields: a type and whether it is optional. -/
    def FieldValue (v : Term) : Prop := ∃ (t : Term) (o : Bool), v = .tuple #[t, boolAtom o] ∧ FlatTerm t

    def bareIntersection : Term := .function "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]

    theorem merge_fun (n : Nat) (S : List (Term × Term)) (key v₁ v₂ : Term) (h₁ : FieldValue v₁)
        (h₂ : FieldValue v₂) :
        Throws (Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
          (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) bareIntersection (.map S) key v₁ v₂) FieldValue := by
      obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁
      obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂
      obtain ⟨e, run, fe⟩ := flat_inter n f₁ f₂
      have dispatch : Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) bareIntersection
          #[t₁, t₂] = .ok e := by
        rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]; exact run
      unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
      have result : ∀ o, FieldValue (.tuple #[e, boolAtom o]) := fun o => ⟨e, o, rfl, fe⟩
      cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, dispatch]
      all_goals first
        | exact Or.inl ⟨_, rfl, result Bool.true⟩
        | exact Or.inl ⟨_, rfl, result Bool.false⟩
        | (rcases flat_empty (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) fe S with h | h <;>
            simp [h, Throws, Lynx.Except.guard, Lynx.Except.tryWith, isMember] <;> exact ⟨e, Bool.false, rfl, fe⟩)

    def fieldsTerm (l : List (Term × Term)) : Term := Term.list (l.map fun e => .tuple #[e.1, e.2])

    def Fields (v : Term) : Prop := ∃ l : List (Term × Term), v = fieldsTerm l ∧ ∀ e ∈ l, FieldValue e.2

    def mergeFun (S : List (Term × Term)) : Term :=
      .function "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-0-" 3 #[bareIntersection, .map S]

    theorem Throws.cons {e : Except Exception Term} (h : Throws e Fields) (x : Term × Term)
        (hx : FieldValue x.2) :
        Throws (e >>= fun r => pure (Term.cons (.tuple #[x.1, x.2]) r)) Fields := by
      rcases h with ⟨v, rfl, l, rfl, hl⟩ | rfl
      · refine Or.inl ⟨_, rfl, x :: l, rfl, fun e me => ?_⟩
        rcases List.mem_cons.mp me with rfl | me
        · exact hx
        · exact hl e me
      · exact Or.inr rfl

    theorem merge_fields (n : Nat) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
        l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue e.2) → (∀ e ∈ l₂, FieldValue e.2) →
        Throws (Erlang.orddict.«merge/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (mergeFun S)
          (fieldsTerm l₁) (fieldsTerm l₂)) Fields := by
      intro N
      induction N with
      | zero =>
        intro l₁ l₂ size h₁ h₂
        have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
        obtain ⟨rfl, rfl⟩ := this
        left
        refine ⟨.nil, ?_, [], rfl, by simp⟩
        unfold Erlang.orddict.«merge/3»
        simp [fieldsTerm, Lynx.Except.guard, mergeFun, Erlang.erlang.«is_function/2»]
      | succ N ih =>
        intro l₁ l₂ size h₁ h₂
        match l₁, l₂ with
        | [], l₂ =>
          left
          refine ⟨fieldsTerm l₂, ?_, l₂, rfl, h₂⟩
          unfold Erlang.orddict.«merge/3»
          cases l₂ <;> simp [fieldsTerm, Lynx.Except.guard, mergeFun, Erlang.erlang.«is_function/2»]
        | x :: xs, [] =>
          left
          refine ⟨fieldsTerm (x :: xs), ?_, x :: xs, rfl, h₁⟩
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Lynx.Except.guard, mergeFun, Erlang.erlang.«is_function/2»]
        | x :: xs, y :: ys =>
          have hx := h₁ x List.mem_cons_self
          have hy := h₂ y List.mem_cons_self
          have hxs : ∀ e ∈ xs, FieldValue e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
          have hys : ∀ e ∈ ys, FieldValue e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
          simp only [List.length_cons] at size
          rcases cmp : Term.compare x.1 y.1
          · have rest := ih xs (y :: ys) (by simp; omega) hxs h₂
            have := rest.cons x hx
            unfold Erlang.orddict.«merge/3»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp] using this
          · have hv := merge_fun n S x.1 x.2 y.2 hx hy
            have rest := ih xs ys (by omega) hxs hys
            unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, mergeFun,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure]
            rcases hv with ⟨v, hv, fv⟩ | hv
            · rw [hv]
              simp only [Lynx.Except.ok_bind]
              have := rest.cons (x.1, v) fv
              simpa [fieldsTerm, mergeFun] using this
            · rw [hv]
              exact Or.inr rfl
          · have rest := ih (x :: xs) ys (by simp; omega) h₁ hys
            have := rest.cons y hy
            unfold Erlang.orddict.«merge/3»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] using this

    theorem any_bool (d : Dispatcher) (f : Term) (l : List Term) (isFun : ∃ m nm caps, f = .function m nm 1 caps)
        (hf : ∀ x ∈ l, ∃ b, d.pure f #[x] = .ok (boolAtom b)) :
        ∃ b, Erlang.lists.«any/2» d f (Term.list l) = .ok (boolAtom b) := by
      have tail : ∀ l : List Term, (∀ x ∈ l, ∃ b, d.pure f #[x] = .ok (boolAtom b)) →
          ∃ b, Erlang.lists.«any_1/2» d f (Term.list l) = .ok (boolAtom b) := by
        intro l
        induction l with
        | nil => intro _; exact ⟨Bool.false, by simp [Erlang.lists.«any_1/2», boolAtom]⟩
        | cons x xs ih =>
          intro hf
          obtain ⟨b, hb⟩ := hf x List.mem_cons_self
          obtain ⟨b', hb'⟩ := ih fun y my => hf y (List.mem_cons_of_mem _ my)
          cases b
          · exact ⟨b', by rw [Erlang.lists.«any_1/2».eq_def]; simp [hb, boolAtom, hb']⟩
          · exact ⟨Bool.true, by rw [Erlang.lists.«any_1/2».eq_def]; simp [hb, boolAtom]⟩
      obtain ⟨m, nm, caps, rfl⟩ := isFun
      cases l with
      | nil => exact ⟨Bool.false, by simp [Erlang.lists.«any/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», boolAtom]⟩
      | cons x xs =>
        obtain ⟨b, hb⟩ := hf x List.mem_cons_self
        obtain ⟨b', hb'⟩ := tail xs fun y my => hf y (List.mem_cons_of_mem _ my)
        cases b
        · exact ⟨b', by simp [Erlang.lists.«any/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», hb, boolAtom, hb']⟩
        · exact ⟨Bool.true, by simp [Erlang.lists.«any/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», hb, boolAtom]⟩

    theorem all_bool (d : Dispatcher) (f : Term) (l : List Term) (isFun : ∃ m nm caps, f = .function m nm 1 caps)
        (hf : ∀ x ∈ l, ∃ b, d.pure f #[x] = .ok (boolAtom b)) :
        ∃ b, Erlang.lists.«all/2» d f (Term.list l) = .ok (boolAtom b) := by
      have tail : ∀ l : List Term, (∀ x ∈ l, ∃ b, d.pure f #[x] = .ok (boolAtom b)) →
          ∃ b, Erlang.lists.«all_1/2» d f (Term.list l) = .ok (boolAtom b) := by
        intro l
        induction l with
        | nil => intro _; exact ⟨Bool.true, by simp [Erlang.lists.«all_1/2», boolAtom]⟩
        | cons x xs ih =>
          intro hf
          obtain ⟨b, hb⟩ := hf x List.mem_cons_self
          obtain ⟨b', hb'⟩ := ih fun y my => hf y (List.mem_cons_of_mem _ my)
          cases b
          · exact ⟨Bool.false, by rw [Erlang.lists.«all_1/2».eq_def]; simp [hb, boolAtom]⟩
          · exact ⟨b', by rw [Erlang.lists.«all_1/2».eq_def]; simp [hb, boolAtom, hb']⟩
      obtain ⟨m, nm, caps, rfl⟩ := isFun
      cases l with
      | nil => exact ⟨Bool.true, by simp [Erlang.lists.«all/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», boolAtom]⟩
      | cons x xs =>
        obtain ⟨b, hb⟩ := hf x List.mem_cons_self
        obtain ⟨b', hb'⟩ := tail xs fun y my => hf y (List.mem_cons_of_mem _ my)
        cases b
        · exact ⟨Bool.false, by simp [Erlang.lists.«all/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», hb, boolAtom]⟩
        · exact ⟨b', by simp [Erlang.lists.«all/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», hb, boolAtom, hb']⟩

    /-- Predicates on the optional flags of fields return Booleans. -/
    theorem optional_bool (d : Dispatcher) (f : Term) (lam : Term → Except Exception Term)
        (isF : ∀ x, d.pure f #[x] = lam x) (flag : Bool → Bool)
        (lamOk : ∀ k t o, lam (.tuple #[k, .tuple #[t, boolAtom o]]) = .ok (boolAtom (flag o)))
        (l : List (Term × Term)) (hl : ∀ e ∈ l, FieldValue e.2) :
        ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]), ∃ b, d.pure f #[x] = .ok (boolAtom b) := by
      intro x mx
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨t, o, ho, -⟩ := hl e me
      rw [isF, ho, lamOk]
      exact ⟨_, rfl⟩

    theorem closed_fun₀ (k t : Term) (o : Bool) :
        Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-0-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
          .ok (boolAtom (!o)) := by
      cases o <;> simp [Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-0-/1», boolAtom,
        Erlang.erlang.«not/1»]

    theorem closed_fun₁ (k t : Term) (o : Bool) :
        Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-1-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
          .ok (boolAtom (!o)) := by
      cases o <;> simp [Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-1-/1», boolAtom,
        Erlang.erlang.«not/1»]

    theorem closed_fields (n : Nat) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
        l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue e.2) → (∀ e ∈ l₂, FieldValue e.2) →
        Throws (Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection
          (.map S)) Fields := by
      have tails : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue e.2) → (∀ e ∈ l₂, FieldValue e.2) →
          ∃ b, Lynx.Except.orElse
            (Erlang.lists.«any/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 3))
              (.function "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-0-" 1 #[]) (fieldsTerm l₁))
            (Erlang.lists.«any/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 3))
              (.function "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-1-" 1 #[]) (fieldsTerm l₂))
            Bool.true = .ok (boolAtom b) := by
        intro l₁ l₂ h₁ h₂
        obtain ⟨b₁, r₁⟩ := any_bool _ _ _ ⟨_, _, _, rfl⟩ (optional_bool _ _ _
          (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-0-/1».pure (n + 3)) _
          closed_fun₀ l₁ h₁)
        obtain ⟨b₂, r₂⟩ := any_bool _ _ _ ⟨_, _, _, rfl⟩ (optional_bool _ _ _
          (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-1-/1».pure (n + 3)) _
          closed_fun₁ l₂ h₂)
        simp only [fieldsTerm] at r₁ r₂ ⊢
        cases b₁ <;> cases b₂ <;> simp [r₁, r₂, boolAtom, Lynx.Except.orElse]
      have tailCase : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue e.2) → (∀ e ∈ l₂, FieldValue e.2) →
          (l₁ = [] ∨ l₂ = []) →
          Throws (Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection
            (.map S)) Fields := by
        intro l₁ l₂ h₁ h₂ empty
        obtain ⟨b, hb⟩ := tails l₁ l₂ h₁ h₂
        cases b
        · refine Or.inl ⟨.nil, ?_, [], rfl, by simp⟩
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          rcases empty with rfl | rfl
          · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
          · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
        · refine Or.inr ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          rcases empty with rfl | rfl
          · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
          · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
      intro N
      induction N with
      | zero =>
        intro l₁ l₂ size h₁ h₂
        exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
      | succ N ih =>
        intro l₁ l₂ size h₁ h₂
        match l₁, l₂ with
        | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
        | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
        | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
          obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁ _ List.mem_cons_self
          obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂ _ List.mem_cons_self
          have hxs : ∀ e ∈ xs, FieldValue e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
          have hys : ∀ e ∈ ys, FieldValue e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
          simp only [List.length_cons] at size
          rcases cmp : Term.compare k₁ k₂
          · cases o₁
            · refine Or.inr ?_
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simp [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember]
            · have rest := ih xs ((k₂, _) :: ys) (by simp; omega) hxs h₂
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using rest
          · obtain ⟨e, run, fe⟩ := flat_inter (n + 1) f₁ f₂
            have dispatch : Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) bareIntersection
                #[t₁, t₂] = .ok e := by
              rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]; exact run
            have rest := ih xs ys (by omega) hxs hys
            have value : FieldValue (.tuple #[e, boolAtom (o₁ && o₂)]) := ⟨e, _, rfl, fe⟩
            have cons := rest.cons (k₁, .tuple #[e, boolAtom (o₁ && o₂)]) value
            have notLt : ¬(Term.compare k₁ k₂).isLT = Bool.true := by simp [cmp]
            have notGt : ¬(Term.compare k₁ k₂).isGT = Bool.true := by simp [cmp]
            rcases flat_empty (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) fe S with empty | empty <;>
              cases o₁ <;> cases o₂ <;>
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» <;>
              simp [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember,
                Lynx.Except.andAlso, dispatch, empty] at cons ⊢ <;>
              first | exact cons | exact Or.inr rfl
          · have cmp' : Term.compare k₂ k₁ = .lt := Std.OrientedCmp.lt_of_gt cmp
            cases o₂
            · refine Or.inr ?_
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simp [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember]
            · have rest := ih ((k₁, _) :: xs) ys (by simp; omega) h₁ hys
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember]
                using rest

    theorem open_closed_fun (k t : Term) (o : Bool) :
        Elixir.Module.Types.Descr.«-map_literal_intersection_open_closed/4-fun-0-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
          .ok (boolAtom o) := by
      simp [Elixir.Module.Types.Descr.«-map_literal_intersection_open_closed/4-fun-0-/1»]

    theorem open_closed_fields (n : Nat) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
        l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue e.2) → (∀ e ∈ l₂, FieldValue e.2) →
        Throws (Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection
          (.map S)) Fields := by
      have tailCase : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue e.2) → (∀ e ∈ l₂, FieldValue e.2) →
          (l₁ = [] ∨ l₂ = []) →
          Throws (Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection
            (.map S)) Fields := by
        intro l₁ l₂ h₁ h₂ empty
        obtain ⟨b, hb⟩ := all_bool _ _ _ ⟨_, _, _, rfl⟩ (optional_bool _ _ _
          (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_open_closed/4-fun-0-/1».pure (n + 3)) _
          open_closed_fun l₁ h₁)
        cases b
        · refine Or.inr ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          rcases empty with rfl | rfl
          · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
          · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
        · refine Or.inl ⟨fieldsTerm l₂, ?_, l₂, rfl, h₂⟩
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          rcases empty with rfl | rfl
          · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
          · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom, Lynx.Except.guard, isMember]
      intro N
      induction N with
      | zero =>
        intro l₁ l₂ size h₁ h₂
        exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
      | succ N ih =>
        intro l₁ l₂ size h₁ h₂
        match l₁, l₂ with
        | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
        | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
        | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
          obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁ _ List.mem_cons_self
          obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂ _ List.mem_cons_self
          have hxs : ∀ e ∈ xs, FieldValue e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
          have hys : ∀ e ∈ ys, FieldValue e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
          simp only [List.length_cons] at size
          rcases cmp : Term.compare k₁ k₂
          · cases o₁
            · refine Or.inr ?_
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
              simp [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember]
            · have rest := ih xs ((k₂, _) :: ys) (by simp; omega) hxs h₂
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
              simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using rest
          · obtain ⟨e, run, fe⟩ := flat_inter (n + 1) f₁ f₂
            have dispatch : Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) bareIntersection
                #[t₁, t₂] = .ok e := by
              rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]; exact run
            have rest := ih xs ys (by omega) hxs hys
            have value : FieldValue (.tuple #[e, boolAtom (o₁ && o₂)]) := ⟨e, _, rfl, fe⟩
            have cons := rest.cons (k₁, .tuple #[e, boolAtom (o₁ && o₂)]) value
            rcases flat_empty (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) fe S with empty | empty <;>
              cases o₁ <;> cases o₂ <;>
              unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» <;>
              simp [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember,
                Lynx.Except.andAlso, dispatch, empty] at cons ⊢ <;>
              first | exact cons | exact Or.inr rfl
          · have rest := ih ((k₁, _) :: xs) ys (by simp; omega) h₁ hys
            have := rest.cons (k₂, _) (h₂ _ List.mem_cons_self)
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] using this

    /-- Lines of maps: a tag and fields. -/
    def MapPos (p : Term) : Prop :=
      ∃ (tag : String) (l : List (Term × Term)), p = .tuple #[.atom tag, fieldsTerm l] ∧
        (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, FieldValue e.2

    /-- Map literals: a key, a tag, and fields. -/
    def MapLit (t : Term) : Prop :=
      ∃ (k : Int) (tag : String) (l : List (Term × Term)), t = .tuple #[.integer k, .atom tag, fieldsTerm l] ∧
        (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, FieldValue e.2

    theorem Throws.wrap {e : Except Exception Term} (h : Throws e Fields) (tag : String)
        (htag : tag = "open" ∨ tag = "closed") :
        Throws (e >>= fun r => pure (Term.tuple #[.atom tag, r])) MapPos := by
      rcases h with ⟨v, rfl, l, rfl, hl⟩ | rfl
      · exact Or.inl ⟨_, rfl, tag, l, rfl, htag, hl⟩
      · exact Or.inr rfl

    theorem literal_ok (n : Nat) (S : List (Term × Term)) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
        (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List (Term × Term)) (h₁ : ∀ e ∈ l₁, FieldValue e.2)
        (h₂ : ∀ e ∈ l₂, FieldValue e.2) :
        Throws (Elixir.Module.Types.Descr.«map_literal_intersection/6» (Dispatcher.ofTable Erlang.program.fun_table (n + 3))
          (.atom t₁) (fieldsTerm l₁) (.atom t₂) (fieldsTerm l₂) bareIntersection (.map S)) MapPos := by
      have size := Nat.le_refl (l₁.length + l₂.length)
      have size' : l₂.length + l₁.length ≤ l₁.length + l₂.length := by omega
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
      · have := (merge_fields n S _ l₁ l₂ size h₁ h₂).wrap "open" (Or.inl rfl)
        simpa [mergeFun] using this
      · simpa using (open_closed_fields n S _ l₁ l₂ size h₁ h₂).wrap "closed" (Or.inr rfl)
      · simpa using (open_closed_fields n S _ l₂ l₁ size' h₂ h₁).wrap "closed" (Or.inr rfl)
      · simpa using (closed_fields n S _ l₁ l₂ size h₁ h₂).wrap "closed" (Or.inr rfl)

    theorem map_line_ok (n : Nat) (S : List (Term × Term)) {p t : Term} (hp : MapPos p) (ht : MapLit t) :
        Elixir.Module.Types.Descr.«map_line_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 3))
            p t (.map S) = .ok (.atom "empty") ∨
          ∃ p', Elixir.Module.Types.Descr.«map_line_intersection/3»
            (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) p t (.map S) = .ok p' ∧ MapPos p' := by
      obtain ⟨t₁, l₁, rfl, g₁, h₁⟩ := hp
      obtain ⟨k, t₂, l₂, rfl, g₂, h₂⟩ := ht
      rcases literal_ok n S t₁ t₂ g₁ g₂ l₁ l₂ h₁ h₂ with ⟨v, run, hv⟩ | run
      · right
        refine ⟨v, ?_, hv⟩
        unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
        simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
        simp [run]
      · left
        unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
        simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
        simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason]

    theorem map_bdd_empty_unsat (n : Nat) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
        (lits : ∀ t, ok t → MapLit t) (unsat : Unsat r) :
        ∀ pos negs S, MapPos pos →
          Elixir.Module.Types.Descr.«map_bdd_empty?/4» (Dispatcher.ofTable Erlang.program.fun_table (n + 3))
            pos negs r (.map S) = .ok (.atom "true") := by
      revert lits unsat
      refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLit t) → Unsat r → ∀ pos negs S, MapPos pos →
          Elixir.Module.Types.Descr.«map_bdd_empty?/4» (Dispatcher.ofTable Erlang.program.fun_table (n + 3))
            pos negs r (.map S) = .ok (.atom "true")) ?_ ?_ ?_ ?_ ok r wr
      · intro _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
      · intro _ _ _ pos negs S _
        unfold Elixir.Module.Types.Descr.«map_bdd_empty?/4»
        rfl
      · intro _ k x y _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
      · intro ok h lit c u d _ okl hc hu hd ic iu id lits unsat pos negs S hp
        obtain ⟨uc, uu, ud⟩ := unsat_children hc hu hd unsat
        have lits' : ∀ t, Above ok lit t → MapLit t := fun t ht => lits t ht.1
        have dTrue := id lits' ud pos (.cons lit negs) S hp
        have uTrue := iu lits' uu pos negs S hp
        unfold Elixir.Module.Types.Descr.«map_bdd_empty?/4»
        simp only [dTrue, uTrue, Lynx.Except.andAlso]
        rcases map_line_ok n S hp (lits lit okl) with line | ⟨p', line, hp'⟩
        · simp [line]
        · have cTrue := ic lits' uc p' negs S hp'
          obtain ⟨tg, l, rfl, -, -⟩ := hp'
          simp [line, cTrue]

    def EmptyMap (r : Term) : Prop :=
      ∀ n S, Elixir.Module.Types.Descr.«map_empty?/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) r
        (.map S) = .ok (.atom "true")

    theorem map_empty_unsat {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (lits : ∀ t, ok t → MapLit t)
        (unsat : Unsat r) : EmptyMap r := by
      intro n S
      have run := fun S' => map_bdd_empty_unsat n wr lits unsat (.tuple #[.atom "open", .nil]) .nil S'
        ⟨"open", [], rfl, Or.inl rfl, by simp⟩
      unfold Elixir.Module.Types.Descr.«map_empty?/2»
      by_cases seen : S.any (fun e => Term.exactCompare (.cons (.atom "map") r) e.1 == .eq) = Bool.true
      · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
      · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true,
          Term.false, Erlang.maps.«put/3», run]

    theorem Valid.flat {X : List (Term × Term)} (valid : Valid X) : Flat X := by
      exact ⟨valid, valid.keys⟩

    /-- Field types of map literals in the specification: the top type or valid types. -/
    def FieldType (t : Term) : Prop := t = .atom "term" ∨ ∃ X, t = .map X ∧ Valid X

    def FieldValueV (v : Term) : Prop := ∃ (t : Term) (o : Bool), v = .tuple #[t, boolAtom o] ∧ FieldType t

    /-- Map literals of the specification. -/
    def MapLitV (t : Term) : Prop :=
      ∃ (k : Int) (tag : String) (l : List (Term × Term)), t = .tuple #[.integer k, .atom tag, fieldsTerm l] ∧
        (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, FieldValueV e.2

    theorem FieldType.flat {t : Term} (h : FieldType t) : FlatTerm t := by
      rcases h with rfl | ⟨X, rfl, valid⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, rfl, valid.flat⟩

    theorem MapLitV.lit {t : Term} (h : MapLitV t) : MapLit t := by
      obtain ⟨k, tag, l, rfl, tags, fields⟩ := h
      refine ⟨k, tag, l, rfl, tags, fun e me => ?_⟩
      obtain ⟨ty, o, he, ft⟩ := fields e me
      exact ⟨ty, o, he, ft.flat⟩

    def MapOk (t : Term) : Prop := MapLitV t ∧ ¬IsTop t

    /-- Map types are the top map literal or ordered BDDs of other map literals. -/
    abbrev MapField (w : Term) : Prop :=
      (∃ k : Int, w = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd MapOk w

    def MapCancel (x nb : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«map_intersection/2» x nb = .ok r ∧ (kept (.atom "map", r) = Bool.true → EmptyMap r)

    theorem map_top_lit : MapLit (.tuple #[.integer 61102469, .atom "open", .nil]) :=
      ⟨61102469, "open", [], rfl, Or.inl rfl, by simp⟩

    theorem map_intersection_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
        (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
        Elixir.Module.Types.Descr.«map_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«map_intersection/2»
      split
      · exact (hx _ rfl).elim
      · exact (hy _ rfl).elim
      · rfl

    theorem map_cancel (x : Term) (field : MapField x) :
        ∃ nb, Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok nb ∧
          (kept (.atom "map", nb) = Bool.true → MapCancel x nb) := by
      rcases field with ⟨k, rfl⟩ | wx
      · exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«map_difference/2»], fun k => by simp [kept] at k⟩
      have notTop := not_top_of_ok wx fun t h => h.2
      rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
        unfold Elixir.Module.Types.Descr.«map_difference/2»
        simp [diff_leaf_top]
      · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun _ => ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩⟩
        · unfold Elixir.Module.Types.Descr.«map_difference/2»
          simp [diff_leaf_bot]
        · unfold Elixir.Module.Types.Descr.«map_intersection/2»
          rfl
      · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
        have wnb := keep _ wx
        refine ⟨nb, ?_, fun _ => ?_⟩
        · unfold Elixir.Module.Types.Descr.«map_difference/2»
          split
          · next _ _ e => exact (notTop _ e).elim
          · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact run
          · next h₁ => exact (h₁ _ _ rfl rfl).elim
        · have wl : Bdd MapLit (.tuple #[.integer k, tg, l]) := wx.mono fun _ h => h.1.lit
          obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1.lit)
          refine ⟨r, ?_, fun _ => map_empty_unsat (kr _ wl (wnb.mono fun _ h => h.1.lit)) (fun _ h => h) fun ρ resp => ?_⟩
          · rw [map_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
            exact rr
          · rw [sr ρ resp, sem ρ resp]
            cases eval ρ (.tuple #[.integer k, tg, l]) <;> rfl
      · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
        have wnb := keep _ wx
        refine ⟨nb, ?_, fun _ => ?_⟩
        · unfold Elixir.Module.Types.Descr.«map_difference/2»
          simp [run]
        · have wl : Bdd MapLit (.tuple #[.integer h, lit, c, u, d]) := wx.mono fun _ h => h.1.lit
          obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1.lit)
          refine ⟨r, ?_, fun _ => map_empty_unsat (kr _ wl (wnb.mono fun _ h => h.1.lit)) (fun _ h => h) fun ρ resp => ?_⟩
          · rw [map_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
            exact rr
          · rw [sr ρ resp, sem ρ resp]
            cases eval ρ (.tuple #[.integer h, lit, c, u, d]) <;> rfl

    /-! Reading the map specification. -/

    theorem field_type_spec {t : Term} (h : «field_type?/1» t = .ok Term.true) : FieldType t := by
      unfold «field_type?/1» at h
      split at h
      · exact Or.inl rfl
      · obtain ⟨X, rfl, valid⟩ := valid_map _ h
        exact Or.inr ⟨X, rfl, valid⟩

    theorem map_fields_spec (fs : Term) (h : «map_fields?/1» fs = .ok Term.true) :
        ∃ l : List (Term × Term), fs = fieldsTerm l ∧ ∀ e ∈ l, FieldValueV e.2 := by
      unfold «map_fields?/1» at h
      split at h
      · rename_i k t o rest
        simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
        obtain ⟨⟨hb, ht⟩, hr⟩ := h
        obtain ⟨l, rfl, hl⟩ := map_fields_spec rest hr
        have ob : ∃ b, o = boolAtom b := by
          cases o <;> simp [Erlang.erlang.«is_boolean/1»] at hb
          rename_i name
          by_cases t : name = "true"
          · exact ⟨Bool.true, by simp [boolAtom, t]⟩
          · by_cases f : name = "false"
            · exact ⟨Bool.false, by simp [boolAtom, f]⟩
            · simp [t, f] at hb
        obtain ⟨b, rfl⟩ := ob
        refine ⟨(k, .tuple #[t, boolAtom b]) :: l, rfl, fun e me => ?_⟩
        rcases List.mem_cons.mp me with rfl | me
        · exact ⟨t, b, rfl, field_type_spec ht⟩
        · exact hl e me
      · exact ⟨[], rfl, by simp⟩
      · simp [Term.true] at h
    termination_by sizeOf fs
    decreasing_by all_goals (simp_wf; subst_vars; simp; omega)

    theorem map_literal_spec {lit lower : Term} (h : «map_literal?/2» lit lower = .ok Term.true) :
        IsLeaf lit ∧ Term.compare lower lit = .lt ∧ MapOk lit := by
      unfold «map_literal?/2» at h
      simp only at h
      split at h
      · rename_i key tag fields
        simp only [Lynx.Except.guard, Lynx.Except.tryWith] at h
        split at h
        · next member =>
          have tags : tag = .atom "open" ∨ tag = .atom "closed" := by
            by_cases o : tag = .atom "open"
            · exact Or.inl o
            · by_cases c : tag = .atom "closed"
              · exact Or.inr c
              · simp [isMember, o, c] at member
          cases key <;> simp [Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true] at h
          rename_i k
          by_cases gt : (Term.compare (.tuple #[.integer k, tag, fields]) lower).isGT = Bool.true
          · have lt : Term.compare lower (.tuple #[.integer k, tag, fields]) = .lt :=
              Std.OrientedCmp.lt_of_gt (by simpa [Ordering.isGT_iff_eq_gt] using gt)
            rcases tags with rfl | rfl
            · by_cases en : fields = .nil
              · subst en
                simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2»] at h
              · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», en] at h
                obtain ⟨l, rfl, hl⟩ := map_fields_spec _ h
                refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "open", l, rfl, Or.inl rfl, hl⟩, ?_⟩
                rintro ⟨_, e⟩
                simp at e
                exact en e.2
            · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2»] at h
              obtain ⟨l, rfl, hl⟩ := map_fields_spec _ h
              refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "closed", l, rfl, Or.inr rfl, hl⟩, ?_⟩
              rintro ⟨_, e⟩
              simp at e
          · simp [Erlang.erlang.«>/2», gt] at h
        · simp [Term.true] at h
      · simp [Term.true] at h

    theorem ordered_map_spec : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
        «ordered_map_bdd?/2» b lower = .ok Term.true → Bdd (fun t => Term.compare lower t = .lt ∧ MapOk t) b := by
      intro n
      induction n with
      | zero => intro b _ size; cases b <;> simp at size <;> omega
      | succ n ih =>
        intro b lower size h
        unfold «ordered_map_bdd?/2» at h
        split at h
        · exact Bdd.top
        · exact Bdd.bot
        · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := map_literal_spec h
          simp at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
        · rename_i hash lit c u d
          simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
          obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
          obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := map_literal_spec hl
          cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
          rename_i h'
          obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
          have lift : ∀ t, (Term.compare (.tuple #[.integer k, x, y]) t = .lt ∧ MapOk t) →
              Above (fun t => Term.compare lower t = .lt ∧ MapOk t) (.tuple #[.integer k, x, y]) t :=
            fun t ht => ⟨⟨Std.TransCmp.lt_trans lt ht.1, ht.2⟩, ht.1⟩
          exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
            (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
            (ih d _ (by simp at size; omega) hd).mono lift⟩
        · simp [Term.true] at h

    theorem map_bdd_spec {w : Term} (h : «map_bdd?/1» w = .ok Term.true) : MapField w := by
      unfold «map_bdd?/1» at h
      split at h
      · rename_i key
        cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
        exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ((ordered_map_spec _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)
    """

    # List types are the top list literal or ordered BDDs of other list literals,
    # so negations hold the same literals and the list intersection shortcuts
    # never apply. What remains of a list type and its negation has no line.
    postlude ~LEAN"""
    open BddProofs

    /-- List literals other than the top literal `{_, term, term}`, which list operations treat as the top type. -/
    def ListOk (t : Term) : Prop := ¬∃ k : Term, t = .tuple #[k, .atom "term", .atom "term"]

    theorem list_literal_spec {lit lower : Term} (h : «list_literal?/2» lit lower = .ok Term.true) :
        IsLeaf lit ∧ Term.compare lower lit = .lt ∧ ListOk lit := by
      unfold «list_literal?/2» at h
      split at h
      · rename_i key list last
        cases key <;> simp [Lynx.Except.andAlso_eq_true, Erlang.erlang.«is_integer/1», Erlang.erlang.«>/2»] at h
        rename_i k
        refine ⟨⟨k, list, last, rfl⟩, Std.OrientedCmp.lt_of_gt h.1, ?_⟩
        rintro ⟨_, e⟩
        simp at e
        obtain ⟨-, rfl, rfl⟩ := e
        simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2»] at h
      · simp [Term.true] at h

    theorem ordered_spec : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n → «ordered_bdd?/2» b lower = .ok Term.true →
        Bdd (fun t => Term.compare lower t = .lt ∧ ListOk t) b := by
      intro n
      induction n with
      | zero => intro b _ size; cases b <;> simp at size <;> omega
      | succ n ih =>
        intro b lower size h
        unfold «ordered_bdd?/2» at h
        split at h
        · exact Bdd.top
        · exact Bdd.bot
        · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := list_literal_spec h
          simp at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
        · rename_i hash lit c u d
          simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
          obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
          obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := list_literal_spec hl
          cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
          rename_i h'
          obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
          have lift : ∀ t, (Term.compare (.tuple #[.integer k, x, y]) t = .lt ∧ ListOk t) →
              Above (fun t => Term.compare lower t = .lt ∧ ListOk t) (.tuple #[.integer k, x, y]) t :=
            fun t ht => ⟨⟨Std.TransCmp.lt_trans lt ht.1, ht.2⟩, ht.1⟩
          exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
            (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
            (ih d _ (by simp at size; omega) hd).mono lift⟩
        · simp [Term.true] at h

    /-- List types are the top list literal or ordered BDDs of other list literals. -/
    abbrev ListField (w : Term) : Prop :=
      (∃ k : Int, w = .tuple #[.integer k, .atom "term", .atom "term"]) ∨ Bdd ListOk w

    theorem list_bdd_spec {w : Term} (h : «list_bdd?/1» w = .ok Term.true) : ListField w := by
      unfold «list_bdd?/1» at h
      split at h
      · rename_i key
        cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
        exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ((ordered_spec _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)

    /-- Function types map arities to BDDs. -/
    def ArityBdds (w : Term) : Prop :=
      ∀ t R, w = .tuple #[t, .map R] → ∀ q v, mapLookup R q = some v → Bdd (fun _ => True) v

    theorem arity_bdds_spec (es : List (Term × Term))
        (valid : «arity_bdds?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
        ∀ p ∈ es, Bdd (fun _ => True) p.2 := by
      induction es with
      | nil => simp
      | cons e rest ih =>
        simp only [List.map_cons, Term.list, «arity_bdds?/1», Term.true, Lynx.Except.andAlso_eq_true] at valid
        intro p member
        rcases List.mem_cons.mp member with rfl | member
        · exact (any_bdd_spec _ _ _ (Nat.le_refl _) valid.1).mono fun _ _ => trivial
        · exact ih valid.2 p member

    theorem arity_bdds_map (R : List (Term × Term))
        (valid : «arity_bdds?/1» (Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
        ∀ q v, mapLookup R q = some v → Bdd (fun _ => True) v := by
      intro q v lookup
      obtain ⟨p, mp, -, rfl⟩ := lookup_found _ q v (by rw [mapLookup_mapEntries]; exact lookup)
      exact arity_bdds_spec _ valid p mp

    /-- What `negatable?/1` checks of a type. -/
    structure Negatable (X : List (Term × Term)) : Prop where
      keys : ∀ q, (mapLookup X q).isSome →
        q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨ q = .atom "list" ∨ q = .atom "tuple" ∨
          q = .atom "map"
      bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
      atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
      atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []
      funs : ∀ w, mapLookup X (.atom "fun") = some w → FunField w
      arities : ∀ w, mapLookup X (.atom "fun") = some w → ArityBdds w
      lists : ∀ w, mapLookup X (.atom "list") = some w → ListField w
      tuples : ∀ w, mapLookup X (.atom "tuple") = some w → TupleField w
      maps : ∀ w, mapLookup X (.atom "map") = some w → MapField w

    theorem Negatable.static {X : List (Term × Term)} (valid : Negatable X) :
        mapLookup X (.atom "dynamic") = Option.none := by
      cases h : mapLookup X (.atom "dynamic") with
      | none => rfl
      | some w =>
        rcases valid.keys _ (by rw [h]; rfl) with bad | bad | bad | bad | bad | bad <;> simp only [Term.atom.injEq] at bad <;>
          exact absurd bad (by decide)

    /-- Each field `negatable_fields?/1` accepts. -/
    theorem negatable_fields_spec (es : List (Term × Term))
        (valid : «negatable_fields?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
        ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
          (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) ∨
          (p.1 = .atom "fun" ∧ FunField p.2 ∧ ArityBdds p.2) ∨
          (p.1 = .atom "list" ∧ ListField p.2) ∨ (p.1 = .atom "tuple" ∧ TupleField p.2) ∨
          (p.1 = .atom "map" ∧ MapField p.2) := by
      induction es with
      | nil => simp
      | cons e rest ih =>
        obtain ⟨k, w⟩ := e
        simp only [List.map_cons, Term.list, «negatable_fields?/1», Term.true, Lynx.Except.andAlso_eq_true] at valid
        have head : (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
            (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
            (k = .atom "fun" ∧ FunField w ∧ ArityBdds w) ∨
            (k = .atom "list" ∧ ListField w) ∨ (k = .atom "tuple" ∧ TupleField w) ∨ (k = .atom "map" ∧ MapField w) := by
          have field := valid.1
          have fallback : «valid_fields?/1» (Term.list [.tuple #[k, w]]) = .ok Term.true →
              (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
                (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
                (k = .atom "fun" ∧ FunField w ∧ ArityBdds w) ∨ (k = .atom "list" ∧ ListField w) ∨
                (k = .atom "tuple" ∧ TupleField w) ∨ (k = .atom "map" ∧ MapField w) := fun h => by
            rcases valid_fields [(k, w)] (by simpa [Term.list] using h) (k, w) (by simp) with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          unfold «negatable_field?/1» at field
          simp only at field
          split at field
          · rename_i tag arities shape
            simp at shape
            obtain ⟨rfl, rfl⟩ := shape
            simp only [Lynx.Except.guard, Lynx.Except.tryWith] at field
            split at field
            · rename_i member
              refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
              cases arities <;> simp [Erlang.erlang.«is_map/1», Lynx.Except.andAlso] at field
              rename_i R
              have bdds : ArityBdds (.tuple #[tag, .map R]) := by
                intro t R' e
                simp at e
                obtain ⟨-, rfl⟩ := e
                exact arity_bdds_map R (by simpa [Erlang.maps.«to_list/1»] using field)
              by_cases u : tag = .atom "union"
              · exact ⟨⟨Bool.true, R, by simp [u]⟩, bdds⟩
              · by_cases n : tag = .atom "negation"
                · exact ⟨⟨Bool.false, R, by simp [n]⟩, bdds⟩
                · simp [isMember, u, n] at member
            · exact fallback (by simpa using field)
          · split at field
            · rename_i bdd shape
              simp at shape
              obtain ⟨rfl, rfl⟩ := shape
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, list_bdd_spec field⟩)))
            · rename_i bdd shape
              simp at shape
              obtain ⟨rfl, rfl⟩ := shape
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tuple_bdd_spec field⟩))))
            · rename_i bdd shape
              simp at shape
              obtain ⟨rfl, rfl⟩ := shape
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, map_bdd_spec field⟩))))
            · exact fallback field
        intro p member
        rcases List.mem_cons.mp member with rfl | member
        · exact head
        · exact ih valid.2 p member

    theorem negatable_map (descr : Term) (valid : «negatable?/1» descr = .ok Term.true) :
        ∃ X, descr = .map X ∧ Negatable X := by
      cases descr <;> simp [«negatable?/1», Term.true] at valid
      rename_i X
      simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at valid
      have each := negatable_fields_spec (mapEntries X) valid
      have entry (q w : Term) (lookup : mapLookup X q = some w) :
          ∃ p ∈ mapEntries X, exactCompare q p.1 = .eq ∧ p.2 = w :=
        lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
      have key : ∀ {q : Term} {name : String}, exactCompare q (.atom name) = .eq → q = .atom name :=
        fun e => (exactCompare_eq_atom _ _).mp e
      refine ⟨X, rfl, ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?atomU,
        fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_⟩⟩
      case atomU =>
        obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
        rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
          first | exact f.2 S e | (simp at qp)
      · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
        obtain ⟨p, mp, qp, -⟩ := entry q w lookup
        rcases each p mp with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> rw [k] at qp <;> simp [key qp]
      all_goals
        obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
        rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
          first | exact f | exact f.1 | exact f.2 | (simp at qp)

    /-- A list BDD of other literals is not a top literal itself. -/
    theorem not_top_leaf {x : Term} (wx : Bdd ListOk x) : ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"] := by
      intro k e
      subst e
      rcases wx.shape with h | h | ⟨k', x', y', h⟩ | ⟨h', lit, c, u, d, h⟩ <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Bdd.leaf_iff.mp wx ⟨_, rfl⟩

    /-- The negation of a list type. -/
    theorem list_negation (k : Int) (x : Term) (field : ListField x) :
        (Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer k, .atom "term", .atom "term"]) x =
          .ok (.atom "bdd_bot")) ∨
        (Bdd ListOk x ∧ ∃ y, Elixir.Module.Types.Descr.«list_difference/2»
            (.tuple #[.integer k, .atom "term", .atom "term"]) x = .ok y ∧
          Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x) := by
      rcases field with ⟨k', rfl⟩ | wx
      · left; simp [Elixir.Module.Types.Descr.«list_difference/2»]
      · right
        obtain ⟨y, run, keep, sem⟩ := neg_ok wx
        refine ⟨wx, y, ?_, keep _ wx, sem⟩
        have nt := not_top_leaf wx
        unfold Elixir.Module.Types.Descr.«list_difference/2»
        split
        · exact (nt _ rfl).elim
        · exact run
        · next h₁ h₂ => first | exact (h₁ _ rfl).elim | exact (h₁ _ _ rfl).elim | exact absurd rfl (h₁ _) | simp_all

    /-- The intersection of list types of other literals. -/
    theorem list_intersection_bdd {x y : Term} (wx : Bdd ListOk x) (wy : Bdd ListOk y) :
        Elixir.Module.Types.Descr.«list_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«list_intersection/2»
      split
      · exact (not_top_leaf wx _ rfl).elim
      · exact (not_top_leaf wy _ rfl).elim
      · rfl

    /-- What remains of a list or tuple type and its negation. -/
    def Gone (q w : Term) : Prop :=
      (q = .atom "list" ∧ Bdd ListOk w ∧ Unsat w) ∨ (q = .atom "tuple" ∧ EmptyTuple w) ∨
        (q = .atom "map" ∧ EmptyMap w)

    theorem Gone.congr {q k w : Term} (e : exactCompare q k = .eq) (gone : Gone k w) : Gone q w := by
      rcases gone with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact Or.inl ⟨(exactCompare_eq_atom _ _).mp e, h⟩
      · exact Or.inr (Or.inl ⟨(exactCompare_eq_atom _ _).mp e, h⟩)
      · exact Or.inr (Or.inr ⟨(exactCompare_eq_atom _ _).mp e, h⟩)

    /-- Types holding only what remains of list and tuple types and their negations are empty. -/
    theorem empty_gone (n : Nat) (I : List (Term × Term)) (only : ∀ q w, mapLookup I q = some w → Gone q w) :
        Elixir.Module.Types.Descr.«empty?/1» (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (.map I) =
          .ok Term.true := by
      have absent : ∀ name, name ≠ "list" → name ≠ "tuple" → name ≠ "map" →
          mapLookup I (.atom name) = Option.none := by
        intro name nl nt nm
        cases h : mapLookup I (.atom name) with
        | none => rfl
        | some w => rcases only _ w h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> simp at e <;> simp_all
      have none : ∀ name, name ≠ "list" → name ≠ "tuple" → name ≠ "map" →
          I.any (fun e => exactCompare (.atom name) e.1 == .eq) = Bool.false := by
        intro name nl nt nm
        have := absent name nl nt nm
        rw [Bool.eq_false_iff]
        intro hany
        obtain ⟨e, me, he⟩ := List.any_eq_true.mp hany
        have := (mapLookup_isSome I (.atom name)).mpr ⟨e, me, by simpa using he⟩
        simp_all
      have anyKey : ∀ name, (I.any fun e => exactCompare (.atom name) e.1 == .eq) =
          (mapLookup I (.atom name)).isSome := by
        intro name
        rw [Bool.eq_iff_iff, mapLookup_isSome]
        simp
      simp only [Elixir.Module.Types.Descr.«empty?/1»]
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
      simp [getMapKeys_single, absent "dynamic" (by decide) (by decide) (by decide), Erlang.erlang.«==/2»,
        Erlang.erlang.«is_map_key/2», none "atom" (by decide) (by decide) (by decide),
        none "bitmap" (by decide) (by decide) (by decide), none "fun" (by decide) (by decide) (by decide),
        Term.true, Term.false]
      by_cases empty : I = []
      · simp [empty]
      simp only [empty, if_false, anyKey]
      simp [Erlang.erlang.«not/1»]
      have tupleOk : ∀ r, mapLookup I (.atom "tuple") = some r →
          Elixir.Module.Types.Descr.«tuple_empty?/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 1 + 2)) r
            (.map []) = .ok (.atom "true") := fun r h => by
        rcases only _ r h with ⟨e, -⟩ | ⟨-, gone⟩ | ⟨e, -⟩
        · simp at e
        · exact gone (n + 1) []
        · simp at e
      have mapOk : ∀ r, mapLookup I (.atom "map") = some r →
          Elixir.Module.Types.Descr.«map_empty?/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) r (.map []) =
            .ok (.atom "true") := fun r h => by
        rcases only _ r h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, gone⟩
        · simp at e
        · simp at e
        · exact gone n []
      have listOk : ∀ r, mapLookup I (.atom "list") = some r →
          Elixir.Module.Types.Descr.«list_empty?/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) r (.map []) =
            .ok (.atom "true") := fun r h => by
        rcases only _ r h with ⟨-, wr, unsat⟩ | ⟨e, -⟩ | ⟨e, -⟩
        · exact list_empty_unsat _ wr unsat []
        · simp at e
        · simp at e
      cases ht : mapLookup I (.atom "tuple") <;> cases hm : mapLookup I (.atom "map") <;>
        cases hl : mapLookup I (.atom "list") <;>
        first
          | (simp [tupleOk _ ht, mapOk _ hm, listOk _ hl]; done)
          | (simp [tupleOk _ ht, mapOk _ hm]; done)
          | (simp [tupleOk _ ht, listOk _ hl]; done)
          | (simp [mapOk _ hm, listOk _ hl]; done)
          | (simp [tupleOk _ ht]; done)
          | (simp [mapOk _ hm]; done)
          | (simp [listOk _ hl]; done)
          | (simp; done)
    """

    # Negations are differences from the top type, which no type intersects.
    postlude ~LEAN"""
    /-- Symmetrical intersections whose common fields intersect to what remains of a type and its negation. -/
    theorem symmetrical_gone (depth : Nat) (name : String) (captures : Array Term) (L R : List (Term × Term))
        (g : Term → Term → Term → Term)
        (common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.function "Elixir.Module.Types.Descr" name 3 captures) #[q, x, y] = .ok (g q x y) ∧
          (kept (q, g q x y) = Bool.true → Gone q (g q x y))) :
        ∃ I, Elixir.Module.Types.Descr.«symmetrical_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
          (.map L) (.map R) (.function "Elixir.Module.Types.Descr" name 3 captures) = .ok (.map I) ∧
          ∀ q w, mapLookup I q = some w → Gone q w := by
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        name captures L R g (fun e member y hy => (common e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy).1)
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] I kept (by
          intro e _
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure,
            keep_field])
      refine ⟨out, ?_, fun q w hw => ?_⟩
      · unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runO]
      rw [lookO q] at hw
      cases hit : (mapEntries I).find? (fun e => decide (exactCompare q e.1 = .eq)) with
      | none => simp [hit] at hw
      | some e =>
        rw [hit] at hw
        have qe : exactCompare q e.1 = .eq := by simpa using List.find?_some hit
        have inI : mapLookup I e.1 = some e.2 :=
          mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hit)
        rw [lookI e.1] at inI
        cases hL : (mapEntries L).find? (fun f => decide (exactCompare e.1 f.1 = .eq)) with
        | none => simp [hL] at inI
        | some f =>
          rw [hL] at inI
          obtain ⟨y, hy, value⟩ := Option.map_eq_some_iff.mp inI
          have hx := mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hL)
          have ef : exactCompare e.1 f.1 = .eq := by simpa using List.find?_some hL
          have keep : kept e = kept (f.1, g f.1 f.2 y) := by rw [value]; rfl
          by_cases k : kept e = Bool.true
          · simp [k] at hw
            subst hw
            have gone := (common f.1 f.2 y hx hy).2 (by rw [← keep]; exact k)
            rw [value] at gone
            exact gone.congr (Std.TransCmp.eq_trans qe ef)
          · simp [k] at hw

    /-- Intersections keep at most an unsatisfiable list BDD when every common bitmap is
    disjoint, every common atom field holds no atom, function types cancel out, and list
    types are negations of each other. -/
    theorem intersection_disjoint (depth : Nat) (L R : List (Term × Term)) (validL : Negatable L)
        (staticR : mapLookup R (.atom "dynamic") = Option.none)
        (bitmaps : ∀ (b₁ : Nat) w, mapLookup L (.atom "bitmap") = some (.integer b₁) →
          mapLookup R (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0)
        (atoms : ∀ x y, mapLookup L (.atom "atom") = some x → mapLookup R (.atom "atom") = some y →
          ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
            x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
            y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
            Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
            (p₁ || p₂) = Bool.true ∧
            ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false)
        (funs : ∀ x y, mapLookup L (.atom "fun") = some x → mapLookup R (.atom "fun") = some y →
          Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table depth) x y =
            .ok (.integer 0))
        (lists : ∀ x y, mapLookup L (.atom "list") = some x → mapLookup R (.atom "list") = some y →
          Bdd ListOk x ∧ Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x)
        (tuples : ∀ x y, mapLookup L (.atom "tuple") = some x → mapLookup R (.atom "tuple") = some y →
          TupleCancel x y)
        (maps : ∀ x y, mapLookup L (.atom "map") = some x → mapLookup R (.atom "map") = some y →
          MapCancel x y) :
        ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map I) ∧
          ∀ q w, mapLookup I q = some w → Gone q w := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      -- Each common field intersects to a value the filter drops.
      have common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            q x y = .ok (g q x y) ∧
            (kept (q, g q x y) = Bool.true → Gone q (g q x y)) := by
        intro q x y hx hy
        rcases validL.keys q (by simp [hx]) with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hx
          obtain ⟨b₂, rfl, disjoint⟩ := bitmaps b₁ y hx hy
          simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», Erlang.erlang.«band/2», kept, disjoint]
        · obtain ⟨p₁, S₁, p₂, S₂, rfl, rfl, set₁, set₂, union, none⟩ := atoms x y hx hy
          rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, -, tag, nonempty, mE⟩ | ⟨hE, -⟩
          · exfalso
            have positive : p = Bool.true := by rw [tag, union]
            apply nonempty positive
            apply nil_of_lookup_none
            intro q
            have := mE q
            rw [none q, positive] at this
            cases h : mapLookup E q with
            | none => rfl
            | some _ => simp [h] at this
          · simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE, kept]
        · simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», funs x y hx hy, kept]
        · obtain ⟨wx, wy, sem⟩ := lists x y hx hy
          obtain ⟨r, run, keep, semr⟩ := inter_ok wx wy
          have value : g (.atom "list") x y = r := by
            simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», list_intersection_bdd wx wy, run]
          refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», list_intersection_bdd wx wy, run, value],
            fun _ => Or.inl ⟨rfl, value ▸ keep _ wx wy, fun ρ resp => ?_⟩⟩
          rw [value, semr ρ resp, sem ρ resp]
          cases eval ρ x <;> rfl
        · obtain ⟨r, run, empty⟩ := tuples x y hx hy
          have value : g (.atom "tuple") x y = r := by
            simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», run]
          refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run, value], fun k => ?_⟩
          rw [value] at k ⊢
          exact Or.inr (Or.inl ⟨rfl, empty k⟩)
        · obtain ⟨r, run, empty⟩ := maps x y hx hy
          have value : g (.atom "map") x y = r := by
            simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», run]
          refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run, value], fun k => ?_⟩
          rw [value] at k ⊢
          exact Or.inr (Or.inr ⟨rfl, empty k⟩)
      obtain ⟨I, run, only⟩ := symmetrical_gone depth "bare_intersection" #[] L R g fun q x y hx hy =>
        ⟨by rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure]; exact (common q x y hx hy).1,
          (common q x y hx hy).2⟩
      refine ⟨I, ?_, only⟩
      have absent : mapLookup R (.atom "dynamic") = Option.none := staticR
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»
      simp [getMapKeys_single, validL.static, absent, run]

    /-- The top type holds every bitmap and the negations of no atoms and of no functions. -/
    theorem unfolded_term_fields : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
        mapLookup T (.atom "bitmap") = some (.integer 255) ∧
        mapLookup T (.atom "atom") = some (.tuple #[.atom "negation", .map []]) ∧
        mapLookup T (.atom "fun") = some (.tuple #[.atom "negation", .map []]) ∧
        mapLookup T (.atom "dynamic") = Option.none :=
      ⟨_, rfl, by simp [mapLookup], by simp [mapLookup], by simp [mapLookup], by simp [mapLookup]⟩

    theorem negation_fields (depth : Nat) (X : List (Term × Term)) (valid : Negatable X) (nonempty : X ≠ []) :
        ∃ N, Elixir.Module.Types.Descr.«bare_negation/1»
            (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map X) = .ok (.map N) ∧
          mapLookup N (.atom "dynamic") = Option.none ∧
          (∀ (b₁ : Nat) w, mapLookup X (.atom "bitmap") = some (.integer b₁) →
            mapLookup N (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0) ∧
          (∀ x y, mapLookup X (.atom "atom") = some x → mapLookup N (.atom "atom") = some y →
            ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
              x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
              y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
              Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
              (p₁ || p₂) = Bool.true ∧
              ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) ∧
          (∀ x y, mapLookup X (.atom "fun") = some x → mapLookup N (.atom "fun") = some y → ∀ m,
            Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table m) x y =
              .ok (.integer 0)) ∧
          (∀ x y, mapLookup X (.atom "list") = some x → mapLookup N (.atom "list") = some y →
            Bdd ListOk x ∧ Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x) ∧
          (∀ x y, mapLookup X (.atom "tuple") = some x → mapLookup N (.atom "tuple") = some y →
            TupleCancel x y) ∧
          (∀ x y, mapLookup X (.atom "map") = some x → mapLookup N (.atom "map") = some y →
            MapCancel x y) ∧
          (∀ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) → ∀ name t,
            mapLookup T (.atom name) = some t →
            (mapLookup X (.atom name) = Option.none → mapLookup N (.atom name) = some t) ∧
            ∀ x w, mapLookup X (.atom name) = some x →
              Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
                (.atom name) t x = .ok w →
              mapLookup N (.atom name) = if kept (.atom name, w) then some w else Option.none) := by
      obtain ⟨T, term, termBitmap, termAtom, termFun, termDynamic⟩ := unfolded_term_fields
      have termTuple : mapLookup T (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      have termMap : mapLookup T (.atom "map") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      have termList : mapLookup T (.atom "list") =
          some (.tuple #[.integer 46675407, .atom "term", .atom "term"]) := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have noAtoms : Erlang.sets.elements? (.map []) = some [] := by simp [Erlang.sets.elements?]
      obtain ⟨N, fold, lookN⟩ := difference_fold depth (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
        g (mapEntries X) T (mapEntries_distinct X) (by
        intro e member v₁ found
        have hy := mapLookup_of_mem_mapEntries member
        rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure]
        rcases valid.keys e.1 (by simp [hy]) with key | key | key | key | key | key <;> rw [key] at found hy ⊢
        · rw [termBitmap] at found
          cases found
          obtain ⟨b, value, -⟩ := valid.bitmap e.2 hy
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», value]
        · rw [termAtom] at found
          cases found
          obtain ⟨p, S, value, set⟩ := valid.atom e.2 hy
          rw [value]
          rcases atom_difference false [] p S noAtoms set with ⟨_, _, hE, -⟩ | ⟨hE, -⟩ <;>
            simp only [Bool.false_eq_true, ite_false] at hE <;>
            simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
        · rw [termFun] at found
          cases found
          obtain ⟨y, run, -⟩ := fun_negation depth e.2 (valid.funs e.2 hy)
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
        · rw [termList] at found
          cases found
          rcases list_negation 46675407 e.2 (valid.lists e.2 hy) with run | ⟨-, y, run, -⟩ <;>
            simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
        · rw [termTuple] at found
          cases found
          obtain ⟨y, run, -⟩ := tuple_cancel e.2 (valid.tuples e.2 hy)
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
        · rw [termMap] at found
          cases found
          obtain ⟨y, run, -⟩ := map_cancel e.2 (valid.maps e.2 hy)
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run])
      have run : Elixir.Module.Types.Descr.«bare_negation/1»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map X) = .ok (.map N) := by
        simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
        unfold Elixir.Module.Types.Descr.«bare_difference/2»
        simp [Erlang.erlang.«==/2», unfold_map, static_map valid.static, nonempty]
        unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
        simp [Erlang.erlang.«==/2», nonempty, term, Erlang.maps.«fold/3»]
        simpa using fold
      refine ⟨N, run, ?_, fun b₁ w hX hN => ?_, fun x y hX hN => ?_, fun x y hX hN m => ?_, fun x y hX hN => ?_,
        fun x y hX hN => ?_, fun x y hX hN => ?_, fun T' term' name t hT => ?_⟩
      · rw [lookN, find_atom, valid.static]
        exact termDynamic
      · rw [lookN, find_atom, hX] at hN
        have le : 255 &&& b₁ ≤ 255 := Nat.and_le_left
        have value : g (.atom "bitmap") (.integer 255) (.integer b₁) = .integer ↑(255 - (255 &&& b₁)) := by
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]
          omega
        simp only [Option.map_some, termBitmap, Option.bind_some, value] at hN
        refine ⟨255 - (255 &&& b₁), ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
        · split at hN <;> simp_all
        · simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
          cases b₁.testBit i <;> simp
      · obtain ⟨pR, SR, rfl, setR⟩ := valid.atom x hX
        rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termAtom, Option.bind_some] at hN
        rcases atom_difference false [] pR SR noAtoms setR with ⟨p, E, hE, setE, tag, -, mE⟩ | ⟨hE, -⟩ <;>
          simp only [Bool.false_eq_true, ite_false] at hE
        · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
              (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) =
              .tuple #[.atom (if p then "union" else "negation"), .map E] := by
            simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
          have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) =
              Bool.true := by
            simp [kept]
          simp only [value, keep, ite_true, Option.some.injEq] at hN
          refine ⟨pR, SR, p, E, rfl, hN.symm, setR, setE, by rw [tag]; cases pR <;> rfl, fun q => ?_⟩
          rw [mE q]
          cases (mapLookup SR q).isSome <;> cases pR <;> simp [mapLookup]
        · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
              (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) = .integer 0 := by
            simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
          have drop : kept (.atom "atom", .integer 0) = Bool.false := by simp [kept]
          simp [value, drop] at hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termFun, Option.bind_some] at hN
        obtain ⟨w, negation, either⟩ := fun_negation depth x (valid.funs x hX)
        have value : g (.atom "fun") (.tuple #[.atom "negation", .map []]) x = w := by
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», negation]
        rw [value] at hN
        rcases either with rfl | all
        · simp [kept] at hN
        · split at hN
          · cases hN; exact all m
          · cases hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termList, Option.bind_some] at hN
        rcases list_negation 46675407 x (valid.lists x hX) with run | ⟨wx, w, run, wy, sem⟩
        · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x =
              .atom "bdd_bot" := by
            simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
          simp [value, kept] at hN
        · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x = w := by
            simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
          rw [value] at hN
          split at hN
          · cases hN; exact ⟨wx, wy, sem⟩
          · cases hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termTuple, Option.bind_some] at hN
        obtain ⟨w, run, cancel⟩ := tuple_cancel x (valid.tuples x hX)
        have value : g (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
        rw [value] at hN
        split at hN
        · rename_i k; cases hN; exact cancel k
        · cases hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termMap, Option.bind_some] at hN
        obtain ⟨w, run, cancel⟩ := map_cancel x (valid.maps x hX)
        have value : g (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
        rw [value] at hN
        split at hN
        · rename_i k; cases hN; exact cancel k
        · cases hN
      · rw [term] at term'
        cases term'
        refine ⟨fun hX => ?_, fun x w hX run => ?_⟩
        · rw [lookN, find_atom, hX]
          exact hT
        · rw [lookN, find_atom, hX]
          have value : g (.atom name) t x = w := by simp [g, run]
          simp only [Option.map_some, hT, Option.bind_some, value]
    """

    # The optimized operations compute the same negations of bitmaps, atoms, functions,
    # lists, and tuples, while open maps of one field negate to open maps of one field.
    # Their intersections fall back to BDD intersections, since the negation of a BDD
    # node is never a leaf, or intersect literals whose fields do not meet.
    postlude ~LEAN"""
    open BddProofs

    /-- Negations of list types are the same as without optimizations. -/
    theorem opt_list_difference_top (k : Int) (x seen : Term) :
        Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[.integer k, .atom "term", .atom "term"]) x seen =
          Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer k, .atom "term", .atom "term"]) x := by
      unfold Elixir.Module.Types.Descr.«opt_list_difference/3» Elixir.Module.Types.Descr.«list_difference/2»
      split
      · rfl
      · next h => split <;> simp_all
      · next h₁ h₂ => obtain ⟨-, rfl, rfl⟩ := h₂; exact (h₁ rfl rfl).elim
      · next h _ _ => exact (h _ rfl).elim

    /-- Intersections of list types with a type that is not a leaf are the same as without optimizations. -/
    theorem opt_list_intersection_node {x y seen : Term} (wx : Bdd ListOk x) (ny : ∀ k a b, y ≠ .tuple #[k, a, b]) :
        Elixir.Module.Types.Descr.«opt_list_intersection/3» d x y seen =
          Elixir.Module.Types.Descr.«list_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
      split
      · exact (not_top_leaf wx _ rfl).elim
      · exact (ny _ _ _ rfl).elim
      · exact (ny _ _ _ rfl).elim
      · rfl


    /-- Negations of tuple types are the same as without optimizations. -/
    theorem opt_tuple_difference_top (n : Nat) (x : Term) (field : TupleField x) :
        Elixir.Module.Types.Descr.«opt_tuple_difference/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 1))
          (.tuple #[.integer 61102469, .atom "open", .nil]) x =
          Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      rcases field with ⟨k, rfl⟩ | wx
      · simp [Elixir.Module.Types.Descr.«opt_tuple_difference/2», Elixir.Module.Types.Descr.«tuple_difference/2»]
      rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2» Elixir.Module.Types.Descr.«tuple_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/3»
        rfl
      · unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2» Elixir.Module.Types.Descr.«tuple_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/3»
        rfl
      · obtain ⟨⟨k', tag, ls, e, tags, -⟩, notTop⟩ := Bdd.leaf_iff.mp wx
        simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        by_cases special : tag = "closed" ∧ ls = []
        · obtain ⟨rfl, rfl⟩ := special
          rfl
        · have open' : ¬(tag = "open" ∧ ls = []) := by
            rintro ⟨rfl, rfl⟩
            exact notTop ⟨_, rfl⟩
          have ne : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠ .tuple #[k₁, .atom "closed", .nil] := by
            intro k₁ e
            simp at e
            apply special
            refine ⟨e.2.1, ?_⟩
            cases ls <;> simp_all [Term.list]
          have neTop : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠ .tuple #[k₁, .atom "open", .nil] := by
            intro k₁ e
            simp at e
            apply open'
            refine ⟨e.2.1, ?_⟩
            cases ls <;> simp_all [Term.list]
          have plain : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil])
              (.tuple #[.integer k, .atom tag, Term.list ls]) =
              Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer k, .atom tag, Term.list ls]) := by
            unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            split
            · next _ _ e => exact (neTop _ e).elim
            · next _ _ e => exact (ne _ e).elim
            · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; rfl
            · next h₁ => exact (h₁ _ _ rfl rfl).elim
          have opt : Elixir.Module.Types.Descr.«opt_tuple_difference/2» (Dispatcher.ofTable Erlang.program.fun_table (n + 1))
              (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom tag, Term.list ls]) =
              Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer k, .atom tag, Term.list ls]) := by
            unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2»
            split
            · next _ _ e => exact (neTop _ e).elim
            · next _ _ e => exact (ne _ e).elim
            · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; rfl
            · next h₁ => exact (h₁ _ _ rfl rfl).elim
          rw [plain, opt]
      · unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2» Elixir.Module.Types.Descr.«tuple_difference/2»
        simp

    /-- Optimized intersections of tuple types fall back to plain ones unless a leaf meets an open leaf or a node. -/
    theorem opt_tuple_intersection_fallback {d : Dispatcher} {x y seen : Term} (hx : ∀ k e, x ≠ .tuple #[k, .atom "open", e])
        (hy : ∀ a b c, y ≠ .tuple #[a, b, c]) :
        Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y seen = Elixir.Module.Types.Descr.«tuple_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
      split
      · exact (hx _ _ rfl).elim
      · exact (hy _ _ _ rfl).elim
      · exact (hy _ _ _ rfl).elim
      · exact (hx _ _ rfl).elim
      · exact (hy _ _ _ rfl).elim
      · rfl

    /-- Optimized intersections of tuple types with their negations. -/
    theorem opt_tuple_cancel (d : Dispatcher) (x : Term) (field : TupleField x) :
        ∃ nb, Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok nb ∧
          (kept (.atom "tuple", nb) = Bool.true → ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x nb (.map []) =
            .ok r ∧ (kept (.atom "tuple", r) = Bool.true → EmptyTuple r)) := by
      obtain ⟨nb, run, cancel⟩ := tuple_cancel x field
      refine ⟨nb, run, fun k => ?_⟩
      rcases field with ⟨k', rfl⟩ | wx
      · simp [Elixir.Module.Types.Descr.«tuple_difference/2»] at run
        subst run
        simp [kept] at k
      have notTop := not_top_of_ok wx fun t h => h.2
      rcases wx.shape with rfl | rfl | ⟨kx, tg, l, rfl⟩ | ⟨h, lit, c, u, d', rfl⟩
      · -- the top BDD has no negation
        unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
        simp [diff_leaf_top] at run
        subst run
        simp [kept] at k
      · -- the empty BDD meets the top literal
        unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
        simp [diff_leaf_bot] at run
        subst run
        refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
        unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
        rfl
      · obtain ⟨⟨k', tag, ls, e, tags, elems⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
        simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        by_cases special : tag = "closed" ∧ ls = []
        · obtain ⟨rfl, rfl⟩ := special
          obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
          have runK : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil])
              (.tuple #[.integer kx, .atom "closed", Term.list []]) =
              .ok (.tuple #[.integer ((1 <<< 27) + hash), .atom "open", Term.list [.atom "term"]]) := by
            unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
              Elixir.Module.Types.Descr.«bdd_leaf_key/2», Lynx.Except.guard, Erlang.erlang.«is_list/1»,
              Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»]
            rfl
          rw [runK] at run
          cases run
          refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
          unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
          simp [Elixir.Module.Types.Descr.«opt_bdd_seen/4», Erlang.maps.«put/3»,
            Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3», Elixir.Module.Types.Descr.«tuple_literal_intersection/5»,
            Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Lynx.Except.guard,
            Erlang.erlang.«</2», Term.list, getMapKeys_single, mapLookup]
          rfl
        · have open' : ¬(tag = "open" ∧ ls = []) := by
            rintro ⟨rfl, rfl⟩
            exact notTopX ⟨_, rfl⟩
          have wL : Bdd TupleLit (.tuple #[.integer kx, .atom tag, Term.list ls]) :=
            Bdd.leaf_iff.mpr ⟨kx, tag, ls, rfl, tags, elems⟩
          obtain ⟨h₁, node⟩ := node_new (.tuple #[.integer kx, .atom tag, Term.list ls]) (.atom "bdd_bot")
            (.atom "bdd_bot") (.atom "bdd_top") ⟨kx, _, _, rfl⟩ (Bdd.bot (ok := fun _ => True))
            (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
          have eq : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil])
              (.tuple #[.integer kx, .atom tag, Term.list ls]) =
              .ok (.tuple #[.integer h₁, .tuple #[.integer kx, .atom tag, Term.list ls], .atom "bdd_bot",
                .atom "bdd_bot", .atom "bdd_top"]) := by
            unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            split
            · next _ _ e =>
              exfalso
              simp at e
              obtain ⟨-, rfl, hl⟩ := e
              exact notTopX ⟨_, by rw [hl]⟩
            · rename_i h₁ h₂
              simp at h₁ h₂
              obtain ⟨-, rfl⟩ := h₁
              obtain ⟨-, rfl, hl⟩ := h₂
              exact (special ⟨rfl, by cases ls <;> simp_all [Term.list]⟩).elim
            · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; simp [Elixir.Module.Types.Descr.«bdd_negation/1», node]
            · next h₂ => exact (h₂ _ _ rfl rfl).elim
          rw [eq] at run
          cases run
          rcases tags with rfl | rfl
          · -- open leaves meet nodes of open literals, which intersect as usual
            obtain ⟨e₀, ls', rfl⟩ : ∃ e₀ ls', ls = e₀ :: ls' := by
              cases ls with
              | nil => exact (open' ⟨rfl, rfl⟩).elim
              | cons e₀ ls' => exact ⟨e₀, ls', rfl⟩
            have wn : Bdd TupleLit (.tuple #[.integer h₁, .tuple #[.integer kx, .atom "open", Term.list (e₀ :: ls')],
                .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) :=
              Bdd.node_iff.mpr ⟨⟨kx, _, _, rfl⟩, Bdd.leaf_iff.mp wL, Bdd.bot, Bdd.bot, Bdd.top⟩
            obtain ⟨r, rr, kr, sr⟩ := inter_ok wn wL
            refine ⟨r, ?_, fun _ => tuple_empty_unsat (kr _ wn wL) (fun _ h => h) fun ρ resp => ?_⟩
            · unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
              simp only [Term.list] at rr ⊢
              simp [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3», rr]
            · rw [sr ρ resp]
              cases ρ (.tuple #[.integer kx, .atom "open", Term.list (e₀ :: ls')]) <;> simp
          · -- closed leaves fall back to plain intersections
            rw [opt_tuple_intersection_fallback (fun _ _ e => by simp at e) (fun _ _ _ e => by simp at e)]
            exact cancel k
      · obtain ⟨y, runy, keepy, semy, leafless⟩ := neg_okN wx
        have : nb = y := by
          unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
          simp [runy] at run
          exact run.symm
        subst this
        have hy : ∀ a b c, nb ≠ .tuple #[a, b, c] := fun a b c e => by subst e; exact NoLeaf.leaf leafless
        rw [opt_tuple_intersection_fallback (fun _ _ e => by simp at e) hy]
        exact cancel k


    /-- Optimized negations of types: their fields are what the plain negation computes, except for maps. -/
    theorem opt_negation_fields (depth : Nat) (X : List (Term × Term)) (valid : Negatable X) (nonempty : X ≠ [])
        (seen : Term) (P : Term → Term → Prop)
        (maps : ∀ x, mapLookup X (.atom "map") = some x → ∃ y,
          Elixir.Module.Types.Descr.«opt_map_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.tuple #[.integer 61102469, .atom "open", .nil]) x seen = .ok y ∧ (kept (.atom "map", y) = Bool.true → P x y)) :
        ∃ N, Elixir.Module.Types.Descr.«opt_difference/3»
            (Dispatcher.ofTable Erlang.program.fun_table (depth + 3)) (.atom "term") (.map X) seen = .ok (.map N) ∧
          mapLookup N (.atom "dynamic") = Option.none ∧
          (∀ (b₁ : Nat) w, mapLookup X (.atom "bitmap") = some (.integer b₁) →
            mapLookup N (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0) ∧
          (∀ x y, mapLookup X (.atom "atom") = some x → mapLookup N (.atom "atom") = some y →
            ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
              x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
              y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
              Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
              (p₁ || p₂) = Bool.true ∧
              ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) ∧
          (∀ x y, mapLookup X (.atom "fun") = some x → mapLookup N (.atom "fun") = some y → ∀ m,
            Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table m) x y =
              .ok (.integer 0)) ∧
          (∀ x y, mapLookup X (.atom "list") = some x → mapLookup N (.atom "list") = some y →
            Bdd ListOk x ∧ Bdd ListOk y ∧ NoLeaf y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x) ∧
          (∀ x y, mapLookup X (.atom "tuple") = some x → mapLookup N (.atom "tuple") = some y → ∀ d,
            ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y (.map []) = .ok r ∧
              (kept (.atom "tuple", r) = Bool.true → EmptyTuple r)) ∧
          (∀ x y, mapLookup X (.atom "map") = some x → mapLookup N (.atom "map") = some y → P x y) ∧
          (mapLookup X (.atom "tuple") = Option.none →
            mapLookup N (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil])) ∧
          (∀ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) → ∀ name t,
            mapLookup T (.atom name) = some t →
            (mapLookup X (.atom name) = Option.none → mapLookup N (.atom name) = some t) ∧
            ∀ x w, mapLookup X (.atom name) = some x →
              Elixir.Module.Types.Descr.«opt_difference/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
                (.atom name) t x seen = .ok w →
              mapLookup N (.atom name) = if kept (.atom name, w) then some w else Option.none) := by
      obtain ⟨T, term, termBitmap, termAtom, termFun, termDynamic⟩ := unfolded_term_fields
      have termTuple : mapLookup T (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      have termMap : mapLookup T (.atom "map") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      have termList : mapLookup T (.atom "list") =
          some (.tuple #[.integer 46675407, .atom "term", .atom "term"]) := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«opt_difference/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
          k₀ v₁ v₂ seen with
        | .ok w => w
        | .error _ => .nil
      have noAtoms : Erlang.sets.elements? (.map []) = some [] := by simp [Erlang.sets.elements?]
      obtain ⟨N, fold, lookN⟩ := difference_fold (depth + 1)
        (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-0-" 3 #[seen])
        g (mapEntries X) T (mapEntries_distinct X) (by
        intro e member v₁ found
        have hy := mapLookup_of_mem_mapEntries member
        rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-0-/3».pure]
        simp only [Elixir.Module.Types.Descr.«-opt_difference/3-anonymous-0-/4»]
        rcases valid.keys e.1 (by simp [hy]) with key | key | key | key | key | key <;> rw [key] at found hy ⊢
        · rw [termBitmap] at found
          cases found
          obtain ⟨b, value, -⟩ := valid.bitmap e.2 hy
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», Erlang.erlang.«band/2», value]
        · rw [termAtom] at found
          cases found
          obtain ⟨p, S, value, set⟩ := valid.atom e.2 hy
          rw [value]
          rcases atom_difference false [] p S noAtoms set with ⟨_, _, hE, -⟩ | ⟨hE, -⟩ <;>
            simp only [Bool.false_eq_true, ite_false] at hE <;>
            simp only [g, Elixir.Module.Types.Descr.«opt_difference/4», hE]
        · rw [termFun] at found
          cases found
          obtain ⟨y, run, -⟩ := fun_negation (depth + 1) e.2 (valid.funs e.2 hy)
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», run]
        · rw [termList] at found
          cases found
          rcases list_negation 46675407 e.2 (valid.lists e.2 hy) with run | ⟨-, y, run, -⟩ <;>
            simp [g, Elixir.Module.Types.Descr.«opt_difference/4», opt_list_difference_top, run]
        · rw [termTuple] at found
          cases found
          obtain ⟨y, run, -⟩ := opt_tuple_cancel (Dispatcher.ofTable Erlang.program.fun_table 0) e.2 (valid.tuples e.2 hy)
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», opt_tuple_difference_top depth e.2 (valid.tuples e.2 hy), run]
        · rw [termMap] at found
          cases found
          obtain ⟨y, run, -⟩ := maps e.2 hy
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», run])
      have run : Elixir.Module.Types.Descr.«opt_difference/3»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 3)) (.atom "term") (.map X) seen = .ok (.map N) := by
        unfold Elixir.Module.Types.Descr.«opt_difference/3»
        simp [Erlang.erlang.«==/2», unfold_map, static_map valid.static, nonempty]
        unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
        simp [Erlang.erlang.«==/2», nonempty, term, Erlang.maps.«fold/3»]
        simpa using fold
      refine ⟨N, run, ?_, fun b₁ w hX hN => ?_, fun x y hX hN => ?_, fun x y hX hN m => ?_, fun x y hX hN => ?_,
        fun x y hX hN => ?_, fun x y hX hN => ?_, fun hX => ?_, fun T' term' name t hT => ?_⟩
      · rw [lookN, find_atom, valid.static]
        exact termDynamic
      · rw [lookN, find_atom, hX] at hN
        have le : 255 &&& b₁ ≤ 255 := Nat.and_le_left
        have value : g (.atom "bitmap") (.integer 255) (.integer b₁) = .integer ↑(255 - (255 &&& b₁)) := by
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», Erlang.erlang.«band/2»]
          omega
        simp only [Option.map_some, termBitmap, Option.bind_some, value] at hN
        refine ⟨255 - (255 &&& b₁), ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
        · split at hN <;> simp_all
        · simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
          cases b₁.testBit i <;> simp
      · obtain ⟨pR, SR, rfl, setR⟩ := valid.atom x hX
        rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termAtom, Option.bind_some] at hN
        rcases atom_difference false [] pR SR noAtoms setR with ⟨p, E, hE, setE, tag, -, mE⟩ | ⟨hE, -⟩ <;>
          simp only [Bool.false_eq_true, ite_false] at hE
        · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
              (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) =
              .tuple #[.atom (if p then "union" else "negation"), .map E] := by
            simp only [g, Elixir.Module.Types.Descr.«opt_difference/4», hE]
          have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) =
              Bool.true := by
            simp [kept]
          simp only [value, keep, ite_true, Option.some.injEq] at hN
          refine ⟨pR, SR, p, E, rfl, hN.symm, setR, setE, by rw [tag]; cases pR <;> rfl, fun q => ?_⟩
          rw [mE q]
          cases (mapLookup SR q).isSome <;> cases pR <;> simp [mapLookup]
        · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
              (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) = .integer 0 := by
            simp only [g, Elixir.Module.Types.Descr.«opt_difference/4», hE]
          have drop : kept (.atom "atom", .integer 0) = Bool.false := by simp [kept]
          simp [value, drop] at hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termFun, Option.bind_some] at hN
        obtain ⟨w, negation, either⟩ := fun_negation (depth + 1) x (valid.funs x hX)
        have value : g (.atom "fun") (.tuple #[.atom "negation", .map []]) x = w := by
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», negation]
        rw [value] at hN
        rcases either with rfl | all
        · simp [kept] at hN
        · split at hN
          · cases hN; exact all m
          · cases hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termList, Option.bind_some] at hN
        rcases list_negation 46675407 x (valid.lists x hX) with run | ⟨wx, w, run, wy, sem⟩
        · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x =
              .atom "bdd_bot" := by
            simp [g, Elixir.Module.Types.Descr.«opt_difference/4», opt_list_difference_top, run]
          simp [value, kept] at hN
        · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x = w := by
            simp [g, Elixir.Module.Types.Descr.«opt_difference/4», opt_list_difference_top, run]
          rw [value] at hN
          split at hN
          · cases hN
            refine ⟨wx, wy, ?_, sem⟩
            obtain ⟨w', run', -, -, leafless⟩ := neg_okN wx
            have nt := not_top_leaf wx
            have : Elixir.Module.Types.Descr.«list_difference/2»
                (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x = .ok w' := by
              unfold Elixir.Module.Types.Descr.«list_difference/2»
              split
              · exact (nt _ rfl).elim
              · exact run'
              · next h₁ h₂ => first | exact (h₁ _ rfl).elim | exact (h₁ _ _ rfl).elim | exact absurd rfl (h₁ _) | simp_all
            rw [this] at run
            cases run
            exact leafless
          · cases hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termTuple, Option.bind_some] at hN
        intro d
        obtain ⟨w, run, cancel⟩ := opt_tuple_cancel d x (valid.tuples x hX)
        have value : g (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», opt_tuple_difference_top depth x (valid.tuples x hX), run]
        rw [value] at hN
        split at hN
        · rename_i k; cases hN; exact cancel k
        · cases hN
      · rw [lookN, find_atom, hX] at hN
        simp only [Option.map_some, termMap, Option.bind_some] at hN
        obtain ⟨w, run, cancel⟩ := maps x hX
        have value : g (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
          simp [g, Elixir.Module.Types.Descr.«opt_difference/4», run]
        rw [value] at hN
        split at hN
        · rename_i k; cases hN; exact cancel k
        · cases hN
      · rw [lookN, find_atom, hX]
        exact termTuple
      · rw [term] at term'
        cases term'
        refine ⟨fun hX => ?_, fun x w hX run => ?_⟩
        · rw [lookN, find_atom, hX]
          exact hT
        · rw [lookN, find_atom, hX]
          have value : g (.atom name) t x = w := by simp [g, run]
          simp only [Option.map_some, hT, Option.bind_some, value]

    /-- Optimized intersections of types whose common fields cancel out. -/
    theorem opt_intersection_disjoint (depth : Nat) (L R : List (Term × Term)) (seen : Term) (validL : Negatable L)
        (staticR : mapLookup R (.atom "dynamic") = Option.none)
        (bitmaps : ∀ (b₁ : Nat) w, mapLookup L (.atom "bitmap") = some (.integer b₁) →
          mapLookup R (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0)
        (atoms : ∀ x y, mapLookup L (.atom "atom") = some x → mapLookup R (.atom "atom") = some y →
          ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
            x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
            y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
            Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
            (p₁ || p₂) = Bool.true ∧
            ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false)
        (funs : ∀ x y, mapLookup L (.atom "fun") = some x → mapLookup R (.atom "fun") = some y →
          Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table depth) x y =
            .ok (.integer 0))
        (lists : ∀ x y, mapLookup L (.atom "list") = some x → mapLookup R (.atom "list") = some y →
          Bdd ListOk x ∧ Bdd ListOk y ∧ NoLeaf y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x)
        (tuples : ∀ x y, mapLookup L (.atom "tuple") = some x → mapLookup R (.atom "tuple") = some y →
          ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            x y seen = .ok r ∧ (kept (.atom "tuple", r) = Bool.true → EmptyTuple r))
        (maps : ∀ x y, mapLookup L (.atom "map") = some x → mapLookup R (.atom "map") = some y →
          ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            x y seen = .ok r ∧ (kept (.atom "map", r) = Bool.true → EmptyMap r)) :
        ∃ I, Elixir.Module.Types.Descr.«opt_intersection/3»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) seen = .ok (.map I) ∧
          ∀ q w, mapLookup I q = some w → Gone q w := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«opt_intersection/4» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ seen with
        | .ok w => w
        | .error _ => .nil
      have common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          Elixir.Module.Types.Descr.«opt_intersection/4» (Dispatcher.ofTable Erlang.program.fun_table depth)
            q x y seen = .ok (g q x y) ∧
            (kept (q, g q x y) = Bool.true → Gone q (g q x y)) := by
        intro q x y hx hy
        rcases validL.keys q (by simp [hx]) with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hx
          obtain ⟨b₂, rfl, disjoint⟩ := bitmaps b₁ y hx hy
          simp [g, Elixir.Module.Types.Descr.«opt_intersection/4», Erlang.erlang.«band/2», kept, disjoint]
        · obtain ⟨p₁, S₁, p₂, S₂, rfl, rfl, set₁, set₂, union, none⟩ := atoms x y hx hy
          rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, -, tag, nonempty, mE⟩ | ⟨hE, -⟩
          · exfalso
            have positive : p = Bool.true := by rw [tag, union]
            apply nonempty positive
            apply nil_of_lookup_none
            intro q
            have := mE q
            rw [none q, positive] at this
            cases h : mapLookup E q with
            | none => rfl
            | some _ => simp [h] at this
          · simp [g, Elixir.Module.Types.Descr.«opt_intersection/4», hE, kept]
        · simp [g, Elixir.Module.Types.Descr.«opt_intersection/4», funs x y hx hy, kept]
        · obtain ⟨wx, wy, ny, sem⟩ := lists x y hx hy
          obtain ⟨r, run, keep, semr⟩ := inter_ok wx wy
          have leafless : ∀ k a b, y ≠ .tuple #[k, a, b] := fun k a b e => by subst e; exact NoLeaf.leaf ny
          have value : g (.atom "list") x y = r := by
            simp [g, Elixir.Module.Types.Descr.«opt_intersection/4», opt_list_intersection_node wx leafless,
              list_intersection_bdd wx wy, run]
          refine ⟨by simp [Elixir.Module.Types.Descr.«opt_intersection/4», opt_list_intersection_node wx leafless,
              list_intersection_bdd wx wy, run, value],
            fun _ => Or.inl ⟨rfl, value ▸ keep _ wx wy, fun ρ resp => ?_⟩⟩
          rw [value, semr ρ resp, sem ρ resp]
          cases eval ρ x <;> rfl
        · obtain ⟨r, run, empty⟩ := tuples x y hx hy
          have value : g (.atom "tuple") x y = r := by
            simp [g, Elixir.Module.Types.Descr.«opt_intersection/4», run]
          refine ⟨by simp [Elixir.Module.Types.Descr.«opt_intersection/4», run, value], fun k => ?_⟩
          rw [value] at k ⊢
          exact Or.inr (Or.inl ⟨rfl, empty k⟩)
        · obtain ⟨r, run, empty⟩ := maps x y hx hy
          have value : g (.atom "map") x y = r := by
            simp [g, Elixir.Module.Types.Descr.«opt_intersection/4», run]
          refine ⟨by simp [Elixir.Module.Types.Descr.«opt_intersection/4», run, value], fun k => ?_⟩
          rw [value] at k ⊢
          exact Or.inr (Or.inr ⟨rfl, empty k⟩)
      obtain ⟨I, run, only⟩ := symmetrical_gone depth "-opt_intersection/3-anonymous-0-" #[seen] L R g
        fun q x y hx hy =>
          ⟨by rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_intersection/3-anonymous-0-/3».pure]
              simp only [Elixir.Module.Types.Descr.«-opt_intersection/3-anonymous-0-/4»]
              exact (common q x y hx hy).1,
            (common q x y hx hy).2⟩
      refine ⟨I, ?_, only⟩
      have absent : mapLookup R (.atom "dynamic") = Option.none := staticR
      unfold Elixir.Module.Types.Descr.«opt_intersection/3»
      simp [getMapKeys_single, validL.static, absent, run]

    /-- The top tuple literal is not empty. -/
    theorem tuple_empty_top (d : Dispatcher) :
        Elixir.Module.Types.Descr.«tuple_empty?/2» d (.tuple #[.integer 61102469, .atom "open", .nil]) (.map []) =
          .ok (.atom "false") := by
      unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Erlang.maps.«put/3»,
        Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
        Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Lynx.Except.andAlso,
        Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«zip_intersection/4», Erlang.lists.«reverse/2»,
        Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4», Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2»,
        Erlang.lists.«any/2», Lynx.Except.guard, Erlang.erlang.«>=/2», Erlang.erlang.«/=/2», Erlang.erlang.«is_function/2»]

    theorem any_key (X : List (Term × Term)) (name : String) :
        (X.any fun e => exactCompare (.atom name) e.1 == .eq) = (mapLookup X (.atom name)).isSome := by
      rw [Bool.eq_iff_iff, mapLookup_isSome]
      simp

    /-- Types with a tuple field holding all tuples are not empty. -/
    theorem empty_top_tuple (d : Dispatcher) (N : List (Term × Term)) (static : mapLookup N (.atom "dynamic") = Option.none)
        (tuple : mapLookup N (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil])) :
        Elixir.Module.Types.Descr.«empty_seen?/2» d (.map N) (.map []) = .ok (.atom "false") := by
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
      have nonempty : N ≠ [] := by rintro rfl; simp [mapLookup] at tuple
      simp [getMapKeys_single, static, Erlang.erlang.«==/2», Erlang.erlang.«is_map_key/2», any_key, Term.true, Term.false,
        nonempty, tuple]
      cases ha : mapLookup N (.atom "atom") <;> cases hb : mapLookup N (.atom "bitmap") <;>
        simp [Erlang.erlang.«not/1», Lynx.Except.andAlso, tuple_empty_top]

    theorem Valid.absent {V : List (Term × Term)} (valid : Valid V) (name : String) (nb : name ≠ "bitmap")
        (na : name ≠ "atom") : mapLookup V (.atom name) = Option.none := by
      cases h : mapLookup V (.atom name) with
      | none => rfl
      | some w =>
        rcases valid.keys (.atom name) (by rw [h]; rfl) with e | e
        · cases e; exact absurd rfl nb
        · cases e; exact absurd rfl na

    theorem Valid.negatable {V : List (Term × Term)} (valid : Valid V) : Negatable V := by
      refine ⟨fun q h => ?_, valid.bitmap, valid.atom, valid.atomUnion, fun w h => ?_, fun w h => ?_, fun w h => ?_,
        fun w h => ?_, fun w h => ?_⟩
      · rcases valid.keys q h with rfl | rfl <;> simp
      · simp [valid.absent "fun" (by decide) (by decide)] at h
      · simp [valid.absent "fun" (by decide) (by decide)] at h
      · simp [valid.absent "list" (by decide) (by decide)] at h
      · simp [valid.absent "tuple" (by decide) (by decide)] at h
      · simp [valid.absent "map" (by decide) (by decide)] at h

    /-- Flat field types other than none: their optimized negation is not empty and does not meet them. -/
    theorem field_negation (n : Nat) (V : List (Term × Term)) (valid : Valid V) (nonempty : V ≠ []) (seen : Term) :
        ∃ D, Elixir.Module.Types.Descr.«opt_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 3))
            (.atom "term") (.map V) seen = .ok (.map D) ∧
          (∀ d, Elixir.Module.Types.Descr.«empty_seen?/2» d (.map D) (.map []) = .ok (.atom "false")) ∧
          ∀ m seen', ∃ I, Elixir.Module.Types.Descr.«opt_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table (m + 1))
            (.map V) (.map D) seen' = .ok (.map I) ∧
            ∀ k, Elixir.Module.Types.Descr.«empty_seen?/2» (Dispatcher.ofTable Erlang.program.fun_table (k + 3)) (.map I)
              (.map []) = .ok (.atom "true") := by
      have absent := valid.absent
      obtain ⟨D, run, static, bitmaps, atoms, -, -, -, -, tuple, -⟩ := opt_negation_fields n V valid.negatable nonempty seen
        (fun _ _ => True) (fun x h => by simp [absent "map" (by decide) (by decide)] at h)
      refine ⟨D, run, fun d => empty_top_tuple d D static (tuple (absent "tuple" (by decide) (by decide))), fun m seen' => ?_⟩
      obtain ⟨I, runI, only⟩ := opt_intersection_disjoint m V D seen' valid.negatable static bitmaps atoms
        (fun x y h => by simp [absent "fun" (by decide) (by decide)] at h)
        (fun x y h => by simp [absent "list" (by decide) (by decide)] at h)
        (fun x y h => by simp [absent "tuple" (by decide) (by decide)] at h)
        (fun x y h => by simp [absent "map" (by decide) (by decide)] at h)
      refine ⟨I, runI, fun k => ?_⟩
      have := empty_gone k I only
      simpa [Elixir.Module.Types.Descr.«empty?/1», Term.true] using this

    /-- Open map literals of one field whose types do not meet, and one of which is required, have no intersection. -/
    theorem one_key_literal_empty (m : Nat) (key t₁ t₂ t F seen : Term) (o₁ o₂ : Bool) (opt : (o₁ && o₂) = Bool.false)
        (inter : Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (m + 1)) F #[t₁, t₂] = .ok t)
        (empty : Elixir.Module.Types.Descr.«empty_seen?/2» (Dispatcher.ofTable Erlang.program.fun_table (m + 1)) t seen =
          .ok (.atom "true")) :
        Elixir.Module.Types.Descr.«map_literal_intersection/6» (Dispatcher.ofTable Erlang.program.fun_table (m + 2))
          (.atom "open") (fieldsTerm [(key, .tuple #[t₁, boolAtom o₁])]) (.atom "open")
          (fieldsTerm [(key, .tuple #[t₂, boolAtom o₂])]) F seen = .error (Exception.throw (.atom "empty")) := by
      have call : Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (m + 2))
          (.function "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-0-" 3 #[F, seen])
          #[key, .tuple #[t₁, boolAtom o₁], .tuple #[t₂, boolAtom o₂]] = .error (Exception.throw (.atom "empty")) := by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure]
        unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
        cases o₁ <;> cases o₂ <;> simp at opt <;>
          simp [boolAtom, Lynx.Except.andAlso, inter, empty, Lynx.Except.guard]
      unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
      simp only [fieldsTerm, List.map, Term.list, pure_bind]
      unfold Erlang.orddict.«merge/3»
      simp [Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», compare_self, call]

    /-- Open map literals of a single field. -/
    def OneKey (x : Term) : Prop := ∃ (k : Int) (key v : Term), x = .tuple #[.integer k, .atom "open", fieldsTerm [(key, v)]]

    /-- Optimized negations of map types other than open maps of one field are the plain ones. -/
    theorem opt_map_difference_eq (n : Nat) (x : Term) (field : MapField x) (notOne : ¬OneKey x) :
        Elixir.Module.Types.Descr.«opt_map_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 2))
          (.tuple #[.integer 61102469, .atom "open", .nil]) x (.map []) =
          Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      rcases field with ⟨k, rfl⟩ | wx
      · simp [Elixir.Module.Types.Descr.«opt_map_difference/3», Elixir.Module.Types.Descr.«map_difference/2»]
      rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_difference/3» Elixir.Module.Types.Descr.«map_difference/2»
        simp [Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup, Erlang.maps.«put/3»]
        unfold Elixir.Module.Types.Descr.«bdd_difference/3»
        rfl
      · unfold Elixir.Module.Types.Descr.«opt_map_difference/3» Elixir.Module.Types.Descr.«map_difference/2»
        simp [Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup, Erlang.maps.«put/3»]
        unfold Elixir.Module.Types.Descr.«bdd_difference/3»
        rfl
      · obtain ⟨⟨k', tag, l, e, tags, fields⟩, notTop⟩ := Bdd.leaf_iff.mp wx
        simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        have open' : ¬(tag = "open" ∧ l = []) := by
          rintro ⟨rfl, rfl⟩
          exact notTop ⟨_, rfl⟩
        have one : ¬(tag = "open" ∧ ∃ e, l = [e]) := by
          rintro ⟨rfl, ⟨key, v⟩, rfl⟩
          exact notOne ⟨k, key, v, rfl⟩
        have neTop : ∀ k₁, Term.tuple #[.integer k, .atom tag, fieldsTerm l] ≠ .tuple #[k₁, .atom "open", .nil] := by
          intro k₁ e
          simp at e
          apply open'
          refine ⟨e.2.1, ?_⟩
          cases l <;> simp_all [fieldsTerm, Term.list]
        have plain : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil])
            (.tuple #[.integer k, .atom tag, fieldsTerm l]) =
            Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer k, .atom tag, fieldsTerm l]) := by
          unfold Elixir.Module.Types.Descr.«map_difference/2»
          split
          · next _ _ e => exact (neTop _ e).elim
          · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; rfl
          · next h₁ => exact (h₁ _ _ rfl rfl).elim
        rw [plain]
        rcases l with _ | ⟨e₀, _ | ⟨e₁, l'⟩⟩
        · rcases tags with rfl | rfl
          · exact (open' ⟨rfl, rfl⟩).elim
          simp only [fieldsTerm, List.map, Term.list]
          rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
          simp
        · rcases tags with rfl | rfl
          · exact (one ⟨rfl, e₀, rfl⟩).elim
          simp only [fieldsTerm, List.map, Term.list]
          rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
          simp
        · simp only [fieldsTerm, List.map, Term.list]
          rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
          simp
      · unfold Elixir.Module.Types.Descr.«opt_map_difference/3» Elixir.Module.Types.Descr.«map_difference/2»
        simp

    theorem difference_term_term (d : Dispatcher) (x S : Term) :
        Elixir.Module.Types.Descr.«opt_difference/3» d x (.atom "term") S = .ok (.map []) := by
      unfold Elixir.Module.Types.Descr.«opt_difference/3»
      rfl

    theorem difference_term_none (d : Dispatcher) (S : Term) :
        Elixir.Module.Types.Descr.«opt_difference/3» d (.atom "term") (.map []) S = .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«opt_difference/3»
      simp [Lynx.Except.guard, Erlang.erlang.«==/2»]

    theorem leaf_new_open (key f : Term) : ∃ kd : Int,
        Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "open") (Term.list [.tuple #[key, f]]) =
          .ok (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, f)]]) := by
      obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.tuple #[key, f]]))
      refine ⟨(1 <<< 27) + hash, ?_⟩
      simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2»,
        Erlang.erlang.«is_list/1», Erlang.erlang.«length/1», Erlang.erlang.«bsl/2», fieldsTerm, Lynx.Except.guard]
      rfl

    /-- The difference of the top type with a field type of the specification, which never meets it. -/
    theorem one_key_field (n : Nat) (v S : Term) (fv : FieldType v) :
        ∃ D', Elixir.Module.Types.Descr.«opt_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 4))
            (.atom "term") v S = .ok D' ∧
          (Elixir.Module.Types.Descr.«empty?/1» (Dispatcher.ofTable Erlang.program.fun_table (n + 4)) D' =
            .ok (.atom "true") ∨
            Elixir.Module.Types.Descr.«empty?/1» (Dispatcher.ofTable Erlang.program.fun_table (n + 4)) D' =
              .ok (.atom "false")) ∧
          ∀ m S', ∃ t, Elixir.Module.Types.Descr.«opt_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table (m + 2))
            v D' S' = .ok t ∧
            Elixir.Module.Types.Descr.«empty_seen?/2» (Dispatcher.ofTable Erlang.program.fun_table (m + 3)) t (.map []) =
              .ok (.atom "true") := by
      have noneEmpty : ∀ d, Elixir.Module.Types.Descr.«empty_seen?/2» d (.map []) (.map []) = .ok (.atom "true") :=
        fun d => by simpa [Elixir.Module.Types.Descr.«empty?/1», Term.true] using empty_none d
      rcases fv with rfl | ⟨V, rfl, valid⟩
      · exact ⟨.map [], difference_term_term _ _ S, Or.inl (empty_none _),
          fun m S' => ⟨.map [], by unfold Elixir.Module.Types.Descr.«opt_intersection/3»; rfl, noneEmpty _⟩⟩
      by_cases nonempty : V = []
      · subst nonempty
        exact ⟨.atom "term", difference_term_none _ S, Or.inr (by simp [Elixir.Module.Types.Descr.«empty?/1»]),
          fun m S' => ⟨.map [], by unfold Elixir.Module.Types.Descr.«opt_intersection/3»; rfl, noneEmpty _⟩⟩
      · obtain ⟨D, run, nonemptyD, meet⟩ := field_negation (n + 1) V valid nonempty S
        refine ⟨.map D, run, Or.inr (by simpa [Elixir.Module.Types.Descr.«empty?/1»] using nonemptyD _), fun m S' => ?_⟩
        obtain ⟨I, runI, emptyI⟩ := meet (m + 1) S'
        exact ⟨.map I, runI, emptyI m⟩

    /-- Optimized intersections of map types fall back to plain ones unless a leaf meets an open leaf or a node. -/
    theorem opt_map_intersection_fallback {d : Dispatcher} {x y seen : Term} (hx : ∀ k e, x ≠ .tuple #[k, .atom "open", e])
        (hy : ∀ a b c, y ≠ .tuple #[a, b, c]) :
        Elixir.Module.Types.Descr.«opt_map_intersection/3» d x y seen = Elixir.Module.Types.Descr.«map_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
      split
      · exact (hx _ _ rfl).elim
      · exact (hy _ _ _ rfl).elim
      · exact (hy _ _ _ rfl).elim
      · exact (hx _ _ rfl).elim
      · exact (hy _ _ _ rfl).elim
      · rfl

    /-- Optimized intersections of map types with their optimized negations. -/
    theorem opt_map_cancel (n : Nat) (x : Term) (field : MapField x) :
        ∃ nb, Elixir.Module.Types.Descr.«opt_map_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 5))
          (.tuple #[.integer 61102469, .atom "open", .nil]) x (.map []) = .ok nb ∧
          (kept (.atom "map", nb) = Bool.true → ∀ m, ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3»
            (Dispatcher.ofTable Erlang.program.fun_table (m + 4)) x nb (.map []) = .ok r ∧
            (kept (.atom "map", r) = Bool.true → EmptyMap r)) := by
      by_cases one : OneKey x
      · obtain ⟨k, key, w, rfl⟩ := one
        have fw : FieldValueV w := by
          rcases field with ⟨k', e⟩ | wx
          · simp [fieldsTerm, Term.list] at e
          · obtain ⟨⟨k', tag, l, e, -, fields⟩, -⟩ := Bdd.leaf_iff.mp wx
            simp at e
            obtain ⟨-, -, hl⟩ := e
            rcases l with _ | ⟨⟨key', w'⟩, _ | ⟨_, _⟩⟩ <;> simp [fieldsTerm, Term.list] at hl
            obtain ⟨-, rfl⟩ := hl
            exact fields (key', w) (by simp)
        obtain ⟨v, o, rfl, fv⟩ := fw
        obtain ⟨D', hD, empty, meet⟩ := one_key_field (n + 1) v
          (.map [(.tuple #[.atom "map_difference", .tuple #[.integer 61102469, .atom "open", .nil],
            .tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]], .atom "true")]) fv
        have hD5 : Elixir.Module.Types.Descr.«opt_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 5))
            (.atom "term") v (.map [(.tuple #[.atom "map_difference", .tuple #[.integer 61102469, .atom "open", .nil],
            .tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]], .atom "true")]) =
            .ok D' := hD
        obtain ⟨kd, leaf⟩ := leaf_new_open key (.tuple #[D', boolAtom !o])
        have run : ∀ e, Elixir.Module.Types.Descr.«empty?/1» (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) D' =
            .ok (.atom e) → Elixir.Module.Types.Descr.«opt_map_difference/3»
              (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) (.tuple #[.integer 61102469, .atom "open", .nil])
              (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]) (.map []) =
            if o = Bool.true ∧ e = "true" then .ok (.atom "bdd_bot")
            else .ok (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[D', boolAtom !o])]]) := by
          intro e he
          simp only [fieldsTerm, List.map, Term.list] at leaf hD5 ⊢
          unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
          cases o <;> simp [boolAtom] at leaf hD5 <;>
            simp [Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup,
            Erlang.maps.«put/3», Elixir.Module.Types.Descr.«map_key_tag_to_field/1»,
            Elixir.Module.Types.Descr.«field_opt_difference/3», hD5, Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom,
            Elixir.Module.Types.Descr.«field_empty?/1», he, leaf, Lynx.Except.guard, Term.list]
          all_goals by_cases ee : e = "true" <;> simp_all [Lynx.Except.guard]
        have runAny : ∃ nb, Elixir.Module.Types.Descr.«opt_map_difference/3»
            (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) (.tuple #[.integer 61102469, .atom "open", .nil])
            (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]) (.map []) = .ok nb ∧
            (nb = .atom "bdd_bot" ∨ nb = .tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[D', boolAtom !o])]]) := by
          have empty' : Elixir.Module.Types.Descr.«empty?/1» (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) D' =
              .ok (.atom "true") ∨ Elixir.Module.Types.Descr.«empty?/1» (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) D' =
              .ok (.atom "false") := empty
          rcases empty' with he | he <;> rw [run _ he] <;> split <;> exact ⟨_, rfl, by simp⟩
        obtain ⟨nb, hnb, shape⟩ := runAny
        refine ⟨nb, hnb, fun kn m => ?_⟩
        rcases shape with rfl | rfl
        · simp [kept] at kn
        · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
          let S₃ : Term := .map [(.tuple #[.atom "map_intersection",
            .tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]],
            .tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[D', boolAtom !o])]]], .atom "true")]
          obtain ⟨t, inter, empty⟩ := meet m S₃
          have lit := one_key_literal_empty (m + 2) key v D' t
            (.function "Elixir.Module.Types.Descr" "-opt_map_leaf_intersection/3-fun-0-" 2 #[S₃]) (.map []) o (!o)
            (by cases o <;> rfl)
            (by rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_map_leaf_intersection/3-fun-0-/2».pure]; exact inter) empty
          unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
          simp only [fieldsTerm, List.map, Term.list] at lit ⊢
          simp [Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup, Erlang.maps.«put/3»]
          unfold Elixir.Module.Types.Descr.«opt_map_leaf_intersection/3»
          simp [S₃, fieldsTerm, Term.list] at lit
          simp [lit]
          rfl
      · obtain ⟨nb, run, cancel⟩ := map_cancel x field
        refine ⟨nb, by rw [opt_map_difference_eq (n + 3) x field one]; exact run, fun k m => ?_⟩
        rcases field with ⟨k', rfl⟩ | wx
        · simp [Elixir.Module.Types.Descr.«map_difference/2»] at run
          subst run
          simp [kept] at k
        have notTop := not_top_of_ok wx fun t h => h.2
        rcases wx.shape with rfl | rfl | ⟨kx, tg, l, rfl⟩ | ⟨h, lit, c, u, d', rfl⟩
        · unfold Elixir.Module.Types.Descr.«map_difference/2» at run
          simp [diff_leaf_top] at run
          subst run
          simp [kept] at k
        · unfold Elixir.Module.Types.Descr.«map_difference/2» at run
          simp [diff_leaf_bot] at run
          subst run
          refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
          unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
          rfl
        · obtain ⟨⟨k', tag, ls, e, tags, fields⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
          simp at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          have wL : Bdd MapLit (.tuple #[.integer kx, .atom tag, fieldsTerm ls]) :=
            Bdd.leaf_iff.mpr (Bdd.leaf_iff.mp wx).1.lit
          obtain ⟨h₁, node⟩ := node_new (.tuple #[.integer kx, .atom tag, fieldsTerm ls]) (.atom "bdd_bot")
            (.atom "bdd_bot") (.atom "bdd_top") ⟨kx, _, _, rfl⟩ (Bdd.bot (ok := fun _ => True))
            (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
          have eq : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil])
              (.tuple #[.integer kx, .atom tag, fieldsTerm ls]) =
              .ok (.tuple #[.integer h₁, .tuple #[.integer kx, .atom tag, fieldsTerm ls], .atom "bdd_bot",
                .atom "bdd_bot", .atom "bdd_top"]) := by
            unfold Elixir.Module.Types.Descr.«map_difference/2»
            split
            · next _ _ e => exact (notTop _ e).elim
            · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq
              simp [Elixir.Module.Types.Descr.«bdd_negation/1», node]
            · next h₂ => exact (h₂ _ _ rfl rfl).elim
          rw [eq] at run
          cases run
          rcases tags with rfl | rfl
          · -- open leaves meet nodes of open literals, which intersect as usual
            obtain ⟨e₀, ls', rfl⟩ : ∃ e₀ ls', ls = e₀ :: ls' := by
              cases ls with
              | nil => exact (notTopX ⟨_, rfl⟩).elim
              | cons e₀ ls' => exact ⟨e₀, ls', rfl⟩
            have wn : Bdd MapLit (.tuple #[.integer h₁, .tuple #[.integer kx, .atom "open", fieldsTerm (e₀ :: ls')],
                .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) :=
              Bdd.node_iff.mpr ⟨⟨kx, _, _, rfl⟩, Bdd.leaf_iff.mp wL, Bdd.bot, Bdd.bot, Bdd.top⟩
            obtain ⟨r, rr, kr, sr⟩ := inter_ok wn wL
            refine ⟨r, ?_, fun _ => map_empty_unsat (kr _ wn wL) (fun _ h => h) fun ρ resp => ?_⟩
            · unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
              simp only [fieldsTerm, List.map, Term.list] at rr ⊢
              simp [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3», rr]
            · rw [sr ρ resp]
              cases ρ (.tuple #[.integer kx, .atom "open", fieldsTerm (e₀ :: ls')]) <;> simp
          · -- closed leaves fall back to plain intersections
            rw [opt_map_intersection_fallback (fun _ _ e => by simp at e) (fun _ _ _ e => by simp at e)]
            exact cancel k
        · obtain ⟨y, runy, keepy, semy, leafless⟩ := neg_okN wx
          have : nb = y := by
            unfold Elixir.Module.Types.Descr.«map_difference/2» at run
            simp [runy] at run
            exact run.symm
          subst this
          have hy : ∀ a b c, nb ≠ .tuple #[a, b, c] := fun a b c e => by subst e; exact NoLeaf.leaf leafless
          rw [opt_map_intersection_fallback (fun _ _ e => by simp at e) hy]
          exact cancel k

    end Elixir.STTDescrProofsTest
    """

    # The top type is a subtype of a type united with its negation: each field of the top
    # type, minus what the type and its negation unite into at that field, is empty.
    # Propositional BDD unions are tautologies, while `{}` and its negation `{term, ...}`
    # are checked as concrete tuple lines.
    postlude ~LEAN"""
    namespace Elixir.STTDescrProofsTest
    open Lynx Lynx.Term BddProofs

    /-- A field of the left type whose difference with the right type is empty. -/
    def Covered (d : Dispatcher) (U : List (Term × Term)) (q t : Term) : Prop :=
      ∃ u w, mapLookup U q = some u ∧ Elixir.Module.Types.Descr.«bare_difference/3» d q t u = .ok w ∧
        (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
          Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))

    theorem iterator_covered (d : Dispatcher) (U : List (Term × Term)) :
        ∀ es : List (Term × Term), (∀ e ∈ es, Covered d U e.1 e.2) →
          (do
            let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
            Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» d it (.map U) (.map [])) =
            .ok (.atom "true") := by
      intro es
      induction es with
      | nil =>
        intro _
        simp [Term.list, Erlang.maps.«next/1»]
        unfold Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3»
        rfl
      | cons e rest ih =>
        intro all
        obtain ⟨u, w, hu, run, empty⟩ := all e (by simp)
        have tail := ih (fun e' m => all e' (by simp [m]))
        simp only [List.map, Term.list] at tail ⊢
        simp only [Erlang.maps.«next/1», Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, hu, run]
        rcases empty with h | h | h
        · simpa [h] using tail
        · simpa [h] using tail
        · refine ⟨?_, tail⟩
          by_cases h₀ : w = .integer 0
          · simp [h₀]
          · by_cases h₁ : w = .atom "bdd_bot"
            · simp [h₁]
            · right
              simp [h₀, h₁, h]

    /-- The top type is a subtype of static types covering each of its fields. -/
    theorem subtype_term (d : Dispatcher) (T U : List (Term × Term))
        (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
        (static : mapLookup U (.atom "dynamic") = Option.none)
        (covered : ∀ e ∈ mapEntries T, Covered d U e.1 e.2) :
        Elixir.Module.Types.Descr.«subtype?/2» d (.atom "term") (.map U) = .ok (.atom "true") := by
      have walk := iterator_covered d U (mapEntries T) covered
      have staticT : mapLookup T (.atom "dynamic") = Option.none := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [term, unfold_map, Erlang.erlang.«is_map_key/2», getMapKeys_single, static, staticT, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Lynx.Except.guard, Erlang.erlang.«/=/2»]
      unfold Elixir.Module.Types.Descr.«subtype_static?/2»
      by_cases same : exactCompare (.map U) (.map T) = .eq
      · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, staticT, unfold_map, Erlang.maps.«iterator/1»]
        exact walk


    /-- The difference of a field of the top type with a field type is empty. -/
    def CoveredVal (d : Dispatcher) (q t u : Term) : Prop :=
      ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» d q t u = .ok w ∧
        (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
          Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))

    /-- What a field type and its negation unite into covers the field of the top type. -/
    def KeyOk (dn du dc : Dispatcher) (q t x : Term) : Prop :=
      ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» dn q t x = .ok w ∧
        (kept (q, w) = Bool.false → CoveredVal dc q t x) ∧
        (kept (q, w) = Bool.true → ∃ u, Elixir.Module.Types.Descr.«bare_union/3» du q x w = .ok u ∧ CoveredVal dc q t u)

    theorem bitmap_absent (dc : Dispatcher) : CoveredVal dc (.atom "bitmap") (.integer 255) (.integer 255) :=
      ⟨.integer 0, by simp [Elixir.Module.Types.Descr.«bare_difference/3»]; rfl, Or.inl rfl⟩

    theorem bitmap_key (dn du dc : Dispatcher) (b : Nat) (le : b ≤ 255) :
        KeyOk dn du dc (.atom "bitmap") (.integer 255) (.integer b) := by
      have band : (255 : Nat) &&& b = b := by
        rw [Nat.and_comm]
        have := Nat.and_two_pow_sub_one_eq_mod b 8
        simp at this
        omega
      refine ⟨.integer ↑(255 - b), ?_, fun k => ?_, fun _ => ?_⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]
        omega
      · refine ⟨.integer ↑(255 - b), ?_, ?_⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]; omega
        · simp [kept] at k; left; simp [k]
      · refine ⟨.integer 255, ?_, .integer 0, ?_, Or.inl rfl⟩
        · have disjoint : b &&& (255 - b) = 0 := Nat.eq_of_testBit_eq fun i => by
            rw [← band]; simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
            cases b.testBit i <;> simp
          have := add_eq_or b (255 - b) disjoint
          simp [Elixir.Module.Types.Descr.«bare_union/3», Erlang.erlang.«bor/2»]
          omega
        · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]

    theorem no_atoms : Erlang.sets.elements? (.map []) = some [] := by simp [Erlang.sets.elements?]

    /-- Sets without members are empty. -/
    theorem set_none {left right : Term} {f : Term → Term → Except Exception Term} {E : List (Term × Term)}
        (run : f left right = .ok (.map E)) (none : ∀ q, (mapLookup E q).isSome = Bool.false) :
        f left right = .ok (.map []) := by
      rw [run, nil_of_lookup_none E fun q => by simpa using none q]

    theorem atom_absent (dc : Dispatcher) :
        CoveredVal dc (.atom "atom") (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "negation", .map []]) := by
      obtain ⟨E, hE, -, m⟩ := Erlang.sets.subtract_member _ _ _ _ no_atoms no_atoms
      have run := set_none hE fun q => by rw [m]; simp [mapLookup]
      refine ⟨.integer 0, ?_, Or.inl rfl⟩
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.sets.«size/1»]

    theorem atom_key (dn du dc : Dispatcher) (p : Bool) (S : List (Term × Term))
        (set : Erlang.sets.elements? (.map S) = some S) :
        KeyOk dn du dc (.atom "atom") (.tuple #[.atom "negation", .map []])
          (.tuple #[.atom (if p then "union" else "negation"), .map S]) := by
      cases p
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set no_atoms
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine ⟨.tuple #[.atom "union", .map E], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
          · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, size, nonzero]
          · obtain ⟨F, hF, -, mF⟩ := Erlang.sets.subtract_member _ _ _ _ set setE
            have run := set_none hF fun q => by rw [mF, m]; simp [mapLookup]
            exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«atom_union/2», run],
              atom_absent dc⟩
        · refine ⟨.integer 0, ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
          · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, size]
          · obtain rfl : S = [] := nil_of_lookup_none S fun q => by
              have := m q
              rw [empty q] at this
              simpa [mapLookup] using this
            exact atom_absent dc
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ no_atoms set
        refine ⟨.tuple #[.atom "negation", .map E], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
            Erlang.erlang.«==/2», Lynx.Except.andAlso]
        · obtain ⟨F, hF, -, mF⟩ := Erlang.sets.subtract_member _ _ _ _ setE set
          have run := set_none hF fun q => by rw [mF, m]; simp [mapLookup]
          exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«atom_union/2», run],
            atom_absent dc⟩

    theorem loop_ne_nil (f : Term → Term → Bool) :
        ∀ (l : List Term) (a : Term) (acc : List Term), List.eraseDupsBy.loop f l (a :: acc) ≠ [] := by
      intro l
      induction l with
      | nil => intro a acc; simp [List.eraseDupsBy.loop]
      | cons x xs ih =>
        intro a acc
        simp only [List.eraseDupsBy.loop]
        split
        · exact ih a acc
        · exact ih x (a :: acc)

    theorem fun_absent (n : Nat) :
        CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "fun") (.tuple #[.atom "negation", .map []])
          (.tuple #[.atom "negation", .map []]) := by
      have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
          (.map []) (.map []) = .ok (.map []) := by
        simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
      refine ⟨.integer 0, ?_, Or.inl rfl⟩
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
        Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]

    theorem fun_key (n m k : Nat) (x : Term) (field : FunField x) :
        KeyOk (Dispatcher.ofTable Erlang.program.fun_table n) (Dispatcher.ofTable Erlang.program.fun_table m)
          (Dispatcher.ofTable Erlang.program.fun_table k) (.atom "fun") (.tuple #[.atom "negation", .map []]) x := by
      obtain ⟨pos, R, rfl⟩ := field
      cases pos with
      | true =>
        obtain ⟨out, merge, look⟩ := Erlang.maps.merge_with_lookup (Dispatcher.ofTable Erlang.program.fun_table n)
          "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] R (fun _ _ _ => .nil)
          (by intro e _ v found; simp [mapLookup] at found)
        have same : ∀ q, mapLookup R q = mapLookup out q := by
          intro q
          rw [look q, ← mapLookup_mapEntries R]
          simp only [mapLookup]
          cases (mapEntries R).find? (fun e => decide (exactCompare q e.1 = .eq)) <;> simp
        refine ⟨.tuple #[.atom "negation", .map out], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2»,
            Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», merge,
            Erlang.erlang.«==/2», Lynx.Except.andAlso]
        · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2»,
            repr_cancel m out R same], fun_absent k⟩
      | false =>
        have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
            (.map R) (.map []) = .ok (.map R) := by
          simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
        by_cases empty : ((R.map Prod.fst).eraseDupsBy (fun a b => exactCompare a b == .eq)).length = 0
        · refine ⟨.integer 0, ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
          · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
              Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
          · obtain rfl : R = [] := by
              cases R with
              | nil => rfl
              | cons e rest =>
                simp [List.eraseDupsBy, List.eraseDupsBy.loop] at empty
                exact (loop_ne_nil _ _ _ [] empty).elim
            exact fun_absent k
        · refine ⟨.tuple #[.atom "union", .map R], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
          · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
              Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
          · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2»,
              repr_cancel m R R (fun _ => rfl)], fun_absent k⟩

    theorem list_absent (dc : Dispatcher) (k : Int) :
        CoveredVal dc (.atom "list") (.tuple #[.integer k, .atom "term", .atom "term"])
          (.tuple #[.integer k, .atom "term", .atom "term"]) :=
      ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
        Or.inr (Or.inl rfl)⟩

    /-- The difference of all lists with a list BDD of other literals is its negation. -/
    theorem list_difference_bdd (k : Int) {x : Term} (wx : Bdd ListOk x) :
        Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer k, .atom "term", .atom "term"]) x =
          Elixir.Module.Types.Descr.«bdd_negation/1» x := by
      have nt := not_top_leaf wx
      unfold Elixir.Module.Types.Descr.«list_difference/2»
      split
      · exact (nt _ rfl).elim
      · rfl
      · next h₁ h₂ => first | exact (h₁ _ rfl).elim | exact (h₁ _ _ rfl).elim | exact absurd rfl (h₁ _) | simp_all

    theorem list_key (dn du dc : Dispatcher) (k : Int) (x : Term) (field : ListField x) :
        KeyOk dn du dc (.atom "list") (.tuple #[.integer k, .atom "term", .atom "term"]) x := by
      rcases field with ⟨k', rfl⟩ | wx
      · refine ⟨.atom "bdd_bot", ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»]
        · exact ⟨.atom "bdd_bot", by
            simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
            Or.inr (Or.inl rfl)⟩
      obtain ⟨w, run, keep, sem⟩ := neg_ok wx
      have diff : Elixir.Module.Types.Descr.«bare_difference/3» dn (.atom "list")
          (.tuple #[.integer k, .atom "term", .atom "term"]) x = .ok w := by
        simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wx, run]
      have ww := keep _ wx
      refine ⟨w, diff, fun kw => ⟨w, by
          simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wx, run], ?_⟩, fun _ => ?_⟩
      · simp [kept] at kw
        by_cases e : w = .integer 0
        · exact Or.inl e
        · exact Or.inr (Or.inl (kw e))
      obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
      have wu := keepU _ wx ww
      have unionRun : Elixir.Module.Types.Descr.«list_union/2» x w = Elixir.Module.Types.Descr.«bdd_union/2» x w := by
        have nx := not_top_leaf wx
        have nw := not_top_leaf ww
        unfold Elixir.Module.Types.Descr.«list_union/2»
        split
        · exact (nx _ rfl).elim
        · exact (nw _ rfl).elim
        · rfl
      obtain ⟨w', runW, keepW, semW⟩ := neg_ok wu
      refine ⟨u, by simp [Elixir.Module.Types.Descr.«bare_union/3», unionRun, runU], w', ?_, Or.inr (Or.inr ?_)⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wu, runW]
      · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
        exact list_empty_unsat dc (keepW _ wu) (fun ρ resp => by
          rw [semW ρ resp, semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl) []


    theorem remove_atom_leaf (s : String) (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_remove/2» (.atom s) (.tuple #[k, x, y]) = .ok (.atom s) := by
      unfold Elixir.Module.Types.Descr.«bdd_remove/2»
      unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]


    theorem union_bot_leaf (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_bot") (.tuple #[k, x, y]) = .ok (.tuple #[k, x, y]) := by
      unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem union_leaf_bot (k x y : Term) :
        Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.tuple #[k, x, y]) := by
      unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]

    theorem union_two_leaves {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (lt : Term.compare a b = .lt) :
        ∃ h : Int, Elixir.Module.Types.Descr.«bdd_union/2» a b =
          .ok (.tuple #[.integer h, a, .atom "bdd_top", b, .atom "bdd_bot"]) := by
      have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
      have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
      have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
      have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
      have same : ¬exactCompare a b = .eq := fun e => by
        rw [compare_eq_of_exactCompare_eq _ _ e] at lt; cases lt
      have same' : ¬exactCompare b a = .eq := fun e => same (Std.OrientedCmp.eq_symm e)
      obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt wa ha hb lt
      rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
      · obtain ⟨_, _, _, rfl⟩ := la; simp at e
      obtain ⟨h₁, node⟩ := node_new a (.atom "bdd_top") b (.atom "bdd_bot") la (Bdd.top (ok := fun _ => True))
        wb (Bdd.bot (ok := fun _ => True))
      refine ⟨h₁, ?_⟩
      obtain ⟨_, _, _, rfl⟩ := la
      obtain ⟨_, _, _, rfl⟩ := lb
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, remove_atom_leaf, union_bot_leaf, union_leaf_bot, node, same']

    theorem union_two_leaves_gt {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (gt : Term.compare a b = .gt) :
        ∃ h : Int, Elixir.Module.Types.Descr.«bdd_union/2» a b =
          .ok (.tuple #[.integer h, b, .atom "bdd_top", a, .atom "bdd_bot"]) := by
      have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
      have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
      have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
      have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
      have same : ¬exactCompare a b = .eq := fun e => by
        rw [compare_eq_of_exactCompare_eq _ _ e] at gt; cases gt
      have same' : ¬exactCompare b a = .eq := fun e => same (Std.OrientedCmp.eq_symm e)
      obtain ⟨h₀, c, u, d, run, split⟩ := compare_gt wb ha hb gt
      rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
      · obtain ⟨_, _, _, rfl⟩ := lb; simp at e
      obtain ⟨h₁, node⟩ := node_new b (.atom "bdd_top") a (.atom "bdd_bot") lb (Bdd.top (ok := fun _ => True))
        wa (Bdd.bot (ok := fun _ => True))
      refine ⟨h₁, ?_⟩
      obtain ⟨_, _, _, rfl⟩ := la
      obtain ⟨_, _, _, rfl⟩ := lb
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, run, remove_atom_leaf, union_bot_leaf, union_leaf_bot, node, same']

    theorem inter_bot_any (b : Term) :
        Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_bot") b = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      by_cases e : exactCompare b (.atom "bdd_bot") = .eq
      · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», e]
      · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», e]
        split <;> simp_all

    theorem inter_top_any (b : Term) :
        Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_top") b = .ok b := by
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      by_cases e : exactCompare b (.atom "bdd_top") = .eq
      · have := (exactCompare_eq_atom _ _).mp e; subst this; simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
      · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», e]

    /-- The negation of the union of two leaves negates each in turn. -/
    theorem neg_union_leaves {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (lt : Term.compare a b = .lt) (h : Int) :
        ∃ h₁ h₂ : Int, Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, a, .atom "bdd_top", b, .atom "bdd_bot"]) =
          .ok (.tuple #[.integer h₁, a, .atom "bdd_bot", .atom "bdd_bot",
            .tuple #[.integer h₂, b, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]]) := by
      obtain ⟨hA, nodeA⟩ := node_new a (.atom "bdd_bot") (.atom "bdd_bot") (.atom "bdd_top") la
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
      obtain ⟨hB, nodeB⟩ := node_new b (.atom "bdd_bot") (.atom "bdd_bot") (.atom "bdd_top") lb
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
      let nB : Term := .tuple #[.integer hB, b, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]
      have wnB : Bdd (fun _ => True) nB := by
        obtain ⟨_, _, _, rfl⟩ := lb
        simp [nB, Bdd, IsLeaf]
      have wnA : Bdd (fun _ => True) (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) := by
        obtain ⟨_, _, _, rfl⟩ := la
        simp [Bdd, IsLeaf]
      obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt (b := nB) wnA (by simp [head]) (by simp [nB, head]) lt
      rcases split with ⟨_, e⟩ | ⟨e, -⟩
      · simp at e
        obtain ⟨-, rfl, rfl, rfl⟩ := e
        obtain ⟨h₃, node3⟩ := node_new a (.atom "bdd_bot") (.atom "bdd_bot") nB la
          (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) wnB
        refine ⟨h₃, hB, ?_⟩
        have notSame : ¬exactCompare nB (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) = .eq := by
          intro e
          obtain ⟨_, _, _, _, _, e', b₁, -⟩ := tuple5_exact e
          simp at e'
          obtain ⟨-, rfl, -⟩ := e'
          rw [compare_eq_of_exactCompare_eq _ _ (Std.OrientedCmp.eq_symm b₁)] at lt
          cases lt
        have inter : Elixir.Module.Types.Descr.«bdd_intersection/2»
            (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) nB =
              .ok (.tuple #[.integer h₃, a, .atom "bdd_bot", .atom "bdd_bot", nB]) := by
          conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
          simp [nB, Lynx.Except.guard, Erlang.erlang.«=:=/2», notSame, run, inter_bot_any, inter_top_any, node3]
        have negTop : Elixir.Module.Types.Descr.«bdd_negation/1» (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
          unfold Elixir.Module.Types.Descr.«bdd_negation/1»; rfl
        have negBot : Elixir.Module.Types.Descr.«bdd_negation/1» (.atom "bdd_bot") = .ok (.atom "bdd_top") := by
          unfold Elixir.Module.Types.Descr.«bdd_negation/1»; rfl
        have negB : Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok nB := by
          obtain ⟨_, _, _, rfl⟩ := lb
          unfold Elixir.Module.Types.Descr.«bdd_negation/1»
          simpa using nodeB
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simp [negTop, negBot, nodeA, negB, inter, Lynx.Except.guard, Erlang.erlang.«=:=/2», nB]
      · obtain ⟨_, _, _, rfl⟩ := la
        simp at e

    theorem elements_term (d : Dispatcher) (acc tag negs S e : Term) (he : e = .nil ∨ e = Term.list [.atom "term"]) :
        Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d acc tag e (Term.list [.atom "term"]) negs S =
          .ok (.atom "true") := by
      have inter : Elixir.Module.Types.Descr.«bare_intersection/2» d (.atom "term") (.atom "term") = .ok (.atom "term") := by
        unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
      have diff : Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") (.atom "term") = .ok (.map []) := by
        unfold Elixir.Module.Types.Descr.«bare_difference/2»; rfl
      have seenTerm : Elixir.Module.Types.Descr.«empty_seen?/2» d (.atom "term") S = .ok (.atom "false") := by
        unfold Elixir.Module.Types.Descr.«empty_seen?/2»; rfl
      have seenNone : Elixir.Module.Types.Descr.«empty_seen?/2» d (.map []) S = .ok (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«empty_seen?/2»
        simp [getMapKeys, Erlang.erlang.«==/2»]
      rcases he with rfl | rfl <;>
      · rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]
        simp [Term.list, inter, diff, seenTerm, seenNone, Lynx.Except.guard, isMember]
        rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]
        rfl

    theorem elements_nil (d : Dispatcher) (acc tag e negs S : Term) :
        Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d acc tag e .nil negs S = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]; rfl

    theorem cmp10 : Ord.compare (1 : Int) 0 = .gt := by decide
    theorem cmp01 : Ord.compare (0 : Int) 1 = .lt := by decide
    theorem cmp11 : Ord.compare (1 : Int) 1 = .eq := by decide

    theorem dup_zero : Erlang.lists.«duplicate/2» (.integer 0) (.atom "term") = .ok .nil := by
      simp [Erlang.lists.«duplicate/2», Lynx.Except.guard, Erlang.erlang.«>=/2», Erlang.erlang.«and/2»]
      rw [Erlang.lists.«duplicate/3».eq_def]
      simp

    theorem dup_one : Erlang.lists.«duplicate/2» (.integer 1) (.atom "term") = .ok (Term.list [.atom "term"]) := by
      simp [Erlang.lists.«duplicate/2», Lynx.Except.guard, Erlang.erlang.«>=/2», Erlang.erlang.«and/2», cmp10]
      rw [Erlang.lists.«duplicate/3».eq_def]
      simp
      rw [Erlang.lists.«duplicate/3».eq_def]
      simp [Term.list]

    theorem fill_zero : Elixir.Module.Types.Descr.«tuple_fill/2» .nil (.integer 0) = .ok .nil := by
      simp [Elixir.Module.Types.Descr.«tuple_fill/2», Erlang.erlang.«length/1», Erlang.erlang.«</2»,
        dup_zero, dup_one, Erlang.erlang.«++/2», cmp10]

    theorem fill_one : Elixir.Module.Types.Descr.«tuple_fill/2» .nil (.integer 1) = .ok (Term.list [.atom "term"]) := by
      simp [Elixir.Module.Types.Descr.«tuple_fill/2», Erlang.erlang.«length/1», Erlang.erlang.«</2»,
        dup_zero, dup_one, Erlang.erlang.«++/2», cmp10]

    theorem line_lt (d : Dispatcher) (k H : Int) (S : Term) :
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]])
            (.cons (.tuple #[.integer k, .atom "closed", .nil]) .nil)) S = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«length/1», Lynx.Except.orElse,
        Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2»,
        elements_term d _ _ _ S _ (Or.inl rfl), Elixir.Module.Types.Descr.«tuple_empty_arity?/7»,
        Elixir.Module.Types.Descr.«tuple_empty_sizes?/5», Lynx.Except.guard, fill_zero, fill_one, cmp01, cmp11,
        elements_nil, elements_term d _ _ _ S _ (Or.inr rfl)]

    theorem line_gt (d : Dispatcher) (k H : Int) (S : Term) :
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer k, .atom "closed", .nil])
            (.cons (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) .nil)) S = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«length/1», Lynx.Except.orElse,
        Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», elements_nil,
        Elixir.Module.Types.Descr.«tuple_empty_arity?/7»,
        Elixir.Module.Types.Descr.«tuple_empty_sizes?/5», Lynx.Except.guard, fill_zero, fill_one, cmp01, cmp11,
        elements_nil, elements_term d _ _ _ S _ (Or.inr rfl)]

    theorem any_nil (d : Dispatcher) (m n : String) (caps : Array Term) :
        Erlang.lists.«any/2» d (.function m n 1 caps) .nil = .ok (.atom "false") := by
      simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2»]

    theorem special_lt (d : Dispatcher) (h₁ h₂ k H : Int) :
        Elixir.Module.Types.Descr.«tuple_empty?/2» d
          (.tuple #[.integer h₁, .tuple #[.integer k, .atom "closed", .nil], .atom "bdd_bot", .atom "bdd_bot",
            .tuple #[.integer h₂, .tuple #[.integer H, .atom "open", Term.list [.atom "term"]], .atom "bdd_bot",
              .atom "bdd_bot", .atom "bdd_top"]]) (.map []) = .ok (.atom "true") := by
      unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.true, Term.false,
        Erlang.maps.«put/3»]
      simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
        Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Lynx.Except.guard,
        Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
        Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
        Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]
      rw [line_lt]; rfl

    theorem special_gt (d : Dispatcher) (h₁ h₂ k H : Int) :
        Elixir.Module.Types.Descr.«tuple_empty?/2» d
          (.tuple #[.integer h₁, .tuple #[.integer H, .atom "open", Term.list [.atom "term"]], .atom "bdd_bot", .atom "bdd_bot",
            .tuple #[.integer h₂, .tuple #[.integer k, .atom "closed", .nil], .atom "bdd_bot",
              .atom "bdd_bot", .atom "bdd_top"]]) (.map []) = .ok (.atom "true") := by
      unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.true, Term.false,
        Erlang.maps.«put/3»]
      simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
        Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Lynx.Except.guard,
        Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
        Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
        Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]
      rw [line_gt]; rfl

    theorem dropped {q w : Term} (k : kept (q, w) = Bool.false) : w = .integer 0 ∨ w = .atom "bdd_bot" := by
      simp [kept] at k
      by_cases e : w = .integer 0
      · exact Or.inl e
      · exact Or.inr (k e)

    /-- The difference of all tuples with a tautology of tuple literals is empty. -/
    theorem tuple_taut (n : Nat) {u : Term} (wu : Bdd TupleOk u) (taut : ∀ ρ, Resp ρ → eval ρ u = Bool.true) :
        CoveredVal (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) (.atom "tuple")
          (.tuple #[.integer 61102469, .atom "open", .nil]) u := by
      rcases wu.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, d, e, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
        simp [Elixir.Module.Types.Descr.«bare_difference/3»]
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [diff_leaf_top]
      · have := taut _ (resp_const Bool.false); simp [eval] at this
      · have := taut _ (resp_const Bool.false); simp [eval] at this
      · obtain ⟨w, run, keep, sem⟩ := neg_ok wu
        refine ⟨w, ?_, Or.inr (Or.inr ?_)⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [run]
        · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
          exact tuple_empty_unsat (keep _ wu) (fun _ h => h.1) (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) n []

    theorem tuple_union_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
        (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
        Elixir.Module.Types.Descr.«tuple_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
      unfold Elixir.Module.Types.Descr.«tuple_union/2»
      split
      · exact (hx _ rfl).elim
      · exact (hy _ rfl).elim
      · rfl

    theorem tuple_absent (n : Nat) :
        CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "tuple")
          (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer 61102469, .atom "open", .nil]) :=
      ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»],
        Or.inr (Or.inl rfl)⟩

    /-- A tuple BDD that is neither bottom, top, nor `{}` has its negation as difference. -/
    theorem tuple_key_neg (dn du : Dispatcher) (n : Nat) (x : Term) (wx : Bdd TupleOk x)
        (run : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x =
          Elixir.Module.Types.Descr.«bdd_negation/1» x) :
        KeyOk dn du (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) (.atom "tuple")
          (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      have notTop := not_top_of_ok wx fun t h => h.2
      obtain ⟨w, neg, keep, sem⟩ := neg_ok wx
      have ww := keep _ wx
      have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
          (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w := by
        intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», run, neg]
      refine ⟨w, diff _, fun kw => ⟨w, diff _, ?_⟩, fun _ => ?_⟩
      · rcases dropped kw with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
      have wu := keepU _ wx ww
      refine ⟨u, ?_, tuple_taut n wu fun ρ resp => ?_⟩
      · simp [Elixir.Module.Types.Descr.«bare_union/3», tuple_union_bdd notTop (not_top_of_ok ww fun t h => h.2), runU]
      · rw [semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl

    theorem tuple_key (dn du : Dispatcher) (n : Nat) (x : Term) (field : TupleField x) :
        KeyOk dn du (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) (.atom "tuple")
          (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      rcases field with ⟨k, rfl⟩ | wx
      · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
            (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) =
              .ok (.atom "bdd_bot") := by
          intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»]
        exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
      have notTop := not_top_of_ok wx fun t h => h.2
      rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
            (.tuple #[.integer 61102469, .atom "open", .nil]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
          intro d
          simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [diff_leaf_top]
        exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
      · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [diff_leaf_bot]
        · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«tuple_union/2»],
            tuple_absent _⟩
      · obtain ⟨⟨k', tag, ls, e, tags, elems⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
        simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        by_cases special : tag = "closed" ∧ ls = []
        · obtain ⟨rfl, rfl⟩ := special
          obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
          let W : Term := .tuple #[.integer ((1 <<< 27) + hash), .atom "open", Term.list [.atom "term"]]
          have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
              (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "closed", Term.list []]) =
                .ok W := by
            intro d
            simp [Elixir.Module.Types.Descr.«bare_difference/3»]
            unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
              Elixir.Module.Types.Descr.«bdd_leaf_key/2», Lynx.Except.guard, Erlang.erlang.«is_list/1»,
              Erlang.erlang.«length/1», Erlang.erlang.«bsl/2», W]
            rfl
          refine ⟨W, diff _, fun k => by simp [kept, W] at k, fun _ => ?_⟩
          have lX : IsLeaf (.tuple #[.integer k, .atom "closed", Term.list []]) := ⟨_, _, _, rfl⟩
          have lW : IsLeaf W := ⟨_, _, _, rfl⟩
          have unionRun : ∀ u, Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k, .atom "closed", Term.list []]) W = .ok u →
              Elixir.Module.Types.Descr.«bare_union/3» du (.atom "tuple") (.tuple #[.integer k, .atom "closed", Term.list []]) W =
                .ok u := by
            intro u run
            simp [Elixir.Module.Types.Descr.«bare_union/3»]
            rw [tuple_union_bdd notTop (by intro k e; simp [W] at e)]
            exact run
          by_cases order : k ≤ (1 <<< 27) + hash
          · have lt : Term.compare (.tuple #[.integer k, .atom "closed", Term.list []]) W = .lt := by
              have ca : (Term.atom "closed").compare (.atom "open") = .lt := by cbv
              simp [W, compare_tuple, List.compareLex_cons_cons, ca]
              have order' : k ≤ 134217728 + (hash : Int) := by simpa using order
              rcases Int.lt_or_eq_of_le order' with o | o
              · simp [Int.compare_eq_lt.mpr o]
              · rw [o]; simp
            obtain ⟨h, run⟩ := union_two_leaves lX lW lt
            obtain ⟨h₁, h₂, neg⟩ := neg_union_leaves lX lW lt h
            refine ⟨_, unionRun _ run, .tuple #[.integer h₁, (.tuple #[.integer k, .atom "closed", Term.list []]), .atom "bdd_bot", .atom "bdd_bot",
              .tuple #[.integer h₂, W, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]], ?_, Or.inr (Or.inr ?_)⟩
            · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
              unfold Elixir.Module.Types.Descr.«tuple_difference/2»
              simp [neg]
            · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
              exact special_lt _ _ _ _ _
          · have lt : Term.compare W (.tuple #[.integer k, .atom "closed", Term.list []]) = .lt := by
              have o : 134217728 + (hash : Int) < k := by simp at order; omega
              simp [W, compare_tuple, List.compareLex_cons_cons, Int.compare_eq_lt.mpr o]
            have gt : Term.compare (.tuple #[.integer k, .atom "closed", Term.list []]) W = .gt := by
              rw [Std.OrientedCmp.gt_iff_lt]; exact lt
            obtain ⟨h, run⟩ := union_two_leaves_gt lX lW gt
            obtain ⟨h₁, h₂, neg⟩ := neg_union_leaves lW lX lt h
            refine ⟨_, unionRun _ run, .tuple #[.integer h₁, W, .atom "bdd_bot", .atom "bdd_bot",
              .tuple #[.integer h₂, (.tuple #[.integer k, .atom "closed", Term.list []]), .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]], ?_, Or.inr (Or.inr ?_)⟩
            · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
              unfold Elixir.Module.Types.Descr.«tuple_difference/2»
              simp [neg]
            · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
              exact special_gt _ _ _ _ _
        · have notSpecial : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠
              .tuple #[k₁, .atom "closed", .nil] := by
            intro k₁ e
            simp at e
            apply special
            refine ⟨e.2.1, ?_⟩
            cases ls <;> simp_all [Term.list]
          refine tuple_key_neg dn du n _ wx ?_
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          split
          · next _ _ e =>
            exfalso
            simp at e
            obtain ⟨-, rfl, hl⟩ := e
            exact notTopX ⟨_, by rw [hl]⟩
          · next _ _ e => exact (notSpecial _ e).elim
          · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; rfl
          · next h₁ => exact (h₁ _ _ rfl rfl).elim
      · refine tuple_key_neg dn du n _ wx ?_
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp

    theorem map_taut (n : Nat) {u : Term} (wu : Bdd MapOk u) (taut : ∀ ρ, Resp ρ → eval ρ u = Bool.true) :
        CoveredVal (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil]) u := by
      rcases wu.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, d, e, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
        simp [Elixir.Module.Types.Descr.«bare_difference/3»]
        unfold Elixir.Module.Types.Descr.«map_difference/2»
        simp [diff_leaf_top]
      · have := taut _ (resp_const Bool.false); simp [eval] at this
      · have := taut _ (resp_const Bool.false); simp [eval] at this
      · obtain ⟨w, run, keep, sem⟩ := neg_ok wu
        refine ⟨w, ?_, Or.inr (Or.inr ?_)⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«map_difference/2»
          simp [run]
        · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
          exact map_empty_unsat (keep _ wu) (fun _ h => h.1.lit) (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) n []

    theorem map_union_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
        (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
        Elixir.Module.Types.Descr.«map_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
      unfold Elixir.Module.Types.Descr.«map_union/2»
      split
      · exact (hx _ rfl).elim
      · exact (hy _ rfl).elim
      · rfl

    theorem map_absent (n : Nat) :
        CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer 61102469, .atom "open", .nil]) :=
      ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»],
        Or.inr (Or.inl rfl)⟩

    theorem map_key (dn du : Dispatcher) (n : Nat) (x : Term) (field : MapField x) :
        KeyOk dn du (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      rcases field with ⟨k, rfl⟩ | wx
      · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
            (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) =
              .ok (.atom "bdd_bot") := by
          intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»]
        exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
      have notTop := not_top_of_ok wx fun t h => h.2
      have neg : (∃ h lit c u d, x = .tuple #[.integer h, lit, c, u, d]) ∨ (∃ k x₁ y₁, x = .tuple #[.integer k, x₁, y₁]) →
          KeyOk dn du (Dispatcher.ofTable Erlang.program.fun_table (n + 3)) (.atom "map")
            (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
        intro shape
        obtain ⟨w, neg, keep, sem⟩ := neg_ok wx
        have ww := keep _ wx
        have run : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x =
            .ok w := by
          unfold Elixir.Module.Types.Descr.«map_difference/2»
          rcases shape with ⟨h, lit, c, u, d, rfl⟩ | ⟨k, x₁, y₁, rfl⟩
          · simp [neg]
          · split
            · next _ _ e => exact (notTop _ e).elim
            · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact neg
            · next h₁ => exact (h₁ _ _ rfl rfl).elim
        have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
            (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w := by
          intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», run]
        refine ⟨w, diff _, fun kw => ⟨w, diff _, ?_⟩, fun _ => ?_⟩
        · rcases dropped kw with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
        have wu := keepU _ wx ww
        refine ⟨u, ?_, map_taut n wu fun ρ resp => ?_⟩
        · simp [Elixir.Module.Types.Descr.«bare_union/3», map_union_bdd notTop (not_top_of_ok ww fun t h => h.2), runU]
        · rw [semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl
      rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
            (.tuple #[.integer 61102469, .atom "open", .nil]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
          intro d
          simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«map_difference/2»
          simp [diff_leaf_top]
        exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
      · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«map_difference/2»
          simp [diff_leaf_bot]
        · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«map_union/2»],
            map_absent _⟩
      · exact neg (Or.inr ⟨_, _, _, rfl⟩)
      · exact neg (Or.inl ⟨_, _, _, _, _, rfl⟩)

    /-- Unions of static types merge their fields, uniting those in both. -/
    theorem union_lookup (depth : Nat) (L R : List (Term × Term))
        (staticL : mapLookup L (.atom "dynamic") = Option.none) (staticR : mapLookup R (.atom "dynamic") = Option.none)
        (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          ∃ u, Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) q x y = .ok u) :
        ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.map L) (.map R) = .ok (.map U) ∧
          ∀ name, (mapLookup R (.atom name) = Option.none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
            (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = Option.none →
              mapLookup U (.atom name) = some y) ∧
            (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
              Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y =
                .ok u → mapLookup U (.atom name) = some u) := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have value : ∀ q x y u, Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          q x y = .ok u → g q x y = u := by
        intro q x y u run; simp [g, run]
      obtain ⟨U, run, look⟩ : ∃ U, Elixir.Module.Types.Descr.«bare_union/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map U) ∧
          ∀ name, mapLookup U (.atom name) =
            match mapLookup R (.atom name) with
            | some y => some (match mapLookup L (.atom name) with | some x => g (.atom name) x y | none => y)
            | none => mapLookup L (.atom name) := by
        unfold Elixir.Module.Types.Descr.«bare_union/2»
        simp [getMapKeys_single, Erlang.erlang.«==/2», staticL, staticR]
        by_cases emptyL : L = []
        · subst emptyL
          refine ⟨R, by simp, fun name => ?_⟩
          cases mapLookup R (.atom name) <;> simp [mapLookup]
        by_cases emptyR : R = []
        · subst emptyR
          exact ⟨L, by simp [emptyL], fun name => by simp [mapLookup]⟩
        simp only [emptyL, emptyR]
        unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
        obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr" "bare_union" #[] L R g (by
            intro e me x hx
            have hy := mapLookup_of_mem_mapEntries me
            obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
            rw [Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure, ru, value _ _ _ _ ru])
        refine ⟨out, by simpa using run, fun name => ?_⟩
        rw [look, find_atom]
        cases mapLookup R (.atom name) <;> rfl
      refine ⟨U, run, fun name => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩⟩
      · rw [look, hR]
      · rw [look, hR, hL]
      · rw [look, hR, hL]; simp only [value _ _ _ _ ru]

    theorem term_keys {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
        {q t : Term} (hT : mapLookup T q = some t) :
        (q = .atom "bitmap" ∧ t = .integer 255) ∨ (q = .atom "atom" ∧ t = .tuple #[.atom "negation", .map []]) ∨
          (q = .atom "fun" ∧ t = .tuple #[.atom "negation", .map []]) ∨
          (q = .atom "list" ∧ t = .tuple #[.integer 46675407, .atom "term", .atom "term"]) ∨
          (q = .atom "tuple" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) ∨
          (q = .atom "map" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) := by
      simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at term
      cases term
      simp only [mapLookup, List.find?] at hT
      split at hT
      · simp at hT; rename_i e; simp at e; simp [e, hT]
      split at hT
      · simp at hT; rename_i e; simp at e; simp [e, hT]
      split at hT
      · simp at hT; rename_i e; simp at e; simp [e, hT]
      split at hT
      · simp at hT; rename_i e; simp at e; simp [e, hT]
      split at hT
      · simp at hT; rename_i e; simp at e; simp [e, hT]
      split at hT
      · simp at hT; rename_i e; simp at e; simp [e, hT]
      · simp at hT

    /-- Each field of the top type is covered by what a field type and its negation unite into. -/
    theorem key_ok (X : List (Term × Term)) (valid : Negatable X) {T : List (Term × Term)}
        (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) {q t x : Term}
        (hT : mapLookup T q = some t) (hX : mapLookup X q = some x) :
        KeyOk (Dispatcher.ofTable Erlang.program.fun_table 98) (Dispatcher.ofTable Erlang.program.fun_table 99)
          (Dispatcher.ofTable Erlang.program.fun_table 100) q t x := by
      rcases term_keys term hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨b, rfl, -, le⟩ := valid.bitmap x hX
        exact bitmap_key _ _ _ b le
      · obtain ⟨p, S, rfl, set⟩ := valid.atom x hX
        exact atom_key _ _ _ p S set
      · exact fun_key 98 99 100 x (valid.funs x hX)
      · exact list_key _ _ _ _ x (valid.lists x hX)
      · exact tuple_key _ _ 98 x (valid.tuples x hX)
      · exact map_key _ _ 97 x (valid.maps x hX)

    /-- Fields of the top type are covered by themselves. -/
    theorem key_absent {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
        {q t : Term} (hT : mapLookup T q = some t) :
        CoveredVal (Dispatcher.ofTable Erlang.program.fun_table 100) q t t := by
      rcases term_keys term hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact bitmap_absent _
      · exact atom_absent _
      · exact fun_absent _
      · exact list_absent _ _
      · exact tuple_absent _
      · exact map_absent _

    theorem atom_key_of {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
        {q t : Term} (hT : mapLookup T q = some t) : ∃ name, q = .atom name := by
      rcases term_keys term hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨_, rfl⟩

    /-- A type united with its negation covers the top type. -/
    theorem union_negation_covers (X : List (Term × Term)) (valid : Negatable X) (nonempty : X ≠ []) :
        ∃ N U, Elixir.Module.Types.Descr.«bare_negation/1» (Dispatcher.ofTable Erlang.program.fun_table 100) (.map X) =
            .ok (.map N) ∧
          Elixir.Module.Types.Descr.«bare_union/2» (Dispatcher.ofTable Erlang.program.fun_table 100) (.map X) (.map N) =
            .ok (.map U) ∧
          Elixir.Module.Types.Descr.«subtype?/2» (Dispatcher.ofTable Erlang.program.fun_table 100) (.atom "term")
            (.map U) = .ok (.atom "true") := by
      obtain ⟨N, negation, staticN, -, -, -, -, -, -, lookups⟩ := negation_fields 98 X valid nonempty
      obtain ⟨T, term, -⟩ := unfolded_term_fields
      have inT : ∀ q x, mapLookup X q = some x → ∃ t, mapLookup T q = some t := by
        intro q x hX
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        rcases valid.keys q (by simp [hX]) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mapLookup]
      obtain ⟨U, union, lookU⟩ := union_lookup 99 X N valid.static staticN (by
        intro q x y hX hN
        obtain ⟨t, hT⟩ := inT q x hX
        obtain ⟨name, rfl⟩ := atom_key_of term hT
        obtain ⟨w, run, -, keep⟩ := key_ok X valid term hT hX
        have look := (lookups T term name t hT).2 x w hX run
        rw [hN] at look
        by_cases k : kept (.atom name, w) = Bool.true
        · simp only [k, ite_true, Option.some.injEq] at look
          obtain ⟨u, ru, -⟩ := keep k
          exact ⟨u, look ▸ ru⟩
        · simp [k] at look)
      refine ⟨N, U, negation, union, subtype_term _ T U term ?_ fun e member => ?_⟩
      · rw [(lookU "dynamic").1 staticN]
        exact valid.static
      have hT := mapLookup_of_mem_mapEntries member
      obtain ⟨name, key⟩ := atom_key_of term hT
      rw [key] at hT ⊢
      cases hX : mapLookup X (.atom name) with
      | none =>
        have hN := (lookups T term name e.2 hT).1 hX
        obtain ⟨w, run, empty⟩ := key_absent term hT
        exact ⟨e.2, w, (lookU name).2.1 _ hN hX, run, empty⟩
      | some x =>
        obtain ⟨w, run, drop, keep⟩ := key_ok X valid term hT hX
        have look := (lookups T term name e.2 hT).2 x w hX run
        by_cases k : kept (.atom name, w) = Bool.true
        · obtain ⟨u, ru, w', rw', empty⟩ := keep k
          simp only [k, ite_true] at look
          exact ⟨u, w', (lookU name).2.2 x w u hX look ru, rw', empty⟩
        · simp only [k, Bool.false_eq_true, ite_false] at look
          obtain ⟨w', rw', empty⟩ := drop (by simpa using k)
          exact ⟨x, w', by rw [(lookU name).1 look, hX], rw', empty⟩

    end Elixir.STTDescrProofsTest
    """

    # Optimized unions of a type with its optimized negation fuse open maps of a single
    # field into one, except for `:__struct__` keys, which only fuse when one side is a
    # subtype. Basic types, whose fields are non-empty bitmaps, atoms, or the top function,
    # list, tuple, and map types, compute set operations, so the fused fields and the map
    # lines of both single field maps can be checked directly.
    postlude ~LEAN"""
    namespace Elixir.STTDescrProofsTest
    open Lynx Lynx.Term BddProofs

    /-! Basic types: static types whose fields are non-empty bitmaps, non-empty atom types, or the
    top function, list, tuple, and map types. Their operations follow the operations on sets. -/

    /-- The bitmap of a type, which is zero when the field is absent. -/
    def bits (X : List (Term × Term)) : Nat :=
      match mapLookup X (.atom "bitmap") with
      | some (.integer b) => b.toNat
      | _ => 0

    /-- The top values of the function, list, tuple, and map fields. -/
    def topValue : String → Option Term
      | "fun" => some (.tuple #[.atom "negation", .map []])
      | "list" => some (.tuple #[.integer 46675407, .atom "term", .atom "term"])
      | "tuple" => some (.tuple #[.integer 61102469, .atom "open", .nil])
      | "map" => some (.tuple #[.integer 61102469, .atom "open", .nil])
      | _ => none

    /-- Whether the atom field of a type holds the term `q`. -/
    def amemV : Option Term → Term → Bool
      | some (.tuple ⟨[.atom "union", .map S]⟩), q => (mapLookup S q).isSome
      | some (.tuple ⟨[.atom "negation", .map S]⟩), q => !(mapLookup S q).isSome
      | _, _ => false

    def amem (M : List (Term × Term)) (q : Term) : Bool := amemV (mapLookup M (.atom "atom")) q

    theorem amemV_field (pos : Bool) (S : List (Term × Term)) (q : Term) :
        amemV (some (.tuple #[.atom (if pos then "union" else "negation"), .map S])) q =
          (pos == (mapLookup S q).isSome) := by
      cases pos <;> cases h : (mapLookup S q).isSome <;> simp [amemV, h]

    /-- The fields of basic types. -/
    def FieldOk (name : String) (w : Term) : Prop :=
      (name = "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (name = "atom" ∧ AtomField w ∧ ∃ q, amemV (some w) q = Bool.true) ∨
      (name ≠ "bitmap" ∧ name ≠ "atom" ∧ topValue name = some w)

    /-- Whether a type has the field `name`. -/
    def has (M : List (Term × Term)) (name : String) : Bool := (mapLookup M (.atom name)).isSome

    structure Basic (M : List (Term × Term)) : Prop where
      keys : ∀ q, (mapLookup M q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
        q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map"
      bitmap : ∀ w, mapLookup M (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
      atom : ∀ w, mapLookup M (.atom "atom") = some w → AtomField w ∧ ∃ q, amem M q = Bool.true
      top : ∀ name w, name ≠ "bitmap" → name ≠ "atom" → mapLookup M (.atom name) = some w → topValue name = some w

    /-- Seen sets that never hold the top tuple and map literals, whose emptiness is then computed. -/
    def SeenOk (S : Term) : Prop :=
      ∃ L : List (Term × Term), S = .map L ∧ ∀ e ∈ L, ∀ kind : String,
        exactCompare (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 ≠ .eq

    theorem seenOk_nil : SeenOk (.map []) := ⟨[], rfl, by simp⟩

    /-- Seen sets of a single key other than the top literals. -/
    theorem seenOk_one (key v : Term)
        (fresh : ∀ kind : String, exactCompare (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil])) key ≠ .eq) :
        SeenOk (.map [(key, v)]) := ⟨_, rfl, by simpa using fresh⟩

    theorem seenOk_node (h a b c d v : Term) : SeenOk (.map [(.cons (.atom "map") (.tuple #[h, a, b, c, d]), v)]) := by
      refine seenOk_one _ _ fun kind hit => ?_
      rw [exactCompare_cons, exactCompare_tuple] at hit
      simp [Ordering.then] at hit
      split at hit <;> simp_all

    theorem seen_absent {S : Term} (ok : SeenOk S) (kind : String) :
        ∃ L, S = .map L ∧ L.any (fun e => Term.exactCompare
          (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 == .eq) = Bool.false := by
      obtain ⟨L, rfl, all⟩ := ok
      refine ⟨L, rfl, ?_⟩
      simp only [List.any_eq_false]
      intro e member hit
      exact all e member kind (beq_iff_eq.mp hit)

    theorem line_inter_open (d : Dispatcher) (k : Int) (fs S : Term) :
        Elixir.Module.Types.Descr.«map_line_intersection/3» d (.tuple #[.atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fs]) S = .ok (.tuple #[.atom "open", fs]) := by
      simp [Elixir.Module.Types.Descr.«map_line_intersection/3», Elixir.Module.Types.Descr.«map_literal_intersection/6»]
      rw [Erlang.orddict.«merge/3».eq_def]
      simp [Erlang.erlang.«is_function/2»]

    theorem tuple_top_nonempty (d : Dispatcher) {S : Term} (ok : SeenOk S) :
        Elixir.Module.Types.Descr.«tuple_empty?/2» d (.tuple #[.integer 61102469, .atom "open", .nil]) S =
          .ok (.atom "false") := by
      obtain ⟨L, rfl, fresh⟩ := seen_absent ok "tuple"
      unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh, Term.true,
        Term.false, Erlang.maps.«put/3»]
      simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
        Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Lynx.Except.guard,
        Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
        Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
        Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil, Erlang.erlang.«>=/2»]

    theorem map_top_nonempty (d : Dispatcher) {S : Term} (ok : SeenOk S) :
        Elixir.Module.Types.Descr.«map_empty?/2» d (.tuple #[.integer 61102469, .atom "open", .nil]) S =
          .ok (.atom "false") := by
      obtain ⟨L, rfl, fresh⟩ := seen_absent ok "map"
      unfold Elixir.Module.Types.Descr.«map_empty?/2»
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh, Term.true,
        Term.false, Erlang.maps.«put/3»]
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      have line := line_inter_open d 61102469 .nil
      simp [line, Elixir.Module.Types.Descr.«init_map_line_empty?/4», any_nil]
      rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      simp

    theorem list_top_nonempty (d : Dispatcher) (S : Term) :
        Elixir.Module.Types.Descr.«list_empty?/2» d (.tuple #[.integer 46675407, .atom "term", .atom "term"]) S =
          .ok (.atom "false") := by
      unfold Elixir.Module.Types.Descr.«list_empty?/2»
      simp

    theorem fun_top_nonempty (d : Dispatcher) (S : Term) :
        Elixir.Module.Types.Descr.«fun_empty?/2» d (.tuple #[.atom "negation", .map []]) S = .ok (.atom "false") := by
      unfold Elixir.Module.Types.Descr.«fun_empty?/2»
      simp

    theorem empty_none_seen (d : Dispatcher) (S : Term) :
        Elixir.Module.Types.Descr.«empty_seen?/2» d (.map []) S = .ok (.atom "true") := by
      unfold Elixir.Module.Types.Descr.«empty_seen?/2»
      simp [getMapKeys, Erlang.erlang.«==/2»]

    /-- Basic types are empty exactly when they have no fields. -/
    theorem empty_basic (d : Dispatcher) {M : List (Term × Term)} (basic : Basic M) {S : Term} (ok : SeenOk S)
        (nonempty : M ≠ []) : Elixir.Module.Types.Descr.«empty_seen?/2» d (.map M) S = .ok (.atom "false") := by
      have static : mapLookup M (.atom "dynamic") = Option.none := by
        cases h : mapLookup M (.atom "dynamic") with
        | none => rfl
        | some w =>
          rcases basic.keys _ (by rw [h]; rfl) with e | e | e | e | e | e <;> simp at e
      have top : ∀ name, name ≠ "bitmap" → name ≠ "atom" → ∀ w, mapLookup M (.atom name) = some w →
          topValue name = some w := fun name n₁ n₂ w h => basic.top name w n₁ n₂ h
      unfold Elixir.Module.Types.Descr.«empty_seen?/2»
      simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
      have tupleV := top "tuple" (by decide) (by decide)
      have mapV := top "map" (by decide) (by decide)
      have listV := top "list" (by decide) (by decide)
      have funV := top "fun" (by decide) (by decide)
      simp only [topValue] at tupleV mapV listV funV
      cases ha : mapLookup M (.atom "atom") with
      | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso]
      | none =>
      cases hb : mapLookup M (.atom "bitmap") with
      | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso]
      | none =>
      have nT := tuple_top_nonempty d ok
      have nM := map_top_nonempty d ok
      have nL := list_top_nonempty d S
      have nF := fun_top_nonempty d S
      cases ht : mapLookup M (.atom "tuple") <;> cases hm : mapLookup M (.atom "map") <;>
        cases hl : mapLookup M (.atom "list") <;> cases hf : mapLookup M (.atom "fun") <;>
        simp_all [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», Lynx.Except.andAlso]
      apply nonempty
      apply nil_of_lookup_none
      intro q
      cases h : mapLookup M q with
      | none => rfl
      | some w =>
        rcases basic.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

    theorem le_sum_of_mem : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.sum
      | [], _, h => by simp at h
      | y :: ys, x, h => by
        rcases List.mem_cons.mp h with rfl | h
        · simp
        · have := le_sum_of_mem ys x h; simp; omega

    /-- A non-empty atom type: a non-empty union, or any negation, as some atom is not in a set. -/
    theorem fresh_atom (E : List (Term × Term)) : ∃ q, mapLookup E q = Option.none := by
      let n : Nat := (E.map fun e => match e.1 with | .atom m => m.length | _ => 0).sum + 1
      refine ⟨.atom (String.ofList (List.replicate n 'a')), ?_⟩
      simp only [mapLookup, Option.map_eq_none_iff, List.find?_eq_none]
      intro e member hit
      have same := (exactCompare_eq_atom _ _).mp (Std.OrientedCmp.eq_symm (of_decide_eq_true hit))
      have le : (match e.1 with | .atom m => m.length | _ => 0) ≤
          (E.map fun e => match e.1 with | .atom m => m.length | _ => 0).sum :=
        le_sum_of_mem _ _ (List.mem_map_of_mem member)
      rw [same] at le
      simp at le
      omega

    /-- Atom types from set operations are non-empty unless they are `0`. -/
    theorem atom_nonempty (p : Bool) (E : List (Term × Term)) (ne : p = Bool.true → E ≠ []) :
        ∃ q, amemV (some (.tuple #[.atom (if p then "union" else "negation"), .map E])) q = Bool.true := by
      cases p
      · obtain ⟨q, hq⟩ := fresh_atom E
        exact ⟨q, by simp [amemV, hq]⟩
      · cases E with
        | nil => exact absurd rfl (ne rfl)
        | cons e rest => exact ⟨e.1, by simp [amemV, mapLookup]⟩

    theorem top_cases {name : String} {w : Term} (h : topValue name = some w) :
        (name = "fun" ∧ w = .tuple #[.atom "negation", .map []]) ∨
        (name = "list" ∧ w = .tuple #[.integer 46675407, .atom "term", .atom "term"]) ∨
        (name = "tuple" ∧ w = .tuple #[.integer 61102469, .atom "open", .nil]) ∨
        (name = "map" ∧ w = .tuple #[.integer 61102469, .atom "open", .nil]) := by
      unfold topValue at h
      split at h <;> simp_all

    /-- The difference of two fields of basic types at the same key. -/
    theorem diff_key (d : Dispatcher) (name : String) (x y : Term) (hx : FieldOk name x) (hy : FieldOk name y) :
        ∃ r, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y = .ok r ∧
          (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
          (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a - (a &&& b))) ∧
          (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
            (amemV (some x) q && !amemV (some y) q)) ∧
          (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.false) := by
      rcases hx with ⟨rfl, a, rfl, a₁, a₂⟩ | ⟨rfl, ⟨p₁, S₁, rfl, set₁⟩, -⟩ | ⟨n₁, n₂, tx⟩
      · rcases hy with ⟨-, b, rfl, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
        · have le : a &&& b ≤ a := Nat.and_le_left
          refine ⟨.integer ↑(a - (a &&& b)), ?_, fun k => ?_, fun _ => ⟨a, b, rfl, rfl, rfl⟩, by simp, by simp⟩
          · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]; omega
          · simp [kept] at k
            exact Or.inl ⟨rfl, _, rfl, by omega, by omega⟩
        · simp at e
        · simp at e
      · rcases hy with ⟨e, -⟩ | ⟨-, ⟨p₂, S₂, rfl, set₂⟩, -⟩ | ⟨-, e, -⟩
        · simp at e
        · rcases atom_difference p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -, ne, mE⟩ | ⟨hE, mE⟩
          · have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) = Bool.true := by
              simp [kept]
            refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_difference/3», hE],
              fun _ => Or.inr (Or.inl ⟨rfl, ⟨p, E, rfl, setE⟩, atom_nonempty p E ne⟩), by simp, fun _ q => ?_, by simp⟩
            rw [keep]; simp only [ite_true, amemV_field, mE]
          · refine ⟨.integer 0, by simp [Elixir.Module.Types.Descr.«bare_difference/3», hE], fun k => by simp [kept] at k,
              by simp, fun _ q => ?_, by simp⟩
            have := mE q
            simp only [kept, amemV_field] at this ⊢
            simp [amemV, this]
        · simp at e
      · rcases hy with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, ty⟩
        · exact absurd e n₁
        · exact absurd e n₂
        rw [tx] at ty; cases ty
        refine ?_
        rcases top_cases tx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» d (.map []) (.map []) = .ok (.map []) := by
            simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
          refine ⟨.integer 0, ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
            Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]
        · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»]
        · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»]
        · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»]

    theorem Basic.static {M : List (Term × Term)} (basic : Basic M) : mapLookup M (.atom "dynamic") = Option.none := by
      cases h : mapLookup M (.atom "dynamic") with
      | none => rfl
      | some w => rcases basic.keys _ (by rw [h]; rfl) with e | e | e | e | e | e <;> simp at e

    theorem Basic.field {M : List (Term × Term)} (basic : Basic M) {name : String} {w : Term}
        (h : mapLookup M (.atom name) = some w) : FieldOk name w := by
      by_cases b : name = "bitmap"
      · subst b; exact Or.inl ⟨rfl, basic.bitmap w h⟩
      by_cases a : name = "atom"
      · subst a
        obtain ⟨field, q, hq⟩ := basic.atom w h
        exact Or.inr (Or.inl ⟨rfl, field, q, by simpa [amem, h] using hq⟩)
      exact Or.inr (Or.inr ⟨b, a, basic.top name w b a h⟩)

    theorem Basic.atomKey {M : List (Term × Term)} (basic : Basic M) {q w : Term} (h : mapLookup M q = some w) :
        ∃ name, q = .atom name := by
      rcases basic.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

    theorem basic_of {M : List (Term × Term)}
        (keys : ∀ q, (mapLookup M q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
          q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map")
        (fields : ∀ name w, mapLookup M (.atom name) = some w → FieldOk name w) : Basic M := by
      refine ⟨keys, fun w h => ?_, fun w h => ?_, fun name w b a h => ?_⟩
      · rcases fields _ w h with ⟨-, ok⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> first | exact ok | simp at e
      · rcases fields _ w h with ⟨e, -⟩ | ⟨-, field, q, hq⟩ | ⟨-, e, -⟩
        · simp at e
        · exact ⟨field, q, by simpa [amem, h] using hq⟩
        · simp at e
      · rcases fields name w h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, top⟩
        · exact absurd e b
        · exact absurd e a
        · exact top

    /-- Folding the difference of basic types gives the basic type of the differences of their fields. -/
    theorem fold_basic (A B C : List (Term × Term)) (bA : Basic A) (bB : Basic B) (g : Term → Term → Term → Term)
        (lookC : ∀ q, mapLookup C q =
          match (mapEntries B).find? (fun e => decide (exactCompare q e.1 = .eq)) with
          | some e => (mapLookup A e.1).bind fun v₁ =>
              if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else Option.none
          | none => mapLookup A q)
        (dk : ∀ name x y, mapLookup A (.atom name) = some x → mapLookup B (.atom name) = some y →
          (∃ r, g (.atom name) x y = r ∧
              (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
              (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a - (a &&& b))) ∧
              (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
                (amemV (some x) q && !amemV (some y) q)) ∧
              (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.false))) :
        Basic C ∧ bits C = bits A - (bits A &&& bits B) ∧ (∀ q, amem C q = (amem A q && !amem B q)) ∧
          ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = (has A name && !has B name) := by
      have look : ∀ name, mapLookup C (.atom name) =
          match mapLookup B (.atom name) with
          | some y => (mapLookup A (.atom name)).bind fun x =>
              if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
          | none => mapLookup A (.atom name) := by
        intro name
        rw [lookC, find_atom]
        cases mapLookup B (.atom name) <;> rfl
      have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
        intro q some
        rw [lookC] at some
        split at some
        · rename_i e hit
          have same : exactCompare q e.1 = .eq := by simpa using List.find?_some hit
          rw [mapLookup_congr same]
          cases h : mapLookup A e.1 <;> simp_all
        · exact some
      refine ⟨basic_of (fun q h => bA.keys q (keys q h)) fun name w h => ?_, ?_, fun q => ?_, fun name b a => ?_⟩
      · rw [look] at h
        cases hy : mapLookup B (.atom name) with
        | none => rw [hy] at h; exact bA.field h
        | some y =>
          rw [hy] at h
          cases hx : mapLookup A (.atom name) with
          | none => rw [hx] at h; cases h
          | some x =>
            rw [hx] at h
            obtain ⟨r, run, ok, -⟩ := dk name x y hx hy
            simp only [run, Option.bind_some] at h
            split at h
            · rename_i k; cases h; exact ok k
            · cases h
      · simp only [bits]
        rw [look]
        cases hy : mapLookup B (.atom "bitmap") with
        | none =>
          cases hx : mapLookup A (.atom "bitmap") with
          | none => simp
          | some x => obtain ⟨a, rfl, -⟩ := bA.bitmap x hx; simp
        | some y =>
          obtain ⟨b, rfl, -⟩ := bB.bitmap _ hy
          cases hx : mapLookup A (.atom "bitmap") with
          | none => simp
          | some x =>
            obtain ⟨a, rfl, -⟩ := bA.bitmap x hx
            obtain ⟨r, run, -, bm, -⟩ := dk "bitmap" _ _ hx hy
            obtain ⟨a', b', ea, eb, rfl⟩ := bm rfl
            simp only [Term.integer.injEq] at ea eb
            have ea' : a' = a := by omega
            have eb' : b' = b := by omega
            rw [ea', eb'] at run
            simp only [run, Option.bind_some]
            by_cases z : a - (a &&& b) = 0 <;> simp [kept, z]
      · simp only [amem]
        rw [look]
        cases hy : mapLookup B (.atom "atom") with
        | none => simp [amemV]
        | some y =>
          cases hx : mapLookup A (.atom "atom") with
          | none => simp [amemV]
          | some x =>
            obtain ⟨r, run, -, -, am, -⟩ := dk "atom" _ _ hx hy
            have := am rfl q
            simp only [run, Option.bind_some]
            rw [← this]
      · simp only [has]
        rw [look]
        cases hy : mapLookup B (.atom name) with
        | none => simp
        | some y =>
          cases hx : mapLookup A (.atom name) with
          | none => simp
          | some x =>
            obtain ⟨r, run, -, -, -, gone⟩ := dk name _ _ hx hy
            simp [run, gone b a]


    /-- Differences of basic types are basic types of the differences of their fields. -/
    theorem diff_basic (depth : Nat) (left : Term) (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B)
        (hleft : left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧
          Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) :
        ∃ C, Elixir.Module.Types.Descr.«bare_difference/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
            left (.map B) = .ok (.map C) ∧ Basic C ∧
          bits C = bits A - (bits A &&& bits B) ∧ (∀ q, amem C q = (amem A q && !amem B q)) ∧
          ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = (has A name && !has B name) := by
      by_cases emptyB : B = []
      · subst emptyB
        rcases hleft with rfl | ⟨-, ne, -⟩
        rotate_left
        · exact absurd rfl ne
        refine ⟨A, ?_, bA, by simp [bits, mapLookup], fun q => by simp [amem, amemV, mapLookup],
          fun name _ _ => by simp [has, mapLookup]⟩
        unfold Elixir.Module.Types.Descr.«bare_difference/2»
        simp [Erlang.erlang.«==/2»]
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      obtain ⟨C, fold, lookC⟩ := difference_fold depth (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
        g (mapEntries B) A (mapEntries_distinct B) (by
          intro e member v₁ found
          have hy := mapLookup_of_mem_mapEntries member
          obtain ⟨name, key⟩ := bA.atomKey found
          rw [key] at found hy ⊢
          obtain ⟨r, run, -⟩ := diff_key (Dispatcher.ofTable Erlang.program.fun_table depth) name v₁ e.2
            (bA.field found) (bB.field hy)
          rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure, run]
          simp [g, run])
      have run : Elixir.Module.Types.Descr.«bare_difference/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
          left (.map B) = .ok (.map C) := by
        rcases hleft with rfl | ⟨rfl, -, term⟩
        · unfold Elixir.Module.Types.Descr.«bare_difference/2»
          simp [Erlang.erlang.«==/2», unfold_map, static_map bA.static, static_map bB.static, emptyB]
          unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
          simp [Erlang.erlang.«==/2», emptyB, unfold_map, Erlang.maps.«fold/3»]
          simpa using fold
        · unfold Elixir.Module.Types.Descr.«bare_difference/2»
          simp [Erlang.erlang.«==/2», unfold_map, static_map bB.static, emptyB]
          unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
          simp [Erlang.erlang.«==/2», emptyB, unfold_map, Erlang.maps.«fold/3», term]
          simpa using fold
      have gval : ∀ name x y r, Elixir.Module.Types.Descr.«bare_difference/3»
          (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y = .ok r → g (.atom name) x y = r := by
        intro name x y r h; simp [g, h]
      exact ⟨C, run, fold_basic A B C bA bB g lookC fun name x y hx hy => by
        obtain ⟨r, run, rest⟩ := diff_key (Dispatcher.ofTable Erlang.program.fun_table depth) name x y
          (bA.field hx) (bB.field hy)
        exact ⟨r, gval _ _ _ _ run, rest⟩⟩

    /-- The intersection of two fields of basic types at the same key. -/
    theorem inter_key (d : Dispatcher) (name : String) (x y : Term) (hx : FieldOk name x) (hy : FieldOk name y) :
        ∃ r, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom name) x y = .ok r ∧
          (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
          (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a &&& b)) ∧
          (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
            (amemV (some x) q && amemV (some y) q)) ∧
          (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.true) := by
      rcases hx with ⟨rfl, a, rfl, a₁, a₂⟩ | ⟨rfl, ⟨p₁, S₁, rfl, set₁⟩, -⟩ | ⟨n₁, n₂, tx⟩
      · rcases hy with ⟨-, b, rfl, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
        · have le : a &&& b ≤ a := Nat.and_le_left
          refine ⟨.integer ↑(a &&& b), ?_, fun k => ?_, fun _ => ⟨a, b, rfl, rfl, rfl⟩, by simp, by simp⟩
          · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Erlang.erlang.«band/2»]
          · simp [kept] at k
            exact Or.inl ⟨rfl, _, rfl, by omega, by omega⟩
        · simp at e
        · simp at e
      · rcases hy with ⟨e, -⟩ | ⟨-, ⟨p₂, S₂, rfl, set₂⟩, -⟩ | ⟨-, e, -⟩
        · simp at e
        · rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -, ne, mE⟩ | ⟨hE, mE⟩
          · have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) = Bool.true := by
              simp [kept]
            refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», hE],
              fun _ => Or.inr (Or.inl ⟨rfl, ⟨p, E, rfl, setE⟩, atom_nonempty p E ne⟩), by simp, fun _ q => ?_, by simp⟩
            rw [keep]; simp only [ite_true, amemV_field, mE]
          · refine ⟨.integer 0, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», hE], fun k => by simp [kept] at k,
              by simp, fun _ q => ?_, by simp⟩
            have := mE q
            simp only [kept, amemV_field] at this ⊢
            simp [amemV, this]
        · simp at e
      · rcases hy with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, ty⟩
        · exact absurd e n₁
        · exact absurd e n₂
        rw [tx] at ty; cases ty
        refine ⟨x, ?_, fun _ => Or.inr (Or.inr ⟨n₁, n₂, tx⟩), fun e => absurd e n₁, fun e => absurd e n₂, fun _ _ => ?_⟩
        · rcases top_cases tx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · have union : Elixir.Module.Types.Descr.«fun_repr_union/2» d (.map []) (.map []) = .ok (.map []) := by
              simp [Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3»,
                Erlang.maps.«merge_with/3»]
            simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», union,
              Erlang.erlang.«==/2», Lynx.Except.andAlso]
          · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«list_intersection/2»]
          · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«tuple_intersection/2»]
          · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«map_intersection/2»]
        · rcases top_cases tx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [kept]

    /-- Intersections of basic types are basic types of the intersections of their fields. -/
    theorem find_isSome (M : List (Term × Term)) (q : Term) {e : Term × Term}
        (hit : (mapEntries M).find? (fun e => decide (exactCompare q e.1 = .eq)) = some e) :
        (mapLookup M q).isSome := by
      rw [← mapLookup_mapEntries]
      simp [mapLookup, hit]

    theorem inter_basic (depth : Nat) (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B) :
        ∃ C, Elixir.Module.Types.Descr.«bare_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.map A) (.map B) = .ok (.map C) ∧ Basic C ∧
          bits C = bits A &&& bits B ∧ (∀ q, amem C q = (amem A q && amem B q)) ∧
          ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = (has A name && has B name) := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have gval : ∀ name x y r, Elixir.Module.Types.Descr.«bare_intersection/3»
          (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y = .ok r → g (.atom name) x y = r := by
        intro name x y r h; simp [g, h]
      have ik := fun name x y (hx : mapLookup A (.atom name) = some x) (hy : mapLookup B (.atom name) = some y) =>
        inter_key (Dispatcher.ofTable Erlang.program.fun_table depth) name x y (bA.field hx) (bB.field hy)
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr" "bare_intersection" #[] A B g (by
          intro e me y hy
          have hx := mapLookup_of_mem_mapEntries me
          obtain ⟨name, key⟩ := bA.atomKey hx
          rw [key] at hx hy ⊢
          obtain ⟨r, run, -⟩ := ik name e.2 y hx hy
          rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, run, gval _ _ _ _ run])
      obtain ⟨C, runC, lookC⟩ := Erlang.maps.filter_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] I kept (by
          intro e _
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
      have run : Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map A) (.map B) = .ok (.map C) := by
        unfold Elixir.Module.Types.Descr.«bare_intersection/2»
        simp [getMapKeys_single, bA.static, bB.static]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runC]
      have look : ∀ name, mapLookup C (.atom name) =
          match mapLookup A (.atom name), mapLookup B (.atom name) with
          | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
          | _, _ => Option.none := by
        intro name
        rw [lookC, find_atom, lookI, find_atom]
        cases mapLookup A (.atom name) <;> cases hR : mapLookup B (.atom name) <;> simp [hR]
      have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
        intro q some
        rw [lookC] at some
        split at some
        · rename_i e hit
          have hI := find_isSome I q hit
          rw [lookI] at hI
          split at hI
          · rename_i e' hit'
            exact find_isSome A q hit'
          · simp at hI
        · simp at some
      refine ⟨C, run, basic_of (fun q h => bA.keys q (keys q h)) fun name w h => ?_, ?_, fun q => ?_, fun name b a => ?_⟩
      · rw [look] at h
        cases hx : mapLookup A (.atom name) <;> cases hy : mapLookup B (.atom name) <;> rw [hx, hy] at h <;>
          try simp at h
        rename_i x y
        obtain ⟨r, run, ok, -⟩ := ik name x y hx hy
        simp only [gval _ _ _ _ run] at h
        obtain ⟨k, rfl⟩ := h
        exact ok k
      · simp only [bits]
        rw [look]
        cases hx : mapLookup A (.atom "bitmap") with
        | none => simp
        | some x =>
          obtain ⟨a, rfl, -⟩ := bA.bitmap x hx
          cases hy : mapLookup B (.atom "bitmap") with
          | none => simp
          | some y =>
            obtain ⟨b, rfl, -⟩ := bB.bitmap _ hy
            obtain ⟨r, run, -, bm, -⟩ := ik "bitmap" _ _ hx hy
            obtain ⟨a', b', ea, eb, rfl⟩ := bm rfl
            simp only [Term.integer.injEq] at ea eb
            have ea' : a' = a := by omega
            have eb' : b' = b := by omega
            rw [ea', eb'] at run
            simp only [gval _ _ _ _ run]
            by_cases z : a &&& b = 0 <;> simp [kept, z]
      · simp only [amem]
        rw [look]
        cases hx : mapLookup A (.atom "atom") with
        | none => simp [amemV]
        | some x =>
          cases hy : mapLookup B (.atom "atom") with
          | none => simp [amemV]
          | some y =>
            obtain ⟨r, run, -, -, am, -⟩ := ik "atom" _ _ hx hy
            have := am rfl q
            simp only [gval _ _ _ _ run]
            rw [← this]
      · simp only [has]
        rw [look]
        cases hx : mapLookup A (.atom name) with
        | none => simp
        | some x =>
          cases hy : mapLookup B (.atom name) with
          | none => simp
          | some y =>
            obtain ⟨r, run, -, -, -, stay⟩ := ik name _ _ hx hy
            simp [gval _ _ _ _ run, stay b a]

    /-- Optimized unions of static types merge their fields, uniting those in both. -/
    theorem opt_union_lookup (depth : Nat) (L R : List (Term × Term)) (seen : Term)
        (staticL : mapLookup L (.atom "dynamic") = Option.none) (staticR : mapLookup R (.atom "dynamic") = Option.none)
        (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          ∃ u, Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth) q x y seen = .ok u) :
        ∃ U, Elixir.Module.Types.Descr.«opt_union/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.map L) (.map R) seen = .ok (.map U) ∧
          (∀ name, (mapLookup R (.atom name) = Option.none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
            (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = Option.none →
              mapLookup U (.atom name) = some y) ∧
            (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
              Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y seen =
                .ok u → mapLookup U (.atom name) = some u)) ∧
          ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ seen with
        | .ok w => w
        | .error _ => .nil
      have value : ∀ q x y u, Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth)
          q x y seen = .ok u → g q x y = u := by
        intro q x y u run; simp [g, run]
      obtain ⟨U, run, look, keys⟩ : ∃ U, Elixir.Module.Types.Descr.«opt_union/3»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) seen = .ok (.map U) ∧
          (∀ name, mapLookup U (.atom name) =
            match mapLookup R (.atom name) with
            | some y => some (match mapLookup L (.atom name) with | some x => g (.atom name) x y | none => y)
            | none => mapLookup L (.atom name)) ∧
          ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome := by
        unfold Elixir.Module.Types.Descr.«opt_union/3»
        simp [getMapKeys_single, Erlang.erlang.«==/2», staticL, staticR]
        by_cases emptyL : L = []
        · subst emptyL
          refine ⟨R, by simp, fun name => ?_, fun q h => Or.inr h⟩
          cases mapLookup R (.atom name) <;> simp [mapLookup]
        by_cases emptyR : R = []
        · subst emptyR
          exact ⟨L, by simp [emptyL], fun name => by simp [mapLookup], fun q h => Or.inl h⟩
        simp only [emptyL, emptyR]
        unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
        obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr" "-opt_union/3-anonymous-0-"
            #[seen] L R g (by
            intro e me x hx
            have hy := mapLookup_of_mem_mapEntries me
            obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
            rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_union/3-anonymous-0-/3».pure]
            simp only [Elixir.Module.Types.Descr.«-opt_union/3-anonymous-0-/4»]
            rw [ru, value _ _ _ _ ru])
        refine ⟨out, by simpa using run, fun name => ?_, fun q h => ?_⟩
        · rw [look, find_atom]
          cases mapLookup R (.atom name) <;> rfl
        · rw [look] at h
          split at h
          · rename_i e hit; exact Or.inr (find_isSome R q hit)
          · exact Or.inl h
      refine ⟨U, run, fun name => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩, keys⟩
      · rw [look, hR]
      · rw [look, hR, hL]
      · rw [look, hR, hL]; simp only [value _ _ _ _ ru]


    /-- Optimized unions with basic types without top fields are basic types of the unions of their fields. -/
    theorem union_basic (depth : Nat) (A B : List (Term × Term)) (seen : Term) (bA : Basic A) (bB : Basic B)
        (noTops : ∀ name, name ≠ "bitmap" → name ≠ "atom" → has A name = Bool.false) :
        ∃ C, Elixir.Module.Types.Descr.«opt_union/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.map A) (.map B) seen = .ok (.map C) ∧ Basic C ∧
          bits C = bits A ||| bits B ∧ (∀ q, amem C q = (amem A q || amem B q)) ∧
          ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = has B name := by
      have uk : ∀ q x y, mapLookup A q = some x → mapLookup B q = some y →
          ∃ name, q = .atom name ∧ ∃ u, Elixir.Module.Types.Descr.«opt_union/4»
            (Dispatcher.ofTable Erlang.program.fun_table depth) q x y seen = .ok u ∧ FieldOk name u ∧
            (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ u = .integer ↑(a ||| b)) ∧
            (name = "atom" → ∀ q', amemV (some u) q' = (amemV (some x) q' || amemV (some y) q')) := by
        intro q x y hx hy
        obtain ⟨name, rfl⟩ := bA.atomKey hx
        refine ⟨name, rfl, ?_⟩
        rcases bA.field hx with ⟨rfl, a, rfl, a₁, a₂⟩ | ⟨rfl, ⟨p₁, S₁, rfl, set₁⟩, q₁, hq₁⟩ | ⟨n₁, n₂, -⟩
        · obtain ⟨b, rfl, b₁, b₂⟩ := bB.bitmap y hy
          have : a ||| b ≤ 255 := by
            apply Nat.le_of_lt_succ
            exact Nat.or_lt_two_pow (by omega : a < 2 ^ 8) (by omega : b < 2 ^ 8)
          have : a ≤ a ||| b := Nat.left_le_or
          refine ⟨.integer ↑(a ||| b), by simp [Elixir.Module.Types.Descr.«opt_union/4», Erlang.erlang.«bor/2»],
            Or.inl ⟨rfl, _, rfl, by omega, by omega⟩, fun _ => ⟨a, b, rfl, rfl, rfl⟩, by simp⟩
        · obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := bB.atom y hy
          obtain ⟨p, E, hE, setE, mE⟩ := atom_union p₁ S₁ p₂ S₂ set₁ set₂
          have mem : ∀ q', amemV (some (.tuple #[.atom (if p then "union" else "negation"), .map E])) q' =
              (amemV (some (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])) q' ||
                amemV (some (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂])) q') := by
            intro q'; simp only [amemV_field, mE]
          refine ⟨_, by simp [Elixir.Module.Types.Descr.«opt_union/4», hE],
            Or.inr (Or.inl ⟨rfl, ⟨p, E, rfl, setE⟩, q₁, by rw [mem, hq₁]; rfl⟩), by simp, fun _ => mem⟩
        · have := noTops name n₁ n₂
          simp [has, hx] at this
      obtain ⟨C, run, look⟩ := opt_union_lookup depth A B seen bA.static bB.static (by
        intro q x y hx hy
        obtain ⟨name, -, u, run, -⟩ := uk q x y hx hy
        exact ⟨u, run⟩)
      refine ⟨C, run, basic_of (fun q h => ?_) fun name w h => ?_, ?_, fun q => ?_, fun name b a => ?_⟩
      · rcases look.2 q h with h | h
        · exact bA.keys q h
        · exact bB.keys q h
      · cases hy : mapLookup B (.atom name) with
        | none => rw [(look.1 name).1 hy] at h; exact bA.field h
        | some y =>
          cases hx : mapLookup A (.atom name) with
          | none => rw [(look.1 name).2.1 y hy hx] at h; cases h; exact bB.field hy
          | some x =>
            obtain ⟨name', e, u, ru, ok, -⟩ := uk _ x y hx hy
            cases e
            rw [(look.1 name).2.2 x y u hx hy ru] at h; cases h; exact ok
      · simp only [bits]
        cases hy : mapLookup B (.atom "bitmap") with
        | none =>
          rw [(look.1 "bitmap").1 hy]
          cases hx : mapLookup A (.atom "bitmap") with
          | none => simp
          | some x => obtain ⟨a, rfl, -⟩ := bA.bitmap x hx; simp
        | some y =>
          obtain ⟨b, rfl, -⟩ := bB.bitmap _ hy
          cases hx : mapLookup A (.atom "bitmap") with
          | none => rw [(look.1 "bitmap").2.1 _ hy hx]; simp
          | some x =>
            obtain ⟨name', e, u, ru, -, bm, -⟩ := uk _ x _ hx hy
            cases e
            obtain ⟨a, b', rfl, eb, rfl⟩ := bm rfl
            simp only [Term.integer.injEq] at eb
            have eb' : b' = b := by omega
            subst eb'
            rw [(look.1 "bitmap").2.2 _ _ _ hx hy ru]
            simp
      · simp only [amem]
        cases hy : mapLookup B (.atom "atom") with
        | none =>
          rw [(look.1 "atom").1 hy]
          simp [amemV]
        | some y =>
          cases hx : mapLookup A (.atom "atom") with
          | none => rw [(look.1 "atom").2.1 _ hy hx]; simp [amemV]
          | some x =>
            obtain ⟨name', e, u, ru, -, -, am⟩ := uk _ x _ hx hy
            cases e
            rw [(look.1 "atom").2.2 _ _ _ hx hy ru]
            exact am rfl q
      · simp only [has]
        have none := noTops name b a
        simp only [has, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at none
        cases hy : mapLookup B (.atom name) with
        | none => rw [(look.1 name).1 hy, none]
        | some y => rw [(look.1 name).2.1 _ hy none]

    /-- Types of non-empty bitmaps and atoms are basic types without top fields. -/
    theorem Valid.basic {V : List (Term × Term)} (valid : Valid V) :
        Basic V ∧ ∀ name, name ≠ "bitmap" → name ≠ "atom" → has V name = Bool.false := by
      have none : ∀ name, name ≠ "bitmap" → name ≠ "atom" → mapLookup V (.atom name) = Option.none := by
        intro name b a
        cases h : mapLookup V (.atom name) with
        | none => rfl
        | some w =>
          rcases valid.keys _ (by rw [h]; rfl) with e | e <;> simp at e <;> contradiction
      refine ⟨basic_of (fun q h => ?_) fun name w h => ?_, fun name b a => by simp [has, none name b a]⟩
      · rcases valid.keys q h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · by_cases b : name = "bitmap"
        · subst b; exact Or.inl ⟨rfl, valid.bitmap w h⟩
        by_cases a : name = "atom"
        · subst a
          obtain ⟨p, S, rfl, set⟩ := valid.atom w h
          exact Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩,
            atom_nonempty p S fun pt => by subst pt; exact valid.atomUnion S (by simpa using h)⟩)
        · rw [none name b a] at h; cases h

    /-- The top type is the basic type of every field. -/
    theorem term_basic {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) :
        Basic T ∧ bits T = 255 ∧ (∀ q, amem T q = Bool.true) ∧
          ∀ name, name ≠ "bitmap" → name ≠ "atom" → has T name = (topValue name).isSome := by
      have keyed := fun q t (h : mapLookup T q = some t) => term_keys term h
      have eqT := term
      simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at eqT
      cases eqT
      refine ⟨basic_of (fun q h => ?_) fun name w h => ?_, by simp [bits, mapLookup], fun q => ?_, fun name b a => ?_⟩
      · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
        rcases keyed q t ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
      · rcases keyed _ w h with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;>
          simp only [Term.atom.injEq] at e <;> subst e
        · exact Or.inl ⟨rfl, 255, rfl, by omega, by omega⟩
        · obtain ⟨q, hq⟩ := fresh_atom []
          exact Or.inr (Or.inl ⟨rfl, ⟨false, [], rfl, by simp [Erlang.sets.elements?]⟩, q, by simp [amemV, mapLookup]⟩)
        all_goals exact Or.inr (Or.inr ⟨by decide, by decide, rfl⟩)
      · simp [amem, amemV, mapLookup]
      · simp only [has]
        cases h : mapLookup _ (.atom name) with
        | none =>
          unfold topValue
          split <;> simp_all [mapLookup]
        | some t =>
          rcases keyed _ t h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;>
            simp only [Term.atom.injEq] at e <;> subst e <;> simp_all [topValue]

    /-- Optimized negations of basic types without top fields are basic types of the complements. -/
    theorem opt_negation_basic (depth : Nat) (B : List (Term × Term)) (seen : Term) (bB : Basic B)
        (noTops : ∀ name, name ≠ "bitmap" → name ≠ "atom" → has B name = Bool.false) (nonempty : B ≠ []) :
        ∃ C, Elixir.Module.Types.Descr.«opt_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 3))
            (.atom "term") (.map B) seen = .ok (.map C) ∧ Basic C ∧
          bits C = 255 - (255 &&& bits B) ∧ (∀ q, amem C q = !amem B q) ∧
          ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = (topValue name).isSome := by
      obtain ⟨T, term, -⟩ := unfolded_term_fields
      obtain ⟨bT, bitsT, amemT, hasT⟩ := term_basic term
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«opt_difference/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
          k₀ v₁ v₂ seen with
        | .ok w => w
        | .error _ => .nil
      have same : ∀ name x y, mapLookup B (.atom name) = some y →
          Elixir.Module.Types.Descr.«opt_difference/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.atom name) x y seen =
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.atom name) x y := by
        intro name x y hy
        by_cases b : name = "bitmap"
        · subst b; simp [Elixir.Module.Types.Descr.«opt_difference/4», Elixir.Module.Types.Descr.«bare_difference/3»]
        by_cases a : name = "atom"
        · subst a; simp [Elixir.Module.Types.Descr.«opt_difference/4», Elixir.Module.Types.Descr.«bare_difference/3»]
        · have h₁ := noTops name b a
          simp [has, hy] at h₁
      obtain ⟨C, fold, lookC⟩ := difference_fold (depth + 1)
        (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-0-" 3 #[seen])
        g (mapEntries B) T (mapEntries_distinct B) (by
          intro e member v₁ found
          have hy := mapLookup_of_mem_mapEntries member
          obtain ⟨name, key⟩ := bT.atomKey found
          rw [key] at found hy ⊢
          obtain ⟨r, run, -⟩ := diff_key (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) name v₁ e.2
            (bT.field found) (bB.field hy)
          rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-0-/3».pure]
          simp only [Elixir.Module.Types.Descr.«-opt_difference/3-anonymous-0-/4»]
          rw [same name _ _ hy, run]
          simp [g, same name _ _ hy, run])
      have run : Elixir.Module.Types.Descr.«opt_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 3))
          (.atom "term") (.map B) seen = .ok (.map C) := by
        unfold Elixir.Module.Types.Descr.«opt_difference/3»
        simp [Erlang.erlang.«==/2», unfold_map, static_map bB.static, nonempty]
        unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
        simp [Erlang.erlang.«==/2», nonempty, term, Erlang.maps.«fold/3»]
        simpa using fold
      obtain ⟨bC, bitsC, amemC, hasC⟩ := fold_basic T B C bT bB g lookC fun name x y hx hy => by
        obtain ⟨r, run, rest⟩ := diff_key (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) name x y
          (bT.field hx) (bB.field hy)
        exact ⟨r, by simp [g, same name _ _ hy, run], rest⟩
      refine ⟨C, run, bC, by rw [bitsC, bitsT], fun q => by rw [amemC, amemT]; rfl, fun name b a => ?_⟩
      rw [hasC name b a, hasT name b a, noTops name b a]
      simp

    /-- Basic types that share nothing. -/
    def Disjoint (A B : List (Term × Term)) : Prop :=
      bits A &&& bits B = 0 ∧ (∀ q, (amem A q && amem B q) = Bool.false) ∧
        ∀ name, name ≠ "bitmap" → name ≠ "atom" → (has A name && has B name) = Bool.false

    /-- Fields of basic types are not empty. -/
    theorem empty_key_field (d : Dispatcher) {name : String} {x : Term} (hx : FieldOk name x) {S : Term} (ok : SeenOk S) :
        Elixir.Module.Types.Descr.«empty_key?/3» d (.atom name) x S = .ok (.atom "false") := by
      rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, top⟩
      · simp [Elixir.Module.Types.Descr.«empty_key?/3»]
      · simp [Elixir.Module.Types.Descr.«empty_key?/3»]
      · rcases top_cases top with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [Elixir.Module.Types.Descr.«empty_key?/3», fun_top_nonempty, list_top_nonempty,
            tuple_top_nonempty d ok, map_top_nonempty d ok]

    /-- A field of a basic type is not a subtype of a disjoint field. -/
    theorem entry_false (d : Dispatcher) (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B)
        (disjoint : Disjoint A B) {S : Term} (ok : SeenOk S) (name : String) (x : Term)
        (hx : mapLookup A (.atom name) = some x) :
        (match mapLookup B (.atom name) with
          | some y => do
            let value ← Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y
            Lynx.Except.orElse (.ok (Lynx.Term.isMember value [.integer 0, .atom "bdd_bot"]))
              (Elixir.Module.Types.Descr.«empty_key?/3» d (.atom name) value S)
          | none => Elixir.Module.Types.Descr.«empty_key?/3» d (.atom name) x S) = .ok (.atom "false") := by
      obtain ⟨dbits, datom, dtop⟩ := disjoint
      cases hy : mapLookup B (.atom name) with
      | none => exact empty_key_field d (bA.field hx) ok
      | some y =>
        obtain ⟨r, run, field, bm, am, gone⟩ := diff_key d name x y (bA.field hx) (bB.field hy)
        have keep : kept (.atom name, r) = Bool.true := by
          rcases bA.field hx with ⟨rfl, a, rfl, a₁, -⟩ | ⟨rfl, -, q, hq⟩ | ⟨b, a, -⟩
          · obtain ⟨a', b', ea, eb, rfl⟩ := bm rfl
            obtain ⟨b, rfl, -⟩ := bB.bitmap y hy
            simp only [Term.integer.injEq] at ea eb
            have : a &&& b = 0 := by simpa [bits, hx, hy] using dbits
            have ea' : a' = a := by omega
            have eb' : b' = b := by omega
            subst ea' eb'
            simp [kept, this]; omega
          · have := am rfl q
            have dq := datom q
            simp only [amem, hx, hy, hq] at dq
            simp only [Bool.true_and] at dq
            cases k : kept (.atom "atom", r)
            · rw [k, hq, dq] at this
              simp [amemV] at this
            · rfl
          · have := dtop name b a
            simp [has, hx, hy] at this
        have field' := field keep
        have notMember : Lynx.Term.isMember r [.integer 0, .atom "bdd_bot"] = .atom "false" := by
          simp [kept] at keep
          simp [isMember, keep]
        simp [run, notMember, Lynx.Except.orElse, empty_key_field d field' ok]

    theorem amemV_congr {x y : Term} (fx : AtomField x) (fy : AtomField y) (e : exactCompare y x = .eq) (q : Term) :
        amemV (some y) q = amemV (some x) q := by
      obtain ⟨p₁, S₁, rfl, -⟩ := fx
      obtain ⟨p₂, S₂, rfl, -⟩ := fy
      rw [exactCompare_tuple] at e
      simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at e
      obtain ⟨tags, maps⟩ := e
      have rel := lookup_of_map_exactCompare_eq _ _ maps.1 q
      have same : (mapLookup S₂ q).isSome = (mapLookup S₁ q).isSome := by
        simp only [mapLookup]
        cases h₂ : (S₂.find? fun e => decide (exactCompare q e.1 = .eq)) <;>
          cases h₁ : (S₁.find? fun e => decide (exactCompare q e.1 = .eq)) <;> simp_all
      rw [amemV_field, amemV_field, same]
      cases p₁ <;> cases p₂ <;> simp_all

    theorem entries_cons {A : List (Term × Term)} (nonempty : A ≠ []) : ∃ e rest, mapEntries A = e :: rest := by
      cases h : mapEntries A with
      | nil =>
        apply absurd _ nonempty
        apply nil_of_lookup_none
        intro q
        rw [← mapLookup_mapEntries, h]
        rfl
      | cons e rest => exact ⟨e, rest, rfl⟩

    /-- A non-empty basic type is not a subtype of a disjoint basic type. -/
    theorem subtype_false (d : Dispatcher) (left : Term) (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B)
        (hleft : left = .map A ∨ (left = .atom "term" ∧ Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A)))
        (nonempty : A ≠ []) (disjoint : Disjoint A B) :
        Elixir.Module.Types.Descr.«subtype?/2» d left (.map B) = .ok (.atom "false") := by
      obtain ⟨e, rest, entries⟩ := entries_cons nonempty
      have he : mapLookup A e.1 = some e.2 := mapLookup_of_mem_mapEntries (by rw [entries]; simp)
      obtain ⟨name, key⟩ := bA.atomKey he
      have hx : mapLookup A (.atom name) = some e.2 := by rw [← key]; exact he
      have differ : exactCompare (.map B) (.map A) ≠ .eq := by
        intro equal
        have rel := lookup_of_map_exactCompare_eq _ _ equal (.atom name)
        change Option.Rel _ (mapLookup B (.atom name)) (mapLookup A (.atom name)) at rel
        rw [hx] at rel
        cases hy : mapLookup B (.atom name) with
        | none => rw [hy] at rel; cases rel
        | some y =>
          rw [hy] at rel
          cases rel
          rename_i same
          obtain ⟨dbits, datom, dtop⟩ := disjoint
          rcases bA.field hx with ⟨rfl, a, ea, a₁, -⟩ | ⟨rfl, fx, q, hq⟩ | ⟨b, a, -⟩
          · obtain ⟨b, rfl, -⟩ := bB.bitmap y hy
            rw [ea] at same hx
            simp at same
            have : a &&& b = 0 := by simpa [bits, hx, hy] using dbits
            have ab : b = a := by omega
            subst ab
            simp at this; omega
          · obtain ⟨fy, -⟩ := bB.atom y hy
            have := datom q
            simp only [amem, hx, hy, amemV_congr fx fy same q, hq] at this
            simp at this
          · have := dtop name b a
            simp [has, hx, hy] at this
      have first := entry_false d A B bA bB disjoint seenOk_nil name e.2 hx
      have walk : (do
          let it ← Erlang.maps.«next/1» (Term.list ((mapEntries A).map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» d it (.map B) (.map [])) =
          .ok (.atom "false") := by
        rw [entries]
        simp only [List.map, Term.list, Erlang.maps.«next/1», Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
        rw [key] at *
        cases hy : mapLookup B (.atom name) with
        | none => simp [hy] at first; simp [getMapKeys_single, hy, first, Lynx.Except.andAlso]
        | some y =>
          simp [hy] at first
          simp [getMapKeys_single, hy, Lynx.Except.andAlso]
          cases hb : Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) e.2 y with
          | error => simp [hb] at first
          | ok r =>
            simp only [hb, Lynx.Except.ok_bind] at first ⊢
            simp [first]
      rcases hleft with rfl | ⟨rfl, term⟩
      · unfold Elixir.Module.Types.Descr.«subtype?/2»
        simp [unfold_map, Erlang.erlang.«is_map_key/2», bA.static, bB.static, any_key, Lynx.Except.andAlso,
          Erlang.erlang.«/=/2»]
        unfold Elixir.Module.Types.Descr.«subtype_static?/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», differ, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, bA.static, unfold_map, Erlang.maps.«iterator/1»]
        exact walk
      · unfold Elixir.Module.Types.Descr.«subtype?/2»
        simp [term, unfold_map, Erlang.erlang.«is_map_key/2», bA.static, bB.static, any_key, Lynx.Except.andAlso,
          Erlang.erlang.«/=/2»]
        unfold Elixir.Module.Types.Descr.«subtype_static?/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», differ, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, bA.static, unfold_map, Erlang.maps.«iterator/1»]
        exact walk

    theorem field_subtype_short (d : Dispatcher) (v₁ v₂ : Term) :
        Elixir.Module.Types.Descr.«field_subtype?/2» d (.tuple #[v₁, boolAtom Bool.true]) (.tuple #[v₂, boolAtom Bool.false]) =
          .ok (.atom "false") := by
      simp [Elixir.Module.Types.Descr.«field_subtype?/2», boolAtom, Lynx.Except.andAlso]

    theorem field_subtype_long (d : Dispatcher) (v₁ v₂ : Term) (o₁ o₂ : Bool) (h : o₁ = Bool.false ∨ o₂ = Bool.true) (b : Bool)
        (sub : Elixir.Module.Types.Descr.«subtype?/2» d v₁ v₂ = .ok (boolAtom b)) :
        Elixir.Module.Types.Descr.«field_subtype?/2» d (.tuple #[v₁, boolAtom o₁]) (.tuple #[v₂, boolAtom o₂]) =
          .ok (boolAtom b) := by
      cases o₁ <;> cases o₂ <;> cases b <;>
        simp_all [Elixir.Module.Types.Descr.«field_subtype?/2», boolAtom, Lynx.Except.andAlso]

    /-- The empty type is a subtype of the top type. -/
    theorem none_subtype_term (d : Dispatcher) :
        Elixir.Module.Types.Descr.«subtype?/2» d (.map []) (.atom "term") = .ok (.atom "true") := by
      obtain ⟨T, term, bitmapT, -, -, staticT⟩ := unfolded_term_fields
      have differ : exactCompare (.map T) (.map []) ≠ .eq := by
        intro e
        have := map_exactCompare_empty _ e
        subst this
        simp [mapLookup] at bitmapT
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [term, unfold_map, Erlang.erlang.«is_map_key/2», staticT, any_key, Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
      unfold Elixir.Module.Types.Descr.«subtype_static?/2»
      simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», differ, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
      rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
      simp [getMapKeys_single, unfold_map, Erlang.maps.«iterator/1», mapLookup, Erlang.maps.«next/1»]
      rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
      rfl

    theorem bdd_bot_map (d : Dispatcher) (p n S : Term) :
        Elixir.Module.Types.Descr.«map_bdd_empty?/4» d p n (.atom "bdd_bot") S = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]; rfl

    theorem field_empty_optional (d : Dispatcher) (v S : Term) :
        Elixir.Module.Types.Descr.«field_empty_seen?/3» d v (boolAtom Bool.true) S = .ok (.atom "false") := by
      simp [Elixir.Module.Types.Descr.«field_empty_seen?/3», boolAtom]

    theorem field_empty_required (d : Dispatcher) (v S : Term) :
        Elixir.Module.Types.Descr.«field_empty_seen?/3» d v (boolAtom Bool.false) S =
          Elixir.Module.Types.Descr.«empty_seen?/2» d v S := by
      simp [Elixir.Module.Types.Descr.«field_empty_seen?/3», boolAtom]

    theorem inter_term_left (d : Dispatcher) (v : Term) :
        Elixir.Module.Types.Descr.«bare_intersection/2» d (.atom "term") v = .ok v := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl

    /-- An open map minus an open map of the same single field, whose difference is empty. -/
    theorem line_meet (d : Dispatcher) (key P vA S : Term) (kA : Int) (p oA : Bool) (M Z : Term)
        (hM : Elixir.Module.Types.Descr.«bare_intersection/2» d P vA = .ok M)
        (hFM : Elixir.Module.Types.Descr.«field_empty_seen?/3» d M (boolAtom (p && oA)) S = .ok (.atom "false"))
        (hZ : Elixir.Module.Types.Descr.«bare_difference/2» d P vA = .ok Z)
        (hFZ : Elixir.Module.Types.Descr.«field_empty_seen?/3» d Z (boolAtom (p && !oA)) S = .ok (.atom "true")) :
        Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") (fieldsTerm [(key, .tuple #[P, boolAtom p])])
          (.cons (.tuple #[.integer kA, .atom "open", fieldsTerm [(key, .tuple #[vA, boolAtom oA])]]) .nil) S =
          .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      simp [fieldsTerm, Term.list, Elixir.Module.Types.Descr.«map_check_domain_keys?/3», Erlang.erlang.«==/2»,
        Lynx.Except.orElse]
      rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
      simp [Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»]
      rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/10».eq_def]
      simp [hM, hZ, Lynx.Except.andAlso, Lynx.Except.guard, Erlang.erlang.«not/1»]
      have done : Elixir.Module.Types.Descr.«map_line_meet_empty?/7» d .nil .nil (.atom "open") (.atom "open")
          (.cons (.tuple #[key, .tuple #[M, boolAtom (p && oA)]]) .nil) .nil S = .ok (.atom "true") := by
        rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]; rfl
      cases p <;> cases oA <;> simp_all [boolAtom]

    /-- An open map minus an open map of a single field, then minus the remaining negations. -/
    theorem line_first (d : Dispatcher) (key vB nB S negs : Term) (kB : Int) (oB : Bool)
        (hFB : Elixir.Module.Types.Descr.«field_empty_seen?/3» d vB (boolAtom oB) S = .ok (.atom "false"))
        (hN : Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") vB = .ok nB)
        (rest : Elixir.Module.Types.Descr.«field_empty_seen?/3» d nB (boolAtom !oB) S = .ok (.atom "true") ∨
          (Elixir.Module.Types.Descr.«field_empty_seen?/3» d nB (boolAtom !oB) S = .ok (.atom "false") ∧
            Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") (fieldsTerm [(key, .tuple #[nB, boolAtom !oB])])
              negs S = .ok (.atom "true"))) :
        Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer kB, .atom "open", fieldsTerm [(key, .tuple #[vB, boolAtom oB])]]) negs) S =
          .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      simp [fieldsTerm, Term.list, Elixir.Module.Types.Descr.«map_check_domain_keys?/3», Erlang.erlang.«==/2»,
        Lynx.Except.orElse]
      rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
      simp [Elixir.Module.Types.Descr.«map_key_tag_to_field/1»]
      rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/10».eq_def]
      have done : ∀ f, Elixir.Module.Types.Descr.«map_line_meet_empty?/7» d .nil .nil (.atom "open") (.atom "open")
          (.cons (.tuple #[key, f]) .nil) negs S = .ok (.atom "true") := by
        intro f; rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]; rfl
      simp [inter_term_left, hN, Lynx.Except.andAlso, Lynx.Except.guard, Erlang.erlang.«not/1»]
      rcases rest with hF | ⟨hF, line⟩ <;> cases oB <;> simp_all [boolAtom, fieldsTerm, Term.list, Erlang.lists.«reverse/2»]

    theorem bdd_one (d : Dispatcher) (h k : Int) (fs S : Term)
        (line : Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer k, .atom "open", fs]) .nil) S = .ok (.atom "true")) :
        Elixir.Module.Types.Descr.«map_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil
          (.tuple #[.integer h, .tuple #[.integer k, .atom "open", fs], .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) S =
          .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      simp [bdd_bot_map, line_inter_open]
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      simp [Elixir.Module.Types.Descr.«init_map_line_empty?/4», any_nil, line]

    theorem bdd_two (d : Dispatcher) (h₁ h₂ kA kB : Int) (fA fB S : Term)
        (line : Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer kB, .atom "open", fB]) (.cons (.tuple #[.integer kA, .atom "open", fA]) .nil)) S =
            .ok (.atom "true")) :
        Elixir.Module.Types.Descr.«map_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil
          (.tuple #[.integer h₁, .tuple #[.integer kA, .atom "open", fA], .atom "bdd_bot", .atom "bdd_bot",
            .tuple #[.integer h₂, .tuple #[.integer kB, .atom "open", fB], .atom "bdd_bot", .atom "bdd_bot",
              .atom "bdd_top"]]) S = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      simp [bdd_bot_map, line_inter_open]
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      simp [bdd_bot_map, line_inter_open]
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      simp [Elixir.Module.Types.Descr.«init_map_line_empty?/4», any_nil, line]

    /-- Map BDDs are empty when their only lines are empty from any seen set of map nodes. -/
    theorem map_empty_of (d : Dispatcher) (r : Term) (h : Int) (lit c u e : Term) (shape : r = .tuple #[.integer h, lit, c, u, e])
        (run : ∀ S, SeenOk S → Elixir.Module.Types.Descr.«map_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil r S =
          .ok (.atom "true")) :
        Elixir.Module.Types.Descr.«map_empty?/2» d r (.map []) = .ok (.atom "true") := by
      subst shape
      unfold Elixir.Module.Types.Descr.«map_empty?/2»
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.true, Term.false,
        Erlang.maps.«put/3»]
      exact run _ (seenOk_node _ _ _ _ _ _)

    /-- The map difference of the top map with a map leaf other than the top literal is its negation. -/
    theorem map_difference_leaf (k : Int) (tag fs : Term) (notTop : ¬(tag = .atom "open" ∧ fs = .nil)) :
        Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, tag, fs]) =
          Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer k, tag, fs]) := by
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      split
      · next _ _ e => simp at e; exact absurd ⟨e.2.1, e.2.2⟩ notTop
      · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; rfl
      · next h₁ => exact (h₁ _ _ rfl rfl).elim

    /-- An open map of a single optional field covering `term()` covers all maps. -/
    theorem one_key_cover (d : Dispatcher) (k : Int) (key F N : Term)
        (hN : Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") F = .ok N)
        (hE : ∀ S, SeenOk S → Elixir.Module.Types.Descr.«empty_seen?/2» d N S = .ok (.atom "true")) :
        CoveredVal d (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[F, boolAtom Bool.true])]]) := by
      obtain ⟨h, node⟩ := node_new (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[F, boolAtom Bool.true])]])
        (.atom "bdd_bot") (.atom "bdd_bot") (.atom "bdd_top") ⟨_, _, _, rfl⟩
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
      refine ⟨.tuple #[.integer h, .tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[F, boolAtom Bool.true])]],
        .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"], ?_, Or.inr (Or.inr ?_)⟩
      · simp only [Elixir.Module.Types.Descr.«bare_difference/3»]
        rw [map_difference_leaf k _ _ (by simp [fieldsTerm, Term.list])]
        unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simpa using node
      · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
        refine map_empty_of d _ h _ _ _ _ rfl fun S ok => bdd_one d h k _ S ?_
        exact line_first d key F N S .nil k Bool.true (field_empty_optional d F S) hN
          (Or.inl (by rw [show (!Bool.true) = Bool.false from rfl, field_empty_required]; exact hE S ok))

    /-- The union of two open map leaves covers all maps when the lines of both orders are empty. -/
    theorem two_cover (d : Dispatcher) (k₁ k₂ : Int) (fs₁ fs₂ : Term)
        (hne : Term.compare (.tuple #[.integer k₁, .atom "open", fs₁]) (.tuple #[.integer k₂, .atom "open", fs₂]) ≠ .eq)
        (line₁ : ∀ S, SeenOk S → Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer k₂, .atom "open", fs₂]) (.cons (.tuple #[.integer k₁, .atom "open", fs₁]) .nil)) S =
            .ok (.atom "true"))
        (line₂ : ∀ S, SeenOk S → Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer k₁, .atom "open", fs₁]) (.cons (.tuple #[.integer k₂, .atom "open", fs₂]) .nil)) S =
            .ok (.atom "true")) :
        ∃ u, Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k₁, .atom "open", fs₁])
            (.tuple #[.integer k₂, .atom "open", fs₂]) = .ok u ∧
          CoveredVal d (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) u := by
      have l₁ : IsLeaf (.tuple #[.integer k₁, .atom "open", fs₁]) := ⟨_, _, _, rfl⟩
      have l₂ : IsLeaf (.tuple #[.integer k₂, .atom "open", fs₂]) := ⟨_, _, _, rfl⟩
      have cover : ∀ h lo hi kl kh (fl fh : Term), lo = .tuple #[.integer kl, .atom "open", fl] →
          hi = .tuple #[.integer kh, .atom "open", fh] → Term.compare lo hi = .lt →
          (∀ S, SeenOk S → Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") .nil
            (.cons hi (.cons lo .nil)) S = .ok (.atom "true")) →
          CoveredVal d (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil])
            (.tuple #[.integer h, lo, .atom "bdd_top", hi, .atom "bdd_bot"]) := by
        intro h lo hi kl kh fl fh elo ehi lt line
        obtain ⟨h₁, h₂, neg⟩ := neg_union_leaves (by rw [elo]; exact ⟨_, _, _, rfl⟩) (by rw [ehi]; exact ⟨_, _, _, rfl⟩) lt h
        refine ⟨.tuple #[.integer h₁, lo, .atom "bdd_bot", .atom "bdd_bot",
          .tuple #[.integer h₂, hi, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]], ?_, Or.inr (Or.inr ?_)⟩
        · simp only [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«map_difference/2»
          simp [neg]
        · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
          subst elo ehi
          exact map_empty_of d _ h₁ _ _ _ _ rfl fun S ok => bdd_two d h₁ h₂ kl kh fl fh S (line S ok)
      rcases cmp : Term.compare (.tuple #[.integer k₁, .atom "open", fs₁]) (.tuple #[.integer k₂, .atom "open", fs₂])
      · obtain ⟨h, run⟩ := union_two_leaves l₁ l₂ cmp
        exact ⟨_, run, cover h _ _ k₁ k₂ fs₁ fs₂ rfl rfl cmp line₁⟩
      · exact absurd cmp hne
      · obtain ⟨h, run⟩ := union_two_leaves_gt l₁ l₂ cmp
        exact ⟨_, run, cover h _ _ k₂ k₁ fs₂ fs₁ rfl rfl (Std.OrientedCmp.gt_iff_lt.mp cmp) line₂⟩

    theorem bits_le {M : List (Term × Term)} (basic : Basic M) : bits M ≤ 255 := by
      simp only [bits]
      cases h : mapLookup M (.atom "bitmap") with
      | none => simp
      | some w => obtain ⟨b, rfl, -, le⟩ := basic.bitmap w h; simp; omega

    /-- Basic types without bits, atoms, or top fields have no fields. -/
    theorem basic_empty {M : List (Term × Term)} (basic : Basic M) (noBits : bits M = 0)
        (noAtoms : ∀ q, amem M q = Bool.false) (noTops : ∀ name, name ≠ "bitmap" → name ≠ "atom" → has M name = Bool.false) :
        M = [] := by
      apply nil_of_lookup_none
      intro q
      cases h : mapLookup M q with
      | none => rfl
      | some w =>
        obtain ⟨name, rfl⟩ := basic.atomKey h
        by_cases b : name = "bitmap"
        · subst b
          obtain ⟨n, rfl, n₁, -⟩ := basic.bitmap w h
          simp [bits, h] at noBits; omega
        by_cases a : name = "atom"
        · subst a
          obtain ⟨-, q', hq⟩ := basic.atom w h
          rw [noAtoms q'] at hq; cases hq
        · have := noTops name b a
          simp [has, h] at this

    theorem ne_nil_of_has {M : List (Term × Term)} {name : String} (h : has M name = Bool.true) : M ≠ [] := by
      rintro rfl; simp [has, mapLookup] at h

    theorem ne_nil_of_bits {M : List (Term × Term)} (h : bits M ≠ 0) : M ≠ [] := by
      rintro rfl; simp [bits, mapLookup] at h

    theorem ne_nil_of_amem {M : List (Term × Term)} {q : Term} (h : amem M q = Bool.true) : M ≠ [] := by
      rintro rfl; simp [amem, amemV, mapLookup] at h

    /-- Non-empty basic types without top fields have bits or atoms. -/
    theorem basic_witness {M : List (Term × Term)} (basic : Basic M)
        (noTops : ∀ name, name ≠ "bitmap" → name ≠ "atom" → has M name = Bool.false) (nonempty : M ≠ []) :
        bits M ≠ 0 ∨ ∃ q, amem M q = Bool.true := by
      by_cases b : bits M = 0
      · right
        exact Classical.byContradiction fun none => nonempty (basic_empty basic b
          (fun q => Bool.eq_false_iff.mpr fun h => none ⟨q, h⟩) noTops)
      · exact Or.inl b

    theorem band_255 {b : Nat} (le : b ≤ 255) : 255 &&& b = b := by
      rw [Nat.and_comm]
      have := Nat.and_two_pow_sub_one_eq_mod b 8
      simp at this
      omega

    theorem strategy_end (d : Dispatcher) (status : Term) :
        Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d .nil .nil (.atom "open") (.atom "open") status =
          .ok status := by
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      simp [Lynx.Except.guard, Erlang.erlang.«==/2», Lynx.Except.andAlso]
      split <;> (try split) <;> simp_all

    theorem strategy_one (d : Dispatcher) (key f₁ f₂ : Term) (ne : ¬exactCompare f₂ f₁ = .eq)
        (ns : key ≠ .atom "__struct__") :
        Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d (Term.list [.tuple #[key, f₁]])
          (Term.list [.tuple #[key, f₂]]) (.atom "open") (.atom "open") (.atom "all_equal") =
          .ok (.tuple #[.atom "one_key_difference", key, f₁, f₂]) := by
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      simp [Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», Erlang.erlang.«=:=/2», ne,
        Erlang.erlang.«/=/2», Erlang.erlang.«==/2», Lynx.Except.andAlso, ns, strategy_end]

    theorem strategy_struct (d : Dispatcher) (f₁ f₂ : Term) (ne : ¬exactCompare f₂ f₁ = .eq) (b₁₂ b₂₁ : Bool)
        (fs₁₂ : Elixir.Module.Types.Descr.«field_subtype?/2» d f₁ f₂ = .ok (boolAtom b₁₂))
        (fs₂₁ : b₁₂ = Bool.false → Elixir.Module.Types.Descr.«field_subtype?/2» d f₂ f₁ = .ok (boolAtom b₂₁)) :
        Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d (Term.list [.tuple #[.atom "__struct__", f₁]])
          (Term.list [.tuple #[.atom "__struct__", f₂]]) (.atom "open") (.atom "open") (.atom "all_equal") =
          .ok (if b₁₂ then .atom "left_subtype_of_right" else if b₂₁ then .atom "right_subtype_of_left"
            else .atom "none") := by
      rw [Elixir.Module.Types.Descr.«opt_map_union_strategy/5».eq_def]
      simp [Term.list, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», Erlang.erlang.«=:=/2», ne,
        Erlang.erlang.«/=/2», Erlang.erlang.«==/2», Lynx.Except.andAlso, strategy_end]
      cases b₁₂ <;> simp [fs₁₂, boolAtom, Lynx.Except.andAlso, strategy_end]
      cases b₂₁ <;> simp [fs₂₁ rfl, boolAtom, Lynx.Except.andAlso, strategy_end]

    theorem opt_map_union_none (d : Dispatcher) (k₁ k₂ : Int) (key f₁ f₂ : Term)
        (strategy : Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d (Term.list [.tuple #[key, f₁]])
          (Term.list [.tuple #[key, f₂]]) (.atom "open") (.atom "open") (.atom "all_equal") = .ok (.atom "none")) :
        Elixir.Module.Types.Descr.«opt_map_union/3» d (.tuple #[.integer k₁, .atom "open", fieldsTerm [(key, f₁)]])
          (.tuple #[.integer k₂, .atom "open", fieldsTerm [(key, f₂)]]) (.map []) =
        Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k₁, .atom "open", fieldsTerm [(key, f₁)]])
          (.tuple #[.integer k₂, .atom "open", fieldsTerm [(key, f₂)]]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      simp [fieldsTerm, Term.list, Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup,
        Erlang.maps.«put/3»]
      unfold Elixir.Module.Types.Descr.«opt_map_union/5»
      simp only [fieldsTerm, Term.list, List.map] at strategy
      simp [Lynx.Except.guard, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, strategy]

    theorem opt_map_union_left (d : Dispatcher) (k₁ k₂ : Int) (key f₁ f₂ : Term)
        (strategy : Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d (Term.list [.tuple #[key, f₁]])
          (Term.list [.tuple #[key, f₂]]) (.atom "open") (.atom "open") (.atom "all_equal") =
            .ok (.atom "left_subtype_of_right")) :
        Elixir.Module.Types.Descr.«opt_map_union/3» d (.tuple #[.integer k₁, .atom "open", fieldsTerm [(key, f₁)]])
          (.tuple #[.integer k₂, .atom "open", fieldsTerm [(key, f₂)]]) (.map []) =
        Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "open") (Term.list [.tuple #[key, f₂]]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      simp [fieldsTerm, Term.list, Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup,
        Erlang.maps.«put/3»]
      unfold Elixir.Module.Types.Descr.«opt_map_union/5»
      simp only [fieldsTerm, Term.list, List.map] at strategy
      simp [Lynx.Except.guard, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, strategy]

    theorem opt_map_union_fuse (d : Dispatcher) (k₁ k₂ : Int) (key f₁ f₂ F : Term)
        (strategy : Elixir.Module.Types.Descr.«opt_map_union_strategy/5» d (Term.list [.tuple #[key, f₁]])
          (Term.list [.tuple #[key, f₂]]) (.atom "open") (.atom "open") (.atom "all_equal") =
            .ok (.tuple #[.atom "one_key_difference", key, f₁, f₂]))
        (field : Elixir.Module.Types.Descr.«field_opt_union/3» d f₁ f₂
          (.map [(.tuple #[.atom "map_union", .tuple #[.integer k₁, .atom "open", fieldsTerm [(key, f₁)]],
            .tuple #[.integer k₂, .atom "open", fieldsTerm [(key, f₂)]]], .atom "true")]) = .ok F) :
        Elixir.Module.Types.Descr.«opt_map_union/3» d (.tuple #[.integer k₁, .atom "open", fieldsTerm [(key, f₁)]])
          (.tuple #[.integer k₂, .atom "open", fieldsTerm [(key, f₂)]]) (.map []) =
        Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "open") (Term.list [.tuple #[key, F]]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      simp [fieldsTerm, Term.list, Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup,
        Erlang.maps.«put/3»]
      unfold Elixir.Module.Types.Descr.«opt_map_union/5»
      simp only [fieldsTerm, Term.list, List.map] at strategy
      simp only [fieldsTerm, Term.list, List.map] at field
      simp [Lynx.Except.guard, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, strategy, field]
      rw [Erlang.orddict.«store/3».eq_def]
      simp [Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2»]

    /-- What an optimized field type and its optimized negation unite into covers the field of the top type. -/
    def OptKeyOk (dn du dc : Dispatcher) (sD sU q t x : Term) : Prop :=
      ∃ w, Elixir.Module.Types.Descr.«opt_difference/4» dn q t x sD = .ok w ∧
        (kept (q, w) = Bool.false → CoveredVal dc q t x) ∧
        (kept (q, w) = Bool.true → ∃ u, Elixir.Module.Types.Descr.«opt_union/4» du q x w sU = .ok u ∧ CoveredVal dc q t u)

    theorem KeyOk.opt {dn du dc : Dispatcher} {sD sU q t x : Term} (k : KeyOk dn du dc q t x)
        (hd : Elixir.Module.Types.Descr.«opt_difference/4» dn q t x sD = Elixir.Module.Types.Descr.«bare_difference/3» dn q t x)
        (hu : ∀ w, Elixir.Module.Types.Descr.«bare_difference/3» dn q t x = .ok w → kept (q, w) = Bool.true →
          Elixir.Module.Types.Descr.«opt_union/4» du q x w sU = Elixir.Module.Types.Descr.«bare_union/3» du q x w) :
        OptKeyOk dn du dc sD sU q t x := by
      obtain ⟨w, run, drop, keep⟩ := k
      exact ⟨w, by rw [hd, run], drop, fun kw => by rw [hu w run kw]; exact keep kw⟩


    /-- Single field open maps against their optimized negations, given how each side covers maps. -/
    theorem one_key_step (n : Nat) (du dc : Dispatcher) (k : Int) (key v D' : Term) (o e : Bool)
        (hD : Elixir.Module.Types.Descr.«opt_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 5))
          (.atom "term") v (.map [(.tuple #[.atom "map_difference", .tuple #[.integer 61102469, .atom "open", .nil],
            .tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]], .atom "true")]) = .ok D')
        (he : Elixir.Module.Types.Descr.«empty?/1» (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) D' =
          .ok (boolAtom e))
        (drop : o = Bool.true ∧ e = Bool.true → CoveredVal dc (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]))
        (keep : ¬(o = Bool.true ∧ e = Bool.true) → ∀ kd : Int, ∃ u,
          Elixir.Module.Types.Descr.«opt_map_union/3» du
            (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]])
            (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[D', boolAtom !o])]]) (.map []) = .ok u ∧
          CoveredVal dc (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) u) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) du dc (.map []) (.map []) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]) := by
      obtain ⟨kd, leaf⟩ := leaf_new_open key (.tuple #[D', boolAtom !o])
      have run : Elixir.Module.Types.Descr.«opt_map_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 5))
          (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[v, boolAtom o])]]) (.map []) =
          if o = Bool.true ∧ e = Bool.true then .ok (.atom "bdd_bot")
          else .ok (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[D', boolAtom !o])]]) := by
        simp only [fieldsTerm, List.map, Term.list] at leaf hD ⊢
        unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
        cases o <;> simp [boolAtom] at leaf hD <;>
          simp [Elixir.Module.Types.Descr.«opt_bdd_seen/4», getMapKeys_single, mapLookup,
          Erlang.maps.«put/3», Elixir.Module.Types.Descr.«map_key_tag_to_field/1»,
          Elixir.Module.Types.Descr.«field_opt_difference/3», hD, Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom,
          Elixir.Module.Types.Descr.«field_empty?/1», he, leaf, Lynx.Except.guard, Term.list]
        all_goals cases e <;> simp_all [Lynx.Except.guard, boolAtom]
      by_cases dropped : o = Bool.true ∧ e = Bool.true
      · refine ⟨.atom "bdd_bot", ?_, fun _ => drop dropped, fun k => by simp [kept] at k⟩
        simp only [Elixir.Module.Types.Descr.«opt_difference/4»]
        rw [run]; simp only [dropped, and_self, ite_true]
      · obtain ⟨u, ru, cu⟩ := keep dropped kd
        refine ⟨.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[D', boolAtom !o])]], ?_,
          fun k => by simp [kept] at k, fun _ => ⟨u, ?_, cu⟩⟩
        · simp only [Elixir.Module.Types.Descr.«opt_difference/4», run, dropped, ite_false]
        · simp [Elixir.Module.Types.Descr.«opt_union/4», ru]

    /-- An open map minus two open maps of the same single field with opposite optionality. -/
    theorem line_pair (d : Dispatcher) (key vA vB nB M Z S : Term) (kA kB : Int) (oB : Bool)
        (hFB : Elixir.Module.Types.Descr.«field_empty_seen?/3» d vB (boolAtom oB) S = .ok (.atom "false"))
        (hN : Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") vB = .ok nB)
        (hFN : Elixir.Module.Types.Descr.«field_empty_seen?/3» d nB (boolAtom !oB) S = .ok (.atom "false"))
        (hM : Elixir.Module.Types.Descr.«bare_intersection/2» d nB vA = .ok M)
        (hFM : Elixir.Module.Types.Descr.«field_empty_seen?/3» d M (boolAtom !oB) S = .ok (.atom "false"))
        (hZ : Elixir.Module.Types.Descr.«bare_difference/2» d nB vA = .ok Z)
        (hFZ : Elixir.Module.Types.Descr.«empty_seen?/2» d Z S = .ok (.atom "true")) :
        Elixir.Module.Types.Descr.«map_line_empty?/4» d (.atom "open") .nil
          (.cons (.tuple #[.integer kB, .atom "open", fieldsTerm [(key, .tuple #[vB, boolAtom oB])]])
            (.cons (.tuple #[.integer kA, .atom "open", fieldsTerm [(key, .tuple #[vA, boolAtom !oB])]]) .nil)) S =
          .ok (.atom "true") := by
      refine line_first d key vB nB S _ kB oB hFB hN (Or.inr ⟨hFN, ?_⟩)
      refine line_meet d key nB vA S kA (!oB) (!oB) M Z hM (by simpa using hFM) hZ ?_
      cases oB <;> simpa [field_empty_required] using hFZ

    theorem empty_term (d : Dispatcher) (S : Term) :
        Elixir.Module.Types.Descr.«empty_seen?/2» d (.atom "term") S = .ok (.atom "false") := by
      unfold Elixir.Module.Types.Descr.«empty_seen?/2»; rfl

    theorem diff_term_term (d : Dispatcher) (x : Term) :
        Elixir.Module.Types.Descr.«bare_difference/2» d x (.atom "term") = .ok (.map []) := by
      unfold Elixir.Module.Types.Descr.«bare_difference/2»; rfl

    theorem diff_none (d : Dispatcher) (x : Term) :
        Elixir.Module.Types.Descr.«bare_difference/2» d x (.map []) = .ok x := by
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      cases x <;> simp [Erlang.erlang.«==/2»]

    theorem one_key_compare_ne (k₁ k₂ : Int) (key v₁ v₂ : Term) (o : Bool) :
        Term.compare (.tuple #[.integer k₁, .atom "open", fieldsTerm [(key, .tuple #[v₁, boolAtom o])]])
          (.tuple #[.integer k₂, .atom "open", fieldsTerm [(key, .tuple #[v₂, boolAtom !o])]]) ≠ .eq := by
      intro e
      simp [compare_tuple, compare_cons, List.compareLex_cons_cons, Ordering.then_eq_eq, fieldsTerm, Term.list] at e
      cases o <;> simp [boolAtom] at e

    theorem basic_nil : Basic [] := basic_of (fun q h => by simp [mapLookup] at h) fun name w h => by simp [mapLookup] at h

    theorem inter_none (depth : Nat) :
        Elixir.Module.Types.Descr.«bare_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
          (.map []) (.map []) = .ok (.map []) := by
      obtain ⟨C, run, bC, bitsC, amemC, hasC⟩ := inter_basic depth [] [] basic_nil basic_nil
      rw [run, basic_empty bC (by rw [bitsC]; simp [bits, mapLookup]) (fun q => by rw [amemC]; simp [amem, amemV, mapLookup])
        (fun name b a => by rw [hasC name b a]; simp [has, mapLookup])]

    theorem term_ne_nil {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) :
        T ≠ [] := by
      obtain ⟨-, bitsT, -, -⟩ := term_basic term
      rintro rfl
      simp [bits, mapLookup] at bitsT

    theorem term_not_none (d : Dispatcher) :
        Elixir.Module.Types.Descr.«subtype?/2» d (.atom "term") (.map []) = .ok (.atom "false") := by
      obtain ⟨T, term, -⟩ := unfolded_term_fields
      exact subtype_false d _ T [] (term_basic term).1 basic_nil (Or.inr ⟨rfl, term⟩) (term_ne_nil term)
        ⟨by simp [bits, mapLookup], fun q => by simp [amem, amemV, mapLookup], fun name _ _ => by simp [has, mapLookup]⟩

    theorem opt_union_term_left (d : Dispatcher) (x S : Term) :
        Elixir.Module.Types.Descr.«opt_union/3» d (.atom "term") x S = .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«opt_union/3»; rfl

    theorem opt_union_term_right (d : Dispatcher) (S : Term) :
        Elixir.Module.Types.Descr.«opt_union/3» d (.map []) (.atom "term") S = .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«opt_union/3»; rfl

    theorem field_union_term (d : Dispatcher) (v₁ v₂ S : Term) (o₁ o₂ : Bool)
        (union : Elixir.Module.Types.Descr.«opt_union/3» d v₁ v₂ S = .ok (.atom "term")) :
        Elixir.Module.Types.Descr.«field_opt_union/3» d (.tuple #[v₁, boolAtom o₁]) (.tuple #[v₂, boolAtom o₂]) S =
          .ok (.tuple #[.atom "term", boolAtom (o₁ || o₂)]) := by
      simp [Elixir.Module.Types.Descr.«field_opt_union/3», union]
      cases o₁ <;> cases o₂ <;> simp [boolAtom, Erlang.erlang.«or/2»]

    theorem tuple_exact_ne (a b c e : Term) (h : ¬exactCompare b e = .eq) :
        ¬exactCompare (.tuple #[a, b]) (.tuple #[c, e]) = .eq := by
      intro x
      rw [exactCompare_tuple] at x
      simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at x
      exact h x.2.1

    /-- Open maps of a single field of type `term()`. -/
    theorem key_term (n j c : Nat) (k : Int) (key : Term) (o : Bool) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) (Dispatcher.ofTable Erlang.program.fun_table (j + 1))
          (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.map []) (.map []) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.atom "term", boolAtom o])]]) := by
      have dc := Dispatcher.ofTable Erlang.program.fun_table (c + 2)
      refine one_key_step n _ _ k key (.atom "term") (.map []) o Bool.true (difference_term_term _ _ _)
        (by simpa [boolAtom, Elixir.Module.Types.Descr.«empty?/1», Term.true] using empty_none _) ?_ ?_
      · rintro ⟨rfl, -⟩
        exact one_key_cover _ k key (.atom "term") (.map []) (diff_term_term _ _) fun S _ => empty_none_seen _ S
      intro keep kd
      have o0 : o = Bool.false := by cases o <;> simp_all
      subst o0
      have ne : ¬exactCompare (.tuple #[.map [], boolAtom (!Bool.false)]) (.tuple #[.atom "term", boolAtom Bool.false]) = .eq :=
        tuple_exact_ne _ _ _ _ (by simp [boolAtom])
      by_cases ns : key = .atom "__struct__"
      · subst ns
        have strategy := strategy_struct (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) _ _ ne Bool.false Bool.false
          (field_subtype_long _ _ _ _ _ (Or.inl rfl) _ (by simpa [boolAtom] using term_not_none _))
          (fun _ => field_subtype_short _ _ _)
        simp only [ite_false, Bool.false_eq_true] at strategy
        have line₁ : ∀ S, SeenOk S → _ := fun S _ => by
          have := line_pair (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.atom "__struct__") (.atom "term")
            (.map []) (.atom "term") (.atom "term") (.map []) S k kd Bool.true (field_empty_optional _ _ _)
            (diff_none _ _) (by simpa [field_empty_required] using empty_term _ S) (inter_term_left _ _)
            (by simpa [field_empty_required] using empty_term _ S) (diff_term_term _ _) (empty_none_seen _ S)
          simpa using this
        have line₂ : ∀ S, SeenOk S → _ := fun S _ => by
          have := line_pair (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.atom "__struct__") (.map [])
            (.atom "term") (.map []) (.map []) (.map []) S kd k Bool.false
            (by simpa [field_empty_required] using empty_term _ S) (diff_term_term _ _) (field_empty_optional _ _ _)
            (inter_none _) (field_empty_optional _ _ _) (diff_none _ _) (empty_none_seen _ S)
          simpa using this
        obtain ⟨u, run, cover⟩ := two_cover (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) k kd _ _
          (one_key_compare_ne k kd _ _ _ Bool.false) line₁ line₂
        exact ⟨u, by rw [opt_map_union_none _ _ _ _ _ _ strategy]; exact run, cover⟩
      · have strategy := strategy_one (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) key _ _ ne ns
        obtain ⟨kd', leaf⟩ := leaf_new_open key (.tuple #[.atom "term", boolAtom Bool.true])
        refine ⟨_, ?_, one_key_cover _ kd' key (.atom "term") (.map []) (diff_term_term _ _)
          fun S _ => empty_none_seen _ S⟩
        rw [opt_map_union_fuse _ _ _ _ _ _ _ strategy (by
          simpa using field_union_term _ _ _ _ Bool.false Bool.true (opt_union_term_left _ _ _))]
        simpa [fieldsTerm] using leaf

    theorem empty_term_top (d : Dispatcher) :
        Elixir.Module.Types.Descr.«empty?/1» d (.atom "term") = .ok (boolAtom Bool.false) := by
      simp [Elixir.Module.Types.Descr.«empty?/1», boolAtom]

    /-- Open maps of a single field of type `none()`. -/
    theorem key_none (n j c : Nat) (k : Int) (key : Term) (o : Bool) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) (Dispatcher.ofTable Erlang.program.fun_table (j + 1))
          (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.map []) (.map []) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map [], boolAtom o])]]) := by
      refine one_key_step n _ _ k key (.map []) (.atom "term") o Bool.false (difference_term_none _ _)
        (empty_term_top _) (fun h => by simp at h) ?_
      intro _ kd
      have ne : ¬exactCompare (.tuple #[.atom "term", boolAtom !o]) (.tuple #[.map [], boolAtom o]) = .eq :=
        tuple_exact_ne _ _ _ _ (by cases o <;> simp [boolAtom])
      have line₁ : ∀ S, SeenOk S → _ := fun S _ => by
        have := line_pair (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) key (.map [])
          (.atom "term") (.map []) (.map []) (.map []) S k kd Bool.false
          (by simpa [field_empty_required] using empty_term _ S) (diff_term_term _ _) (field_empty_optional _ _ _)
          (inter_none _) (field_empty_optional _ _ _) (diff_none _ _) (empty_none_seen _ S)
        simpa using this
      have line₂ : ∀ S, SeenOk S → _ := fun S _ => by
        have := line_pair (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) key (.atom "term")
          (.map []) (.atom "term") (.atom "term") (.map []) S kd k Bool.true (field_empty_optional _ _ _)
          (diff_none _ _) (by simpa [field_empty_required] using empty_term _ S) (inter_term_left _ _)
          (by simpa [field_empty_required] using empty_term _ S) (diff_term_term _ _) (empty_none_seen _ S)
        simpa using this
      have fused : ∀ (strategy : Elixir.Module.Types.Descr.«opt_map_union_strategy/5»
          (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) (Term.list [.tuple #[key, .tuple #[.map [], boolAtom o]]])
          (Term.list [.tuple #[key, .tuple #[.atom "term", boolAtom !o]]]) (.atom "open") (.atom "open")
          (.atom "all_equal") = .ok (.tuple #[.atom "one_key_difference", key, .tuple #[.map [], boolAtom o],
            .tuple #[.atom "term", boolAtom !o]])), ∃ u, Elixir.Module.Types.Descr.«opt_map_union/3»
            (Dispatcher.ofTable Erlang.program.fun_table (j + 1))
            (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map [], boolAtom o])]])
            (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[.atom "term", boolAtom !o])]]) (.map []) = .ok u ∧
          CoveredVal (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.atom "map")
            (.tuple #[.integer 61102469, .atom "open", .nil]) u := fun strategy => by
        obtain ⟨kd', leaf⟩ := leaf_new_open key (.tuple #[.atom "term", boolAtom Bool.true])
        refine ⟨_, ?_, one_key_cover (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) kd' key (.atom "term")
          (.map []) (diff_term_term _ _) fun S _ => empty_none_seen _ S⟩
        rw [opt_map_union_fuse _ _ _ _ _ _ _ strategy (by
          simpa using field_union_term _ _ _ _ o (!o) (opt_union_term_right _ _))]
        simpa [fieldsTerm] using leaf
      by_cases ns : key = .atom "__struct__"
      · subst ns
        cases o
        · have strategy := strategy_struct (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) _ _ ne Bool.true Bool.false
            (field_subtype_long _ _ _ _ _ (Or.inl rfl) _ (by simpa [boolAtom] using none_subtype_term _))
            (fun h => by simp at h)
          simp only [ite_true] at strategy
          obtain ⟨kd', leaf⟩ := leaf_new_open (.atom "__struct__") (.tuple #[.atom "term", boolAtom Bool.true])
          refine ⟨_, ?_, one_key_cover (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) kd' (.atom "__struct__")
            (.atom "term") (.map []) (diff_term_term _ _) fun S _ => empty_none_seen _ S⟩
          rw [opt_map_union_left _ _ _ _ _ _ strategy]
          simpa [fieldsTerm] using leaf
        · have strategy := strategy_struct (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) _ _ ne Bool.false Bool.false
            (field_subtype_short _ _ _)
            (fun _ => field_subtype_long _ _ _ _ _ (Or.inl rfl) _ (by simpa [boolAtom] using term_not_none _))
          simp only [ite_false, Bool.false_eq_true] at strategy
          obtain ⟨u, run, cover⟩ := two_cover (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) k kd _ _
            (one_key_compare_ne k kd _ _ _ Bool.true) (by simpa using line₁) (by simpa using line₂)
          exact ⟨u, by rw [opt_map_union_none _ _ _ _ _ _ strategy]; exact run, cover⟩
      · exact fused (strategy_one _ key _ _ ne ns)

    theorem field_empty_nonempty (d : Dispatcher) {M : List (Term × Term)} (basic : Basic M) (nonempty : M ≠ [])
        (o : Bool) {S : Term} (ok : SeenOk S) :
        Elixir.Module.Types.Descr.«field_empty_seen?/3» d (.map M) (boolAtom o) S = .ok (.atom "false") := by
      cases o
      · rw [field_empty_required]; exact empty_basic d basic ok nonempty
      · exact field_empty_optional d _ S

    theorem field_union_of (d : Dispatcher) (v₁ v₂ S r : Term) (o₁ o₂ : Bool)
        (union : Elixir.Module.Types.Descr.«opt_union/3» d v₁ v₂ S = .ok r) :
        Elixir.Module.Types.Descr.«field_opt_union/3» d (.tuple #[v₁, boolAtom o₁]) (.tuple #[v₂, boolAtom o₂]) S =
          .ok (.tuple #[r, boolAtom (o₁ || o₂)]) := by
      simp [Elixir.Module.Types.Descr.«field_opt_union/3», union]
      cases o₁ <;> cases o₂ <;> simp [boolAtom, Erlang.erlang.«or/2»]

    theorem empty_basic_top (d : Dispatcher) {M : List (Term × Term)} (basic : Basic M) (nonempty : M ≠ []) :
        Elixir.Module.Types.Descr.«empty?/1» d (.map M) = .ok (boolAtom Bool.false) := by
      simpa [Elixir.Module.Types.Descr.«empty?/1», boolAtom] using empty_basic d basic seenOk_nil nonempty

    theorem has_fun_ne {M : List (Term × Term)} (h : has M "fun" = Bool.true) : M ≠ [] := ne_nil_of_has h

    theorem compl_disjoint {b : Nat} (le : b ≤ 255) : b &&& (255 - (255 &&& b)) = 0 := by
      rw [band_255 le]
      exact Nat.eq_of_testBit_eq fun i => by
        rw [← band_255 le]; simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
        cases b.testBit i <;> simp

    theorem compl_union {b : Nat} (le : b ≤ 255) : b ||| (255 - (255 &&& b)) = 255 := by
      rw [← add_eq_or b _ (compl_disjoint le), band_255 le]; omega

    theorem compl_compl {b : Nat} (le : b ≤ 255) : 255 - (255 &&& (255 - (255 &&& b))) = b := by
      rw [band_255 le, band_255 (by omega : 255 - b ≤ 255)]; omega

    theorem basic_compl_ne {V : List (Term × Term)} (bV : Basic V)
        (noTops : ∀ name, name ≠ "bitmap" → name ≠ "atom" → has V name = Bool.false) (nonempty : V ≠ [])
        {P : List (Term × Term)} (bits_eq : bits P = bits V) (amem_eq : ∀ q, amem P q = amem V q) : P ≠ [] := by
      rcases basic_witness bV noTops nonempty with b | ⟨q, hq⟩
      · exact ne_nil_of_bits (by rw [bits_eq]; exact b)
      · exact ne_nil_of_amem (q := q) (by rw [amem_eq]; exact hq)

    /-- Open maps of a single field of a non-empty type of bitmaps and atoms. -/
    theorem key_valid (n j c : Nat) (k : Int) (key : Term) (o : Bool) (V : List (Term × Term)) (bV : Basic V)
        (noTopsV : ∀ name, name ≠ "bitmap" → name ≠ "atom" → has V name = Bool.false) (nonempty : V ≠ []) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) (Dispatcher.ofTable Erlang.program.fun_table (j + 1))
          (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.map []) (.map []) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil])
          (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map V, boolAtom o])]]) := by
      obtain ⟨D, hD, bD, bitsD, amemD, hasD⟩ := opt_negation_basic (n + 2) V
        (.map [(.tuple #[.atom "map_difference", .tuple #[.integer 61102469, .atom "open", .nil],
          .tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map V, boolAtom o])]]], .atom "true")])
        bV noTopsV nonempty
      have neD : D ≠ [] := has_fun_ne (by rw [hasD "fun" (by decide) (by decide)]; rfl)
      refine one_key_step n _ _ k key (.map V) (.map D) o Bool.false hD (empty_basic_top _ bD neD)
        (fun h => by simp at h) ?_
      intro _ kd
      obtain ⟨T, term, -⟩ := unfolded_term_fields
      obtain ⟨bT, bitsT, amemT, hasT⟩ := term_basic term
      have le := bits_le bV
      have disjVD : Disjoint V D := ⟨by rw [bitsD]; exact compl_disjoint le,
        fun q => by rw [amemD]; cases amem V q <;> rfl, fun name b a => by rw [noTopsV name b a]; rfl⟩
      have disjDV : Disjoint D V := ⟨by rw [Nat.and_comm]; exact disjVD.1,
        fun q => by rw [Bool.and_comm]; exact disjVD.2.1 q, fun name b a => by rw [Bool.and_comm]; exact disjVD.2.2 name b a⟩
      have ne : ¬exactCompare (.tuple #[.map D, boolAtom !o]) (.tuple #[.map V, boolAtom o]) = .eq :=
        tuple_exact_ne _ _ _ _ (by cases o <;> simp [boolAtom])
      have line₁ : ∀ S, SeenOk S → Elixir.Module.Types.Descr.«map_line_empty?/4»
          (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.atom "open") .nil
          (.cons (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[.map D, boolAtom !o])]]) (.cons (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map V, boolAtom o])]]) .nil)) S = .ok (.atom "true") := fun S ok => by
        obtain ⟨P, hP, bP, bitsP, amemP, hasP⟩ := diff_basic c (.atom "term") T D bT bD (Or.inr ⟨rfl, neD, term⟩)
        have bitsP' : bits P = bits V := by rw [bitsP, bitsT, bitsD, compl_compl le]
        have amemP' : ∀ q, amem P q = amem V q := fun q => by rw [amemP, amemT, amemD]; simp
        have neP := basic_compl_ne bV noTopsV nonempty bitsP' amemP'
        obtain ⟨M, hM, bM, bitsM, amemM, hasM⟩ := inter_basic (c + 1) P V bP bV
        have neM := basic_compl_ne bV noTopsV nonempty (by rw [bitsM, bitsP', Nat.and_self])
          (fun q => by rw [amemM, amemP']; simp)
        obtain ⟨Z, hZ, bZ, bitsZ, amemZ, hasZ⟩ := diff_basic c (.map P) P V bP bV (Or.inl rfl)
        have nilZ : Z = [] := basic_empty bZ (by rw [bitsZ, bitsP', Nat.and_self]; omega)
          (fun q => by rw [amemZ, amemP']; simp) (fun name b a => by
            rw [hasZ name b a, hasP name b a, hasT name b a, hasD name b a]; cases (topValue name).isSome <;> rfl)
        subst nilZ
        have := line_pair (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) key (.map V) (.map D) (.map P) (.map M)
          (.map []) S k kd (!o) (field_empty_nonempty _ bD neD _ ok) hP (field_empty_nonempty _ bP neP _ ok) hM
          (field_empty_nonempty _ bM neM _ ok) hZ (empty_none_seen _ S)
        simpa using this
      have line₂ : ∀ S, SeenOk S → Elixir.Module.Types.Descr.«map_line_empty?/4»
          (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.atom "open") .nil
          (.cons (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map V, boolAtom o])]]) (.cons (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[.map D, boolAtom !o])]]) .nil)) S = .ok (.atom "true") := fun S ok => by
        obtain ⟨N, hN, bN, bitsN, amemN, hasN⟩ := diff_basic c (.atom "term") T V bT bV (Or.inr ⟨rfl, nonempty, term⟩)
        have hasNfun : has N "fun" = Bool.true := by
          rw [hasN "fun" (by decide) (by decide), hasT "fun" (by decide) (by decide), noTopsV "fun" (by decide) (by decide)]
          rfl
        obtain ⟨M, hM, bM, bitsM, amemM, hasM⟩ := inter_basic (c + 1) N D bN bD
        have hasMfun : has M "fun" = Bool.true := by
          rw [hasM "fun" (by decide) (by decide), hasNfun, hasD "fun" (by decide) (by decide)]; rfl
        obtain ⟨Z, hZ, bZ, bitsZ, amemZ, hasZ⟩ := diff_basic c (.map N) N D bN bD (Or.inl rfl)
        have nilZ : Z = [] := basic_empty bZ (by rw [bitsZ, bitsN, bitsD, bitsT, Nat.and_self]; omega)
          (fun q => by rw [amemZ, amemN, amemD, amemT]; simp) (fun name b a => by
            rw [hasZ name b a, hasN name b a, hasT name b a, hasD name b a, noTopsV name b a]
            cases (topValue name).isSome <;> rfl)
        subst nilZ
        have := line_pair (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) key (.map D) (.map V) (.map N) (.map M)
          (.map []) S kd k o (field_empty_nonempty _ bV nonempty _ ok) hN
          (field_empty_nonempty _ bN (has_fun_ne hasNfun) _ ok) hM (field_empty_nonempty _ bM (has_fun_ne hasMfun) _ ok)
          hZ (empty_none_seen _ S)
        simpa using this
      have none : Elixir.Module.Types.Descr.«opt_map_union_strategy/5» (Dispatcher.ofTable Erlang.program.fun_table (j + 1))
          (Term.list [.tuple #[key, .tuple #[.map V, boolAtom o]]]) (Term.list [.tuple #[key, .tuple #[.map D, boolAtom !o]]])
          (.atom "open") (.atom "open") (.atom "all_equal") = .ok (.atom "none") →
          ∃ u, Elixir.Module.Types.Descr.«opt_map_union/3» (Dispatcher.ofTable Erlang.program.fun_table (j + 1))
            (.tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map V, boolAtom o])]])
            (.tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[.map D, boolAtom !o])]]) (.map []) = .ok u ∧
          CoveredVal (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.atom "map")
            (.tuple #[.integer 61102469, .atom "open", .nil]) u := fun strategy => by
        obtain ⟨u, run, cover⟩ := two_cover (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) k kd _ _
          (one_key_compare_ne k kd _ _ _ o) line₁ line₂
        exact ⟨u, by rw [opt_map_union_none _ _ _ _ _ _ strategy]; exact run, cover⟩
      by_cases ns : key = .atom "__struct__"
      · subst ns
        cases o
        · exact none (by
            have := strategy_struct (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) _ _ ne Bool.false Bool.false
              (field_subtype_long _ _ _ _ _ (Or.inl rfl) _
                (by simpa [boolAtom] using subtype_false _ _ V D bV bD (Or.inl rfl) nonempty disjVD))
              (fun _ => field_subtype_short _ _ _)
            simpa using this)
        · exact none (by
            have := strategy_struct (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) _ _ ne Bool.false Bool.false
              (field_subtype_short _ _ _)
              (fun _ => field_subtype_long _ _ _ _ _ (Or.inl rfl) _
                (by simpa [boolAtom] using subtype_false _ _ D V bD bV (Or.inl rfl) neD disjDV))
            simpa using this)
      · have strategy := strategy_one (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) key _ _ ne ns
        obtain ⟨U, hU, bU, bitsU, amemU, hasU⟩ := union_basic j V D
          (.map [(.tuple #[.atom "map_union", .tuple #[.integer k, .atom "open", fieldsTerm [(key, .tuple #[.map V, boolAtom o])]],
            .tuple #[.integer kd, .atom "open", fieldsTerm [(key, .tuple #[.map D, boolAtom !o])]]], .atom "true")])
          bV bD noTopsV
        have hasUfun : has U "fun" = Bool.true := by
          rw [hasU "fun" (by decide) (by decide), hasD "fun" (by decide) (by decide)]; rfl
        obtain ⟨C, hC, bC, bitsC, amemC, hasC⟩ := diff_basic c (.atom "term") T U bT bU
          (Or.inr ⟨rfl, has_fun_ne hasUfun, term⟩)
        have nilC : C = [] := basic_empty bC (by rw [bitsC, bitsT, bitsU, bitsD, compl_union le]; rfl)
          (fun q => by rw [amemC, amemT, amemU, amemD]; cases amem V q <;> rfl)
          (fun name b a => by rw [hasC name b a, hasT name b a, hasU name b a, hasD name b a]; cases (topValue name).isSome <;> rfl)
        subst nilC
        obtain ⟨kd', leaf⟩ := leaf_new_open key (.tuple #[.map U, boolAtom Bool.true])
        refine ⟨_, ?_, one_key_cover (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) kd' key (.map U) (.map []) hC
          fun S _ => empty_none_seen _ S⟩
        rw [opt_map_union_fuse _ _ _ _ _ _ _ strategy (by
          have := field_union_of (Dispatcher.ofTable Erlang.program.fun_table (j + 1)) _ _ _ _ o (!o) hU
          simpa using this)]
        simpa [fieldsTerm] using leaf

    /-- Optimized map types of a single open field against their optimized negations. -/
    theorem opt_map_key_one (n j c : Nat) (x : Term) (field : MapField x) (one : OneKey x) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table (n + 5)) (Dispatcher.ofTable Erlang.program.fun_table (j + 1))
          (Dispatcher.ofTable Erlang.program.fun_table (c + 2)) (.map []) (.map []) (.atom "map")
          (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      obtain ⟨k, key, w, rfl⟩ := one
      have fw : FieldValueV w := by
        rcases field with ⟨k', e⟩ | wx
        · simp [fieldsTerm, Term.list] at e
        · obtain ⟨⟨k', tag, l, e, -, fields⟩, -⟩ := Bdd.leaf_iff.mp wx
          simp at e
          obtain ⟨-, -, hl⟩ := e
          rcases l with _ | ⟨⟨key', w'⟩, _ | ⟨_, _⟩⟩ <;> simp [fieldsTerm, Term.list] at hl
          obtain ⟨-, rfl⟩ := hl
          exact fields (key', w) (by simp)
      obtain ⟨v, o, rfl, fv⟩ := fw
      rcases fv with rfl | ⟨V, rfl, valid⟩
      · exact key_term n j c k key o
      by_cases empty : V = []
      · subst empty; exact key_none n j c k key o
      obtain ⟨bV, noTops⟩ := valid.basic
      exact key_valid n j c k key o V bV noTops empty

    /-- A leaf united with its negation is not fused, as the negation is not a chain of unions. -/
    theorem opt_tuple_union_neg_leaf (d : Dispatcher) (k : Int) (a b : Term) (h : Int) :
        Elixir.Module.Types.Descr.«opt_tuple_union/2» d (.tuple #[.integer k, a, b])
          (.tuple #[.integer h, .tuple #[.integer k, a, b], .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) =
          Elixir.Module.Types.Descr.«tuple_union/2»
            (.tuple #[.integer h, .tuple #[.integer k, a, b], .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"])
            (.tuple #[.integer k, a, b]) := by
      simp only [Elixir.Module.Types.Descr.«opt_tuple_union/2»]
      rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
      simp [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3»]

    /-- Nodes are united with what is not a leaf without fusion. -/
    theorem opt_tuple_union_node (d : Dispatcher) (h lit c u e w : Term) (nw : ∀ k a b, w ≠ .tuple #[k, a, b]) :
        Elixir.Module.Types.Descr.«opt_tuple_union/2» d (.tuple #[h, lit, c, u, e]) w =
          Elixir.Module.Types.Descr.«tuple_union/2» (.tuple #[h, lit, c, u, e]) w := by
      unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
      split
      · rename_i heq; simp at heq
      · rename_i heq; simp at heq
      · exact (nw _ _ _ rfl).elim
      · rfl

    theorem opt_tuple_union_special (d : Dispatcher) (k H : Int) :
        Elixir.Module.Types.Descr.«opt_tuple_union/2» d (.tuple #[.integer k, .atom "closed", Term.list []])
          (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) =
          Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k, .atom "closed", Term.list []])
            (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) := by
      simp [Elixir.Module.Types.Descr.«opt_tuple_union/2», Elixir.Module.Types.Descr.«opt_tuple_union_literal/2»,
        Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4», Erlang.erlang.«length/1», Lynx.Except.guard,
        Erlang.erlang.«==/2», Erlang.erlang.«=:=/2», Erlang.erlang.«=</2», Erlang.erlang.«>=/2», Erlang.erlang.«and/2»]
      have : (Ord.compare (0 : Int) 1).isGE = Bool.false := by decide
      simp [this]

    theorem opt_tuple_key (n m : Nat) (du : Dispatcher) (sD sU x : Term) (field : TupleField x) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table (n + 1)) du (Dispatcher.ofTable Erlang.program.fun_table (m + 2))
          sD sU (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      have hd : Elixir.Module.Types.Descr.«opt_difference/4» (Dispatcher.ofTable Erlang.program.fun_table (n + 1))
          (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil]) x sD =
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 1))
            (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
        simp [Elixir.Module.Types.Descr.«opt_difference/4», Elixir.Module.Types.Descr.«bare_difference/3»,
          opt_tuple_difference_top n x field]
      have k := tuple_key (Dispatcher.ofTable Erlang.program.fun_table (n + 1)) du m x field
      have same : ∀ w, Elixir.Module.Types.Descr.«opt_tuple_union/2» du x w = Elixir.Module.Types.Descr.«tuple_union/2» x w →
          Elixir.Module.Types.Descr.«opt_union/4» du (.atom "tuple") x w sU =
            Elixir.Module.Types.Descr.«bare_union/3» du (.atom "tuple") x w := by
        intro w e
        simp [Elixir.Module.Types.Descr.«opt_union/4», Elixir.Module.Types.Descr.«bare_union/3», e]
      rcases field with ⟨k', rfl⟩ | wx
      · exact k.opt hd fun w run kw => by
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»] at run
          subst run; simp [kept] at kw
      have notTop := not_top_of_ok wx fun t h => h.2
      rcases wx.shape with rfl | rfl | ⟨k', tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · exact k.opt hd fun w run kw => by
          simp [Elixir.Module.Types.Descr.«bare_difference/3»] at run
          unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
          simp [diff_leaf_top] at run
          subst run; simp [kept] at kw
      · exact k.opt hd fun w run kw => same w (by
          unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
          split <;> first | rfl | (rename_i heq; simp at heq))
      · obtain ⟨⟨k'', tag, ls, e, -, -⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
        simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        by_cases special : tag = "closed" ∧ ls = []
        · obtain ⟨rfl, rfl⟩ := special
          refine k.opt hd fun w run kw => same w ?_
          obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
          simp [Elixir.Module.Types.Descr.«bare_difference/3»] at run
          unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
          simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
            Elixir.Module.Types.Descr.«bdd_leaf_key/2», Lynx.Except.guard, Erlang.erlang.«is_list/1»,
            Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»] at run
          subst run
          rw [opt_tuple_union_special, tuple_union_bdd notTop (by intro k e; simp at e)]
        · have notSpecial : ∀ k₁, Term.tuple #[.integer k', .atom tag, Term.list ls] ≠
              .tuple #[k₁, .atom "closed", .nil] := by
            intro k₁ e
            simp at e
            apply special
            refine ⟨e.2.1, ?_⟩
            cases ls <;> simp_all [Term.list]
          have leaf : IsLeaf (.tuple #[.integer k', .atom tag, Term.list ls]) := ⟨_, _, _, rfl⟩
          obtain ⟨h, node⟩ := node_new (.tuple #[.integer k', .atom tag, Term.list ls]) (.atom "bdd_bot") (.atom "bdd_bot")
            (.atom "bdd_top") leaf (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
          let w : Term := .tuple #[.integer h, .tuple #[.integer k', .atom tag, Term.list ls], .atom "bdd_bot",
            .atom "bdd_bot", .atom "bdd_top"]
          have neg : Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer k', .atom tag, Term.list ls]) = .ok w := by
            unfold Elixir.Module.Types.Descr.«bdd_negation/1»
            simpa using node
          obtain ⟨w', neg', keep, sem⟩ := neg_ok wx
          rw [neg] at neg'
          cases neg'
          have ww := keep _ wx
          have run : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil])
              (.tuple #[.integer k', .atom tag, Term.list ls]) = .ok w := by
            unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            split
            · next _ _ e =>
              exfalso
              simp at e
              obtain ⟨-, rfl, hl⟩ := e
              exact notTopX ⟨_, by rw [hl]⟩
            · next _ _ e => exact (notSpecial _ e).elim
            · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact neg
            · next h₁ => exact (h₁ _ _ rfl rfl).elim
          obtain ⟨u, runU, keepU, semU⟩ := union_ok ww wx
          refine ⟨w, ?_, fun kw => by simp [kept, w] at kw, fun _ => ⟨u, ?_, tuple_taut m (keepU _ ww wx) fun ρ resp => ?_⟩⟩
          · simp [Elixir.Module.Types.Descr.«opt_difference/4», opt_tuple_difference_top n _ (Or.inr wx), run]
          · simp only [Elixir.Module.Types.Descr.«opt_union/4», w, opt_tuple_union_neg_leaf]
            rw [tuple_union_bdd (by intro k e; simp at e) notTop]
            exact runU
          · rw [semU ρ resp, sem ρ resp]; cases eval ρ (.tuple #[.integer k', .atom tag, Term.list ls]) <;> rfl
      · obtain ⟨w', neg, -, -, leafless⟩ := neg_okN wx
        exact k.opt hd fun w run kw => same w (by
          simp [Elixir.Module.Types.Descr.«bare_difference/3»] at run
          unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
          simp [neg] at run
          subst run
          exact opt_tuple_union_node du _ _ _ _ _ _ fun k a b e => by subst e; exact NoLeaf.leaf leafless)

    theorem opt_map_union_fallback (d : Dispatcher) (x w s : Term)
        (h : (∀ k a b, x ≠ .tuple #[k, a, b]) ∨ (∀ k a b, w ≠ .tuple #[k, a, b])) :
        Elixir.Module.Types.Descr.«opt_map_union/3» d x w s = Elixir.Module.Types.Descr.«map_union/2» x w := by
      unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      split
      · rcases h with h | h
        · exact (h _ _ _ rfl).elim
        · exact (h _ _ _ rfl).elim
      · rfl

    /-- Map types other than open maps of one field unite with their optimized negations as plain ones. -/
    theorem opt_map_key_plain (n m : Nat) (du : Dispatcher) (sU x : Term) (field : MapField x) (notOne : ¬OneKey x) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) du (Dispatcher.ofTable Erlang.program.fun_table (m + 3))
          (.map []) sU (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
      have hd : Elixir.Module.Types.Descr.«opt_difference/4» (Dispatcher.ofTable Erlang.program.fun_table (n + 2))
          (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) x (.map []) =
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table (n + 2))
            (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
        simp [Elixir.Module.Types.Descr.«opt_difference/4», Elixir.Module.Types.Descr.«bare_difference/3»,
          opt_map_difference_eq n x field notOne]
      have same : ∀ w, ((∀ k a b, x ≠ .tuple #[k, a, b]) ∨ (∀ k a b, w ≠ .tuple #[k, a, b])) →
          Elixir.Module.Types.Descr.«opt_union/4» du (.atom "map") x w sU =
            Elixir.Module.Types.Descr.«bare_union/3» du (.atom "map") x w := by
        intro w h
        simp [Elixir.Module.Types.Descr.«opt_union/4», Elixir.Module.Types.Descr.«bare_union/3»,
          opt_map_union_fallback du x w sU h]
      refine (map_key (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) du m x field).opt hd fun w run kw => same w ?_
      rcases field with ⟨k', rfl⟩ | wx
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»] at run
        subst run; simp [kept] at kw
      rcases wx.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · left; intro k a b e; cases e
      · left; intro k a b e; cases e
      · right
        have notTop := not_top_of_ok wx fun t h => h.2
        obtain ⟨w', neg, -, -, leafless⟩ := neg_okN wx
        simp [Elixir.Module.Types.Descr.«bare_difference/3»] at run
        unfold Elixir.Module.Types.Descr.«map_difference/2» at run
        split at run
        · next _ _ e => exact (notTop _ e).elim
        · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq
          rw [neg] at run; cases run
          intro k a b e; subst e; exact NoLeaf.leaf leafless
        · next h₁ => exact (h₁ _ _ rfl rfl).elim
      · left; intro k a b e; simp at e

    /-- Bitmaps, atoms, functions, and lists are united and negated by the plain operations. -/
    theorem opt_key_simple {dn du dc : Dispatcher} {sD sU q t x : Term} (k : KeyOk dn du dc q t x)
        (key : q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
          (q = .atom "list" ∧ ∃ h : Int, t = .tuple #[.integer h, .atom "term", .atom "term"])) :
        OptKeyOk dn du dc sD sU q t x := by
      refine k.opt ?_ fun w _ _ => ?_
      · rcases key with rfl | rfl | rfl | ⟨rfl, h, rfl⟩ <;>
          simp [Elixir.Module.Types.Descr.«opt_difference/4», Elixir.Module.Types.Descr.«bare_difference/3»,
            opt_list_difference_top]
      · rcases key with rfl | rfl | rfl | ⟨rfl, -⟩ <;>
          simp [Elixir.Module.Types.Descr.«opt_union/4», Elixir.Module.Types.Descr.«bare_union/3»]

    /-- Each field of the top type is covered by what an optimized type and its negation unite into. -/
    theorem opt_key_ok (X : List (Term × Term)) (valid : Negatable X) {T : List (Term × Term)}
        (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) {q t x : Term}
        (hT : mapLookup T q = some t) (hX : mapLookup X q = some x) :
        OptKeyOk (Dispatcher.ofTable Erlang.program.fun_table 98) (Dispatcher.ofTable Erlang.program.fun_table 99)
          (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) (.map []) q t x := by
      have k := key_ok X valid term hT hX
      rcases term_keys term hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact opt_key_simple k (Or.inl rfl)
      · exact opt_key_simple k (Or.inr (Or.inl rfl))
      · exact opt_key_simple k (Or.inr (Or.inr (Or.inl rfl)))
      · exact opt_key_simple k (Or.inr (Or.inr (Or.inr ⟨rfl, _, rfl⟩)))
      · exact opt_tuple_key 97 98 _ _ _ x (valid.tuples x hX)
      · by_cases one : OneKey x
        · exact opt_map_key_one 93 98 98 x (valid.maps x hX) one
        · exact opt_map_key_plain 96 97 _ _ x (valid.maps x hX) one

    /-- An optimized type united with its optimized negation covers the top type. -/
    theorem opt_union_negation_covers (X : List (Term × Term)) (valid : Negatable X) (nonempty : X ≠ []) :
        ∃ N U, Elixir.Module.Types.Descr.«opt_negation/1» (Dispatcher.ofTable Erlang.program.fun_table 100) (.map X) =
            .ok (.map N) ∧
          Elixir.Module.Types.Descr.«opt_union/2» (Dispatcher.ofTable Erlang.program.fun_table 100) (.map X) (.map N) =
            .ok (.map U) ∧
          Elixir.Module.Types.Descr.«subtype?/2» (Dispatcher.ofTable Erlang.program.fun_table 100) (.atom "term")
            (.map U) = .ok (.atom "true") := by
      obtain ⟨T, term, -⟩ := unfolded_term_fields
      have termMap : mapLookup T (.atom "map") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        simp [mapLookup]
      obtain ⟨N, negation, staticN, -, -, -, -, -, -, -, lookups⟩ := opt_negation_fields 97 X valid nonempty (.map [])
        (fun _ _ => True) (fun x hX => by
          obtain ⟨w, run, -⟩ := opt_key_ok X valid term termMap hX
          exact ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_difference/4»] using run, fun _ => trivial⟩)
      have inT : ∀ q x, mapLookup X q = some x → ∃ t, mapLookup T q = some t := by
        intro q x hX
        have := term
        simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
        cases this
        rcases valid.keys q (by simp [hX]) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mapLookup]
      obtain ⟨U, union, lookU, -⟩ := opt_union_lookup 99 X N (.map []) valid.static staticN (by
        intro q x y hX hN
        obtain ⟨t, hT⟩ := inT q x hX
        obtain ⟨name, rfl⟩ := atom_key_of term hT
        obtain ⟨w, run, -, keep⟩ := opt_key_ok X valid term hT hX
        have look := (lookups T term name t hT).2 x w hX run
        rw [hN] at look
        by_cases k : kept (.atom name, w) = Bool.true
        · simp only [k, ite_true, Option.some.injEq] at look
          obtain ⟨u, ru, -⟩ := keep k
          exact ⟨u, look ▸ ru⟩
        · simp [k] at look)
      refine ⟨N, U, ?_, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using union,
        subtype_term _ T U term ?_ fun e member => ?_⟩
      · rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
        simpa [Elixir.Module.Types.Descr.«opt_difference/2»] using negation
      · rw [(lookU "dynamic").1 staticN]
        exact valid.static
      have hT := mapLookup_of_mem_mapEntries member
      obtain ⟨name, key⟩ := atom_key_of term hT
      rw [key] at hT ⊢
      cases hX : mapLookup X (.atom name) with
      | none =>
        have hN := (lookups T term name e.2 hT).1 hX
        obtain ⟨w, run, empty⟩ := key_absent term hT
        exact ⟨e.2, w, (lookU name).2.1 _ hN hX, run, empty⟩
      | some x =>
        obtain ⟨w, run, drop, keep⟩ := opt_key_ok X valid term hT hX
        have look := (lookups T term name e.2 hT).2 x w hX run
        by_cases k : kept (.atom name, w) = Bool.true
        · obtain ⟨u, ru, w', rw', empty⟩ := keep k
          simp only [k, ite_true] at look
          exact ⟨u, w', (lookU name).2.2 x w u hX look ru, rw', empty⟩
        · simp only [k, Bool.false_eq_true, ite_false] at look
          obtain ⟨w', rw', empty⟩ := drop (by simpa using k)
          exact ⟨x, w', by rw [(lookU name).1 look, hX], rw', empty⟩

    end Elixir.STTDescrProofsTest
    """

    # De Morgan's law for the plain operations. Each field denotes a propositional predicate:
    # bitmaps their bits, atoms their members, functions their BDDs per arity, and lists,
    # tuples, and maps their BDDs. Unions, intersections, and negations compute the
    # connectives, under valuations that some tuple realizes for tuple literals, since the
    # negation of `{}` is `{term, ...}`. A type whose fields hold no more than another's is
    # its subtype, since tuple lines that no realizable valuation satisfies are empty.
    postlude ~LEAN"""
    namespace Elixir.STTDescrProofsTest
    open Lynx Lynx.Term BddProofs

    abbrev D (n : Nat) : Dispatcher := Dispatcher.ofTable Erlang.program.fun_table n

    /-- The general clause of `tuple_line_empty?/4`. -/
    theorem line_cons (d : Dispatcher) (tag : String) (l : List Term) (k : Int) (ntag : String) (nl rest : List Term)
        (S : Term) (notTop : ¬(ntag = "open" ∧ nl = [])) (notLast : ¬(tag = "open" ∧ ntag = "closed" ∧ rest = [])) :
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom tag) (Term.list l)
            (.cons (.tuple #[.integer k, .atom ntag, Term.list nl]) (Term.list rest)) S =
          if (tag = "closed" ∧ l.length < nl.length) ∨ (ntag = "closed" ∧ nl.length < l.length) then
            Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom tag) (Term.list l) (Term.list rest) S
          else Lynx.Except.andAlso
            (Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d .nil (.atom tag) (Term.list l) (Term.list nl)
              (Term.list rest) S)
            (Elixir.Module.Types.Descr.«tuple_empty_arity?/7» d (.integer l.length) (.integer nl.length) (.atom tag)
              (Term.list l) (.atom ntag) (Term.list rest) S) true := by
      rw [Elixir.Module.Types.Descr.«tuple_line_empty?/4».eq_def]
      have listNil : ∀ xs : List Term, Term.list xs = .nil ↔ xs = [] := by
        intro xs; cases xs <;> simp [Term.list]
      split
      · rename_i heq; simp at heq
      · rename_i heq
        simp [listNil] at heq
        exact absurd ⟨heq.1.2.1, heq.1.2.2⟩ notTop
      · rename_i htag heq
        simp [listNil] at heq htag
        exact absurd ⟨htag, heq.1.2.1, heq.2⟩ notLast
      · rename_i heq _
        simp at heq
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq
        simp [length_list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», Lynx.Except.orElse,
          Lynx.Except.andAlso]
        by_cases tc : tag = "closed" <;> by_cases nc : ntag = "closed" <;>
          rcases Nat.lt_trichotomy l.length nl.length with h | h | h <;>
          simp [tc, nc, h, Int.compare_eq_lt, Int.compare_eq_gt, Nat.lt_irrefl, Nat.lt_asymm, Lynx.Except.andAlso] <;>
          omega
      · rename_i h₄ _
        exact (h₄ _ _ _ _ rfl).elim

    theorem reverse_list (l t : List Term) :
        Erlang.lists.«reverse/2» (Term.list l) (Term.list t) = .ok (Term.list (l.reverse ++ t)) := by
      induction l generalizing t with
      | nil => simp [Term.list, Erlang.lists.«reverse/2»]
      | cons h rest ih =>
        have := ih (h :: t)
        simp [Term.list, Erlang.lists.«reverse/2»] at this ⊢
        exact this

    theorem reverse_tail (l : List Term) (t : Term) :
        Erlang.lists.«reverse/2» (Term.list l) t = .ok (l.foldl (fun a x => .cons x a) t) := by
      induction l generalizing t with
      | nil => simp [Term.list, Erlang.lists.«reverse/2»]
      | cons h rest ih =>
        have := ih (.cons h t)
        simp [Term.list, Erlang.lists.«reverse/2»] at this ⊢
        exact this

    theorem list_reverse_append (l t : List Term) :
        Term.list (l.reverse ++ t) = l.foldl (fun a x => .cons x a) (Term.list t) := by
      induction l generalizing t with
      | nil => simp
      | cons h rest ih => simp [ih (h :: t), Term.list]

    theorem elements_done (d : Dispatcher) (acc tag l rest S : Term) :
        Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d acc tag l .nil rest S = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]
      rfl

    /-- One step of `tuple_elements_empty?/6`, which checks the element `ty` against the negated element `nt`. -/
    theorem elements_step (d : Dispatcher) (acc : List Term) (tag : Term) (l : List Term) (nt : Term)
        (nl : List Term) (rest S ty : Term) (es : List Term)
        (hl : (l = [] ∧ ty = .atom "term" ∧ es = []) ∨ l = ty :: es) (meet : Term)
        (hmeet : Elixir.Module.Types.Descr.«bare_intersection/2» d ty nt = .ok meet) :
        (Elixir.Module.Types.Descr.«empty_seen?/2» d meet S = .ok (.atom "true") →
          Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list acc) tag (Term.list l) (.cons nt (Term.list nl))
            rest S = Elixir.Module.Types.Descr.«tuple_line_empty?/4» d tag (Term.list (acc.reverse ++ ty :: es)) rest S) ∧
        (∀ diff, Elixir.Module.Types.Descr.«empty_seen?/2» d meet S = .ok (.atom "false") →
          Elixir.Module.Types.Descr.«bare_difference/2» d ty nt = .ok diff →
          (Elixir.Module.Types.Descr.«empty_seen?/2» d diff S = .ok (.atom "true") →
            Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list acc) tag (Term.list l)
              (.cons nt (Term.list nl)) rest S =
            Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list (ty :: acc)) tag (Term.list es)
              (Term.list nl) rest S) ∧
          (Elixir.Module.Types.Descr.«empty_seen?/2» d diff S = .ok (.atom "false") →
            Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list acc) tag (Term.list l)
              (.cons nt (Term.list nl)) rest S =
            Lynx.Except.andAlso
              (Elixir.Module.Types.Descr.«tuple_line_empty?/4» d tag (Term.list (acc.reverse ++ diff :: es)) rest S)
              (Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list (meet :: acc)) tag (Term.list es)
                (Term.list nl) rest S) true)) := by
      refine ⟨fun empty => ?_, fun diff full hdiff => ⟨fun emptyD => ?_, fun fullD => ?_⟩⟩ <;>
        rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def] <;>
        rcases hl with ⟨rfl, rfl, rfl⟩ | rfl
      all_goals simp [Term.list, hmeet, Lynx.Except.guard, isMember, reverse_tail, list_reverse_append, *]

    theorem dup_list (x : Term) : ∀ (n : Nat) (t : List Term),
        Erlang.lists.«duplicate/3» (.integer n) x (Term.list t) = .ok (Term.list (List.replicate n x ++ t)) := by
      intro n
      induction n with
      | zero => intro t; rw [Erlang.lists.«duplicate/3».eq_def]; simp
      | succ n ih =>
        intro t
        rw [Erlang.lists.«duplicate/3».eq_def]
        have := ih (x :: t)
        simp only [Term.list] at this
        split
        · rename_i h; simp at h; omega
        · simp [this, List.replicate_succ', List.append_assoc]

    theorem dup_nat (x : Term) (n : Nat) :
        Erlang.lists.«duplicate/2» (.integer n) x = .ok (Term.list (List.replicate n x)) := by
      have := dup_list x n []
      simp only [List.append_nil, Term.list] at this
      simp [Erlang.lists.«duplicate/2», Lynx.Except.guard, Erlang.erlang.«>=/2», Erlang.erlang.«and/2», this,
        Int.isGE_compare]

    theorem append_list (a b : List Term) : Erlang.erlang.«++/2» (Term.list a) (Term.list b) = .ok (Term.list (a ++ b)) := by
      induction a with
      | nil => simp [Term.list, Erlang.erlang.«++/2»]
      | cons h t ih => simp [Term.list, Erlang.erlang.«++/2»] at ih ⊢; simp [ih]

    theorem fill_list (l : List Term) (k : Nat) (h : l.length ≤ k) :
        Elixir.Module.Types.Descr.«tuple_fill/2» (Term.list l) (.integer k) =
          .ok (Term.list (l ++ List.replicate (k - l.length) (.atom "term"))) := by
      have pad : ((k : Int) - (l.length : Int)) = ((k - l.length : Nat) : Int) := by omega
      have nonneg : ¬((k - l.length : Nat) : Int) < 0 := by omega
      simp [Elixir.Module.Types.Descr.«tuple_fill/2», length_list, pad, nonneg, dup_nat, append_list]

    /-- `tuple_empty_sizes?/5` checks the closed tuples of each size from `i` below `m`. -/
    theorem sizes_all (d : Dispatcher) (l : List Term) (m : Nat) (rest S : Term)
        (lines : ∀ i, l.length ≤ i → i < m → Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed")
          (Term.list (l ++ List.replicate (i - l.length) (.atom "term"))) rest S = .ok (.atom "true")) :
        ∀ i, l.length ≤ i → Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer i) (.integer m)
          (Term.list l) rest S = .ok (.atom "true") := by
      intro i le
      induction h : m - i generalizing i with
      | zero =>
        rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
        have : ¬(i : Int) < m := by omega
        simp [Lynx.Except.guard, Int.compare_eq_lt, this]
      | succ k ih =>
        rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
        have lt : (i : Int) < m := by omega
        have next := ih (i + 1) (by omega) (by omega)
        simp only [Int.natCast_add, Int.natCast_one] at next
        simp [Lynx.Except.guard, Int.compare_eq_lt, lt, fill_list l i le, lines i le (by omega), Lynx.Except.andAlso, next]

    /-- `tuple_empty_arity?/7` holds for closed lines, or when the sizes and the larger open tuples are empty. -/
    theorem arity_true (d : Dispatcher) (n m : Nat) (tag : String) (l : List Term) (ntag : String) (rest S : Term)
        (ok : tag = "closed" ∨ (Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer n) (.integer m)
          (Term.list l) rest S = .ok (.atom "true") ∧ (ntag = "open" ∨ (l.length ≤ m + 1 ∧
            Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open")
              (Term.list (l ++ List.replicate (m + 1 - l.length) (.atom "term"))) rest S = .ok (.atom "true"))))) :
        Elixir.Module.Types.Descr.«tuple_empty_arity?/7» d (.integer n) (.integer m) (.atom tag) (Term.list l)
          (.atom ntag) rest S = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«tuple_empty_arity?/7».eq_def]
      rcases ok with rfl | ⟨sizes, rfl | ⟨le, line⟩⟩
      · simp [Erlang.erlang.«==/2», Lynx.Except.orElse]
      · by_cases c : tag = "closed"
        · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c]
        · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, sizes, Lynx.Except.andAlso]
      · by_cases c : tag = "closed"
        · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c]
        · have fill := fill_list l (m + 1) le
          simp only [Int.natCast_add, Int.natCast_one] at fill
          by_cases o : ntag = "open"
          · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, sizes, Lynx.Except.andAlso, o]
          · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, sizes, Lynx.Except.andAlso, o, fill, line]

    /-- A negated top literal empties any line. -/
    theorem line_top (d : Dispatcher) (tag l : Term) (k : Int) (rest S : Term) :
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d tag l
          (.cons (.tuple #[.integer k, .atom "open", .nil]) rest) S = .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«tuple_line_empty?/4».eq_def]
      split <;> simp_all

    /-! Elements of tuple lines: the top type or basic types. -/

    def LElem (e : Term) : Prop := e = .atom "term" ∨ ∃ M, e = .map M ∧ Basic M

    theorem elem_lelem {e : Term} (h : ElemTerm e) : LElem e := by
      rcases h with rfl | ⟨X, rfl, valid⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, rfl, (Valid.basic valid).1⟩

    theorem lelem_full (d : Dispatcher) {e : Term} (h : LElem e) (full : e ≠ .map []) {S : Term} (ok : SeenOk S) :
        Elixir.Module.Types.Descr.«empty_seen?/2» d e S = .ok (.atom "false") := by
      rcases h with rfl | ⟨M, rfl, basic⟩
      · rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl
      · exact empty_basic d basic ok fun e => full (by rw [e])

    theorem inter_term_right (d : Dispatcher) (e : Term) :
        Elixir.Module.Types.Descr.«bare_intersection/2» d e (.atom "term") = .ok e := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»
      split <;> simp_all

    theorem diff_term_right (d : Dispatcher) (e : Term) :
        Elixir.Module.Types.Descr.«bare_difference/2» d e (.atom "term") = .ok (.map []) := by
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      rfl

    theorem lelem_inter (n : Nat) {a b : Term} (ha : LElem a) (hb : LElem b) :
        ∃ c, Elixir.Module.Types.Descr.«bare_intersection/2» (D (n + 2)) a b = .ok c ∧ LElem c := by
      rcases ha with rfl | ⟨A, rfl, bA⟩
      · exact ⟨b, by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl, hb⟩
      rcases hb with rfl | ⟨B, rfl, bB⟩
      · exact ⟨_, inter_term_right _ _, Or.inr ⟨A, rfl, bA⟩⟩
      obtain ⟨C, run, bC, -⟩ := inter_basic (n + 1) A B bA bB
      exact ⟨_, run, Or.inr ⟨C, rfl, bC⟩⟩

    theorem lelem_diff (n : Nat) {a b : Term} (ha : LElem a) (hb : LElem b) :
        ∃ c, Elixir.Module.Types.Descr.«bare_difference/2» (D (n + 2)) a b = .ok c ∧ LElem c := by
      rcases hb with rfl | ⟨B, rfl, bB⟩
      · exact ⟨_, diff_term_right _ _, Or.inr ⟨[], rfl, basic_nil⟩⟩
      by_cases empty : B = []
      · subst empty
        refine ⟨a, ?_, ha⟩
        unfold Elixir.Module.Types.Descr.«bare_difference/2»
        rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]
      rcases ha with rfl | ⟨A, rfl, bA⟩
      · obtain ⟨T, term, -⟩ := unfolded_term_fields
        obtain ⟨C, run, bC, -⟩ := diff_basic n (.atom "term") T B (term_basic term).1 bB (Or.inr ⟨rfl, empty, term⟩)
        exact ⟨_, run, Or.inr ⟨C, rfl, bC⟩⟩
      · obtain ⟨C, run, bC, -⟩ := diff_basic n (.map A) A B bA bB (Or.inl rfl)
        exact ⟨_, run, Or.inr ⟨C, rfl, bC⟩⟩

    /-! Tuple lines whose negations hold `{}` or `{term, ...}`. -/

    /-- The empty tuple literal `{}`. -/
    def IsE (t : Term) : Prop := ∃ k : Int, t = .tuple #[.integer k, .atom "closed", .nil]

    /-- The literal `{term, ...}` of tuples with at least one element. -/
    def IsH (t : Term) : Prop := ∃ k : Int, t = .tuple #[.integer k, .atom "open", Term.list [.atom "term"]]

    def Full (e : Term) : Prop := LElem e ∧ e ≠ .map []

    theorem andAlso_true : Lynx.Except.andAlso (.ok (.atom "true")) (.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      simp [Lynx.Except.andAlso]

    theorem list_cons (x : Term) (xs : List Term) : Term.list (x :: xs) = .cons x (Term.list xs) := rfl

    /-- `{}` minus the negations, which hold `{}`, is empty. -/
    theorem line_closed_empty (d : Dispatcher) (S : Term) : ∀ negs : List Term, (∀ t ∈ negs, TupleLit t) →
        (∃ t ∈ negs, IsE t) →
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed") (Term.list []) (Term.list negs) S =
          .ok (.atom "true") := by
      intro negs
      induction negs with
      | nil => intro _ ⟨t, m, _⟩; simp at m
      | cons N rest ih =>
        intro lits ⟨t, mt, et⟩
        obtain ⟨k, tag', nl, rfl, -, -⟩ := lits N List.mem_cons_self
        rw [list_cons]
        by_cases top : tag' = "open" ∧ nl = []
        · obtain ⟨rfl, rfl⟩ := top
          exact line_top d _ _ k _ S
        rw [line_cons d "closed" [] k tag' nl rest S top (by simp)]
        by_cases m0 : nl = []
        · subst m0
          simp only [List.length_nil, Nat.lt_irrefl, and_false, or_self, if_false]
          rw [elements_done, arity_true d 0 0 "closed" [] tag' (Term.list rest) S (Or.inl rfl)]
          exact andAlso_true
        · have pos : 0 < nl.length := List.length_pos_iff.mpr m0
          simp only [List.length_nil, pos, and_true, true_or, if_true]
          refine ih (fun t m => lits t (List.mem_cons_of_mem _ m)) ⟨t, ?_, et⟩
          rcases List.mem_cons.mp mt with rfl | m
          · obtain ⟨k', e⟩ := et
            simp at e
            exact absurd (by cases nl <;> simp_all [Term.list]) m0
          · exact m

    /-- Checking each element of a line against a negated literal produces lines of full elements. -/
    theorem elements_all (n : Nat) {S : Term} (seen : SeenOk S) (tag rest : Term)
        (lineOk : ∀ l, l ≠ [] → (∀ e ∈ l, Full e) →
          Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D (n + 2)) tag (Term.list l) rest S = .ok (.atom "true")) :
        ∀ nl : List Term, (∀ e ∈ nl, ElemTerm e) → ∀ acc l : List Term, (∀ e ∈ acc, Full e) → (∀ e ∈ l, Full e) →
          Elixir.Module.Types.Descr.«tuple_elements_empty?/6» (D (n + 2)) (Term.list acc) tag (Term.list l)
            (Term.list nl) rest S = .ok (.atom "true") := by
      intro nl
      induction nl with
      | nil => intro _ acc l _ _; exact elements_done _ _ _ _ _ _
      | cons nt nl ih =>
        intro hnl acc l hacc hl
        obtain ⟨ty, es, hshape, hty, hes⟩ : ∃ ty es, ((l = [] ∧ ty = .atom "term" ∧ es = []) ∨ l = ty :: es) ∧
            Full ty ∧ ∀ e ∈ es, Full e := by
          cases l with
          | nil => exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, ⟨Or.inl rfl, by simp⟩, by simp⟩
          | cons x xs => exact ⟨x, xs, Or.inr rfl, hl x List.mem_cons_self, fun e m => hl e (List.mem_cons_of_mem _ m)⟩
        have hnt := elem_lelem (hnl nt List.mem_cons_self)
        have hnl' : ∀ e ∈ nl, ElemTerm e := fun e m => hnl e (List.mem_cons_of_mem _ m)
        obtain ⟨meet, hmeet, lmeet⟩ := lelem_inter n hty.1 hnt
        have step := elements_step (D (n + 2)) acc tag l nt nl rest S ty es hshape meet hmeet
        rw [list_cons]
        have allRev : ∀ x, Full x → ∀ e ∈ acc.reverse ++ x :: es, Full e := by
          intro x hx e m
          simp only [List.mem_append, List.mem_reverse, List.mem_cons] at m
          rcases m with m | rfl | m
          · exact hacc e m
          · exact hx
          · exact hes e m
        by_cases emptyMeet : meet = .map []
        · subst emptyMeet
          rw [step.1 (empty_none_seen _ _)]
          exact lineOk _ (by simp) (allRev ty hty)
        · have fullMeet := lelem_full (D (n + 2)) lmeet emptyMeet seen
          obtain ⟨diff, hdiff, ldiff⟩ := lelem_diff n hty.1 hnt
          by_cases emptyDiff : diff = .map []
          · subst emptyDiff
            rw [(step.2 _ fullMeet hdiff).1 (empty_none_seen _ _)]
            exact ih hnl' (ty :: acc) es (fun e m => by
              rcases List.mem_cons.mp m with rfl | m
              · exact hty
              · exact hacc e m) hes
          · rw [(step.2 _ fullMeet hdiff).2 (lelem_full (D (n + 2)) ldiff emptyDiff seen),
              lineOk _ (by simp) (allRev diff ⟨ldiff, emptyDiff⟩),
              ih hnl' (meet :: acc) es (fun e m => by
                rcases List.mem_cons.mp m with rfl | m
                · exact ⟨lmeet, emptyMeet⟩
                · exact hacc e m) hes]
            exact andAlso_true

    theorem full_term : Full (.atom "term") := ⟨Or.inl rfl, by simp⟩

    theorem full_fill {l : List Term} (hl : ∀ e ∈ l, Full e) (k : Nat) :
        ∀ e ∈ l ++ List.replicate k (.atom "term"), Full e := by
      intro e m
      rcases List.mem_append.mp m with m | m
      · exact hl e m
      · rw [List.eq_of_mem_replicate m]; exact full_term

    /-- A line of at least one element minus negations that hold `{term, ...}` is empty. -/
    theorem line_full (n : Nat) {S : Term} (seen : SeenOk S) : ∀ negs : List Term, (∀ t ∈ negs, TupleLit t) →
        (∃ t ∈ negs, IsH t) → ∀ (tag : String) (l : List Term), l ≠ [] → (∀ e ∈ l, Full e) →
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D (n + 2)) (.atom tag) (Term.list l) (Term.list negs) S =
          .ok (.atom "true") := by
      intro negs
      induction negs with
      | nil => intro _ ⟨t, m, _⟩; simp at m
      | cons N rest ih =>
        intro lits ⟨t, mt, ht⟩ tag l ne hl
        obtain ⟨k, tag', nl, rfl, -, hnl⟩ := lits N List.mem_cons_self
        have lits' : ∀ t ∈ rest, TupleLit t := fun t m => lits t (List.mem_cons_of_mem _ m)
        rw [list_cons]
        by_cases top : tag' = "open" ∧ nl = []
        · obtain ⟨rfl, rfl⟩ := top
          exact line_top _ _ _ k _ S
        have pos : 0 < l.length := List.length_pos_iff.mpr ne
        by_cases isH : IsH (.tuple #[.integer k, .atom tag', Term.list nl])
        · obtain ⟨k', e⟩ := isH
          simp at e
          obtain ⟨_, htag, hlist⟩ := e
          have hnl : nl = [.atom "term"] := by
            cases nl with
            | nil => simp [Term.list] at hlist
            | cons x xs => cases xs <;> simp_all [Term.list]
          subst htag hnl
          rw [line_cons _ tag l k "open" [.atom "term"] rest S top (by simp)]
          have cond : ¬((tag = "closed" ∧ l.length < [Term.atom "term"].length) ∨
              ("open" = "closed" ∧ [Term.atom "term"].length < l.length)) := by
            rintro (⟨-, h⟩ | ⟨h, -⟩)
            · simp only [List.length_singleton] at h; omega
            · simp at h
          rw [ite_eq_right_of_eq_false _ _ (eq_false cond)]
          obtain ⟨ty, es, rfl⟩ : ∃ ty es, l = ty :: es := by cases l <;> simp_all
          have hty := hl ty List.mem_cons_self
          have step := elements_step (D (n + 2)) [] (.atom tag) (ty :: es) (.atom "term") [] (Term.list rest) S ty es
            (Or.inr rfl) ty (inter_term_right _ _)
          have step' := (step.2 _ (lelem_full _ hty.1 hty.2 seen) (diff_term_right _ _)).1 (empty_none_seen _ _)
          have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D (n + 2)) (.integer (ty :: es).length)
              (.integer [Term.atom "term"].length) (.atom tag) (Term.list (ty :: es)) (.atom "open") (Term.list rest) S =
              .ok (.atom "true") := by
            refine arity_true _ _ _ tag _ "open" _ S ?_
            by_cases c : tag = "closed"
            · exact Or.inl c
            · exact Or.inr ⟨sizes_all _ _ _ _ _ (fun i le lt => by simp at lt le; omega) _ (Nat.le_refl _), Or.inl rfl⟩
          simp only [Term.list] at step' arity ⊢
          rw [step', elements_done, arity]
          exact andAlso_true
        · have hrest : ∃ t ∈ rest, IsH t := by
            rcases List.mem_cons.mp mt with rfl | m
            · exact absurd ht isH
            · exact ⟨t, m, ht⟩
          have notLast : ¬(tag = "open" ∧ tag' = "closed" ∧ rest = []) := by
            rintro ⟨-, -, rfl⟩
            simp at hrest
          rw [line_cons _ tag l k tag' nl rest S top notLast]
          by_cases cond : (tag = "closed" ∧ l.length < nl.length) ∨ (tag' = "closed" ∧ nl.length < l.length)
          · rw [ite_eq_left_of_eq_true _ _ (eq_true cond)]
            exact ih lits' hrest tag l ne hl
          rw [ite_eq_right_of_eq_false _ _ (eq_false cond),
            elements_all n seen (.atom tag) (Term.list rest) (fun l' ne' hl' => ih lits' hrest tag l' ne' hl') nl hnl [] l
              (by simp) hl,
            arity_true _ _ _ tag _ tag' _ S ?_]
          · exact andAlso_true
          by_cases c : tag = "closed"
          · exact Or.inl c
          refine Or.inr ⟨sizes_all _ _ _ _ _ (fun i _ _ => ih lits' hrest "closed" _ (by simp [ne]) (full_fill hl _)) _
            (Nat.le_refl _), ?_⟩
          by_cases o : tag' = "open"
          · exact Or.inl o
          · have closed : tag' = "closed" := by
              rcases lits (.tuple #[.integer k, .atom tag', Term.list nl]) List.mem_cons_self with ⟨_, _, _, e, g, -⟩
              simp at e; obtain ⟨-, rfl, -⟩ := e; rcases g with g | g <;> simp_all
            refine Or.inr ⟨by simp [closed] at cond; omega, ih lits' hrest "open" _ (by simp [ne]) (full_fill hl _)⟩

    /-- Any line minus negations that hold both `{}` and `{term, ...}` is empty. -/
    theorem line_both (n : Nat) {S : Term} (seen : SeenOk S) (negs : List Term) (lits : ∀ t ∈ negs, TupleLit t)
        (hE : ∃ t ∈ negs, IsE t) (hH : ∃ t ∈ negs, IsH t) (tag : String) (htag : tag = "open" ∨ tag = "closed")
        (l : List Term) (hl : ∀ e ∈ l, Full e) :
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D (n + 2)) (.atom tag) (Term.list l) (Term.list negs) S =
          .ok (.atom "true") := by
      by_cases ne : l ≠ []
      · exact line_full n seen negs lits hH tag l ne hl
      simp only [ne_eq, Decidable.not_not] at ne
      subst ne
      rcases htag with rfl | rfl
      case inr => exact line_closed_empty _ S negs lits hE
      obtain ⟨N, rest, rfl⟩ : ∃ N rest, negs = N :: rest := by
        cases negs with
        | nil => obtain ⟨t, m, _⟩ := hE; simp at m
        | cons N rest => exact ⟨N, rest, rfl⟩
      obtain ⟨k, tag', nl, rfl, htag', hnl⟩ := lits _ List.mem_cons_self
      have lits' : ∀ t ∈ rest, TupleLit t := fun t m => lits t (List.mem_cons_of_mem _ m)
      rw [list_cons]
      by_cases top : tag' = "open" ∧ nl = []
      · obtain ⟨rfl, rfl⟩ := top
        exact line_top _ _ _ k _ S
      have notE : IsE (.tuple #[.integer k, .atom tag', Term.list nl]) → tag' = "closed" ∧ nl = [] := by
        rintro ⟨k', e⟩
        simp at e
        obtain ⟨-, rfl, e⟩ := e
        exact ⟨rfl, by cases nl <;> simp_all [Term.list]⟩
      have notH : IsH (.tuple #[.integer k, .atom tag', Term.list nl]) → tag' = "open" ∧ nl = [.atom "term"] := by
        rintro ⟨k', e⟩
        simp at e
        obtain ⟨-, rfl, e⟩ := e
        refine ⟨rfl, ?_⟩
        cases nl with
        | nil => simp [Term.list] at e
        | cons x xs => cases xs <;> simp_all [Term.list]
      have inRest : ∀ {P : Term → Prop}, (∃ t ∈ (.tuple #[.integer k, .atom tag', Term.list nl]) :: rest, P t) →
          ¬P (.tuple #[.integer k, .atom tag', Term.list nl]) → ∃ t ∈ rest, P t := by
        intro P ⟨t, m, ht⟩ np
        rcases List.mem_cons.mp m with rfl | m
        · exact absurd ht np
        · exact ⟨t, m, ht⟩
      have notLast : ¬("open" = "open" ∧ tag' = "closed" ∧ rest = []) := by
        rintro ⟨-, rfl, rfl⟩
        obtain ⟨t, m, ht⟩ := hH
        simp at m; subst m
        have := (notH ht).1; simp at this
      rw [line_cons _ "open" [] k tag' nl rest S top notLast,
        ite_eq_right_of_eq_false _ _ (eq_false (by simp))]
      have closedLines : (∃ t ∈ rest, IsE t) → (∃ t ∈ rest, IsH t) → ∀ i, ([] : List Term).length ≤ i → i < nl.length →
          Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D (n + 2)) (.atom "closed")
            (Term.list (([] : List Term) ++ List.replicate (i - ([] : List Term).length) (.atom "term"))) (Term.list rest) S =
              .ok (.atom "true") := by
        intro hE' hH' i _ _
        cases i with
        | zero => exact line_closed_empty _ S rest lits' hE'
        | succ i => exact line_full n seen rest lits' hH' "closed" _ (by simp) (full_fill (by simp) _)
      by_cases isH : IsH (.tuple #[.integer k, .atom tag', Term.list nl])
      · obtain ⟨rfl, rfl⟩ := notH isH
        have hE' := inRest hE fun e => by have := (notE e).1; simp at this
        have step := elements_step (D (n + 2)) [] (.atom "open") [] (.atom "term") [] (Term.list rest) S (.atom "term") []
          (Or.inl ⟨rfl, rfl, rfl⟩) (.atom "term") (inter_term_right _ _)
        have step' := (step.2 _ (lelem_full _ (Or.inl rfl) (by simp) seen) (diff_term_right _ _)).1 (empty_none_seen _ _)
        have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D (n + 2)) (.integer ([] : List Term).length)
            (.integer [Term.atom "term"].length) (.atom "open") (Term.list []) (.atom "open") (Term.list rest) S =
            .ok (.atom "true") :=
          arity_true _ _ _ _ _ _ _ S (Or.inr ⟨sizes_all _ _ _ _ _ (fun i _ lt => by
            cases i with
            | zero => exact line_closed_empty _ S rest lits' hE'
            | succ i => simp at lt) _ (Nat.le_refl _), Or.inl rfl⟩)
        simp only [Term.list] at step' arity ⊢
        rw [step', elements_done, arity]
        exact andAlso_true
      have hH' := inRest hH isH
      by_cases isE : IsE (.tuple #[.integer k, .atom tag', Term.list nl])
      · obtain ⟨rfl, rfl⟩ := notE isE
        have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D (n + 2)) (.integer ([] : List Term).length)
            (.integer ([] : List Term).length) (.atom "open") (Term.list []) (.atom "closed") (Term.list rest) S =
            .ok (.atom "true") :=
          arity_true _ _ _ _ _ _ _ S (Or.inr ⟨sizes_all _ _ _ _ _ (fun i _ lt => by simp at lt) _ (Nat.le_refl _),
            Or.inr ⟨by simp, line_full n seen rest lits' hH' "open" _ (by simp) (full_fill (by simp) _)⟩⟩)
        rw [elements_done, arity]
        exact andAlso_true
      have hE' := inRest hE isE
      rw [elements_all n seen (.atom "open") (Term.list rest) (fun l' ne' hl' => line_full n seen rest lits' hH' "open" l' ne' hl')
          nl hnl [] [] (by simp) (by simp),
        arity_true _ _ _ _ _ _ _ S (Or.inr ⟨sizes_all _ _ _ _ _ (closedLines hE' hH') _ (Nat.le_refl _), ?_⟩)]
      · exact andAlso_true
      by_cases o : tag' = "open"
      · exact Or.inl o
      · exact Or.inr ⟨by simp, line_full n seen rest lits' hH' "open" _ (by simp) (full_fill (by simp) _)⟩

    /-! Tuple BDDs that no realizable valuation satisfies are empty. -/

    theorem zip_len (depth : Nat) (l₁ : List Term) (h₁ : ∀ e ∈ l₁, ElemTerm e) :
        ∀ (l₂ : List Term), (∀ e ∈ l₂, ElemTerm e) → ∀ acc : List Term, (∀ e ∈ acc, ElemTerm e) →
        ∃ r : List Term, Elixir.Module.Types.Descr.«zip_intersection/4» (D (depth + 2)) (Term.list l₁) (Term.list l₂)
            (Term.list acc) (.function "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]) = .ok (Term.list r) ∧
          r.length = acc.length + max l₁.length l₂.length ∧ ∀ e ∈ r, ElemTerm e := by
      induction l₁ with
      | nil =>
        intro l₂ h₂ acc ha
        refine ⟨acc.reverse ++ l₂, ?_, by simp, fun e m => ?_⟩
        · unfold Elixir.Module.Types.Descr.«zip_intersection/4»
          exact reverse_list acc l₂
        · rcases List.mem_append.mp m with m | m
          · exact ha e (List.mem_reverse.mp m)
          · exact h₂ e m
      | cons x xs ih =>
        intro l₂ h₂ acc ha
        cases l₂ with
        | nil =>
          refine ⟨acc.reverse ++ x :: xs, ?_, by simp, fun e m => ?_⟩
          · unfold Elixir.Module.Types.Descr.«zip_intersection/4»
            exact reverse_list acc (x :: xs)
          · rcases List.mem_append.mp m with m | m
            · exact ha e (List.mem_reverse.mp m)
            · exact h₁ e m
        | cons y ys =>
          obtain ⟨e, run, he⟩ := elem_inter depth (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
          obtain ⟨r, runr, len, hr⟩ := ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys
            (fun e me => h₂ e (List.mem_cons_of_mem _ me)) (e :: acc) (fun e' me => by
              rcases List.mem_cons.mp me with rfl | me
              · exact he
              · exact ha e' me)
          refine ⟨r, ?_, by simp at len ⊢; omega, hr⟩
          unfold Elixir.Module.Types.Descr.«zip_intersection/4»
          simp [Term.list, run]
          exact runr

    def Disj (t₁ t₂ : String) (n₁ n₂ : Nat) : Prop :=
      (t₁ = "closed" ∧ t₂ = "closed" ∧ n₁ ≠ n₂) ∨ (t₁ = "closed" ∧ t₂ = "open" ∧ n₁ < n₂) ∨
        (t₁ = "open" ∧ t₂ = "closed" ∧ n₂ < n₁)

    theorem strategy_spec (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
        (n₁ n₂ : Nat) : ∃ v, Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» (.atom t₁) (.integer n₁) (.atom t₂)
          (.integer n₂) = .ok v ∧ (v = .atom "disjoint" ↔ Disj t₁ t₂ n₁ n₂) := by
      unfold Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> rcases Nat.lt_trichotomy n₁ n₂ with h | h | h <;>
        simp [Lynx.Except.guard, Erlang.erlang.«/=/2», Erlang.erlang.«==/2», Disj, h, Int.compare_eq_lt,
          Int.compare_eq_gt, Erlang.erlang.«>=/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», Int.isGE_compare] <;>
        first | omega | (have := Nat.le_of_lt h; have := Nat.not_lt.mpr (Nat.le_of_lt h); simp [*]) |
          (have : (n₁ : Int) ≠ n₂ := by omega
           have : n₁ ≠ n₂ := by omega
           simp [*])

    def IsE' (t : Term) : Prop := ∃ k, t = .tuple #[k, .atom "closed", .nil]
    def IsH' (t : Term) : Prop := ∃ k, t = .tuple #[k, .atom "open", Term.list [.atom "term"]]
    def Sized (t : Term) : Prop := ∃ k tag x xs, t = .tuple #[k, tag, .cons x xs]

    /-- Lines known to hold only `{}`. -/
    def PosE (pos : Term) : Prop := pos = .tuple #[.atom "closed", .nil]

    /-- Lines known to hold only tuples with elements. -/
    def PosH (pos : Term) : Prop := ∃ tag x xs, pos = .tuple #[tag, .cons x xs]

    theorem inter_facts (depth : Nat) {pos lit : Term} (hp : TuplePos pos) (hl : TupleOk lit) :
        Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D (depth + 2)) pos lit = .ok (.atom "empty") ∨
          ∃ pos', Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D (depth + 2)) pos lit = .ok pos' ∧
            TuplePos pos' ∧ (PosE pos → PosE pos') ∧ (PosH pos → PosH pos') ∧ (IsE' lit → PosE pos') ∧
            (Sized lit → PosH pos') := by
      obtain ⟨t₁, l₁, rfl, g₁, e₁⟩ := hp
      obtain ⟨⟨k, t₂, l₂, rfl, g₂, e₂⟩, -⟩ := hl
      obtain ⟨v, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
      obtain ⟨r, zip, len, hr⟩ := zip_len depth l₁ e₁ l₂ e₂ [] (by simp)
      simp only [List.length_nil, Nat.zero_add] at len
      unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
      simp only [length_list, Lynx.Except.ok_bind, hv]
      by_cases d : Disj t₁ t₂ l₁.length l₂.length
      · left
        rw [disj.mpr d]
        rfl
      right
      have nv : v ≠ .atom "disjoint" := fun e => d (disj.mp e)
      let tag : String := if t₁ = "open" ∧ t₂ = "open" then "open" else "closed"
      have hr' : ∀ e ∈ r, ElemTerm e := hr
      refine ⟨.tuple #[.atom tag, Term.list r], ?_, ⟨tag, r, rfl, by simp only [tag]; split <;> simp, hr'⟩, ?_⟩
      · split
        · exact absurd rfl nv
        · simp only [Term.list] at zip
          by_cases o₁ : t₁ = "open" <;> by_cases o₂ : t₂ = "open" <;>
            simp [tag, o₁, o₂, Erlang.erlang.«==/2», Lynx.Except.andAlso, zip]
      have nd : ¬Disj t₁ t₂ l₁.length l₂.length := d
      simp only [Disj, not_or, not_and] at nd
      refine ⟨fun pe => ?_, fun ⟨_, x, xs, ph⟩ => ?_, fun ⟨k', le⟩ => ?_, fun ⟨k', tg, x, xs, ls⟩ => ?_⟩
      · simp [PosE] at pe
        obtain ⟨rfl, hl₁⟩ := pe
        have : l₁ = [] := by cases l₁ <;> simp_all [Term.list]
        subst this
        have hl₂ : l₂.length = 0 := by rcases g₂ with rfl | rfl <;> simp at nd <;> first | omega | simp [nd]
        have : r = [] := List.eq_nil_of_length_eq_zero (by rw [len]; simp [hl₂])
        subst this
        simp [PosE, tag, Term.list]
      · simp at ph
        obtain ⟨-, hl₁⟩ := ph
        have : l₁ ≠ [] := by rintro rfl; simp [Term.list] at hl₁
        obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by
          cases r with
          | nil => simp at len; exact absurd (List.length_eq_zero_iff.mp (by omega)) this
          | cons y ys => exact ⟨y, ys, rfl⟩
        exact ⟨_, y, Term.list ys, rfl⟩
      · simp at le
        obtain ⟨-, rfl, hl₂⟩ := le
        have : l₂ = [] := by cases l₂ <;> simp_all [Term.list]
        subst this
        have hl₁ : l₁.length = 0 := by rcases g₁ with rfl | rfl <;> simp at nd <;> first | omega | simp [nd]
        have : r = [] := List.eq_nil_of_length_eq_zero (by rw [len]; simp [hl₁])
        subst this
        simp [PosE, tag, Term.list]
      · simp at ls
        obtain ⟨-, -, hl₂⟩ := ls
        have : l₂ ≠ [] := by rintro rfl; simp [Term.list] at hl₂
        obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by
          cases r with
          | nil => simp at len; exact absurd (List.length_eq_zero_iff.mp (by omega)) this
          | cons y ys => exact ⟨y, ys, rfl⟩
        exact ⟨_, y, Term.list ys, rfl⟩

    theorem cons_cmp {x xs b : Term} (e : Term.compare (.cons x xs) b = .eq) :
        ∃ y ys, b = .cons y ys ∧ Term.compare x y = .eq ∧ Term.compare xs ys = .eq := by
      cases b <;> rw [compare_eq_step] at e <;> simp [Compare.compareStep] at e
      rename_i y ys
      exact ⟨y, ys, rfl, e.1, e.2⟩

    theorem atom_cmp {name : String} {b : Term} (e : Term.compare (.atom name) b = .eq) : b = .atom name :=
      (compare_eq_atom b name).mp (Std.OrientedCmp.eq_symm e)

    theorem isE_cmp {t t' : Term} (h : IsE' t) (e : Term.compare t t' = .eq) : IsE' t' := by
      obtain ⟨k, rfl⟩ := h
      obtain ⟨b₀, b₁, b₂, rfl, -, e₁, e₂⟩ := tuple3_cmp e
      rw [atom_cmp e₁, (nil_compare_eq b₂).mp e₂]
      exact ⟨b₀, rfl⟩

    theorem isH_cmp {t t' : Term} (h : IsH' t) (e : Term.compare t t' = .eq) : IsH' t' := by
      obtain ⟨k, rfl⟩ := h
      obtain ⟨b₀, b₁, b₂, rfl, -, e₁, e₂⟩ := tuple3_cmp e
      obtain ⟨y, ys, rfl, ey, eys⟩ := cons_cmp e₂
      rw [atom_cmp e₁, atom_cmp ey, (nil_compare_eq ys).mp eys]
      exact ⟨b₀, rfl⟩

    theorem sized_cmp {t t' : Term} (h : Sized t) (e : Term.compare t t' = .eq) : Sized t' := by
      obtain ⟨k, tag, x, xs, rfl⟩ := h
      obtain ⟨b₀, b₁, b₂, rfl, -, -, e₂⟩ := tuple3_cmp e
      obtain ⟨y, ys, rfl, -, -⟩ := cons_cmp e₂
      exact ⟨b₀, b₁, y, ys, rfl⟩

    theorem isE_not_sized {t : Term} (h : IsE' t) (s : Sized t) : False := by
      obtain ⟨k, rfl⟩ := h
      obtain ⟨_, _, _, _, e⟩ := s
      simp at e

    theorem isE_not_isH {t : Term} (h : IsE' t) (s : IsH' t) : False := by
      obtain ⟨k, rfl⟩ := h
      obtain ⟨_, e⟩ := s
      simp at e

    theorem isH_sized {t : Term} (h : IsH' t) : Sized t := by
      obtain ⟨k, rfl⟩ := h
      exact ⟨k, _, _, _, rfl⟩

    /-- Valuations of tuple literals that a tuple realizes: `{}` when `e`, otherwise a tuple with elements. -/
    def Consistent (ρ : Term → Bool) (e : Bool) : Prop :=
      (∀ t, IsE' t → ρ t = e) ∧ (∀ t, IsH' t → ρ t = !e) ∧ (e = Bool.true → ∀ t, Sized t → ρ t = Bool.false)

    def Real (ρ : Term → Bool) : Prop := ∃ e, Consistent ρ e

    open Classical in
    noncomputable def realize (e : Bool) (t : Term) : Bool :=
      if IsE' t then e else if IsH' t then !e else if e = Bool.true ∧ Sized t then Bool.false else Bool.true

    theorem realize_resp (e : Bool) : Resp (realize e) := by
      intro a b h
      have h' := Std.OrientedCmp.eq_symm h
      have iE : IsE' a ↔ IsE' b := ⟨fun x => isE_cmp x h, fun x => isE_cmp x h'⟩
      have iH : IsH' a ↔ IsH' b := ⟨fun x => isH_cmp x h, fun x => isH_cmp x h'⟩
      have iS : Sized a ↔ Sized b := ⟨fun x => sized_cmp x h, fun x => sized_cmp x h'⟩
      unfold realize
      by_cases x : IsE' a
      · simp [x, iE.mp x]
      have x' : ¬IsE' b := fun y => x (iE.mpr y)
      by_cases y : IsH' a
      · simp [x, x', y, iH.mp y]
      have y' : ¬IsH' b := fun z => y (iH.mpr z)
      by_cases z : Sized a
      · simp [x, x', y, y', z, iS.mp z]
      · have z' : ¬Sized b := fun w => z (iS.mpr w)
        simp [x, x', y, y', z, z']

    theorem realize_consistent (e : Bool) : Consistent (realize e) e := by
      refine ⟨fun t h => by simp [realize, h], fun t h => ?_, fun he t h => ?_⟩
      · have : ¬IsE' t := fun x => isE_not_isH x h
        simp [realize, this, h]
      · have : ¬IsE' t := fun x => isE_not_sized x h
        by_cases hh : IsH' t
        · simp [realize, this, hh, he]
        · simp [realize, this, hh, he, h]

    theorem consistent_flip {ρ : Term → Bool} {e : Bool} {lit : Term} {v : Bool} (c : Consistent ρ e)
        (hE : IsE' lit → v = e) (hH : IsH' lit → v = !e) (hS : e = Bool.true → Sized lit → v = Bool.false) :
        Consistent (flip ρ lit v) e := by
      refine ⟨fun t h => ?_, fun t h => ?_, fun he t h => ?_⟩ <;> simp only [BddProofs.flip] <;> split
      · next eq => exact hE (isE_cmp h eq)
      · exact c.1 t h
      · next eq => exact hH (isH_cmp h eq)
      · exact c.2.1 t h
      · next eq => exact hS he (sized_cmp h eq)
      · exact c.2.2 he t h

    /-- What the literals gathered by a line allow the realizing tuple to be: `{}` when `e`. -/
    def Allowed (pos : Term) (negs : List Term) (e : Bool) : Prop :=
      (e = Bool.true → (¬∃ t ∈ negs, IsE t) ∧ ¬PosH pos) ∧ (e = Bool.false → (¬∃ t ∈ negs, IsH t) ∧ ¬PosE pos)

    def isNone : Term → Bool
      | .map [] => Bool.true
      | _ => Bool.false

    theorem isNone_iff (e : Term) : isNone e = Bool.true ↔ e = .map [] := by
      unfold isNone
      split <;> simp_all

    theorem any1_list (d : Dispatcher) (f : Term) (res : Term → Bool) :
        ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (boolAtom (res x))) →
          Erlang.lists.«any_1/2» d f (Term.list l) = .ok (boolAtom (l.any res)) := by
      intro l
      induction l with
      | nil => intro _; simp [Erlang.lists.«any_1/2», Term.list, boolAtom]
      | cons x xs ih =>
        intro hf
        rw [Erlang.lists.«any_1/2».eq_def]
        have hx := hf x List.mem_cons_self
        have tail := ih fun y m => hf y (List.mem_cons_of_mem _ m)
        cases h : res x <;> simp [Term.list, hx, h, boolAtom, tail]

    theorem any_list (d : Dispatcher) (m nm : String) (caps : Array Term) (res : Term → Bool) (l : List Term)
        (hf : ∀ x ∈ l, d.pure (.function m nm 1 caps) #[x] = .ok (boolAtom (res x))) :
        Erlang.lists.«any/2» d (.function m nm 1 caps) (Term.list l) = .ok (boolAtom (l.any res)) := by
      cases l with
      | nil => simp [Erlang.lists.«any/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list, boolAtom]
      | cons x xs =>
        have hx := hf x List.mem_cons_self
        have tail := any1_list d _ res xs fun y m => hf y (List.mem_cons_of_mem _ m)
        cases h : res x <;>
          simp [Erlang.lists.«any/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list, hx, h, boolAtom, tail]

    /-- Lines check first whether some element is empty. -/
    theorem elements_check (n : Nat) {S : Term} (seen : SeenOk S) (l : List Term) (hl : ∀ e ∈ l, ElemTerm e) :
        Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D (n + 2)) (Term.list l) S =
          .ok (boolAtom (l.any isNone)) := by
      simp only [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», Lynx.Except.ok_bind]
      refine any_list _ _ _ _ isNone l fun x m => ?_
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2»]
      by_cases e : x = .map []
      · subst e; simpa [isNone, boolAtom] using empty_none_seen _ S
      · have : isNone x = Bool.false := by
          cases h : isNone x
          · rfl
          · exact absurd ((isNone_iff x).mp h) e
        rw [this, lelem_full _ (elem_lelem (hl x m)) e seen]
        rfl

    /-- A line that no tuple can realize is empty. -/
    theorem top_case (n : Nat) {S : Term} (seen : SeenOk S) {tag : String} {l : List Term}
        (g : tag = "open" ∨ tag = "closed") (el : ∀ e ∈ l, ElemTerm e) {negs : List Term} (lits : ∀ t ∈ negs, TupleLit t)
        (none : ∀ e, ¬Allowed (.tuple #[.atom tag, Term.list l]) negs e) :
        Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4» (D (n + 2)) (.atom tag) (Term.list l) (Term.list negs) S =
          .ok (.atom "true") := by
      rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
      simp only [elements_check n seen l el, Lynx.Except.ok_bind]
      by_cases some : l.any isNone = Bool.true
      · simp [some, boolAtom, Lynx.Except.guard, Erlang.erlang.«/=/2», Lynx.Except.andAlso]
      have no : l.any isNone = Bool.false := by cases h : l.any isNone <;> simp_all
      have full : ∀ e ∈ l, Full e := by
        intro e m
        refine ⟨elem_lelem (el e m), fun h => ?_⟩
        have := List.any_eq_false.mp no e m
        rw [h] at this
        simp [isNone] at this
      have A : (∃ t ∈ negs, IsE t) ∨ PosH (.tuple #[.atom tag, Term.list l]) := by
        refine Classical.byContradiction fun h => none Bool.true ⟨fun _ => ⟨fun x => h (Or.inl x), fun x => h (Or.inr x)⟩,
          fun e => by simp at e⟩
      have B : (∃ t ∈ negs, IsH t) ∨ PosE (.tuple #[.atom tag, Term.list l]) := by
        refine Classical.byContradiction fun h => none Bool.false ⟨fun e => by simp at e,
          fun _ => ⟨fun x => h (Or.inl x), fun x => h (Or.inr x)⟩⟩
      have posE : PosE (.tuple #[.atom tag, Term.list l]) → tag = "closed" ∧ l = [] := by
        intro e
        simp [PosE] at e
        exact ⟨e.1, by cases l <;> simp_all [Term.list]⟩
      have posH : PosH (.tuple #[.atom tag, Term.list l]) → l ≠ [] := by
        rintro ⟨_, x, xs, e⟩ rfl
        simp [Term.list] at e
      have nonempty : negs ≠ [] := by
        rintro rfl
        rcases A with ⟨t, m, -⟩ | pa
        · simp at m
        rcases B with ⟨t, m, -⟩ | pb
        · simp at m
        exact posH pa (posE pb).2
      have notNil : Erlang.erlang.«==/2» (Term.list negs) .nil = .ok (.atom "false") := by
        cases negs with
        | nil => exact absurd rfl nonempty
        | cons x xs => simp [Erlang.erlang.«==/2», Term.list, Term.false]
      simp [no, boolAtom, Lynx.Except.guard, Erlang.erlang.«/=/2», Lynx.Except.andAlso, notNil]
      rcases A with hE | pa <;> rcases B with hH | pb
      · exact line_both n seen negs lits hE hH tag g l full
      · obtain ⟨rfl, rfl⟩ := posE pb
        exact line_closed_empty _ S negs lits hE
      · exact line_full n seen negs lits hH tag l (posH pa) full
      · exact absurd (posE pb).2 (posH pa)

    /-- No valuation that a tuple allowed by a line realizes satisfies the BDD. -/
    def RealUnsat (pos : Term) (negs : List Term) (r : Term) : Prop :=
      ∀ e, Allowed pos negs e → ∀ ρ, Resp ρ → Consistent ρ e → eval ρ r = Bool.false

    theorem isE_int {t : Term} (lit : TupleLit t) (h : IsE' t) : IsE t := by
      obtain ⟨k, tag, l, rfl, -, -⟩ := lit
      obtain ⟨k', e⟩ := h
      simp at e
      obtain ⟨-, rfl, e⟩ := e
      exact ⟨k, by rw [e]⟩

    theorem isH_int {t : Term} (lit : TupleLit t) (h : IsH' t) : IsH t := by
      obtain ⟨k, tag, l, rfl, -, -⟩ := lit
      obtain ⟨k', e⟩ := h
      simp at e
      obtain ⟨-, rfl, e⟩ := e
      exact ⟨k, by rw [e]⟩

    /-- Taking the positive branch of a literal keeps the valuations consistent. -/
    theorem flip_pos {ρ : Term → Bool} {e : Bool} {lit pos' : Term} (c : Consistent ρ e)
        (allowed : (e = Bool.true → ¬PosH pos') ∧ (e = Bool.false → ¬PosE pos'))
        (hE : IsE' lit → PosE pos') (hS : Sized lit → PosH pos') : Consistent (flip ρ lit Bool.true) e := by
      refine consistent_flip c (fun h => ?_) (fun h => ?_) (fun he h => ?_)
      · cases e
        · exact absurd (hE h) (allowed.2 rfl)
        · rfl
      · cases e
        · rfl
        · exact absurd (hS (isH_sized h)) (allowed.1 rfl)
      · exact absurd (hS h) (allowed.1 he)

    theorem flip_above {ok : Term → Prop} {lit x : Term} (wx : Bdd (Above ok lit) x) (ρ : Term → Bool) (v : Bool) :
        eval (flip ρ lit v) x = eval ρ x := by
      refine eval_ext wx fun t ht => ?_
      have : Term.compare t lit ≠ .eq := fun e => by
        have := ht.2; rw [Std.OrientedCmp.eq_symm e] at this; cases this
      simp [BddProofs.flip, this]

    theorem flip_self (ρ : Term → Bool) (lit : Term) (v : Bool) : flip ρ lit v lit = v := by
      simp [BddProofs.flip, Std.ReflCmp.compare_self]

    theorem tuple_bdd_real (n : Nat) {S : Term} (seen : SeenOk S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
        (∀ t, ok t → TupleOk t) → ∀ pos negs, TuplePos pos → (∀ t ∈ negs, TupleLit t) → RealUnsat pos negs r →
          Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (n + 2)) pos (Term.list negs) r S = .ok (.atom "true") := by
      refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk t) → ∀ pos negs, TuplePos pos →
        (∀ t ∈ negs, TupleLit t) → RealUnsat pos negs r →
        Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (n + 2)) pos (Term.list negs) r S = .ok (.atom "true"))
        ?_ ?_ ?_ ?_ ok r wr
      · intro ok _ pos negs hp lits g
        obtain ⟨tag, l, rfl, gt, el⟩ := hp
        rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
        simp only
        exact top_case n seen gt el lits fun e allowed => by
          have := g e allowed (realize e) (realize_resp e) (realize_consistent e)
          simp at this
      · intro ok _ pos negs _ _ _
        rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
        split <;> simp_all
      · intro ok k x y okl okLit pos negs hp lits g
        have hl := okLit _ okl
        rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
        rcases inter_facts n hp hl with empty | ⟨pos', run, hp', fE, fH, lE, lS⟩
        · simp [empty]
        obtain ⟨tag, l, rfl, gt, el⟩ := hp'
        simp [run]
        refine top_case n seen gt el lits fun e allowed => ?_
        have c := flip_pos (realize_consistent e) ⟨fun he => (allowed.1 he).2, fun he => (allowed.2 he).2⟩ lE lS
        have := g e ⟨fun he => ⟨(allowed.1 he).1, fun p => (allowed.1 he).2 (fH p)⟩,
          fun he => ⟨(allowed.2 he).1, fun p => (allowed.2 he).2 (fE p)⟩⟩ _ ((realize_resp e).flip _ _) c
        simp [flip_self] at this
      · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits g
        have hl := okLit _ okl
        have okLit' : ∀ t, Above ok lit t → TupleOk t := fun t ht => okLit t ht.1
        have dPart : Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (n + 2)) pos (Term.list (lit :: negs)) d S =
            .ok (.atom "true") := by
          refine idd okLit' pos (lit :: negs) hp (fun t m => ?_) fun e allowed ρ resp cons => ?_
          · rcases List.mem_cons.mp m with rfl | m
            · exact hl.1
            · exact lits t m
          have c' : Consistent (flip ρ lit Bool.false) e := by
            refine consistent_flip cons (fun h => ?_) (fun h => ?_) (fun _ _ => rfl)
            · cases e
              · rfl
              · exact absurd ⟨lit, List.mem_cons_self, isE_int hl.1 h⟩ (allowed.1 rfl).1
            · cases e
              · exact absurd ⟨lit, List.mem_cons_self, isH_int hl.1 h⟩ (allowed.2 rfl).1
              · rfl
          have := g e ⟨fun he => ⟨fun ⟨t, m, ht⟩ => (allowed.1 he).1 ⟨t, List.mem_cons_of_mem _ m, ht⟩, (allowed.1 he).2⟩,
            fun he => ⟨fun ⟨t, m, ht⟩ => (allowed.2 he).1 ⟨t, List.mem_cons_of_mem _ m, ht⟩, (allowed.2 he).2⟩⟩
            _ (resp.flip _ _) c'
          simp only [eval_node, flip_self, flip_above hc, flip_above hu, flip_above hd] at this
          simp at this
          exact this.2
        have uPart := iu okLit' pos negs hp lits fun e allowed ρ resp cons => by
          have := g e allowed ρ resp cons
          simp only [eval_node] at this
          cases hu' : eval ρ u
          · rfl
          · simp [hu'] at this
        rw [list_cons] at dPart
        obtain ⟨tag, l, rfl, gt, el⟩ := hp
        rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
        rcases inter_facts n ⟨tag, l, rfl, gt, el⟩ hl with empty | ⟨pos2, run, hp2, fE, fH, lE, lS⟩
        · simp [empty, dPart, uPart, Lynx.Except.andAlso]
        have cRes := ic okLit' pos2 negs hp2 lits fun e allowed ρ resp cons => by
          have c' := flip_pos cons ⟨fun he => (allowed.1 he).2, fun he => (allowed.2 he).2⟩ lE lS
          have := g e ⟨fun he => ⟨(allowed.1 he).1, fun p => (allowed.1 he).2 (fH p)⟩,
            fun he => ⟨(allowed.2 he).1, fun p => (allowed.2 he).2 (fE p)⟩⟩ _ (resp.flip _ _) c'
          simp only [eval_node, flip_self, flip_above hc, flip_above hu, flip_above hd] at this
          simp at this
          exact this.1
        obtain ⟨tag2, l2, rfl, -⟩ := hp2
        simp [run, dPart, uPart, Lynx.Except.andAlso, cRes]

    /-- Tuple BDDs that no realizable valuation satisfies are empty. -/
    theorem tuple_empty_real (n : Nat) {ok : Term → Prop} (okLit : ∀ t, ok t → TupleOk t) {r : Term} (wr : Bdd ok r)
        (unsat : ∀ ρ, Resp ρ → Real ρ → eval ρ r = Bool.false) :
        Elixir.Module.Types.Descr.«tuple_empty?/2» (D (n + 2)) r (.map []) = .ok (.atom "true") := by
      have fresh : ∀ kind : String, exactCompare (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil]))
          (.cons (.atom "tuple") r) ≠ .eq := by
        intro kind e
        rw [exactCompare_cons] at e
        simp [Ordering.then] at e
        split at e
        · rename_i hk
          obtain ⟨b₀, b₁, b₂, rfl, -, e₁, e₂⟩ := tuple3_exact e
          rw [(exactCompare_eq_atom b₁ "open").mp (Std.OrientedCmp.eq_symm e₁)] at wr
          have : b₂ = .nil := by
            have := Std.OrientedCmp.eq_symm e₂
            cases b₂ <;> rw [exactCompare_eq_step] at this <;> simp [Compare.compareStep] at this
          subst this
          rcases wr.shape with h | h | ⟨k, x, y, h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (okLit _ (Bdd.leaf_iff.mp wr)).2 ⟨_, rfl⟩
        · rename_i ne
          simp at e
          subst e
          exact ne (by simp)
      have seen := seenOk_one (.cons (.atom "tuple") r) (.atom "true") fresh
      have run := tuple_bdd_real n seen wr okLit (.tuple #[.atom "open", .nil]) [] ⟨"open", [], rfl, Or.inl rfl, by simp⟩
        (by simp) fun e _ ρ resp cons => unsat ρ resp ⟨e, cons⟩
      unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.true, Term.false,
        Erlang.maps.«put/3»]
      simpa [Term.list] using run

    /-! Subtyping, field by field. -/

    /-- A field of the left type that the right type covers: their difference is empty, or the right type
    lacks the field and the field is empty. -/
    def KeySub (d : Dispatcher) (B : List (Term × Term)) (q a : Term) : Prop :=
      (∃ b w, mapLookup B q = some b ∧ Elixir.Module.Types.Descr.«bare_difference/3» d q a b = .ok w ∧
        (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
          Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))) ∨
      (mapLookup B q = Option.none ∧ Elixir.Module.Types.Descr.«empty_key?/3» d q a (.map []) = .ok (.atom "true"))

    theorem iterator_sub (d : Dispatcher) (B : List (Term × Term)) :
        ∀ es : List (Term × Term), (∀ e ∈ es, KeySub d B e.1 e.2) →
          (do
            let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
            Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» d it (.map B) (.map [])) =
            .ok (.atom "true") := by
      intro es
      induction es with
      | nil =>
        intro _
        simp [Term.list, Erlang.maps.«next/1»]
        unfold Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3»
        rfl
      | cons e rest ih =>
        intro all
        have tail := ih (fun e' m => all e' (by simp [m]))
        simp only [List.map, Term.list] at tail ⊢
        simp only [Erlang.maps.«next/1», Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
        rcases all e (by simp) with ⟨b, w, hb, run, empty⟩ | ⟨hb, empty⟩
        · simp [getMapKeys_single, hb, run]
          rcases empty with h | h | h
          · simpa [h] using tail
          · simpa [h] using tail
          · refine ⟨?_, tail⟩
            by_cases h₀ : w = .integer 0
            · simp [h₀]
            · by_cases h₁ : w = .atom "bdd_bot"
              · simp [h₁]
              · right
                simp [h₀, h₁, h]
        · simp [getMapKeys_single, hb, empty, tail]

    /-- Static types are subtypes when the right type covers each field of the left type. -/
    theorem subtype_keys (d : Dispatcher) (A B : List (Term × Term)) (sA : mapLookup A (.atom "dynamic") = Option.none)
        (sB : mapLookup B (.atom "dynamic") = Option.none) (keys : ∀ e ∈ mapEntries A, KeySub d B e.1 e.2) :
        Elixir.Module.Types.Descr.«subtype?/2» d (.map A) (.map B) = .ok (.atom "true") := by
      have walk := iterator_sub d B (mapEntries A) keys
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», getMapKeys_single, sA, sB, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Lynx.Except.guard, Erlang.erlang.«/=/2»]
      unfold Elixir.Module.Types.Descr.«subtype_static?/2»
      by_cases same : exactCompare (.map B) (.map A) = .eq
      · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, sA, sB, unfold_map, Erlang.maps.«iterator/1»]
        exact walk

    theorem find_entry {L : List (Term × Term)} {a : Term} {e : Term × Term}
        (hit : (mapEntries L).find? (fun e => decide (exactCompare a e.1 = .eq)) = some e) :
        exactCompare a e.1 = .eq ∧ mapLookup L a = some e.2 := by
      have qe : exactCompare a e.1 = .eq := by simpa using List.find?_some hit
      refine ⟨qe, ?_⟩
      rw [← mapLookup_mapEntries]
      simp [mapLookup, hit]

    theorem find_none {L : List (Term × Term)} {a : Term}
        (hit : (mapEntries L).find? (fun e => decide (exactCompare a e.1 = .eq)) = none) : mapLookup L a = none := by
      rw [← mapLookup_mapEntries]
      simp [mapLookup, hit]

    /-- The fields of an intersection of static types: the kept intersections of their common fields. -/
    theorem inter_lookup (depth : Nat) (L R : List (Term × Term)) (sL : mapLookup L (.atom "dynamic") = Option.none)
        (sR : mapLookup R (.atom "dynamic") = Option.none)
        (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) q x y = .ok w) :
        ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2» (D (depth + 1)) (.map L) (.map R) = .ok (.map I) ∧
          (∀ name, (mapLookup L (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
            (mapLookup R (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
            (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
              Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) (.atom name) x y = .ok w →
              mapLookup I (.atom name) = if kept (.atom name, w) then some w else Option.none)) ∧
          ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have value : ∀ q x y w, Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) q x y = .ok w → g q x y = w := by
        intro q x y w run; simp [g, run]
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (depth + 1)) "Elixir.Module.Types.Descr"
        "bare_intersection" #[] L R g (by
          intro e member y hy
          obtain ⟨w, run⟩ := calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy
          rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, run, value _ _ _ _ run])
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (depth + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] I kept (by
          intro e _
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
      refine ⟨out, ?_, fun name => ?_, fun q h => ?_⟩
      · unfold Elixir.Module.Types.Descr.«bare_intersection/2»
        simp [getMapKeys_single, sL, sR]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runO]
      rotate_left
      · rw [lookO] at h
        cases hit : (mapEntries I).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | none => rw [hit] at h; cases h
        | some e =>
          obtain ⟨-, hI⟩ := find_entry hit
          rw [lookI] at hI
          cases hitL : (mapEntries L).find? (fun e => decide (exactCompare q e.1 = .eq)) with
          | none => rw [hitL] at hI; cases hI
          | some f => rw [(find_entry hitL).2]; rfl
      have look : mapLookup out (.atom name) =
          match mapLookup L (.atom name), mapLookup R (.atom name) with
          | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
          | _, _ => Option.none := by
        rw [lookO, find_atom, lookI, find_atom]
        rcases hL : mapLookup L (.atom name) with _ | x <;> rcases hR : mapLookup R (.atom name) with _ | y <;>
          simp [hR]
      refine ⟨fun hL => by rw [look, hL], fun hR => by rw [look, hR]; cases mapLookup L (.atom name) <;> rfl,
        fun x y w hL hR run => by rw [look, hL, hR]; simp only [value _ _ _ _ run]⟩

    /-! The meaning of fields: points hold a bit index, an atom or an arity, and a valuation of literals. -/

    abbrev Point := Nat × Term × (Term → Bool)

    def isListTop : Term → Bool
      | .tuple ⟨[_, .atom "term", .atom "term"]⟩ => Bool.true
      | _ => Bool.false

    def isOpenTop : Term → Bool
      | .tuple ⟨[_, .atom "open", .nil]⟩ => Bool.true
      | _ => Bool.false

    def bitOf : Term → Nat → Bool
      | .integer b, i => b.toNat.testBit i
      | _, _ => Bool.false

    def arityOf : Term → Term → (Term → Bool) → Bool
      | .tuple ⟨[.atom "union", .map R]⟩, a, ρ => (mapLookup R a).elim Bool.false (eval ρ)
      | .tuple ⟨[.atom "negation", .map R]⟩, a, ρ => !(mapLookup R a).elim Bool.false (eval ρ)
      | _, _, _ => Bool.false

    /-- List fields hold all non-empty lists, or what a BDD of other literals holds. -/
    def denL (x : Term) (ρ : Term → Bool) : Bool := isListTop x || eval ρ x

    theorem listTop_iff (x : Term) : isListTop x = Bool.true ↔ ∃ k, x = .tuple #[k, .atom "term", .atom "term"] := by
      unfold isListTop; split <;> simp_all

    theorem listTop_bdd {x : Term} (wx : Bdd ListOk x) : isListTop x = Bool.false := by
      cases h : isListTop x
      · rfl
      · obtain ⟨k, rfl⟩ := (listTop_iff _).mp h
        exact absurd rfl (not_top_leaf wx k)

    theorem denL_bdd {x : Term} (wx : Bdd ListOk x) (ρ : Term → Bool) : denL x ρ = eval ρ x := by
      simp [denL, listTop_bdd wx]

    theorem denL_top (k : Int) (ρ : Term → Bool) : denL (.tuple #[.integer k, .atom "term", .atom "term"]) ρ = Bool.true := by
      simp [denL, isListTop]

    theorem list_union_spec {x y : Term} (fx : ListField x) (fy : ListField y) :
        ∃ w, Elixir.Module.Types.Descr.«list_union/2» x y = .ok w ∧ ListField w ∧
          (∀ ρ, Resp ρ → denL w ρ = (denL x ρ || denL y ρ)) ∧ isListTop w = (isListTop x || isListTop y) := by
      rcases fx with ⟨k, rfl⟩ | wx
      · refine ⟨_, by unfold Elixir.Module.Types.Descr.«list_union/2»; rfl, Or.inl ⟨k, rfl⟩, fun ρ _ => ?_, ?_⟩
        · simp [denL_top]
        · simp [isListTop]
      rcases fy with ⟨k, rfl⟩ | wy
      · have nx := not_top_leaf wx
        refine ⟨_, ?_, Or.inl ⟨k, rfl⟩, fun ρ _ => ?_, ?_⟩
        · unfold Elixir.Module.Types.Descr.«list_union/2»
          split <;> simp_all
        · simp [denL_top]
        · simp [isListTop]
      obtain ⟨w, run, keep, sem⟩ := union_ok wx wy
      have ww := keep _ wx wy
      refine ⟨w, ?_, Or.inr ww, fun ρ resp => by rw [denL_bdd ww, denL_bdd wx, denL_bdd wy, sem ρ resp], by
        rw [listTop_bdd ww, listTop_bdd wx, listTop_bdd wy]; rfl⟩
      unfold Elixir.Module.Types.Descr.«list_union/2»
      split
      · exact absurd rfl (not_top_leaf wx _)
      · exact absurd rfl (not_top_leaf wy _)
      · exact run

    theorem list_bdd_ne_zero {x : Term} (wx : Bdd ListOk x) : x ≠ .integer 0 := by
      rintro rfl; simp [Bdd] at wx

    theorem list_neg_spec {x : Term} (fx : ListField x) :
        ∃ w, Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x =
            .ok w ∧
          (kept (.atom "list", w) = Bool.true → ListField w ∧ isListTop w = Bool.false ∧
            ∀ ρ, Resp ρ → denL w ρ = !denL x ρ) ∧
          (kept (.atom "list", w) = Bool.false → ∀ ρ, Resp ρ → denL x ρ = Bool.true) := by
      rcases fx with ⟨k, rfl⟩ | wx
      · refine ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«list_difference/2»; rfl, fun k => by simp [kept] at k,
          fun _ ρ _ => denL_top k ρ⟩
      obtain ⟨w, run, keep, sem, -⟩ := neg_okN wx
      have ww := keep _ wx
      refine ⟨w, by rw [list_difference_bdd _ wx, run], fun k => ⟨Or.inr ww, listTop_bdd ww, fun ρ resp => ?_⟩,
        fun k ρ resp => ?_⟩
      · rw [denL_bdd ww, denL_bdd wx, sem ρ resp]
      · rcases dropped k with h | h
        · exact absurd h (list_bdd_ne_zero ww)
        · have := sem ρ resp
          rw [h] at this
          rw [denL_bdd wx]
          cases e : eval ρ x <;> simp_all

    theorem list_inter_spec {x y : Term} (fx : ListField x) (fy : ListField y) :
        ∃ w, Elixir.Module.Types.Descr.«list_intersection/2» x y = .ok w ∧
          (kept (.atom "list", w) = Bool.true → ListField w ∧ (∀ ρ, Resp ρ → denL w ρ = (denL x ρ && denL y ρ)) ∧
            isListTop w = (isListTop x && isListTop y)) ∧
          (kept (.atom "list", w) = Bool.false → (∀ ρ, Resp ρ → (denL x ρ && denL y ρ) = Bool.false) ∧
            (isListTop x && isListTop y) = Bool.false) := by
      have dropBdd : ∀ {w : Term}, Bdd ListOk w → kept (.atom "list", w) = Bool.false → ∀ ρ, eval ρ w = Bool.false := by
        intro w ww k ρ
        rcases dropped k with h | h
        · exact absurd h (list_bdd_ne_zero ww)
        · rw [h]; rfl
      rcases fx with ⟨k, rfl⟩ | wx
      · refine ⟨y, by unfold Elixir.Module.Types.Descr.«list_intersection/2»; rfl, fun _ => ⟨fy, fun ρ _ => ?_, ?_⟩,
          fun kk => ?_⟩
        · simp [denL_top]
        · simp [isListTop]
        · rcases fy with ⟨k', rfl⟩ | wy
          · simp [kept] at kk
          · exact ⟨fun ρ _ => by rw [denL_bdd wy, dropBdd wy kk]; simp, by rw [listTop_bdd wy]; simp⟩
      rcases fy with ⟨k, rfl⟩ | wy
      · have nx := not_top_leaf wx
        refine ⟨x, ?_, fun _ => ⟨Or.inr wx, fun ρ _ => by simp [denL_top], by simp [isListTop]⟩, fun kk =>
          ⟨fun ρ _ => by rw [denL_bdd wx, dropBdd wx kk]; simp, by rw [listTop_bdd wx]; simp⟩⟩
        unfold Elixir.Module.Types.Descr.«list_intersection/2»
        split <;> simp_all
      obtain ⟨w, run, keep, sem⟩ := inter_ok wx wy
      have ww := keep _ wx wy
      refine ⟨w, ?_, fun _ => ⟨Or.inr ww, fun ρ resp => by rw [denL_bdd ww, denL_bdd wx, denL_bdd wy, sem ρ resp],
        by rw [listTop_bdd ww, listTop_bdd wx, listTop_bdd wy]; rfl⟩, fun kk => ⟨fun ρ resp => ?_,
        by rw [listTop_bdd wx]; rfl⟩⟩
      · unfold Elixir.Module.Types.Descr.«list_intersection/2»
        split
        · exact absurd rfl (not_top_leaf wx _)
        · exact absurd rfl (not_top_leaf wy _)
        · exact run
      · rw [denL_bdd wx, denL_bdd wy, ← sem ρ resp, dropBdd ww kk]

    theorem list_sub_spec (d : Dispatcher) {a : Term} (fa : ListField a) (b : Option Term)
        (fb : ∀ y, b = some y → ListField y)
        (incl : ∀ ρ, Resp ρ → denL a ρ = Bool.true → b.elim Bool.false (denL · ρ) = Bool.true)
        (side : ∀ y, b = some y → isListTop y = Bool.true → isListTop a = Bool.true) :
        (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«list_difference/2» a y = .ok w ∧
          (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
            Elixir.Module.Types.Descr.«list_empty?/2» d w (.map []) = .ok (.atom "true"))) ∧
        (b = Option.none → Elixir.Module.Types.Descr.«list_empty?/2» d a (.map []) = .ok (.atom "true")) := by
      refine ⟨fun y hb => ?_, fun hb => ?_⟩
      · subst hb
        have fy := fb y rfl
        rcases fa with ⟨k, rfl⟩ | wa
        · rcases fy with ⟨k', rfl⟩ | wy
          · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«list_difference/2»; rfl, Or.inr (Or.inl rfl)⟩
          · obtain ⟨w, run, keep, sem⟩ := neg_ok wy
            refine ⟨w, by rw [list_difference_bdd _ wy, run], Or.inr (Or.inr (list_empty_unsat d (keep _ wy)
              (fun ρ resp => ?_) []))⟩
            have := incl ρ resp (denL_top k ρ)
            simp only [Option.elim, denL_bdd wy] at this
            rw [sem ρ resp, this]; rfl
        · rcases fy with ⟨k', rfl⟩ | wy
          · have := side _ rfl (by simp [isListTop])
            rw [listTop_bdd wa] at this
            cases this
          · obtain ⟨w, run, keep, sem⟩ := diff_ok wa wy
            refine ⟨w, ?_, Or.inr (Or.inr (list_empty_unsat d (keep _ wa wy) (fun ρ resp => ?_) []))⟩
            · unfold Elixir.Module.Types.Descr.«list_difference/2»
              split
              · exact absurd rfl (not_top_leaf wa _)
              · exact absurd rfl (not_top_leaf wa _)
              · exact run
            · rw [sem ρ resp]
              cases e : eval ρ a
              · rfl
              · have := incl ρ resp (by rw [denL_bdd wa, e])
                simp only [Option.elim, denL_bdd wy] at this
                simp [this]
      · subst hb
        rcases fa with ⟨k, rfl⟩ | wa
        · have := incl _ (resp_const Bool.true) (denL_top k _)
          simp [Option.elim] at this
        · refine list_empty_unsat d wa (fun ρ resp => ?_) []
          cases e : eval ρ a
          · rfl
          · have := incl ρ resp (by rw [denL_bdd wa, e])
            simp [Option.elim] at this

    /-! Map and tuple fields: all maps or tuples, or what a BDD of other literals holds. -/

    def OField (ok : Term → Prop) (x : Term) : Prop := (∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd ok x

    def denO (x : Term) (ρ : Term → Bool) : Bool := isOpenTop x || eval ρ x

    theorem openTop_bdd {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) {x : Term} (wx : Bdd ok x) :
        isOpenTop x = Bool.false := by
      cases h : isOpenTop x
      · rfl
      · unfold isOpenTop at h
        split at h
        · exact absurd rfl (not_top_of_ok wx okNot _)
        · cases h

    theorem denO_bdd {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) {x : Term} (wx : Bdd ok x) (ρ : Term → Bool) :
        denO x ρ = eval ρ x := by
      simp [denO, openTop_bdd okNot wx]

    theorem denO_top (k : Term) (ρ : Term → Bool) : denO (.tuple #[k, .atom "open", .nil]) ρ = Bool.true := by
      simp [denO, isOpenTop]

    theorem bdd_ne_zero {ok : Term → Prop} {x : Term} (wx : Bdd ok x) : x ≠ .integer 0 := by
      rintro rfl; simp [Bdd] at wx

    theorem drop_bdd {ok : Term → Prop} {q w : Term} (ww : Bdd ok w) (k : kept (q, w) = Bool.false) (ρ : Term → Bool) :
        eval ρ w = Bool.false := by
      rcases dropped k with h | h
      · exact absurd h (bdd_ne_zero ww)
      · rw [h]; rfl

    theorem open_union_spec {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) (f : Term → Term → Except Exception Term)
        (h₁ : ∀ k y, f (.tuple #[k, .atom "open", .nil]) y = .ok (.tuple #[k, .atom "open", .nil]))
        (h₂ : ∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
          f x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil]))
        (h₃ : ∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
          f x y = Elixir.Module.Types.Descr.«bdd_union/2» x y)
        {x y : Term} (fx : OField ok x) (fy : OField ok y) :
        ∃ w, f x y = .ok w ∧ OField ok w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) := by
      rcases fx with ⟨k, rfl⟩ | wx
      · exact ⟨_, h₁ _ y, Or.inl ⟨k, rfl⟩, fun ρ _ => by simp [denO_top]⟩
      rcases fy with ⟨k, rfl⟩ | wy
      · exact ⟨_, h₂ x _ (not_top_of_ok wx okNot), Or.inl ⟨k, rfl⟩, fun ρ _ => by simp [denO_top]⟩
      obtain ⟨w, run, keep, sem⟩ := union_ok wx wy
      have ww := keep _ wx wy
      exact ⟨w, by rw [h₃ x y (not_top_of_ok wx okNot) (not_top_of_ok wy okNot), run], Or.inr ww, fun ρ resp => by
        rw [denO_bdd okNot ww, denO_bdd okNot wx, denO_bdd okNot wy, sem ρ resp]⟩

    theorem open_inter_spec {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) (f : Term → Term → Except Exception Term)
        (h₁ : ∀ k y, f (.tuple #[k, .atom "open", .nil]) y = .ok y)
        (h₂ : ∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) → f x (.tuple #[k, .atom "open", .nil]) = .ok x)
        (h₃ : ∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
          f x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y)
        (q : Term) {x y : Term} (fx : OField ok x) (fy : OField ok y) :
        ∃ w, f x y = .ok w ∧ (kept (q, w) = Bool.true → OField ok w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ)) ∧
          (kept (q, w) = Bool.false → ∀ ρ, Resp ρ → (denO x ρ && denO y ρ) = Bool.false) := by
      rcases fx with ⟨k, rfl⟩ | wx
      · refine ⟨y, h₁ _ y, fun _ => ⟨fy, fun ρ _ => by simp [denO_top]⟩, fun kk ρ _ => ?_⟩
        rcases fy with ⟨k', rfl⟩ | wy
        · simp [kept] at kk
        · rw [denO_bdd okNot wy, drop_bdd wy kk]; simp
      rcases fy with ⟨k, rfl⟩ | wy
      · exact ⟨x, h₂ x _ (not_top_of_ok wx okNot), fun _ => ⟨Or.inr wx, fun ρ _ => by simp [denO_top]⟩,
          fun kk ρ _ => by rw [denO_bdd okNot wx, drop_bdd wx kk]; simp⟩
      obtain ⟨w, run, keep, sem⟩ := inter_ok wx wy
      have ww := keep _ wx wy
      refine ⟨w, by rw [h₃ x y (not_top_of_ok wx okNot) (not_top_of_ok wy okNot), run], fun _ => ⟨Or.inr ww,
        fun ρ resp => by rw [denO_bdd okNot ww, denO_bdd okNot wx, denO_bdd okNot wy, sem ρ resp]⟩, fun kk ρ resp => ?_⟩
      rw [denO_bdd okNot wx, denO_bdd okNot wy, ← sem ρ resp, drop_bdd ww kk]

    theorem map_union_shape : (∀ k y, Elixir.Module.Types.Descr.«map_union/2» (.tuple #[k, .atom "open", .nil]) y =
          .ok (.tuple #[k, .atom "open", .nil])) ∧
        (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«map_union/2» x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil])) ∧
        (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«map_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y) := by
      refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => map_union_bdd⟩
      · unfold Elixir.Module.Types.Descr.«map_union/2»; rfl
      · unfold Elixir.Module.Types.Descr.«map_union/2»
        split <;> simp_all

    theorem map_inter_shape : (∀ k y, Elixir.Module.Types.Descr.«map_intersection/2» (.tuple #[k, .atom "open", .nil]) y =
          .ok y) ∧
        (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«map_intersection/2» x (.tuple #[k, .atom "open", .nil]) = .ok x) ∧
        (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«map_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y) := by
      refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => map_intersection_bdd⟩
      · unfold Elixir.Module.Types.Descr.«map_intersection/2»; rfl
      · unfold Elixir.Module.Types.Descr.«map_intersection/2»
        split <;> simp_all

    theorem neg_drop {a b : Bool} (sem : a = !b) (drop : a = Bool.false) : b = Bool.true := by
      subst drop; cases b <;> simp_all

    theorem mapOk_not : ∀ t, MapOk t → ¬IsTop t := fun _ h => h.2

    theorem map_difference_neg {x : Term} (nt : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) (arr : Array Term)
        (hx : x = .tuple arr) {top : Int} :
        Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer top, .atom "open", .nil]) x =
          Elixir.Module.Types.Descr.«bdd_negation/1» x := by
      subst hx
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      split
      · next heq => exact absurd heq (nt _)
      · next heq => rw [heq]
      · next h₁ h₂ => exact absurd rfl (h₂ _ _ rfl)

    theorem map_neg_spec {x : Term} (fx : OField MapOk x) :
        ∃ w, Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w ∧
          (kept (.atom "map", w) = Bool.true → OField MapOk w ∧ ∀ ρ, Resp ρ → denO w ρ = !denO x ρ) ∧
          (kept (.atom "map", w) = Bool.false → ∀ ρ, Resp ρ → denO x ρ = Bool.true) := by
      rcases fx with ⟨k, rfl⟩ | wx
      · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl, fun k => by simp [kept] at k,
          fun _ ρ _ => denO_top _ ρ⟩
      rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, fun _ ρ _ => by simp [denO, isOpenTop]⟩
        unfold Elixir.Module.Types.Descr.«map_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
      · refine ⟨_, ?_, fun _ => ⟨Or.inl ⟨61102469, rfl⟩, fun ρ _ => by simp [denO, isOpenTop]⟩, fun k => by simp [kept] at k⟩
        unfold Elixir.Module.Types.Descr.«map_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
      all_goals
        obtain ⟨w, run, keep, sem⟩ := neg_ok wx
        have ww := keep _ wx
        refine ⟨w, ?_, fun _ => ⟨Or.inr ww, fun ρ resp => by
          rw [denO_bdd mapOk_not ww, denO_bdd mapOk_not wx, sem ρ resp]⟩, fun kk ρ resp => ?_⟩
        · rw [map_difference_neg (not_top_of_ok wx mapOk_not) _ rfl, run]
        · rw [denO_bdd mapOk_not wx]
          exact neg_drop (sem ρ resp) (drop_bdd ww kk ρ)

    theorem map_difference_bdd {a y : Term} (na : ∀ k, a ≠ .tuple #[k, .atom "open", .nil])
        (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
        Elixir.Module.Types.Descr.«map_difference/2» a y = Elixir.Module.Types.Descr.«bdd_difference/2» a y := by
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      split
      · exfalso; simp_all
      · exfalso; simp_all
      · rfl

    theorem mapOk_lit : ∀ t, MapOk t → MapLit t := fun _ h => h.1.lit

    theorem map_sub_spec (n : Nat) {a : Term} (fa : OField MapOk a) (b : Option Term)
        (fb : ∀ y, b = some y → OField MapOk y)
        (incl : ∀ ρ, Resp ρ → denO a ρ = Bool.true → b.elim Bool.false (denO · ρ) = Bool.true) :
        (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«map_difference/2» a y = .ok w ∧
          (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
            Elixir.Module.Types.Descr.«map_empty?/2» (D (n + 3)) w (.map []) = .ok (.atom "true"))) ∧
        (b = Option.none → Elixir.Module.Types.Descr.«map_empty?/2» (D (n + 3)) a (.map []) = .ok (.atom "true")) := by
      refine ⟨fun y hb => ?_, fun hb => ?_⟩
      · subst hb
        rcases fb y rfl with ⟨k', rfl⟩ | wy
        · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl, Or.inr (Or.inl rfl)⟩
        have ny := not_top_of_ok wy mapOk_not
        rcases fa with ⟨k, rfl⟩ | wa
        · have taut : ∀ ρ, Resp ρ → eval ρ y = Bool.true := fun ρ resp => by
            have := incl ρ resp (denO_top _ ρ)
            simpa [Option.elim, denO_bdd mapOk_not wy] using this
          rcases wy.shape with rfl | rfl | ⟨k', x', z', rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
          · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
            unfold Elixir.Module.Types.Descr.«map_difference/2»
            unfold Elixir.Module.Types.Descr.«bdd_difference/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
          · have := taut _ (resp_const Bool.true); simp at this
          all_goals
            obtain ⟨w, run, keep, sem⟩ := neg_ok wy
            refine ⟨w, by rw [map_difference_neg ny _ rfl, run], Or.inr (Or.inr ?_)⟩
            exact map_empty_unsat (keep _ wy) mapOk_lit (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) n []
        · obtain ⟨w, run, keep, sem⟩ := diff_ok wa wy
          refine ⟨w, by rw [map_difference_bdd (not_top_of_ok wa mapOk_not) ny, run], Or.inr (Or.inr ?_)⟩
          refine map_empty_unsat (keep _ wa wy) mapOk_lit (fun ρ resp => ?_) n []
          rw [sem ρ resp]
          cases e : eval ρ a
          · rfl
          · have := incl ρ resp (by rw [denO_bdd mapOk_not wa, e])
            simp only [Option.elim, denO_bdd mapOk_not wy] at this
            simp [this]
      · subst hb
        rcases fa with ⟨k, rfl⟩ | wa
        · have := incl _ (resp_const Bool.true) (denO_top _ _)
          simp [Option.elim] at this
        · refine map_empty_unsat wa mapOk_lit (fun ρ resp => ?_) n []
          cases e : eval ρ a
          · rfl
          · have := incl ρ resp (by rw [denO_bdd mapOk_not wa, e])
            simp [Option.elim] at this

    theorem tuple_union_shape :
        (∀ k y, Elixir.Module.Types.Descr.«tuple_union/2» (.tuple #[k, .atom "open", .nil]) y =
          .ok (.tuple #[k, .atom "open", .nil])) ∧
        (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«tuple_union/2» x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil])) ∧
        (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«tuple_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y) := by
      refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => tuple_union_bdd⟩
      · unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl
      · unfold Elixir.Module.Types.Descr.«tuple_union/2»
        split <;> simp_all

    theorem tuple_inter_shape :
        (∀ k y, Elixir.Module.Types.Descr.«tuple_intersection/2» (.tuple #[k, .atom "open", .nil]) y = .ok y) ∧
        (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«tuple_intersection/2» x (.tuple #[k, .atom "open", .nil]) = .ok x) ∧
        (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
          Elixir.Module.Types.Descr.«tuple_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y) := by
      refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => tuple_intersection_bdd⟩
      · unfold Elixir.Module.Types.Descr.«tuple_intersection/2»; rfl
      · unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
        split <;> simp_all

    theorem tupleOk_not : ∀ t, TupleOk t → ¬IsTop t := fun _ h => h.2

    /-- The difference of the top tuple and `{}`: tuples with at least one element. -/
    theorem tuple_minus_empty (k : Int) : ∃ H : Int, Elixir.Module.Types.Descr.«tuple_difference/2»
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "closed", .nil]) =
          .ok (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) := by
      obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
      refine ⟨(1 <<< 27) + hash, ?_⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
        Elixir.Module.Types.Descr.«bdd_leaf_key/2», Lynx.Except.guard, Erlang.erlang.«is_list/1»,
        Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»]
      rfl

    theorem tuple_difference_neg {x : Term} (nt : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
        (ne : ∀ k, x ≠ .tuple #[k, .atom "closed", .nil]) (arr : Array Term) (hx : x = .tuple arr) {top : Int} :
        Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer top, .atom "open", .nil]) x =
          Elixir.Module.Types.Descr.«bdd_negation/1» x := by
      subst hx
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split
      · exfalso; simp_all
      · exfalso; simp_all
      · next heq => rw [heq]
      · next h₁ h₂ h₃ => exact absurd rfl (h₃ _ _ rfl)

    theorem tuple_difference_bdd {a y : Term} (na : ∀ k, a ≠ .tuple #[k, .atom "open", .nil])
        (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
        (special : ¬((∃ k e, a = .tuple #[k, .atom "open", e]) ∧ ∃ k, y = .tuple #[k, .atom "closed", .nil])) :
        Elixir.Module.Types.Descr.«tuple_difference/2» a y = Elixir.Module.Types.Descr.«bdd_difference/2» a y := by
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split
      · exfalso; simp_all
      · next heq₁ heq₂ => exact absurd ⟨⟨_, _, rfl⟩, ⟨_, rfl⟩⟩ special
      · exfalso; simp_all
      · rfl

    theorem tuple_neg_spec {x : Term} (fx : OField TupleOk x) :
        ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w ∧
          (kept (.atom "tuple", w) = Bool.true → OField TupleOk w ∧ ∀ ρ, Resp ρ → Real ρ → denO w ρ = !denO x ρ) ∧
          (kept (.atom "tuple", w) = Bool.false → ∀ ρ, Resp ρ → Real ρ → denO x ρ = Bool.true) := by
      rcases fx with ⟨k, rfl⟩ | wx
      · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, fun k => by simp [kept] at k,
          fun _ ρ _ _ => denO_top _ ρ⟩
      have nt := not_top_of_ok wx tupleOk_not
      rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, fun _ ρ _ _ => by simp [denO, isOpenTop]⟩
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
      · refine ⟨_, ?_, fun _ => ⟨Or.inl ⟨61102469, rfl⟩, fun ρ _ _ => by simp [denO, isOpenTop]⟩,
          fun k => by simp [kept] at k⟩
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
      · by_cases special : a = .atom "closed" ∧ b = .nil
        · obtain ⟨rfl, rfl⟩ := special
          obtain ⟨H, run⟩ := tuple_minus_empty k
          have lit : TupleOk (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) :=
            ⟨⟨H, "open", [.atom "term"], rfl, Or.inl rfl, by simp [ElemTerm]⟩, fun ⟨_, e⟩ => by simp [Term.list] at e⟩
          refine ⟨_, run, fun _ => ⟨Or.inr (Bdd.leaf_iff.mpr lit), fun ρ _ ⟨e, c⟩ => ?_⟩, fun k => by simp [kept] at k⟩
          simp only [denO, isOpenTop, Term.list, eval_leaf, Bool.false_or]
          rw [c.2.1 _ ⟨_, rfl⟩, c.1 _ ⟨_, rfl⟩]
        · have ne : ∀ k', Term.tuple #[.integer k, a, b] ≠ .tuple #[k', .atom "closed", .nil] := by
            intro k' e; simp at e; exact special ⟨e.2.1, e.2.2⟩
          obtain ⟨w, run, keep, sem⟩ := neg_ok wx
          have ww := keep _ wx
          exact ⟨w, by rw [tuple_difference_neg nt ne _ rfl, run], fun _ => ⟨Or.inr ww, fun ρ resp _ => by
            rw [denO_bdd tupleOk_not ww, denO_bdd tupleOk_not wx, sem ρ resp]⟩, fun kk ρ resp _ => by
            rw [denO_bdd tupleOk_not wx]; exact neg_drop (sem ρ resp) (drop_bdd ww kk ρ)⟩
      · obtain ⟨w, run, keep, sem⟩ := neg_ok wx
        have ww := keep _ wx
        exact ⟨w, by rw [tuple_difference_neg nt (fun _ e => by simp at e) _ rfl, run], fun _ => ⟨Or.inr ww,
          fun ρ resp _ => by rw [denO_bdd tupleOk_not ww, denO_bdd tupleOk_not wx, sem ρ resp]⟩, fun kk ρ resp _ => by
          rw [denO_bdd tupleOk_not wx]; exact neg_drop (sem ρ resp) (drop_bdd ww kk ρ)⟩

    theorem real_realize (e : Bool) : Real (realize e) := ⟨e, realize_consistent e⟩

    theorem tuple_sub_spec (n : Nat) {a : Term} (fa : OField TupleOk a) (b : Option Term)
        (fb : ∀ y, b = some y → OField TupleOk y)
        (incl : ∀ ρ, Resp ρ → Real ρ → denO a ρ = Bool.true → b.elim Bool.false (denO · ρ) = Bool.true) :
        (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» a y = .ok w ∧
          (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
            Elixir.Module.Types.Descr.«tuple_empty?/2» (D (n + 2)) w (.map []) = .ok (.atom "true"))) ∧
        (b = Option.none → Elixir.Module.Types.Descr.«tuple_empty?/2» (D (n + 2)) a (.map []) = .ok (.atom "true")) := by
      have realF := realize_resp Bool.false
      have consF := realize_consistent Bool.false
      refine ⟨fun y hb => ?_, fun hb => ?_⟩
      · subst hb
        rcases fb y rfl with ⟨k', rfl⟩ | wy
        · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, Or.inr (Or.inl rfl)⟩
        have ny := not_top_of_ok wy tupleOk_not
        have yE : ∀ k, y = .tuple #[k, .atom "closed", .nil] → denO a (realize Bool.false) = Bool.false := by
          intro k e
          cases ha : denO a (realize Bool.false)
          · rfl
          · have := incl _ realF (real_realize _) ha
            simp only [Option.elim, e, denO, isOpenTop, eval_leaf, Bool.false_or] at this
            rw [consF.1 _ ⟨_, rfl⟩] at this
            cases this
        rcases fa with ⟨k, rfl⟩ | wa
        · have taut : ∀ ρ, Resp ρ → Real ρ → eval ρ y = Bool.true := fun ρ resp real => by
            have := incl ρ resp real (denO_top _ ρ)
            simpa [Option.elim, denO_bdd tupleOk_not wy] using this
          rcases wy.shape with rfl | rfl | ⟨k', x', z', rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
          · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
            unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            unfold Elixir.Module.Types.Descr.«bdd_difference/2»
            simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
          · have := taut _ realF (real_realize _); simp at this
          · by_cases special : x' = .atom "closed" ∧ z' = .nil
            · obtain ⟨rfl, rfl⟩ := special
              have := yE _ rfl
              simp [denO, isOpenTop] at this
            have ne : ∀ k'', Term.tuple #[.integer k', x', z'] ≠ .tuple #[k'', .atom "closed", .nil] := by
              intro k'' e; simp at e; exact special ⟨e.2.1, e.2.2⟩
            obtain ⟨w, run, keep, sem⟩ := neg_ok wy
            refine ⟨w, ?_, Or.inr (Or.inr (tuple_empty_real n (fun _ h => h) (keep _ wy) fun ρ resp real => ?_))⟩
            · rw [tuple_difference_neg ny ne _ rfl, run]
            · rw [sem ρ resp, taut ρ resp real]; rfl
          · obtain ⟨w, run, keep, sem⟩ := neg_ok wy
            refine ⟨w, ?_, Or.inr (Or.inr (tuple_empty_real n (fun _ h => h) (keep _ wy) fun ρ resp real => ?_))⟩
            · rw [tuple_difference_neg ny (fun _ e => by simp at e) _ rfl, run]
            · rw [sem ρ resp, taut ρ resp real]; rfl
        · have na := not_top_of_ok wa tupleOk_not
          by_cases special : (∃ k e, a = .tuple #[k, .atom "open", e]) ∧ ∃ k, y = .tuple #[k, .atom "closed", .nil]
          · obtain ⟨⟨k, e, rfl⟩, ⟨k', hy⟩⟩ := special
            have := yE k' hy
            obtain ⟨⟨k₀, tag, l, eq, -, -⟩, notTop⟩ : TupleOk (.tuple #[k, .atom "open", e]) := by
              rcases wa.shape with h | h | ⟨k₁, x₁, y₁, h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact Bdd.leaf_iff.mp wa
            simp at eq
            obtain ⟨rfl, -, rfl⟩ := eq
            have notE : ¬IsE' (.tuple #[.integer k₀, .atom "open", Term.list l]) := fun ⟨_, e⟩ => by simp at e
            simp only [denO, eval_leaf] at this
            have r : realize Bool.false (.tuple #[.integer k₀, .atom "open", Term.list l]) = Bool.true := by
              by_cases h : IsH' (.tuple #[.integer k₀, .atom "open", Term.list l]) <;> simp [realize, notE, h]
            simp [r] at this
          obtain ⟨w, run, keep, sem⟩ := diff_ok wa wy
          refine ⟨w, by rw [tuple_difference_bdd na ny special, run],
            Or.inr (Or.inr (tuple_empty_real n (fun _ h => h) (keep _ wa wy) fun ρ resp real => ?_))⟩
          rw [sem ρ resp]
          cases e : eval ρ a
          · rfl
          · have := incl ρ resp real (by rw [denO_bdd tupleOk_not wa, e])
            simp only [Option.elim, denO_bdd tupleOk_not wy] at this
            simp [this]
      · subst hb
        rcases fa with ⟨k, rfl⟩ | wa
        · have := incl _ realF (real_realize _) (denO_top _ _)
          simp [Option.elim] at this
        · refine tuple_empty_real n (fun _ h => h) wa fun ρ resp real => ?_
          cases e : eval ρ a
          · rfl
          · have := incl ρ resp real (by rw [denO_bdd tupleOk_not wa, e])
            simp [Option.elim] at this

    /-! Bitmap fields. -/

    def BitField (x : Term) : Prop := ∃ b : Nat, x = .integer b ∧ 1 ≤ b ∧ b ≤ 255

    theorem bitOf_nat (b i : Nat) : bitOf (.integer b) i = b.testBit i := by simp [bitOf]

    theorem small_bit {b i : Nat} (le : b ≤ 255) (h : b.testBit i = Bool.true) : i < 8 := by
      refine Classical.byContradiction fun hi => ?_
      have : b < 2 ^ i := Nat.lt_of_lt_of_le (by omega : b < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow this] at h
      cases h

    theorem bit_union (d : Dispatcher) {x y : Term} (fx : BitField x) (fy : BitField y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "bitmap") x y = .ok w ∧ BitField w ∧
          ∀ i, bitOf w i = (bitOf x i || bitOf y i) := by
      obtain ⟨a, rfl, a1, a2⟩ := fx
      obtain ⟨b, rfl, b1, b2⟩ := fy
      refine ⟨.integer ↑(a ||| b), ?_, ⟨a ||| b, rfl, Nat.le_trans a1 Nat.left_le_or, ?_⟩, fun i => by
        simp [bitOf_nat, Nat.testBit_or]⟩
      · simp [Elixir.Module.Types.Descr.«bare_union/3», Erlang.erlang.«bor/2»]
      · have := Nat.or_lt_two_pow (n := 8) (by omega : a < 2 ^ 8) (by omega : b < 2 ^ 8)
        omega

    theorem bit_inter (d : Dispatcher) {x y : Term} (fx : BitField x) (fy : BitField y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "bitmap") x y = .ok w ∧
          (kept (.atom "bitmap", w) = Bool.true → BitField w ∧ ∀ i, bitOf w i = (bitOf x i && bitOf y i)) ∧
          (kept (.atom "bitmap", w) = Bool.false → ∀ i, (bitOf x i && bitOf y i) = Bool.false) := by
      obtain ⟨a, rfl, a1, a2⟩ := fx
      obtain ⟨b, rfl, b1, b2⟩ := fy
      refine ⟨.integer ↑(a &&& b), by simp [Elixir.Module.Types.Descr.«bare_intersection/3», bandI], fun k => ⟨?_, fun i => by
        simp [bitOf_nat, Nat.testBit_and]⟩, fun k i => ?_⟩
      · have le : a &&& b ≤ a := Nat.and_le_left
        refine ⟨a &&& b, rfl, ?_, by omega⟩
        by_cases zero : a &&& b = 0
        · simp [kept, zero] at k
        · omega
      · have zero : a &&& b = 0 := by
          rcases dropped k with h | h <;> simp at h
          omega
        have := congrArg (·.testBit i) zero
        simp only [Nat.testBit_and, Nat.zero_testBit] at this
        simp [bitOf_nat, this]

    theorem bit_neg (d : Dispatcher) {x : Term} (fx : BitField x) :
        ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "bitmap") (.integer 255) x = .ok w ∧
          (kept (.atom "bitmap", w) = Bool.true → BitField w ∧ ∀ i, i < 8 → bitOf w i = !bitOf x i) ∧
          (kept (.atom "bitmap", w) = Bool.false → ∀ i, i < 8 → bitOf x i = Bool.true) := by
      obtain ⟨b, rfl, b1, b2⟩ := fx
      have band := band_255 b2
      have bit255 : ∀ i, i < 8 → (255 : Nat).testBit i = Bool.true := by decide
      refine ⟨.integer ↑(255 - b), ?_, fun k => ⟨⟨255 - b, rfl, ?_, by omega⟩, fun i lt => ?_⟩, fun k i lt => ?_⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]
        omega
      · by_cases zero : 255 - b = 0
        · simp [kept, zero] at k
        · omega
      · have := testBit_sub_and 255 b i
        rw [band] at this
        simp [bitOf_nat, this, bit255 i lt]
      · have zero : 255 - b = 0 := by
          rcases dropped k with h | h <;> simp at h
          omega
        have : b = 255 := by omega
        subst this
        simpa [bitOf] using bit255 i lt

    theorem bit_sub (d : Dispatcher) {a : Term} (fa : BitField a) (b : Option Term) (fb : ∀ y, b = some y → BitField y)
        (incl : ∀ i, i < 8 → bitOf a i = Bool.true → b.elim Bool.false (bitOf · i) = Bool.true) :
        (∀ y, b = some y → Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "bitmap") a y = .ok (.integer 0)) ∧
        b ≠ Option.none := by
      obtain ⟨x, rfl, x1, x2⟩ := fa
      refine ⟨fun y hb => ?_, fun hb => ?_⟩
      · subst hb
        obtain ⟨z, rfl, -, z2⟩ := fb _ rfl
        have sub : x &&& z = x := Nat.eq_of_testBit_eq fun i => by
          simp only [Nat.testBit_and]
          cases h : x.testBit i
          · rfl
          · have := incl i (small_bit x2 h) (by simp [bitOf_nat, h])
            simp [Option.elim, bitOf_nat] at this
            simp [this]
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», bandI, sub]
      · subst hb
        obtain ⟨i, hi⟩ : ∃ i, x.testBit i = Bool.true := Nat.exists_testBit_of_ne_zero (by omega)
        have := incl i (small_bit x2 hi) (by simp [bitOf_nat, hi])
        simp [Option.elim] at this

    /-! Atom fields. -/

    def AtomF (x : Term) : Prop := AtomField x ∧ ∃ q, amemV (some x) q = Bool.true

    theorem atom_union_spec (d : Dispatcher) {x y : Term} (fx : AtomF x) (fy : AtomF y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "atom") x y = .ok w ∧ AtomF w ∧
          ∀ q, amemV (some w) q = (amemV (some x) q || amemV (some y) q) := by
      obtain ⟨⟨p₁, S₁, rfl, set₁⟩, q, hq⟩ := fx
      obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fy
      obtain ⟨p, E, run, setE, mem⟩ := atom_union p₁ S₁ p₂ S₂ set₁ set₂
      have sem : ∀ q, amemV (some (.tuple #[.atom (if p then "union" else "negation"), .map E])) q =
          (amemV (some (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])) q ||
            amemV (some (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂])) q) := by
        intro q; rw [amemV_field, amemV_field, amemV_field, mem q]
      exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], ⟨⟨p, E, rfl, setE⟩, q, by rw [sem q, hq]; rfl⟩, sem⟩

    theorem atom_inter_spec (d : Dispatcher) {x y : Term} (fx : AtomF x) (fy : AtomF y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "atom") x y = .ok w ∧
          (kept (.atom "atom", w) = Bool.true → AtomF w ∧
            ∀ q, amemV (some w) q = (amemV (some x) q && amemV (some y) q)) ∧
          (kept (.atom "atom", w) = Bool.false → ∀ q, (amemV (some x) q && amemV (some y) q) = Bool.false) := by
      obtain ⟨⟨p₁, S₁, rfl, set₁⟩, -⟩ := fx
      obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fy
      rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, run, setE, -, ne, mem⟩ | ⟨run, mem⟩
      · refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun _ => ⟨⟨⟨p, E, rfl, setE⟩,
          atom_nonempty p E ne⟩, fun q => ?_⟩, fun k => by simp [kept] at k⟩
        rw [amemV_field, amemV_field, amemV_field, mem q]
      · refine ⟨.integer 0, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun k => by simp [kept] at k,
          fun _ q => ?_⟩
        rw [amemV_field, amemV_field]
        exact mem q

    theorem atom_neg_spec (d : Dispatcher) {x : Term} (fx : AtomF x) :
        ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "atom") (.tuple #[.atom "negation", .map []]) x =
            .ok w ∧
          (kept (.atom "atom", w) = Bool.true → AtomF w ∧ ∀ q, amemV (some w) q = !amemV (some x) q) ∧
          (kept (.atom "atom", w) = Bool.false → ∀ q, amemV (some x) q = Bool.true) := by
      obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fx
      have top : ∀ q, amemV (some (.tuple #[.atom "negation", .map []])) q = Bool.true := by
        intro q; simp [amemV, mapLookup]
      rcases atom_difference Bool.false [] p₂ S₂ no_atoms set₂ with ⟨p, E, run, setE, -, ne, mem⟩ | ⟨run, mem⟩
      · refine ⟨_, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, fun _ => ⟨⟨⟨p, E, rfl, setE⟩,
          atom_nonempty p E ne⟩, fun q => ?_⟩, fun k => by simp [kept] at k⟩
        have := mem q
        rw [amemV_field, amemV_field, this]
        simp [mapLookup]
      · refine ⟨_, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, fun k => by simp [kept] at k,
          fun _ q => ?_⟩
        have := mem q
        rw [amemV_field]
        have empty : (mapLookup ([] : List (Term × Term)) q).isSome = Bool.false := by simp [mapLookup]
        rw [empty] at this
        cases p₂ <;> cases h : (mapLookup S₂ q).isSome <;> simp_all

    theorem atom_sub_spec (d : Dispatcher) {a : Term} (fa : AtomF a) (b : Option Term) (fb : ∀ y, b = some y → AtomF y)
        (incl : ∀ q, amemV (some a) q = Bool.true → b.elim Bool.false (fun y => amemV (some y) q) = Bool.true) :
        (∀ y, b = some y → Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "atom") a y = .ok (.integer 0)) ∧
        b ≠ Option.none := by
      obtain ⟨⟨p₁, S₁, rfl, set₁⟩, q₀, hq₀⟩ := fa
      refine ⟨fun y hb => ?_, fun hb => ?_⟩
      · subst hb
        obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fb _ rfl
        have none : ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome)) = Bool.false := by
          intro q
          have := incl q
          rw [amemV_field] at this
          simp only [Option.elim, amemV_field] at this
          cases h₁ : (p₁ == (mapLookup S₁ q).isSome) <;> simp_all
        rcases atom_difference p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, run, -, -, ne, mem⟩ | ⟨run, -⟩
        · exfalso
          obtain ⟨q, hq⟩ := atom_nonempty p E ne
          rw [amemV_field, mem q, none q] at hq
          cases hq
        · simp [Elixir.Module.Types.Descr.«bare_difference/3», run]
      · subst hb
        have := incl q₀ hq₀
        simp [Option.elim] at this

    /-! Function fields: per arity, the propositional semantics of its BDD, negated for negations. -/

    theorem repr_diff_step (g : Term → Term → Term → Term) (acc : List (Term × Term)) (key v₂ : Term)
        (calls : ∀ v₁, mapLookup acc key = some v₁ →
          Elixir.Module.Types.Descr.«bdd_difference/2» v₁ v₂ = .ok (g key v₁ v₂)) :
        Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3» key v₂ (.map acc) =
          .ok (.map (differenceStep g acc (key, v₂))) := by
      unfold Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3»
      cases found : mapLookup acc key with
      | none => simp [getMapKeys_single, found, differenceStep]
      | some v₁ =>
        simp only [getMapKeys_single, found, Option.toList_some, calls v₁ found, Lynx.Except.ok_bind, member_dropped key,
          differenceStep]
        obtain ⟨e, member, same⟩ := (mapLookup_isSome acc key).mp (by simp [found])
        by_cases keep : kept (key, g key v₁ v₂) <;> simp [keep, Erlang.erlang.«is_map/1», Erlang.maps.«update/3»,
          Erlang.maps.«remove/2»]
        exact ⟨e.1, ⟨e.2, member⟩, same⟩

    theorem repr_diff_fold (n : Nat) (g : Term → Term → Term → Term) (es acc : List (Term × Term))
        (distinct : es.Pairwise (fun a b => exactCompare a.1 b.1 ≠ .eq))
        (calls : ∀ e ∈ es, ∀ v₁, mapLookup acc e.1 = some v₁ →
          Elixir.Module.Types.Descr.«bdd_difference/2» v₁ e.2 = .ok (g e.1 v₁ e.2)) :
        ∃ M, es.foldlM (fun acc entry =>
            (Dispatch.dispatch (D n) (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
              #[entry.1, entry.2, acc] : Except Exception Term)) (.map acc) = .ok (.map M) ∧
          ∀ q, mapLookup M q =
            match es.find? (fun e => decide (exactCompare q e.1 = .eq)) with
            | some e => (mapLookup acc e.1).bind fun v₁ =>
                if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none
            | none => mapLookup acc q := by
      induction es generalizing acc with
      | nil => exact ⟨acc, rfl, fun q => rfl⟩
      | cons e rest ih =>
        have apart := List.pairwise_cons.mp distinct
        have step : (Dispatch.dispatch (D n) (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
            #[e.1, e.2, .map acc] : Except Exception Term) = .ok (.map (differenceStep g acc e)) := by
          rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_difference/2-fun-0-/3».pure,
            repr_diff_step g acc e.1 e.2 (calls e (List.mem_cons_self ..))]
        obtain ⟨M, run, look⟩ := ih (differenceStep g acc e) apart.2 (by
          intro e' member v₁ found
          rw [step_other g acc e e'.1 (fun same => apart.1 e' member (Std.OrientedCmp.eq_symm same))] at found
          exact calls e' (List.mem_cons_of_mem _ member) v₁ found)
        refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_⟩
        rw [look q]
        by_cases same : exactCompare q e.1 = .eq
        · have absent : rest.find? (fun p => decide (exactCompare q p.1 = .eq)) = none := by
            rw [List.find?_eq_none]
            intro p member hit
            exact apart.1 p member (Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm same) (of_decide_eq_true hit))
          simp only [absent, List.find?_cons, same, decide_true]
          exact step_same g acc e q same
        · simp only [List.find?_cons, same, decide_false]
          cases hit : rest.find? (fun p => decide (exactCompare q p.1 = .eq)) with
          | none => exact step_other g acc e q same
          | some e' =>
            have qe' : exactCompare q e'.1 = .eq := by simpa using List.find?_some hit
            have other : exactCompare e'.1 e.1 ≠ .eq := fun same' => same (Std.TransCmp.eq_trans qe' same')
            simp only
            rw [step_other g acc e e'.1 other]

    def evalR (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) : Bool := (mapLookup R a).elim Bool.false (eval ρ)

    def AllBdd (R : List (Term × Term)) : Prop := ∀ q v, mapLookup R q = some v → Bdd (fun _ => True) v

    theorem repr_union_sem (n : Nat) {R₁ R₂ : List (Term × Term)} (b₁ : AllBdd R₁) (b₂ : AllBdd R₂) :
        ∃ M, Elixir.Module.Types.Descr.«fun_repr_union/2» (D (n + 1)) (.map R₁) (.map R₂) = .ok (.map M) ∧ AllBdd M ∧
          ∀ a ρ, Resp ρ → evalR M a ρ = (evalR R₁ a ρ || evalR R₂ a ρ) := by
      let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bdd_union/2» v₁ v₂ with | .ok w => w | .error _ => .nil
      have gspec : ∀ k v₁ v₂, Bdd (fun _ => True) v₁ → Bdd (fun _ => True) v₂ →
          Elixir.Module.Types.Descr.«bdd_union/2» v₁ v₂ = .ok (g k v₁ v₂) ∧ Bdd (fun _ => True) (g k v₁ v₂) ∧
            ∀ ρ, Resp ρ → eval ρ (g k v₁ v₂) = (eval ρ v₁ || eval ρ v₂) := by
        intro k v₁ v₂ w₁ w₂
        obtain ⟨r, run, keep, sem⟩ := union_ok w₁ w₂
        have : g k v₁ v₂ = r := by simp [g, run]
        rw [this]
        exact ⟨run, keep _ w₁ w₂, sem⟩
      obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup (D (n + 1)) "Elixir.Module.Types.Descr"
        "-fun_repr_union/2-fun-0-" #[] R₁ R₂ g (by
          intro e me v hv
          rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_union/2-fun-0-/3».pure]
          simp only [Elixir.Module.Types.Descr.«-fun_repr_union/2-fun-0-/3»]
          exact (gspec e.1 _ _ (b₁ _ _ hv) (b₂ _ _ (mapLookup_of_mem_mapEntries me))).1)
      have shape : ∀ a, (∃ v₁ v₂, mapLookup R₁ a = some v₁ ∧ mapLookup R₂ a = some v₂ ∧
          mapLookup out a = some (g a v₁ v₂)) ∨ (mapLookup R₂ a = none ∧ mapLookup out a = mapLookup R₁ a) ∨
          (mapLookup R₁ a = none ∧ mapLookup out a = mapLookup R₂ a) := by
        intro a
        rw [look a]
        cases hit : (mapEntries R₂).find? (fun e => decide (exactCompare a e.1 = .eq)) with
        | none => exact Or.inr (Or.inl ⟨find_none hit, rfl⟩)
        | some e =>
          obtain ⟨qe, h₂⟩ := find_entry hit
          cases h₁ : mapLookup R₁ e.1 with
          | none =>
            refine Or.inr (Or.inr ⟨by rw [mapLookup_congr qe]; exact h₁, by simp [h₁, h₂]⟩)
          | some v₁ =>
            exact Or.inl ⟨v₁, e.2, by rw [mapLookup_congr qe]; exact h₁, h₂, by simp [h₁]; rfl⟩
      refine ⟨out, by simp [Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», run],
        fun q v h => ?_, fun a ρ resp => ?_⟩
      · rcases shape q with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
        · cases h; exact (gspec q _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1
        · exact b₁ _ _ h
        · exact b₂ _ _ h
      · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨h₂, h₃⟩ | ⟨h₁, h₃⟩ <;> simp only [evalR, h₃]
        · simp [h₁, h₂, (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.2 ρ resp]
        · simp [h₂]
        · simp [h₁]

    theorem repr_inter_sem (n : Nat) {R₁ R₂ : List (Term × Term)} (b₁ : AllBdd R₁) (b₂ : AllBdd R₂) :
        ∃ M, Elixir.Module.Types.Descr.«fun_repr_intersection/2» (D (n + 1)) (.map R₁) (.map R₂) = .ok (.map M) ∧
          AllBdd M ∧ ∀ a ρ, Resp ρ → evalR M a ρ = (evalR R₁ a ρ && evalR R₂ a ρ) := by
      let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bdd_intersection/2» v₁ v₂ with | .ok w => w | .error _ => .nil
      have gspec : ∀ k v₁ v₂, Bdd (fun _ => True) v₁ → Bdd (fun _ => True) v₂ →
          Elixir.Module.Types.Descr.«bdd_intersection/2» v₁ v₂ = .ok (g k v₁ v₂) ∧ Bdd (fun _ => True) (g k v₁ v₂) ∧
            ∀ ρ, Resp ρ → eval ρ (g k v₁ v₂) = (eval ρ v₁ && eval ρ v₂) := by
        intro k v₁ v₂ w₁ w₂
        obtain ⟨r, run, keep, sem⟩ := inter_ok w₁ w₂
        have : g k v₁ v₂ = r := by simp [g, run]
        rw [this]
        exact ⟨run, keep _ w₁ w₂, sem⟩
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (n + 1)) "Elixir.Module.Types.Descr"
        "-fun_repr_intersection/2-fun-0-" #[] R₁ R₂ g (by
          intro e me v hv
          rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_intersection/2-fun-0-/3».pure]
          simp only [Elixir.Module.Types.Descr.«-fun_repr_intersection/2-fun-0-/3»]
          exact (gspec e.1 _ _ (b₁ _ _ (mapLookup_of_mem_mapEntries me)) (b₂ _ _ hv)).1)
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (n + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] I kept (by
          intro e _
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
      have shape : ∀ a, (∃ v₁ v₂, mapLookup R₁ a = some v₁ ∧ mapLookup R₂ a = some v₂ ∧
          mapLookup out a = if kept (a, g a v₁ v₂) then some (g a v₁ v₂) else none) ∨
          ((mapLookup R₁ a = none ∨ mapLookup R₂ a = none) ∧ mapLookup out a = none) := by
        intro a
        rw [lookO a]
        cases hitI : (mapEntries I).find? (fun e => decide (exactCompare a e.1 = .eq)) with
        | none =>
          have hI := find_none hitI
          rw [lookI a] at hI
          refine Or.inr ⟨?_, rfl⟩
          cases hit : (mapEntries R₁).find? (fun e => decide (exactCompare a e.1 = .eq)) with
          | none => exact Or.inl (find_none hit)
          | some e =>
            rw [hit] at hI
            obtain ⟨qe, -⟩ := find_entry hit
            right
            rw [mapLookup_congr qe]
            simpa using hI
        | some eI =>
          obtain ⟨qI, hI⟩ := find_entry hitI
          rw [lookI a] at hI
          cases hit : (mapEntries R₁).find? (fun e => decide (exactCompare a e.1 = .eq)) with
          | none => rw [hit] at hI; cases hI
          | some e =>
            rw [hit] at hI
            obtain ⟨qe, h₁⟩ := find_entry hit
            obtain ⟨v₂, h₂, value⟩ := Option.map_eq_some_iff.mp hI
            refine Or.inl ⟨e.2, v₂, h₁, by rw [mapLookup_congr qe]; exact h₂, ?_⟩
            have : kept eI = kept (a, g a e.2 v₂) := by unfold kept; rw [← value]
            show (if kept eI = Bool.true then some eI.2 else none) = _
            rw [this, ← value]
      refine ⟨out, ?_, fun q v h => ?_, fun a ρ resp => ?_⟩
      · simp [Elixir.Module.Types.Descr.«fun_repr_intersection/2»]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runO]
      · rcases shape q with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
        · split at h
          · cases h; exact (gspec q _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1
          · cases h
        · cases h
      · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨h₁₂, h₃⟩
        · have sem := (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.2 ρ resp
          by_cases k : kept (a, g a v₁ v₂) = Bool.true
          · simp [evalR, h₁, h₂, h₃, k, sem]
          · have := drop_bdd (ok := fun _ => True) (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1 (by simpa using k) ρ
            simp [evalR, h₁, h₂, h₃, k, ← sem, this]
        · rcases h₁₂ with h | h <;> simp [evalR, h, h₃]

    theorem repr_diff_sem (n : Nat) {R₁ R₂ : List (Term × Term)} (b₁ : AllBdd R₁) (b₂ : AllBdd R₂) :
        ∃ M, Elixir.Module.Types.Descr.«fun_repr_difference/2» (D n) (.map R₁) (.map R₂) = .ok (.map M) ∧
          AllBdd M ∧ ∀ a ρ, Resp ρ → evalR M a ρ = (evalR R₁ a ρ && !evalR R₂ a ρ) := by
      let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bdd_difference/2» v₁ v₂ with | .ok w => w | .error _ => .nil
      have gspec : ∀ k v₁ v₂, Bdd (fun _ => True) v₁ → Bdd (fun _ => True) v₂ →
          Elixir.Module.Types.Descr.«bdd_difference/2» v₁ v₂ = .ok (g k v₁ v₂) ∧ Bdd (fun _ => True) (g k v₁ v₂) ∧
            ∀ ρ, Resp ρ → eval ρ (g k v₁ v₂) = (eval ρ v₁ && !eval ρ v₂) := by
        intro k v₁ v₂ w₁ w₂
        obtain ⟨r, run, keep, sem⟩ := diff_ok w₁ w₂
        have : g k v₁ v₂ = r := by simp [g, run]
        rw [this]
        exact ⟨run, keep _ w₁ w₂, sem⟩
      obtain ⟨M, run, look⟩ := repr_diff_fold n g (mapEntries R₂) R₁ (mapEntries_distinct R₂) (by
        intro e me v hv
        exact (gspec e.1 _ _ (b₁ _ _ hv) (b₂ _ _ (mapLookup_of_mem_mapEntries me))).1)
      have shape : ∀ a, (∃ v₁ v₂, mapLookup R₁ a = some v₁ ∧ mapLookup R₂ a = some v₂ ∧
          mapLookup M a = if kept (a, g a v₁ v₂) then some (g a v₁ v₂) else none) ∨
          (mapLookup R₁ a = none ∧ mapLookup M a = none) ∨ (mapLookup R₂ a = none ∧ mapLookup M a = mapLookup R₁ a) := by
        intro a
        rw [look a]
        cases hit : (mapEntries R₂).find? (fun e => decide (exactCompare a e.1 = .eq)) with
        | none => exact Or.inr (Or.inr ⟨find_none hit, rfl⟩)
        | some e =>
          obtain ⟨qe, h₂⟩ := find_entry hit
          cases h₁ : mapLookup R₁ e.1 with
          | none => exact Or.inr (Or.inl ⟨by rw [mapLookup_congr qe]; exact h₁, by simp [h₁]⟩)
          | some v₁ =>
            refine Or.inl ⟨v₁, e.2, by rw [mapLookup_congr qe]; exact h₁, h₂, ?_⟩
            simp only [h₁, Option.bind_some]
            rfl
      refine ⟨M, ?_, fun q v h => ?_, fun a ρ resp => ?_⟩
      · simp only [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
        simpa using run
      · rcases shape q with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
        · split at h
          · cases h; exact (gspec q _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1
          · cases h
        · cases h
        · exact b₁ _ _ h
      · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨h₁, h₃⟩ | ⟨h₂, h₃⟩
        · have sem := (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.2 ρ resp
          by_cases k : kept (a, g a v₁ v₂) = Bool.true
          · simp [evalR, h₁, h₂, h₃, k, sem]
          · have := drop_bdd (ok := fun _ => True) (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1 (by simpa using k) ρ
            simp [evalR, h₁, h₂, h₃, k, ← sem, this]
        · simp [evalR, h₁, h₃]
        · simp [evalR, h₂, h₃]

    def FunF (x : Term) : Prop :=
      ∃ (pos : Bool) (R : List (Term × Term)), x = .tuple #[.atom (if pos then "union" else "negation"), .map R] ∧ AllBdd R

    theorem arity_tag (pos : Bool) (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) :
        arityOf (.tuple #[.atom (if pos then "union" else "negation"), .map R]) a ρ = (pos == evalR R a ρ) := by
      cases pos <;> cases h : evalR R a ρ <;> simp_all [arityOf, evalR]

    theorem size_cases (M : List (Term × Term)) :
        (Erlang.erlang.«map_size/1» (.map M) = .ok (.integer 0) ∧ ∀ q, mapLookup M q = none) ∨
          (∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s)) := by
      cases M with
      | nil => exact Or.inl ⟨rfl, fun q => by simp [mapLookup]⟩
      | cons e rest =>
        right
        refine ⟨_, ?_, rfl⟩
        simp [List.eraseDupsBy, List.eraseDupsBy.loop]
        exact fun h => loop_ne_nil _ _ _ [] h

    theorem evalR_none {M : List (Term × Term)} (none : ∀ q, mapLookup M q = Option.none) (a : Term) (ρ : Term → Bool) :
        evalR M a ρ = Bool.false := by simp [evalR, none a]

    theorem fun_union_spec (n : Nat) {x y : Term} (fx : FunF x) (fy : FunF y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom "fun") x y = .ok w ∧ FunF w ∧
          ∀ a ρ, Resp ρ → arityOf w a ρ = (arityOf x a ρ || arityOf y a ρ) := by
      obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
      obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
      simp only [arity_tag]
      cases p₁ <;> cases p₂
      · obtain ⟨M, run, bM, sem⟩ := repr_inter_sem n b₁ b₂
        refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
          ⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => ?_⟩
        rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
      · obtain ⟨M, run, bM, sem⟩ := repr_diff_sem (n + 1) b₁ b₂
        refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
          ⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => ?_⟩
        rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
      · obtain ⟨M, run, bM, sem⟩ := repr_diff_sem (n + 1) b₂ b₁
        refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
          ⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => ?_⟩
        rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
      · obtain ⟨M, run, bM, sem⟩ := repr_union_sem n b₁ b₂
        refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
          ⟨Bool.true, M, rfl, bM⟩, fun a ρ resp => ?_⟩
        rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl

    theorem arity_union (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) :
        arityOf (.tuple #[.atom "union", .map R]) a ρ = evalR R a ρ := by simp [arityOf, evalR]

    theorem arity_neg (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) :
        arityOf (.tuple #[.atom "negation", .map R]) a ρ = !evalR R a ρ := by simp [arityOf, evalR]

    theorem size_cons (e : Term × Term) (rest : List (Term × Term)) :
        ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map (e :: rest)) = .ok (.integer s) := by
      rcases size_cases (e :: rest) with ⟨_, none⟩ | h
      · have := none e.1
        simp [mapLookup, Std.ReflCmp.compare_self] at this
      · exact h

    /-- Function results: unions whose maps of arities are empty become `0`. -/
    theorem fun_finish (pos : Bool) (M : List (Term × Term)) (bM : AllBdd M) (target : Term → (Term → Bool) → Bool)
        (sem : ∀ a ρ, Resp ρ → (pos == evalR M a ρ) = target a ρ) (e : Except Exception Term)
        (he₁ : pos = Bool.false → e = .ok (.tuple #[.atom "negation", .map M]))
        (he₂ : pos = Bool.true → M = [] → e = .ok (.integer 0))
        (he₃ : pos = Bool.true → M ≠ [] → e = .ok (.tuple #[.atom "union", .map M])) :
        ∃ w, e = .ok w ∧ (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = target a ρ) ∧
          (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → target a ρ = Bool.false) := by
      cases pos
      · exact ⟨_, he₁ rfl, fun _ => ⟨⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => by
          rw [arity_neg, ← sem a ρ resp]; cases evalR M a ρ <;> rfl⟩, fun k => by simp [kept] at k⟩
      · cases M with
        | nil => exact ⟨_, he₂ rfl rfl, fun k => by simp [kept] at k, fun _ a ρ resp => by
            rw [← sem a ρ resp]; simp [evalR, mapLookup]⟩
        | cons x xs => exact ⟨_, he₃ rfl (by simp), fun _ => ⟨⟨Bool.true, _, rfl, bM⟩, fun a ρ resp => by
            rw [arity_union, ← sem a ρ resp]; cases evalR _ a ρ <;> rfl⟩, fun k => by simp [kept] at k⟩

    theorem fun_inter_spec (n : Nat) {x y : Term} (fx : FunF x) (fy : FunF y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom "fun") x y = .ok w ∧
          (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = (arityOf x a ρ && arityOf y a ρ)) ∧
          (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → (arityOf x a ρ && arityOf y a ρ) = Bool.false) := by
      obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
      obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
      have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
        intro M ne; cases M with
        | nil => exact absurd rfl ne
        | cons e rest => exact size_cons e rest
      cases p₁ <;> cases p₂
      · obtain ⟨M, run, bM, sem⟩ := repr_union_sem n b₁ b₂
        refine fun_finish Bool.false M bM _ (fun a ρ resp => ?_) _ (fun _ => ?_) (fun h => by cases h) (fun h => by cases h)
        · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
        · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso]
      · obtain ⟨M, run, bM, sem⟩ := repr_diff_sem (n + 1) b₂ b₁
        refine fun_finish Bool.true M bM _ (fun a ρ resp => ?_) _ (fun h => by cases h) (fun _ hM => ?_) (fun _ hM => ?_)
        · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
        · subst hM
          simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
        · obtain ⟨s, ne, sz⟩ := size M hM
          have : (s : Int) ≠ 0 := by omega
          simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, this, ne]
      · obtain ⟨M, run, bM, sem⟩ := repr_diff_sem (n + 1) b₁ b₂
        refine fun_finish Bool.true M bM _ (fun a ρ resp => ?_) _ (fun h => by cases h) (fun _ hM => ?_) (fun _ hM => ?_)
        · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
        · subst hM
          simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
        · obtain ⟨s, ne, sz⟩ := size M hM
          have : (s : Int) ≠ 0 := by omega
          simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, this, ne]
      · obtain ⟨M, run, bM, sem⟩ := repr_inter_sem n b₁ b₂
        refine fun_finish Bool.true M bM _ (fun a ρ resp => ?_) _ (fun h => by cases h) (fun _ hM => ?_) (fun _ hM => ?_)
        · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
        · subst hM
          simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
        · obtain ⟨s, ne, sz⟩ := size M hM
          have : (s : Int) ≠ 0 := by omega
          simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, this, ne]

    theorem allBdd_nil : AllBdd [] := fun q v h => by simp [mapLookup] at h

    theorem evalR_nil (a : Term) (ρ : Term → Bool) : evalR [] a ρ = Bool.false := by simp [evalR, mapLookup]

    theorem fun_neg_spec (n : Nat) {x : Term} (fx : FunF x) :
        ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun") (.tuple #[.atom "negation", .map []]) x =
            .ok w ∧
          (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = !arityOf x a ρ) ∧
          (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → arityOf x a ρ = Bool.true) := by
      have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
        intro M ne; cases M with
        | nil => exact absurd rfl ne
        | cons e rest => exact size_cons e rest
      obtain ⟨p, R, rfl, b⟩ := fx
      have flip : ∀ (w : Term), (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ →
          (!arityOf (.tuple #[.atom (if p then "union" else "negation"), .map R]) a ρ) = Bool.false) →
          kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ →
            arityOf (.tuple #[.atom (if p then "union" else "negation"), .map R]) a ρ = Bool.true := by
        intro w h k a ρ resp
        have := h k a ρ resp
        cases e : arityOf (.tuple #[.atom (if p then "union" else "negation"), .map R]) a ρ <;> simp_all
      cases p
      · obtain ⟨M, run, bM, sem⟩ := repr_diff_sem (n + 1) b allBdd_nil
        have he₂ : M = [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun")
            (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "negation", .map R]) = .ok (.integer 0) := by
          intro hM; subst hM
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
        have he₃ : M ≠ [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun")
            (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "negation", .map R]) =
              .ok (.tuple #[.atom "union", .map M]) := by
          intro hM
          obtain ⟨s, ne, sz⟩ := size M hM
          have : (s : Int) ≠ 0 := by omega
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, this, ne]
        obtain ⟨w, hw, kw, dw⟩ := fun_finish Bool.true M bM (fun a ρ => !arityOf (.tuple #[.atom "negation", .map R]) a ρ)
          (fun a ρ resp => by rw [sem a ρ resp, arity_neg, evalR_nil]; cases evalR R a ρ <;> rfl) _
          (fun h => by cases h) (fun _ hM => he₂ hM) (fun _ hM => he₃ hM)
        exact ⟨w, hw, kw, flip w dw⟩
      · obtain ⟨M, run, bM, sem⟩ := repr_union_sem n allBdd_nil b
        have he₁ : Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun")
            (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "union", .map R]) =
              .ok (.tuple #[.atom "negation", .map M]) := by
          simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
            Erlang.erlang.«==/2», Lynx.Except.andAlso]
        obtain ⟨w, hw, kw, dw⟩ := fun_finish Bool.false M bM (fun a ρ => !arityOf (.tuple #[.atom "union", .map R]) a ρ)
          (fun a ρ resp => by rw [sem a ρ resp, arity_union, evalR_nil]; cases evalR R a ρ <;> rfl) _
          (fun _ => he₁) (fun h => by cases h) (fun h => by cases h)
        exact ⟨w, hw, kw, flip w dw⟩

    theorem all1_true (d : Dispatcher) (f : Term) :
        ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (.atom "true")) →
          Erlang.lists.«all_1/2» d f (Term.list l) = .ok (.atom "true") := by
      intro l
      induction l with
      | nil => intro _; simp [Erlang.lists.«all_1/2», Term.list]
      | cons x xs ih =>
        intro hf
        rw [Erlang.lists.«all_1/2».eq_def]
        simp [Term.list, hf x List.mem_cons_self, ih fun y m => hf y (List.mem_cons_of_mem _ m)]

    theorem all_true (d : Dispatcher) (m nm : String) (caps : Array Term) (l : List Term)
        (hf : ∀ x ∈ l, d.pure (.function m nm 1 caps) #[x] = .ok (.atom "true")) :
        Erlang.lists.«all/2» d (.function m nm 1 caps) (Term.list l) = .ok (.atom "true") := by
      cases l with
      | nil => simp [Erlang.lists.«all/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list]
      | cons x xs =>
        simp [Erlang.lists.«all/2», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list,
          hf x List.mem_cons_self, all1_true d _ xs fun y m => hf y (List.mem_cons_of_mem _ m)]

    /-- Unions of function types whose BDDs no valuation satisfies are empty. -/
    theorem fun_empty_unsat (n : Nat) (R : List (Term × Term)) (bR : AllBdd R)
        (unsat : ∀ a ρ, Resp ρ → evalR R a ρ = Bool.false) :
        Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) (.tuple #[.atom "union", .map R]) (.map []) =
          .ok (.atom "true") := by
      unfold Elixir.Module.Types.Descr.«fun_empty?/2»
      simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind]
      have list : Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2]) =
          Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2]) := rfl
      refine all_true _ _ _ _ _ fun x m => ?_
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp m
      have hv := mapLookup_of_mem_mapEntries me
      have wv := bR _ _ hv
      have uv : Unsat e.2 := fun ρ resp => by have := unsat e.1 ρ resp; simpa [evalR, hv] using this
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-1-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-1-/2»]
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.true, Term.false,
        Erlang.maps.«put/3», Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf_unsat wv uv, Erlang.lists.«all/2»,
        Lynx.Except.guard, Erlang.erlang.«is_function/2»]

    theorem fresh_arity (R₁ R₂ : List (Term × Term)) : ∃ q, mapLookup R₁ q = none ∧ mapLookup R₂ q = none := by
      obtain ⟨q, hq⟩ := fresh_atom (R₁ ++ R₂)
      refine ⟨q, ?_, ?_⟩ <;> simp only [mapLookup, List.find?_append, Option.map_eq_none_iff, Option.or_eq_none_iff] at hq ⊢
      · exact hq.1
      · exact hq.2

    /-- A union of function types whose arities no valuation satisfies is `0` or empty. -/
    theorem fun_union_empty (n : Nat) (M : List (Term × Term)) (bM : AllBdd M) (unsat : ∀ a ρ, Resp ρ → evalR M a ρ = Bool.false)
        (e : Except Exception Term) (he₂ : M = [] → e = .ok (.integer 0))
        (he₃ : M ≠ [] → e = .ok (.tuple #[.atom "union", .map M])) :
        ∃ w, e = .ok w ∧ (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
          Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) w (.map []) = .ok (.atom "true")) := by
      cases M with
      | nil => exact ⟨_, he₂ rfl, Or.inl rfl⟩
      | cons x xs => exact ⟨_, he₃ (by simp), Or.inr (Or.inr (fun_empty_unsat n _ bM unsat))⟩

    theorem fun_sub_spec (n : Nat) {a : Term} (fa : FunF a) (b : Option Term) (fb : ∀ y, b = some y → FunF y)
        (incl : ∀ q ρ, Resp ρ → arityOf a q ρ = Bool.true → b.elim Bool.false (fun y => arityOf y q ρ) = Bool.true) :
        (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun") a y = .ok w ∧
          (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
            Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) w (.map []) = .ok (.atom "true"))) ∧
        (b = none → Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) a (.map []) = .ok (.atom "true")) := by
      have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
        intro M ne; cases M with
        | nil => exact absurd rfl ne
        | cons e rest => exact size_cons e rest
      obtain ⟨p₁, R₁, rfl, b₁⟩ := fa
      refine ⟨fun y hb => ?_, fun hb => ?_⟩
      · subst hb
        obtain ⟨p₂, R₂, rfl, b₂⟩ := fb _ rfl
        have incl' : ∀ q ρ, Resp ρ → (p₁ == evalR R₁ q ρ) = Bool.true → (p₂ == evalR R₂ q ρ) = Bool.true := by
          intro q ρ resp h
          have := incl q ρ resp (by rw [arity_tag]; exact h)
          simpa [Option.elim, arity_tag] using this
        have finish : ∀ (M : List (Term × Term)), AllBdd M →
            (∀ q ρ, Resp ρ → evalR M q ρ = Bool.false) →
            (M = [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun")
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂]) = .ok (.integer 0)) →
            (M ≠ [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun")
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂]) = .ok (.tuple #[.atom "union", .map M])) →
            ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun")
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂]) = .ok w ∧
              (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
                Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) w (.map []) = .ok (.atom "true")) :=
          fun M bM unsat he₂ he₃ => fun_union_empty n M bM unsat _ he₂ he₃
        cases p₁ <;> cases p₂
        · obtain ⟨M, run, bM, sem⟩ := repr_diff_sem (n + 2) b₂ b₁
          refine finish M bM (fun q ρ resp => ?_) (fun hM => ?_) (fun hM => ?_)
          · have := incl' q ρ resp
            rw [sem q ρ resp]
            cases h₁ : evalR R₁ q ρ <;> cases h₂ : evalR R₂ q ρ <;> simp_all
          · subst hM
            simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
          · obtain ⟨s, ne, sz⟩ := size M hM
            have : (s : Int) ≠ 0 := by omega
            simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, this, ne]
        · exfalso
          obtain ⟨q, h₁, h₂⟩ := fresh_arity R₁ R₂
          have := incl' q _ (resp_const Bool.true)
          simp [evalR, h₁, h₂] at this
        · obtain ⟨M, run, bM, sem⟩ := repr_inter_sem (n + 1) b₁ b₂
          refine finish M bM (fun q ρ resp => ?_) (fun hM => ?_) (fun hM => ?_)
          · have := incl' q ρ resp
            rw [sem q ρ resp]
            cases h₁ : evalR R₁ q ρ <;> cases h₂ : evalR R₂ q ρ <;> simp_all
          · subst hM
            simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
          · obtain ⟨s, ne, sz⟩ := size M hM
            have : (s : Int) ≠ 0 := by omega
            simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, this, ne]
        · obtain ⟨M, run, bM, sem⟩ := repr_diff_sem (n + 2) b₁ b₂
          refine finish M bM (fun q ρ resp => ?_) (fun hM => ?_) (fun hM => ?_)
          · have := incl' q ρ resp
            rw [sem q ρ resp]
            cases h₁ : evalR R₁ q ρ <;> cases h₂ : evalR R₂ q ρ <;> simp_all
          · subst hM
            simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
          · obtain ⟨s, ne, sz⟩ := size M hM
            have : (s : Int) ≠ 0 := by omega
            simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
              Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, this, ne]
      · subst hb
        cases p₁
        · exfalso
          obtain ⟨q, h₁, -⟩ := fresh_arity R₁ R₁
          have := incl q _ (resp_const Bool.true) (by rw [arity_tag]; simp [evalR, h₁])
          simp [Option.elim] at this
        · refine fun_empty_unsat n R₁ b₁ fun q ρ resp => ?_
          cases h : evalR R₁ q ρ
          · rfl
          · have := incl q ρ resp (by rw [arity_tag]; simp [h])
            simp [Option.elim] at this

    /-! Types whose fields have the semantics above. -/

    def names : List String := ["bitmap", "atom", "fun", "list", "tuple", "map"]

    def FieldK (name : String) (x : Term) : Prop :=
      (name = "bitmap" ∧ BitField x) ∨ (name = "atom" ∧ AtomF x) ∨ (name = "fun" ∧ FunF x) ∨
        (name = "list" ∧ ListField x) ∨ (name = "tuple" ∧ OField TupleOk x) ∨ (name = "map" ∧ OField MapOk x)

    structure Sem (X : List (Term × Term)) : Prop where
      keys : ∀ q, (mapLookup X q).isSome → ∃ name ∈ names, q = .atom name
      fields : ∀ name x, mapLookup X (.atom name) = some x → FieldK name x

    def dn (name : String) (x : Option Term) (p : Point) : Bool :=
      match x with
      | none => Bool.false
      | some x => if name = "bitmap" then bitOf x p.1 else if name = "atom" then amemV (some x) p.2.1
          else if name = "fun" then arityOf x p.2.1 p.2.2 else if name = "list" then denL x p.2.2 else denO x p.2.2

    def PtOk (name : String) (p : Point) : Prop :=
      Resp p.2.2 ∧ (name = "bitmap" → p.1 < 8) ∧ (name = "tuple" → Real p.2.2)

    def topL (x : Option Term) : Bool :=
      match x with
      | none => Bool.false
      | some x => isListTop x

    theorem Sem.static {X : List (Term × Term)} (s : Sem X) : mapLookup X (.atom "dynamic") = Option.none := by
      cases h : mapLookup X (.atom "dynamic") with
      | none => rfl
      | some w =>
        obtain ⟨name, m, e⟩ := s.keys (.atom "dynamic") (by rw [h]; rfl)
        simp only [Term.atom.injEq] at e
        subst e
        simp [names] at m

    theorem Sem.absent {X : List (Term × Term)} (s : Sem X) {q : Term} (h : ∀ name ∈ names, q ≠ .atom name) :
        mapLookup X q = Option.none := by
      cases e : mapLookup X q with
      | none => rfl
      | some w =>
        obtain ⟨name, m, rfl⟩ := s.keys q (by simp [e])
        exact absurd rfl (h name m)

    /-- The fields of a union of static types, at any key. -/
    theorem union_any (depth : Nat) (L R : List (Term × Term))
        (staticL : mapLookup L (.atom "dynamic") = Option.none) (staticR : mapLookup R (.atom "dynamic") = Option.none)
        (keysR : ∀ q, (mapLookup R q).isSome → ∃ name, q = .atom name)
        (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          ∃ u, Elixir.Module.Types.Descr.«bare_union/3» (D depth) q x y = .ok u) :
        ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D (depth + 1)) (.map L) (.map R) = .ok (.map U) ∧
          ∀ q, (mapLookup R q = Option.none → mapLookup U q = mapLookup L q) ∧
            (∀ y, mapLookup R q = some y → mapLookup L q = Option.none → mapLookup U q = some y) ∧
            (∀ x y u, mapLookup L q = some x → mapLookup R q = some y →
              Elixir.Module.Types.Descr.«bare_union/3» (D depth) q x y = .ok u → mapLookup U q = some u) := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_union/3» (D depth) k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have value : ∀ q x y u, Elixir.Module.Types.Descr.«bare_union/3» (D depth) q x y = .ok u → g q x y = u := by
        intro q x y u run; simp [g, run]
      obtain ⟨U, run, look⟩ : ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D (depth + 1)) (.map L) (.map R) = .ok (.map U) ∧
          ∀ q, mapLookup U q =
            match (mapEntries R).find? (fun e => decide (exactCompare q e.1 = .eq)) with
            | some e => some (match mapLookup L e.1 with | some x => g e.1 x e.2 | none => e.2)
            | none => mapLookup L q := by
        unfold Elixir.Module.Types.Descr.«bare_union/2»
        simp [getMapKeys_single, Erlang.erlang.«==/2», staticL, staticR]
        by_cases emptyL : L = []
        · subst emptyL
          refine ⟨R, by simp, fun q => ?_⟩
          cases hit : (mapEntries R).find? (fun e => decide (exactCompare q e.1 = .eq)) with
          | none => rw [find_none hit]; simp [mapLookup]
          | some e => rw [(find_entry hit).2]; simp [mapLookup]
        by_cases emptyR : R = []
        · subst emptyR
          exact ⟨L, by simp [emptyL], fun q => by simp [mapLookup]⟩
        simp only [emptyL, emptyR]
        unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
        obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup (D (depth + 1)) "Elixir.Module.Types.Descr" "bare_union" #[]
          L R g (by
            intro e me x hx
            have hy := mapLookup_of_mem_mapEntries me
            obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
            rw [Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure, ru, value _ _ _ _ ru])
        exact ⟨out, by simpa using run, look⟩
      refine ⟨U, run, fun q => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩⟩
      · rw [look q]
        cases hit : (mapEntries R).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | none => rfl
        | some e => rw [(find_entry hit).2] at hR; cases hR
      · rw [look q]
        cases hit : (mapEntries R).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | none => rw [find_none hit] at hR; cases hR
        | some e =>
          obtain ⟨qe, h⟩ := find_entry hit
          rw [h] at hR; cases hR
          simp [← mapLookup_congr qe, hL]
      · rw [look q]
        cases hit : (mapEntries R).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | none => rw [find_none hit] at hR; cases hR
        | some e =>
          obtain ⟨qe, h⟩ := find_entry hit
          rw [h] at hR; cases hR
          obtain ⟨name, hname⟩ := keysR e.1 (by rw [← mapLookup_congr qe, h]; rfl)
          rw [hname] at qe
          obtain rfl := (exactCompare_eq_atom q name).mp qe
          simp [hname, hL, value _ _ _ _ ru]

    theorem dn_bitmap (x : Term) (p : Point) : dn "bitmap" (some x) p = bitOf x p.1 := by simp [dn]
    theorem dn_atom (x : Term) (p : Point) : dn "atom" (some x) p = amemV (some x) p.2.1 := by simp [dn]
    theorem dn_fun (x : Term) (p : Point) : dn "fun" (some x) p = arityOf x p.2.1 p.2.2 := by simp [dn]
    theorem dn_list (x : Term) (p : Point) : dn "list" (some x) p = denL x p.2.2 := by simp [dn]
    theorem dn_tuple (x : Term) (p : Point) : dn "tuple" (some x) p = denO x p.2.2 := by simp [dn]
    theorem dn_map (x : Term) (p : Point) : dn "map" (some x) p = denO x p.2.2 := by simp [dn]
    theorem dn_none (name : String) (p : Point) : dn name Option.none p = Bool.false := rfl

    theorem field_union (n : Nat) {name : String} {x y : Term} (fx : FieldK name x) (fy : FieldK name y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y = .ok w ∧ FieldK name w ∧
          (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
          (name = "list" → isListTop w = (isListTop x || isListTop y)) := by
      rcases fx with ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ <;>
        rcases fy with ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ <;>
        (try simp only [String.reduceEq] at h) <;> (try clear h)
      · obtain ⟨w, run, fw, sem⟩ := bit_union (D (n + 1)) fx fy
        exact ⟨w, run, Or.inl ⟨rfl, fw⟩, fun p _ => by simp [dn_bitmap, sem], fun h => by simp at h⟩
      · obtain ⟨w, run, fw, sem⟩ := atom_union_spec (D (n + 1)) fx fy
        exact ⟨w, run, Or.inr (Or.inl ⟨rfl, fw⟩), fun p _ => by simp [dn_atom, sem], fun h => by simp at h⟩
      · obtain ⟨w, run, fw, sem⟩ := fun_union_spec n fx fy
        exact ⟨w, run, Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), fun p ok => by simp [dn_fun, sem _ _ ok.1], fun h => by simp at h⟩
      · obtain ⟨w, run, fw, sem, top⟩ := list_union_spec fx fy
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩))),
          fun p ok => by simp [dn_list, sem _ ok.1], fun _ => top⟩
      · obtain ⟨w, run, fw, sem⟩ := open_union_spec tupleOk_not _ tuple_union_shape.1 tuple_union_shape.2.1
          tuple_union_shape.2.2 fx fy
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)))),
          fun p ok => by simp [dn_tuple, sem _ ok.1], fun h => by simp at h⟩
      · obtain ⟨w, run, fw, sem⟩ := open_union_spec mapOk_not _ map_union_shape.1 map_union_shape.2.1
          map_union_shape.2.2 fx fy
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw⟩)))),
          fun p ok => by simp [dn_map, sem _ ok.1], fun h => by simp at h⟩

    /-- The fields of the top type. -/
    def TopAt (name : String) (t : Term) : Prop :=
      (name = "bitmap" ∧ t = .integer 255) ∨ (name = "atom" ∧ t = .tuple #[.atom "negation", .map []]) ∨
        (name = "fun" ∧ t = .tuple #[.atom "negation", .map []]) ∨
        (name = "list" ∧ t = .tuple #[.integer 46675407, .atom "term", .atom "term"]) ∨
        (name = "tuple" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) ∨
        (name = "map" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil])

    theorem field_neg (n : Nat) {name : String} {t x : Term} (ht : TopAt name t) (fx : FieldK name x) :
        ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom name) t x = .ok w ∧
          (kept (.atom name, w) = Bool.true → FieldK name w ∧
            (∀ p, PtOk name p → dn name (some w) p = !dn name (some x) p) ∧ (name = "list" → isListTop w = Bool.false)) ∧
          (kept (.atom name, w) = Bool.false → ∀ p, PtOk name p → dn name (some x) p = Bool.true) := by
      rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases fx with ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ <;>
        (try simp only [String.reduceEq] at h) <;> (try clear h)
      · obtain ⟨w, run, k, d⟩ := bit_neg (D (n + 1)) fx
        exact ⟨w, run, fun kw => ⟨Or.inl ⟨rfl, (k kw).1⟩, fun p ok => by simp [dn_bitmap, (k kw).2 _ (ok.2.1 rfl)],
          fun h => by simp at h⟩, fun kw p ok => by simp [dn_bitmap, d kw _ (ok.2.1 rfl)]⟩
      · obtain ⟨w, run, k, d⟩ := atom_neg_spec (D (n + 1)) fx
        exact ⟨w, run, fun kw => ⟨Or.inr (Or.inl ⟨rfl, (k kw).1⟩), fun p ok => by simp [dn_atom, (k kw).2],
          fun h => by simp at h⟩, fun kw p ok => by simp [dn_atom, d kw]⟩
      · obtain ⟨w, run, k, d⟩ := fun_neg_spec n fx
        exact ⟨w, run, fun kw => ⟨Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)), fun p ok => by simp [dn_fun, (k kw).2 _ _ ok.1],
          fun h => by simp at h⟩, fun kw p ok => by simp [dn_fun, d kw _ _ ok.1]⟩
      · obtain ⟨w, run, k, d⟩ := list_neg_spec fx
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, (k kw).1⟩))), fun p ok => by simp [dn_list, (k kw).2.2 _ ok.1], fun _ => (k kw).2.1⟩,
          fun kw p ok => by simp [dn_list, d kw _ ok.1]⟩
      · obtain ⟨w, run, k, d⟩ := tuple_neg_spec fx
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_tuple, (k kw).2 _ ok.1 (ok.2.2 rfl)], fun h => by simp at h⟩,
          fun kw p ok => by simp [dn_tuple, d kw _ ok.1 (ok.2.2 rfl)]⟩
      · obtain ⟨w, run, k, d⟩ := map_neg_spec fx
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_map, (k kw).2 _ ok.1], fun h => by simp at h⟩,
          fun kw p ok => by simp [dn_map, d kw _ ok.1]⟩

    theorem field_inter (n : Nat) {name : String} {x y : Term} (fx : FieldK name x) (fy : FieldK name y) :
        ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom name) x y = .ok w ∧
          (kept (.atom name, w) = Bool.true → FieldK name w ∧
            (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p && dn name (some y) p)) ∧
            (name = "list" → isListTop w = (isListTop x && isListTop y))) ∧
          (kept (.atom name, w) = Bool.false → (∀ p, PtOk name p → (dn name (some x) p && dn name (some y) p) = Bool.false) ∧
            (name = "list" → (isListTop x && isListTop y) = Bool.false)) := by
      rcases fx with ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ <;>
        rcases fy with ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ <;>
        (try simp only [String.reduceEq] at h) <;> (try clear h)
      · obtain ⟨w, run, k, d⟩ := bit_inter (D (n + 1)) fx fy
        exact ⟨w, run, fun kw => ⟨Or.inl ⟨rfl, (k kw).1⟩, fun p _ => by simp [dn_bitmap, (k kw).2], fun h => by simp at h⟩,
          fun kw => ⟨fun p _ => by simp [dn_bitmap, d kw], fun h => by simp at h⟩⟩
      · obtain ⟨w, run, k, d⟩ := atom_inter_spec (D (n + 1)) fx fy
        exact ⟨w, run, fun kw => ⟨Or.inr (Or.inl ⟨rfl, (k kw).1⟩), fun p _ => by simp [dn_atom, (k kw).2],
          fun h => by simp at h⟩, fun kw => ⟨fun p _ => by simp [dn_atom, d kw], fun h => by simp at h⟩⟩
      · obtain ⟨w, run, k, d⟩ := fun_inter_spec n fx fy
        exact ⟨w, run, fun kw => ⟨Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)), fun p ok => by simp [dn_fun, (k kw).2 _ _ ok.1],
          fun h => by simp at h⟩, fun kw => ⟨fun p ok => by simp [dn_fun, d kw _ _ ok.1], fun h => by simp at h⟩⟩
      · obtain ⟨w, run, k, d⟩ := list_inter_spec fx fy
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, (k kw).1⟩))), fun p ok => by simp [dn_list, (k kw).2.1 _ ok.1], fun _ => (k kw).2.2⟩,
          fun kw => ⟨fun p ok => by simp [dn_list, (d kw).1 _ ok.1], fun _ => (d kw).2⟩⟩
      · obtain ⟨w, run, k, d⟩ := open_inter_spec tupleOk_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
          tuple_inter_shape.2.2 (.atom "tuple") fx fy
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_tuple, (k kw).2 _ ok.1], fun h => by simp at h⟩,
          fun kw => ⟨fun p ok => by simp [dn_tuple, d kw _ ok.1], fun h => by simp at h⟩⟩
      · obtain ⟨w, run, k, d⟩ := open_inter_spec mapOk_not _ map_inter_shape.1 map_inter_shape.2.1
          map_inter_shape.2.2 (.atom "map") fx fy
        exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_map, (k kw).2 _ ok.1], fun h => by simp at h⟩,
          fun kw => ⟨fun p ok => by simp [dn_map, d kw _ ok.1], fun h => by simp at h⟩⟩

    theorem dn_elim (name : String) (x : Option Term) (p : Point) :
        dn name x p = x.elim Bool.false (fun y => dn name (some y) p) := by cases x <;> rfl

    theorem field_sub (n : Nat) {name : String} {a : Term} (fa : FieldK name a) (B : List (Term × Term))
        (fb : ∀ y, mapLookup B (.atom name) = some y → FieldK name y)
        (incl : ∀ p, PtOk name p → dn name (some a) p = Bool.true → dn name (mapLookup B (.atom name)) p = Bool.true)
        (side : name = "list" → ∀ y, mapLookup B (.atom name) = some y → isListTop y = Bool.true → isListTop a = Bool.true) :
        KeySub (D (n + 3)) B (.atom name) a := by
      have kind : ∀ {P : Term → Prop}, (∀ y, FieldK name y → P y) → ∀ y, mapLookup B (.atom name) = some y → P y :=
        fun h y hy => h y (fb y hy)
      rcases fa with ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩
      · have fb' : ∀ y, mapLookup B (.atom "bitmap") = some y → BitField y := kind fun y h => by
          rcases h with ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
        obtain ⟨some, notNone⟩ := bit_sub (D (n + 3)) fa _ fb' fun i lt h => by
          have := incl (i, .nil, fun _ => Bool.true) ⟨resp_const _, fun _ => lt, fun e => by simp at e⟩ (by simpa [dn_bitmap])
          rw [dn_elim] at this
          simpa [dn_bitmap] using this
        cases hb : mapLookup B (.atom "bitmap") with
        | none => exact absurd hb notNone
        | some y => exact Or.inl ⟨y, _, hb, some y hb, Or.inl rfl⟩
      · have fb' : ∀ y, mapLookup B (.atom "atom") = some y → AtomF y := kind fun y h => by
          rcases h with ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
        obtain ⟨some, notNone⟩ := atom_sub_spec (D (n + 3)) fa _ fb' fun q h => by
          have := incl (0, q, fun _ => Bool.true) ⟨resp_const _, fun e => by simp at e, fun e => by simp at e⟩
            (by simpa [dn_atom])
          rw [dn_elim] at this
          simpa [dn_atom] using this
        cases hb : mapLookup B (.atom "atom") with
        | none => exact absurd hb notNone
        | some y => exact Or.inl ⟨y, _, hb, some y hb, Or.inl rfl⟩
      · have fb' : ∀ y, mapLookup B (.atom "fun") = some y → FunF y := kind fun y h => by
          rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
        obtain ⟨some, none⟩ := fun_sub_spec (n + 1) fa _ fb' fun q ρ resp h => by
          have := incl (0, q, ρ) ⟨resp, fun e => by simp at e, fun e => by simp at e⟩ (by simpa [dn_fun])
          rw [dn_elim] at this
          simpa [dn_fun] using this
        cases hb : mapLookup B (.atom "fun") with
        | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
        | some y =>
          obtain ⟨w, run, h⟩ := some y hb
          refine Or.inl ⟨y, w, hb, run, ?_⟩
          simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h
      · have fb' : ∀ y, mapLookup B (.atom "list") = some y → ListField y := kind fun y h => by
          rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
        obtain ⟨some, none⟩ := list_sub_spec (D (n + 3)) fa _ fb' (fun ρ resp h => by
          have := incl (0, .nil, ρ) ⟨resp, fun e => by simp at e, fun e => by simp at e⟩ (by simpa [dn_list])
          rw [dn_elim] at this
          simpa [dn_list] using this) (side rfl)
        cases hb : mapLookup B (.atom "list") with
        | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
        | some y =>
          obtain ⟨w, run, h⟩ := some y hb
          refine Or.inl ⟨y, w, hb, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, ?_⟩
          simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h
      · have fb' : ∀ y, mapLookup B (.atom "tuple") = some y → OField TupleOk y := kind fun y h => by
          rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
        obtain ⟨some, none⟩ := tuple_sub_spec (n + 1) fa _ fb' fun ρ resp real h => by
          have := incl (0, .nil, ρ) ⟨resp, fun e => by simp at e, fun _ => real⟩ (by simpa [dn_tuple])
          rw [dn_elim] at this
          simpa [dn_tuple] using this
        cases hb : mapLookup B (.atom "tuple") with
        | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
        | some y =>
          obtain ⟨w, run, h⟩ := some y hb
          refine Or.inl ⟨y, w, hb, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, ?_⟩
          simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h
      · have fb' : ∀ y, mapLookup B (.atom "map") = some y → OField MapOk y := kind fun y h => by
          rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ <;> first | exact h | simp at e
        obtain ⟨some, none⟩ := map_sub_spec n fa _ fb' fun ρ resp h => by
          have := incl (0, .nil, ρ) ⟨resp, fun e => by simp at e, fun e => by simp at e⟩ (by simpa [dn_map])
          rw [dn_elim] at this
          simpa [dn_map] using this
        cases hb : mapLookup B (.atom "map") with
        | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
        | some y =>
          obtain ⟨w, run, h⟩ := some y hb
          refine Or.inl ⟨y, w, hb, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, ?_⟩
          simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h

    /-- A type is a subtype of another when each field holds less, and the right type lacks the top list type
    unless the left type has it too. -/
    theorem sem_sub (n : Nat) (A B : List (Term × Term)) (sA : Sem A) (sB : Sem B)
        (incl : ∀ name ∈ names, ∀ p, PtOk name p → dn name (mapLookup A (.atom name)) p = Bool.true →
          dn name (mapLookup B (.atom name)) p = Bool.true)
        (side : topL (mapLookup B (.atom "list")) = Bool.true → topL (mapLookup A (.atom "list")) = Bool.true) :
        Elixir.Module.Types.Descr.«subtype?/2» (D (n + 3)) (.map A) (.map B) = .ok (.atom "true") := by
      refine subtype_keys _ A B sA.static sB.static fun e member => ?_
      have hA := mapLookup_of_mem_mapEntries member
      obtain ⟨name, m, hname⟩ := sA.keys e.1 (by simp [hA])
      rw [hname] at hA ⊢
      have fa := sA.fields name e.2 hA
      refine field_sub n fa B (sB.fields name) (fun p ok h => incl name m p ok (by rw [hA]; exact h))
        fun hl y hy top => ?_
      subst hl
      have := side (by simp [topL, hy, top])
      simpa [topL, hA] using this

    theorem sem_union (L R : List (Term × Term)) (sL : Sem L) (sR : Sem R) :
        ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D 100) (.map L) (.map R) = .ok (.map U) ∧ Sem U ∧
          (∀ name, ∀ p, PtOk name p → dn name (mapLookup U (.atom name)) p =
            (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p)) ∧
          topL (mapLookup U (.atom "list")) = (topL (mapLookup L (.atom "list")) || topL (mapLookup R (.atom "list"))) ∧
          (L ≠ [] → U ≠ []) ∧
          (mapLookup U (.atom "list")).isNone =
            ((mapLookup L (.atom "list")).isNone && (mapLookup R (.atom "list")).isNone) := by
      have calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          ∃ u, Elixir.Module.Types.Descr.«bare_union/3» (D 99) q x y = .ok u := by
        intro q x y hx hy
        obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
        obtain ⟨w, run, -⟩ := field_union 98 (sL.fields name x hx) (sR.fields name y hy)
        exact ⟨w, run⟩
      obtain ⟨U, run, look⟩ := union_any 99 L R sL.static sR.static
        (fun q h => by obtain ⟨name, -, e⟩ := sR.keys q h; exact ⟨name, e⟩) calls
      -- What the union holds at each field name.
      have at_name : ∀ name, (mapLookup R (.atom name) = Option.none ∧ mapLookup U (.atom name) = mapLookup L (.atom name)) ∨
          (∃ y, mapLookup L (.atom name) = Option.none ∧ mapLookup R (.atom name) = some y ∧
            mapLookup U (.atom name) = some y) ∨
          (∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
            mapLookup U (.atom name) = some w ∧ FieldK name w ∧
            (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
            (name = "list" → isListTop w = (isListTop x || isListTop y))) := by
        intro name
        cases hR : mapLookup R (.atom name) with
        | none => exact Or.inl ⟨rfl, (look _).1 hR⟩
        | some y =>
          cases hL : mapLookup L (.atom name) with
          | none => exact Or.inr (Or.inl ⟨y, rfl, rfl, (look _).2.1 y hR hL⟩)
          | some x =>
            obtain ⟨w, run, fw, sem, top⟩ := field_union 98 (sL.fields name x hL) (sR.fields name y hR)
            exact Or.inr (Or.inr ⟨x, y, w, rfl, rfl, (look _).2.2 x y w hL hR run, fw, sem, top⟩)
      refine ⟨U, run, ⟨fun q h => ?_, fun name w hw => ?_⟩, fun name p ok => ?_, ?_, fun ne => ?_, ?_⟩
      rotate_right
      · rcases at_name "list" with ⟨hR, hU⟩ | ⟨y, hL, hR, hU⟩ | ⟨x, y, w, hL, hR, hU, -⟩
        · simp [hU, hR]
        · simp [hU, hL, hR]
        · simp [hU, hL, hR]
      · cases hR : mapLookup R q with
        | none =>
          rw [(look q).1 hR] at h
          exact sL.keys q h
        | some y => exact sR.keys q (by simp [hR])
      · rcases at_name name with ⟨-, hU⟩ | ⟨y, -, hR, hU⟩ | ⟨x, y, w', -, -, hU, fw, -⟩ <;> rw [hU] at hw
        · exact sL.fields name w hw
        · rw [← Option.some.inj hw]; exact sR.fields name y hR
        · rw [← Option.some.inj hw]; exact fw
      · rcases at_name name with ⟨hR, hU⟩ | ⟨y, hL, hR, hU⟩ | ⟨x, y, w, hL, hR, hU, -, sem, -⟩
        · simp [hU, hR, dn_none]
        · simp [hU, hL, hR, dn_none]
        · rw [hU, hL, hR, sem p ok]
      · rcases at_name "list" with ⟨hR, hU⟩ | ⟨y, hL, hR, hU⟩ | ⟨x, y, w, hL, hR, hU, -, -, top⟩
        · simp [hU, hR, topL]
        · simp [hU, hL, hR, topL]
        · simp [hU, hL, hR, topL, top rfl]
      · intro empty
        subst empty
        cases L with
        | nil => exact ne rfl
        | cons e rest =>
          obtain ⟨name, -, he⟩ := sL.keys e.1 (by simp [mapLookup, Std.ReflCmp.compare_self])
          rcases at_name name with ⟨-, hU⟩ | ⟨y, -, -, hU⟩ | ⟨x, y, w, -, -, hU, -⟩ <;> simp [mapLookup] at hU
          have : mapLookup (e :: rest) (.atom name) ≠ Option.none := by
            rw [← he]; simp [mapLookup, Std.ReflCmp.compare_self]
          exact this hU.symm

    theorem term_top {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
        {q t : Term} (h : mapLookup T q = some t) : ∃ name ∈ names, q = .atom name ∧ TopAt name t := by
      rcases term_keys term h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨"bitmap", by simp [names], rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨"atom", by simp [names], rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨"fun", by simp [names], rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨"list", by simp [names], rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨"tuple", by simp [names], rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
      · exact ⟨"map", by simp [names], rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩

    theorem term_at {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
        {name : String} (m : name ∈ names) : ∃ t, mapLookup T (.atom name) = some t ∧ TopAt name t := by
      simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at term
      cases term
      simp only [names, List.mem_cons, List.mem_nil_iff, or_false] at m
      rcases m with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by simp [mapLookup], Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, by simp [mapLookup], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
      · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩

    theorem top_field {name : String} {t : Term} (ht : TopAt name t) :
        FieldK name t ∧ (∀ p, PtOk name p → dn name (some t) p = Bool.true) ∧
          (name = "list" → isListTop t = Bool.true) := by
      rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨Or.inl ⟨rfl, 255, rfl, by decide, by decide⟩, fun p ok => ?_, fun h => by simp at h⟩
        have lt := ok.2.1 rfl
        have bits : ∀ i, i < 8 → (255 : Nat).testBit i = Bool.true := by decide
        simpa [dn_bitmap, bitOf] using bits p.1 lt
      · refine ⟨Or.inr (Or.inl ⟨rfl, ⟨Bool.false, [], rfl, no_atoms⟩, .nil, by simp [amemV, mapLookup]⟩),
          fun p _ => by simp [dn_atom, amemV, mapLookup], fun h => by simp at h⟩
      · refine ⟨Or.inr (Or.inr (Or.inl ⟨rfl, Bool.false, [], rfl, allBdd_nil⟩)), fun p _ => by
          simp [dn_fun, arityOf, mapLookup], fun h => by simp at h⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩))), fun p _ => by simp [dn_list, denL_top],
          fun _ => by simp [isListTop]⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩)))), fun p _ => by simp [dn_tuple, denO_top],
          fun h => by simp at h⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨_, rfl⟩⟩)))), fun p _ => by simp [dn_map, denO_top],
          fun h => by simp at h⟩

    theorem sem_neg (X : List (Term × Term)) (sX : Sem X) (nonempty : X ≠ []) :
        ∃ N, Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map X) = .ok (.map N) ∧ Sem N ∧
          (∀ name ∈ names, ∀ p, PtOk name p → dn name (mapLookup N (.atom name)) p = !dn name (mapLookup X (.atom name)) p) ∧
          topL (mapLookup N (.atom "list")) = (mapLookup X (.atom "list")).isNone := by
      obtain ⟨T, term, -, -, -, termDynamic⟩ := unfolded_term_fields
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_difference/3» (D 98) k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have value : ∀ q x y w, Elixir.Module.Types.Descr.«bare_difference/3» (D 98) q x y = .ok w → g q x y = w := by
        intro q x y w run; simp [g, run]
      obtain ⟨N, fold, lookN⟩ := difference_fold 98 (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
        g (mapEntries X) T (mapEntries_distinct X) (by
          intro e member v₁ found
          have hy := mapLookup_of_mem_mapEntries member
          rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure]
          obtain ⟨name, -, he, ht⟩ := term_top term found
          rw [he] at hy found ⊢
          obtain ⟨w, run, -⟩ := field_neg 97 ht (sX.fields name e.2 hy)
          rw [run, value _ _ _ _ run])
      have run : Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map X) = .ok (.map N) := by
        simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
        unfold Elixir.Module.Types.Descr.«bare_difference/2»
        simp [Erlang.erlang.«==/2», unfold_map, static_map sX.static, nonempty]
        unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
        simp [Erlang.erlang.«==/2», nonempty, term, Erlang.maps.«fold/3»]
        simpa using fold
      -- What the negation holds at each field name.
      have at_name : ∀ name ∈ names, ∃ t, TopAt name t ∧
          ((mapLookup X (.atom name) = Option.none ∧ mapLookup N (.atom name) = some t) ∨
          (∃ x w, mapLookup X (.atom name) = some x ∧
            Elixir.Module.Types.Descr.«bare_difference/3» (D 98) (.atom name) t x = .ok w ∧
            mapLookup N (.atom name) = if kept (.atom name, w) then some w else Option.none)) := by
        intro name m
        obtain ⟨t, hT, ht⟩ := term_at term m
        refine ⟨t, ht, ?_⟩
        rw [lookN, find_atom]
        cases hX : mapLookup X (.atom name) with
        | none => exact Or.inl ⟨rfl, hT⟩
        | some x =>
          obtain ⟨w, run, -⟩ := field_neg 97 ht (sX.fields name x hX)
          exact Or.inr ⟨x, w, rfl, run, by simp [hT, value _ _ _ _ run]⟩
      have keysN : ∀ q, (mapLookup N q).isSome → ∃ name ∈ names, q = .atom name := by
        intro q h
        rw [lookN] at h
        cases hit : (mapEntries X).find? (fun e => decide (exactCompare q e.1 = .eq)) with
        | none =>
          rw [hit] at h
          obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
          obtain ⟨name, m, rfl, -⟩ := term_top term ht
          exact ⟨name, m, rfl⟩
        | some e =>
          rw [hit] at h
          obtain ⟨qe, -⟩ := find_entry hit
          cases ht : mapLookup T e.1 with
          | none => simp [ht] at h
          | some t =>
            obtain ⟨name, m, he, -⟩ := term_top term ht
            rw [he] at qe
            exact ⟨name, m, (exactCompare_eq_atom q name).mp qe⟩
      refine ⟨N, run, ⟨keysN, fun name w hw => ?_⟩, fun name m p ok => ?_, ?_⟩
      · obtain ⟨name', m, e⟩ := keysN (.atom name) (by simp [hw])
        simp only [Term.atom.injEq] at e
        subst e
        rcases at_name name m with ⟨t, ht, ⟨-, hN⟩ | ⟨x, w', hX, run', hN⟩⟩
        · rw [hN] at hw; rw [← Option.some.inj hw]; exact (top_field ht).1
        · obtain ⟨w'', run'', k, -⟩ := field_neg 97 ht (sX.fields name x hX)
          have e : w'' = w' := by rw [run''] at run'; exact Except.ok.inj run'
          subst e
          by_cases kw : kept (.atom name, w'') = Bool.true
          · simp only [kw, ite_true] at hN
            rw [hN] at hw; rw [← Option.some.inj hw]; exact (k kw).1
          · simp [kw] at hN; rw [hN] at hw; cases hw
      · rcases at_name name m with ⟨t, ht, ⟨hX, hN⟩ | ⟨x, w', hX, run', hN⟩⟩
        · rw [hN, hX, (top_field ht).2.1 p ok]; rfl
        · obtain ⟨w'', run'', k, d⟩ := field_neg 97 ht (sX.fields name x hX)
          have e : w'' = w' := by rw [run''] at run'; exact Except.ok.inj run'
          subst e
          by_cases kw : kept (.atom name, w'') = Bool.true
          · simp only [kw, ite_true] at hN
            rw [hN, hX, (k kw).2.1 p ok]
          · simp only [kw, Bool.false_eq_true, ite_false] at hN
            rw [hN, hX, dn_none, d (by simpa using kw) p ok]; rfl
      · rcases at_name "list" (by simp [names]) with ⟨t, ht, ⟨hX, hN⟩ | ⟨x, w', hX, run', hN⟩⟩
        · simp [hN, hX, topL, (top_field ht).2.2 rfl]
        · obtain ⟨w'', run'', k, -⟩ := field_neg 97 ht (sX.fields "list" x hX)
          have e : w'' = w' := by rw [run''] at run'; exact Except.ok.inj run'
          subst e
          by_cases kw : kept (.atom "list", w'') = Bool.true
          · simp [kw, hN, hX, topL, (k kw).2.2 rfl]
          · simp [kw, hN, hX, topL]

    theorem sem_inter (L R : List (Term × Term)) (sL : Sem L) (sR : Sem R) :
        ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2» (D 100) (.map L) (.map R) = .ok (.map I) ∧ Sem I ∧
          (∀ name, ∀ p, PtOk name p → dn name (mapLookup I (.atom name)) p =
            (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p)) ∧
          topL (mapLookup I (.atom "list")) = (topL (mapLookup L (.atom "list")) && topL (mapLookup R (.atom "list"))) := by
      obtain ⟨I, run, look, keysI⟩ := inter_lookup 99 L R sL.static sR.static (by
        intro q x y hx hy
        obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
        obtain ⟨w, run, -⟩ := field_inter 98 (sL.fields name x hx) (sR.fields name y hy)
        exact ⟨w, run⟩)
      have at_name : ∀ name, ((mapLookup L (.atom name) = Option.none ∨ mapLookup R (.atom name) = Option.none) ∧
          mapLookup I (.atom name) = Option.none) ∨
          (∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
            mapLookup I (.atom name) = (if kept (.atom name, w) then some w else Option.none) ∧
            (kept (.atom name, w) = Bool.true → FieldK name w ∧
              (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p && dn name (some y) p)) ∧
              (name = "list" → isListTop w = (isListTop x && isListTop y))) ∧
            (kept (.atom name, w) = Bool.false →
              (∀ p, PtOk name p → (dn name (some x) p && dn name (some y) p) = Bool.false) ∧
              (name = "list" → (isListTop x && isListTop y) = Bool.false))) := by
        intro name
        cases hL : mapLookup L (.atom name) with
        | none => exact Or.inl ⟨Or.inl rfl, (look name).1 hL⟩
        | some x =>
          cases hR : mapLookup R (.atom name) with
          | none => exact Or.inl ⟨Or.inr rfl, (look name).2.1 hR⟩
          | some y =>
            obtain ⟨w, run, k, d⟩ := field_inter 98 (sL.fields name x hL) (sR.fields name y hR)
            exact Or.inr ⟨x, y, w, rfl, rfl, (look name).2.2 x y w hL hR run, k, d⟩
      refine ⟨I, run, ⟨fun q h => sL.keys q (keysI q h), fun name w hw => ?_⟩, fun name p ok => ?_, ?_⟩
      · rcases at_name name with ⟨-, hI⟩ | ⟨x, y, w', -, -, hI, k, -⟩
        · rw [hI] at hw; cases hw
        · by_cases kw : kept (.atom name, w') = Bool.true
          · simp only [kw, ite_true] at hI
            rw [hI] at hw; rw [← Option.some.inj hw]; exact (k kw).1
          · simp [kw] at hI; rw [hI] at hw; cases hw
      · rcases at_name name with ⟨hLR, hI⟩ | ⟨x, y, w, hL, hR, hI, k, d⟩
        · rcases hLR with h | h <;> simp [hI, h, dn_none]
        · by_cases kw : kept (.atom name, w) = Bool.true
          · simp only [kw, ite_true] at hI
            rw [hI, hL, hR, (k kw).2.1 p ok]
          · simp only [kw, Bool.false_eq_true, ite_false] at hI
            rw [hI, hL, hR, dn_none, (d (by simpa using kw)).1 p ok]
      · rcases at_name "list" with ⟨hLR, hI⟩ | ⟨x, y, w, hL, hR, hI, k, d⟩
        · rcases hLR with h | h <;> simp [hI, h, topL]
        · by_cases kw : kept (.atom "list", w) = Bool.true
          · simp [kw, hI, hL, hR, topL, (k kw).2.2 rfl]
          · simp [kw, hI, hL, hR, topL, (d (by simpa using kw)).2 rfl]

    /-- The negation of a union of two non-empty types holds what the intersection of their negations holds. -/
    theorem de_morgan_sem (L R : List (Term × Term)) (sL : Sem L) (sR : Sem R) (nL : L ≠ []) (nR : R ≠ []) :
        ∃ U A NL NR B, Elixir.Module.Types.Descr.«bare_union/2» (D 100) (.map L) (.map R) = .ok (.map U) ∧
          Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map U) = .ok (.map A) ∧
          Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map L) = .ok (.map NL) ∧
          Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map R) = .ok (.map NR) ∧
          Elixir.Module.Types.Descr.«bare_intersection/2» (D 100) (.map NL) (.map NR) = .ok (.map B) ∧
          Elixir.Module.Types.Descr.«subtype?/2» (D 100) (.map A) (.map B) = .ok (.atom "true") ∧
          Elixir.Module.Types.Descr.«subtype?/2» (D 100) (.map B) (.map A) = .ok (.atom "true") := by
      obtain ⟨U, runU, sU, dU, tU, neU, nU⟩ := sem_union L R sL sR
      obtain ⟨A, runA, sA, dA, tA⟩ := sem_neg U sU (neU nL)
      obtain ⟨NL, runNL, sNL, dNL, tNL⟩ := sem_neg L sL nL
      obtain ⟨NR, runNR, sNR, dNR, tNR⟩ := sem_neg R sR nR
      obtain ⟨B, runB, sB, dB, tB⟩ := sem_inter NL NR sNL sNR
      have same : ∀ name ∈ names, ∀ p, PtOk name p →
          dn name (mapLookup A (.atom name)) p = dn name (mapLookup B (.atom name)) p := by
        intro name m p ok
        rw [dA name m p ok, dU name p ok, dB name p ok, dNL name m p ok, dNR name m p ok]
        cases dn name (mapLookup L (.atom name)) p <;> cases dn name (mapLookup R (.atom name)) p <;> rfl
      have top : topL (mapLookup A (.atom "list")) = topL (mapLookup B (.atom "list")) := by
        rw [tA, tB, tNL, tNR, nU]
      refine ⟨U, A, NL, NR, B, runU, runA, runNL, runNR, runB, sem_sub 97 A B sA sB (fun name m p ok h => ?_)
        (fun h => by rw [top]; exact h), sem_sub 97 B A sB sA (fun name m p ok h => ?_) (fun h => by rw [← top]; exact h)⟩
      · rw [← same name m p ok]; exact h
      · rw [same name m p ok]; exact h

    /-! The law. -/

    theorem Negatable.sem {X : List (Term × Term)} (v : Negatable X) : Sem X := by
      refine ⟨fun q h => ?_, fun name x hx => ?_⟩
      · rcases v.keys q h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
      · rcases v.keys (.atom name) (by simp [hx]) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
          subst e
        · exact Or.inl ⟨rfl, v.bitmap x hx⟩
        · obtain ⟨p, S, rfl, set⟩ := v.atom x hx
          refine Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, atom_nonempty p S fun hp => v.atomUnion S ?_⟩)
          subst hp
          simpa using hx
        · obtain ⟨pos, R, rfl⟩ := v.funs x hx
          exact Or.inr (Or.inr (Or.inl ⟨rfl, pos, R, rfl, fun q w h => v.arities _ hx _ R rfl q w h⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, v.lists x hx⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, v.tuples x hx⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, v.maps x hx⟩))))

    theorem negation_none_term : Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map []) = .ok (.atom "term") := by
      simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Erlang.erlang.«==/2»]

    theorem equal_self (x : Term) : Elixir.Module.Types.Descr.«equal?/2» (D 100) x x = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«equal?/2», Erlang.erlang.«==/2», Std.ReflCmp.compare_self, Lynx.Except.orElse,
        Term.true]

    /-- De Morgan's law for any two types of bitmaps, atoms, functions, lists, tuples, and maps. -/
    theorem de_morgan_union_law (L R : List (Term × Term)) (vL : Negatable L) (vR : Negatable R) :
        (do
          let u ← Elixir.Module.Types.Descr.«bare_union/2» (D 100) (.map L) (.map R)
          let a ← Elixir.Module.Types.Descr.«bare_negation/1» (D 100) u
          let nl ← Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map L)
          let nr ← Elixir.Module.Types.Descr.«bare_negation/1» (D 100) (.map R)
          let b ← Elixir.Module.Types.Descr.«bare_intersection/2» (D 100) nl nr
          Elixir.Module.Types.Descr.«equal?/2» (D 100) a b) = .ok (.atom "true") := by
      by_cases eL : L = [] <;> by_cases eR : R = []
      · subst eL eR
        have union : Elixir.Module.Types.Descr.«bare_union/2» (D 100) (.map []) (.map []) = .ok (.map []) := by
          unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
        have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D 100) (.atom "term") (.atom "term") =
            .ok (.atom "term") := by
          unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
        simp [union, negation_none_term, inter, equal_self]
      · subst eL
        obtain ⟨N, neg, -⟩ := sem_neg R vR.sem eR
        have union : Elixir.Module.Types.Descr.«bare_union/2» (D 100) (.map []) (.map R) = .ok (.map R) := by
          unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
        have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D 100) (.atom "term") (.map N) = .ok (.map N) := by
          unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
        simp [union, neg, negation_none_term, inter, equal_self]
      · subst eR
        obtain ⟨N, neg, -⟩ := sem_neg L vL.sem eL
        have union : Elixir.Module.Types.Descr.«bare_union/2» (D 100) (.map L) (.map []) = .ok (.map L) := by
          unfold Elixir.Module.Types.Descr.«bare_union/2»
          cases L with
          | nil => exact absurd rfl eL
          | cons e rest => simp [Erlang.erlang.«==/2»]
        have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D 100) (.map N) (.atom "term") = .ok (.map N) := by
          unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
        simp [union, neg, negation_none_term, inter, equal_self]
      · obtain ⟨U, A, NL, NR, B, union, negU, negL, negR, inter, sub₁, sub₂⟩ := de_morgan_sem L R vL.sem vR.sem eL eR
        simp only [union, negU, negL, negR, inter, Lynx.Except.ok_bind]
        by_cases c : Term.compare (.map A) (.map B) = .eq <;>
          simp [Elixir.Module.Types.Descr.«equal?/2», sub₁, sub₂, Lynx.Except.orElse, Lynx.Except.andAlso,
            Erlang.erlang.«==/2», c, Term.true, Term.false]

    end Elixir.STTDescrProofsTest
    """

    law intersection_none_empty(descr),
      requires: descr?(descr),
      expects: Descr.empty?(Descr.bare_intersection(descr, Descr.none())),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«intersection_none_empty:requires/1»] at requires
      simp only [Lynx.apply_eq, «intersection_none_empty:ensures/1», Elixir.Module.Types.Descr.«none/0»]
      cases descr with
      | map X =>
        cases dynamic : mapLookup X (.atom "dynamic") with
        | none => simp [intersection_none_static 99 X dynamic, empty_none]
        | some Dy =>
          have inner : Dy = .atom "term" ∨ ∃ Y, Dy = .map Y := by
            simp [«descr?/1», getMapKeys_single, dynamic, Erlang.erlang.«==/2», Erlang.erlang.«is_map/1»,
              Lynx.Except.orElse_eq_true] at requires
            cases Dy <;> simp_all
          simp [intersection_none_dynamic 99 X Dy dynamic inner, empty_none]
      | atom name =>
        by_cases top : name = "term"
        · subst top
          unfold Elixir.Module.Types.Descr.«bare_intersection/2»
          simp [empty_none]
        · simp [«descr?/1», top, Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      | _ => simp [«descr?/1», Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      """

    law intersection_negation_empty(descr),
      requires: negatable?(descr),
      expects: Descr.empty?(Descr.bare_intersection(descr, Descr.bare_negation(descr))),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«intersection_negation_empty:requires/1»] at requires
      obtain ⟨X, rfl, valid⟩ := negatable_map descr requires
      simp only [Lynx.apply_eq, «intersection_negation_empty:ensures/1»]
      by_cases empty : X = []
      · subst empty
        have negation : Elixir.Module.Types.Descr.«bare_negation/1»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) = .ok (.atom "term") := by
          simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
          unfold Elixir.Module.Types.Descr.«bare_difference/2»
          simp [Erlang.erlang.«==/2»]
        have intersection : Elixir.Module.Types.Descr.«bare_intersection/2»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) (.atom "term") = .ok (.map []) := by
          unfold Elixir.Module.Types.Descr.«bare_intersection/2»
          rfl
        simp [negation, intersection, empty_none]
      · obtain ⟨N, negation, static, bitmaps, atoms, funs, lists, tuples, maps, -⟩ := negation_fields 98 X valid empty
        obtain ⟨I, run, only⟩ := intersection_disjoint 99 X N valid static bitmaps atoms
          (fun x y hx hy => funs x y hx hy 99) lists tuples maps
        simp [negation, run, empty_gone 97 I only]
      """

    law opt_intersection_negation_empty(descr),
      requires: negatable?(descr),
      expects: Descr.empty?(Descr.opt_intersection(descr, Descr.opt_negation(descr))),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«opt_intersection_negation_empty:requires/1»] at requires
      obtain ⟨X, rfl, valid⟩ := negatable_map descr requires
      simp only [Lynx.apply_eq, «opt_intersection_negation_empty:ensures/1»]
      by_cases empty : X = []
      · subst empty
        have negation : Elixir.Module.Types.Descr.«opt_negation/1»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) = .ok (.atom "term") := by
          rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
          simp only [Elixir.Module.Types.Descr.«opt_difference/2»]
          unfold Elixir.Module.Types.Descr.«opt_difference/3»
          simp [Erlang.erlang.«==/2»]
        have intersection : Elixir.Module.Types.Descr.«opt_intersection/2»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) (.atom "term") = .ok (.map []) := by
          simp only [Elixir.Module.Types.Descr.«opt_intersection/2»]
          unfold Elixir.Module.Types.Descr.«opt_intersection/3»
          rfl
        simp [negation, intersection, empty_none]
      · obtain ⟨N, negation, static, bitmaps, atoms, funs, lists, tuples, maps, -, -⟩ := opt_negation_fields 97 X valid empty
          (.map []) (fun x y => ∀ m, ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3»
            (Dispatcher.ofTable Erlang.program.fun_table (m + 4)) x y (.map []) = .ok r ∧
            (kept (.atom "map", r) = Bool.true → EmptyMap r))
          (fun x hx => opt_map_cancel 93 x (valid.maps x hx))
        obtain ⟨I, run, only⟩ := opt_intersection_disjoint 99 X N (.map []) valid static bitmaps atoms
          (fun x y hx hy => funs x y hx hy 99) lists (fun x y hx hy => tuples x y hx hy _)
          (fun x y hx hy => maps x y hx hy 95)
        have negation' : Elixir.Module.Types.Descr.«opt_negation/1»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map X) = .ok (.map N) := by
          rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
          simpa [Elixir.Module.Types.Descr.«opt_difference/2»] using negation
        simp [negation', Elixir.Module.Types.Descr.«opt_intersection/2», run, empty_gone 97 I only]
      """

    law union_negation_term(descr),
      requires: negatable?(descr),
      expects: Descr.subtype?(Descr.term(), Descr.bare_union(descr, Descr.bare_negation(descr))),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«union_negation_term:requires/1»] at requires
      obtain ⟨X, rfl, valid⟩ := negatable_map descr requires
      simp only [Lynx.apply_eq, «union_negation_term:ensures/1»]
      by_cases empty : X = []
      · subst empty
        have negation : Elixir.Module.Types.Descr.«bare_negation/1»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) = .ok (.atom "term") := by
          simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
          unfold Elixir.Module.Types.Descr.«bare_difference/2»
          simp [Erlang.erlang.«==/2»]
        have union : Elixir.Module.Types.Descr.«bare_union/2»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) (.atom "term") = .ok (.atom "term") := by
          unfold Elixir.Module.Types.Descr.«bare_union/2»
          rfl
        obtain ⟨T, term, -, -, -, staticT⟩ := unfolded_term_fields
        simp [Elixir.Module.Types.Descr.«term/0», negation, union]
        unfold Elixir.Module.Types.Descr.«subtype?/2»
        simp [term, unfold_map, Erlang.erlang.«is_map_key/2», staticT, any_key, Lynx.Except.andAlso,
          Erlang.erlang.«/=/2»]
        unfold Elixir.Module.Types.Descr.«subtype_static?/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
      · obtain ⟨N, U, negation, union, sub⟩ := union_negation_covers X valid empty
        simp [Elixir.Module.Types.Descr.«term/0», negation, union, sub]
      """

    law opt_union_negation_term(descr),
      requires: negatable?(descr),
      expects: Descr.subtype?(Descr.term(), Descr.opt_union(descr, Descr.opt_negation(descr))),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«opt_union_negation_term:requires/1»] at requires
      obtain ⟨X, rfl, valid⟩ := negatable_map descr requires
      simp only [Lynx.apply_eq, «opt_union_negation_term:ensures/1»]
      by_cases empty : X = []
      · subst empty
        have negation : Elixir.Module.Types.Descr.«opt_negation/1»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) = .ok (.atom "term") := by
          rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
          simp only [Elixir.Module.Types.Descr.«opt_difference/2»]
          unfold Elixir.Module.Types.Descr.«opt_difference/3»
          simp [Erlang.erlang.«==/2»]
        have union : Elixir.Module.Types.Descr.«opt_union/2»
            (Dispatcher.ofTable Erlang.program.fun_table 100) (.map []) (.atom "term") = .ok (.atom "term") := by
          simp only [Elixir.Module.Types.Descr.«opt_union/2»]
          unfold Elixir.Module.Types.Descr.«opt_union/3»
          rfl
        obtain ⟨T, term, -, -, -, staticT⟩ := unfolded_term_fields
        simp [Elixir.Module.Types.Descr.«term/0», negation, union]
        unfold Elixir.Module.Types.Descr.«subtype?/2»
        simp [term, unfold_map, Erlang.erlang.«is_map_key/2», staticT, any_key, Lynx.Except.andAlso,
          Erlang.erlang.«/=/2»]
        unfold Elixir.Module.Types.Descr.«subtype_static?/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2»]
      · obtain ⟨N, U, negation, union, sub⟩ := opt_union_negation_covers X valid empty
        simp [Elixir.Module.Types.Descr.«term/0», negation, union, sub]
      """

    law de_morgan_union(left, right),
      requires: negatable?(left) and negatable?(right),
      expects:
        Descr.equal?(
          Descr.bare_negation(Descr.bare_union(left, right)),
          Descr.bare_intersection(Descr.bare_negation(left), Descr.bare_negation(right))
        ),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«de_morgan_union:requires/2», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨L, rfl, vL⟩ := negatable_map left (by simpa [Term.true] using requires.1)
      obtain ⟨R, rfl, vR⟩ := negatable_map right (by simpa [Term.true] using requires.2)
      simp only [Lynx.apply_eq, «de_morgan_union:ensures/2»]
      exact de_morgan_union_law L R vL vR
      """
  end
end
