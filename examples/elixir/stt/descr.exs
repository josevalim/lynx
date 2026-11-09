# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/stt/descr.exs
# Prove the set operations of Elixir's type system. The empty type law covers every type,
# the negation law covers bitmaps, atoms, functions, lists, tuples, and maps, and the
# membership laws cover bitmaps and atoms.
# Checked against Elixir 1.21.0-dev (2498525de), Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/module/types/descr.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule STTDescrProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  @moduletag timeout: :infinity
  import Bitwise, only: [&&&: 2]
  alias Module.Types.Descr

  # The values a type contains. Bitmap bits stand for the kinds of values
  # without further structure, and atoms are either listed or excluded.
  def member?(value, descr),
    do: bitmap_member?(value, Map.get(descr, :bitmap, 0)) or atom_member?(value, Map.get(descr, :atom))

  defp bitmap_member?(value, bits), do: (bits &&& kind(value)) != 0

  defp kind(value) when is_binary(value), do: 0b1
  defp kind(value) when is_bitstring(value), do: 0b10
  defp kind([]), do: 0b100
  defp kind(value) when is_integer(value), do: 0b1000
  defp kind(value) when is_float(value), do: 0b10000
  defp kind(value) when is_pid(value), do: 0b100000
  defp kind(value) when is_port(value), do: 0b1000000
  defp kind(value) when is_reference(value), do: 0b10000000
  defp kind(_value), do: 0

  defp atom_member?(value, {:union, set}) when is_atom(value), do: :sets.is_element(value, set)
  defp atom_member?(value, {:negation, set}) when is_atom(value), do: not :sets.is_element(value, set)
  defp atom_member?(_value, _atoms), do: false

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

  # Types of bitmaps, atoms, functions, and lists. Function types are unions
  # or negations of maps from arities to BDDs, whose contents are not inspected.
  def negatable?(descr) when is_map(descr), do: negatable_fields?(:maps.to_list(descr))
  def negatable?(_descr), do: false

  defp negatable_fields?([field | fields]), do: negatable_field?(field) and negatable_fields?(fields)
  defp negatable_fields?([]), do: true

  defp negatable_field?({:fun, {tag, arities}}) when tag in [:union, :negation], do: is_map(arities)
  defp negatable_field?({:list, bdd}), do: list_bdd?(bdd)
  defp negatable_field?({:tuple, bdd}), do: tuple_bdd?(bdd)
  defp negatable_field?({:map, bdd}), do: map_bdd?(bdd)
  defp negatable_field?(field), do: valid_fields?([field])

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
  # Erlang's term order. Their elements are the top type or static types of
  # bitmaps, atoms, tuples, and lists, whose BDDs may hold anything.
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
  defp element?(element) when is_map(element), do: element_fields?(:maps.to_list(element))
  defp element?(_element), do: false

  defp element_fields?([{:bitmap, bits} | fields]), do: is_integer(bits) and element_fields?(fields)

  defp element_fields?([{:atom, atoms} | fields]),
    do: valid_fields?([{:atom, atoms}]) and element_fields?(fields)

  defp element_fields?([{key, bdd} | fields]) when key in [:tuple, :list],
    do: any_bdd?(bdd, :bottom) and element_fields?(fields)

  defp element_fields?([]), do: true
  defp element_fields?(_fields), do: false

  defp any_bdd?(:bdd_top, _lower), do: true
  defp any_bdd?(:bdd_bot, _lower), do: true
  defp any_bdd?({key, _, _} = leaf, lower), do: is_integer(key) and leaf > lower

  defp any_bdd?({hash, {key, _, _} = lit, c, u, d}, lower),
    do:
      is_integer(hash) and is_integer(key) and lit > lower and any_bdd?(c, lit) and any_bdd?(u, lit) and
        any_bdd?(d, lit)

  defp any_bdd?(_bdd, _lower), do: false

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

    # Only bitmaps and atoms are modeled so far, so emptiness of the other
    # fields is cut off.
    cutoff &Descr.tuple_line_empty_seen?/4
    cutoff &Descr.init_map_line_empty?/4

    # Map literals with domain keys are not modeled.
    cutoff &Descr.map_domain_intersection/3
    cutoff &Descr.map_key_tag_to_field/1
    cutoff &Descr.fields_merge_with_defaults/5
    # Lists are empty without lines, so their line checks are cut off.
    cutoff &Descr.list_line_empty?/4
    cutoff &Descr.non_empty_list_literals_intersection/2
    cutoff &Descr.fun_empty?/2

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
    termination_suffix &:orddict.merge/3, ~LEAN"partial_fixpoint", recur: true

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

    /-- The fields that membership reads hold a natural bitmap and an atom type. -/
    abbrev Shaped (X : List (Term × Term)) : Prop :=
      (∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b) ∧
        (∀ w, mapLookup X (.atom "atom") = some w → AtomField w)

    /-- What `valid?/1` checks of a type. -/
    structure Valid (X : List (Term × Term)) : Prop where
      keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom"
      bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
      atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w

    theorem Valid.shaped {X : List (Term × Term)} (valid : Valid X) : Shaped X :=
      ⟨fun w found => let ⟨b, field, _⟩ := valid.bitmap w found; ⟨b, field⟩, valid.atom⟩

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
          (p.1 = .atom "atom" ∧ AtomField p.2) := by
      induction es with
      | nil => simp
      | cons e rest ih =>
        obtain ⟨k, w⟩ := e
        have head : ((k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
            (k = .atom "atom" ∧ AtomField w)) ∧
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
            exact ⟨Or.inr ⟨rfl, true, S, rfl, atom_keys_set S valid.1.1⟩, valid.2⟩
          · rename_i set fields heq
            simp at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            simp [Lynx.Except.andAlso_eq_true] at valid
            cases set <;> simp [«atoms?/1»] at valid
            rename_i S
            exact ⟨Or.inr ⟨rfl, false, S, rfl, atom_keys_set S valid.1⟩, valid.2⟩
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
      refine ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_⟩
      · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
        obtain ⟨p, mp, qp, -⟩ := entry q w lookup
        rcases each p mp with ⟨key, -⟩ | ⟨key, -⟩ <;> rw [key] at qp <;> simp at qp <;> simp [qp]
      · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
        rcases each p mp with ⟨key, field⟩ | ⟨key, -⟩
        · exact field
        · rw [key] at qp; simp at qp
      · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
        rcases each p mp with ⟨key, -⟩ | ⟨key, field⟩
        · rw [key] at qp; simp at qp
        · exact field

    theorem valid_map (descr : Term) (valid : «valid?/1» descr = .ok Term.true) :
        ∃ X, descr = .map X ∧ Valid X := by
      cases descr <;> simp [«valid?/1»] at valid
      exact ⟨_, rfl, valid_of _ (by simpa [«valid?/1»] using valid)⟩
    """

    # Membership is a Boolean over the bitmap and atom fields of a type.
    postlude ~LEAN"""
    /-! Membership in terms of the bitmap and atom fields. -/

    /-- The bitmap of a type, which is zero when the field is absent. -/
    def bits (X : List (Term × Term)) : Nat :=
      match mapLookup X (.atom "bitmap") with
      | some (.integer b) => b.toNat
      | _ => 0

    /-- Whether an atom field holds the atom `n`. -/
    def atomIn (n : String) : Option Term → Bool
      | some (.tuple ⟨[.atom "union", .map S]⟩) => (mapLookup S (.atom n)).isSome
      | some (.tuple ⟨[.atom "negation", .map S]⟩) => !(mapLookup S (.atom n)).isSome
      | _ => false

    /-- Whether the atom field of a type holds the atom `n`. -/
    def atoms (n : String) (X : List (Term × Term)) : Bool :=
      atomIn n (mapLookup X (.atom "atom"))

    def atomOf : Term → Option String
      | .atom n => some n
      | _ => none

    /-- Membership of a value whose kind has bits `k`, and which is the atom `a` if any. -/
    def holds (k : Nat) (a : Option String) (X : List (Term × Term)) : Bool :=
      (bits X &&& k != 0) || (match a with | some n => atoms n X | none => false)

    theorem atomIn_field (n : String) (pos : Bool) (S : List (Term × Term)) :
        atomIn n (some (.tuple #[.atom (if pos then "union" else "negation"), .map S])) =
          (pos == (mapLookup S (.atom n)).isSome) := by
      cases pos <;> cases h : (mapLookup S (.atom n)).isSome <;> simp [atomIn, h]

    theorem and_two_pow (x i : Nat) : (x &&& 2 ^ i != 0) = x.testBit i := by
      cases bit : x.testBit i
      · have : x &&& 2 ^ i = 0 := Nat.eq_of_testBit_eq fun j => by
          simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases same : i = j
          · subst same; simp [bit]
          · simp [same]
        simp [this]
      · have : (x &&& 2 ^ i).testBit i = Bool.true := by simp [bit]
        have nonzero : x &&& 2 ^ i ≠ 0 := fun zero => by rw [zero, Nat.zero_testBit] at this; cases this
        simp [nonzero]

    /-- The kinds of values are single bits, except for those without a bit. -/
    theorem kind_eq (value : Term) :
        ∃ k : Nat, «kind/1» value = .ok (.integer k) ∧ (k = 0 ∨ ∃ i, k = 2 ^ i ∧ atomOf value = none) := by
      cases value <;> simp [«kind/1», Erlang.erlang.«is_port/1», atomOf]
      case bitstring bytes lastBits valid =>
        by_cases whole : lastBits = 0
        · subst whole; exact ⟨1, by simp, Or.inr ⟨0, rfl⟩⟩
        · exact ⟨2, by simp, Or.inr ⟨1, rfl⟩⟩
      all_goals first
        | exact ⟨0, rfl, Or.inl rfl⟩
        | exact ⟨1, rfl, Or.inr ⟨0, rfl⟩⟩
        | exact ⟨2, rfl, Or.inr ⟨1, rfl⟩⟩
        | exact ⟨4, rfl, Or.inr ⟨2, rfl⟩⟩
        | exact ⟨8, rfl, Or.inr ⟨3, rfl⟩⟩
        | exact ⟨16, rfl, Or.inr ⟨4, rfl⟩⟩
        | exact ⟨32, rfl, Or.inr ⟨5, rfl⟩⟩
        | exact ⟨64, rfl, Or.inr ⟨6, rfl⟩⟩
        | exact ⟨128, rfl, Or.inr ⟨7, rfl⟩⟩

    theorem is_element_eq (q : Term) (X : List (Term × Term)) :
        Erlang.sets.«is_element/2» q (.map X) =
          .ok (if (mapLookup X q).isSome then .atom "true" else .atom "false") := by
      unfold Erlang.sets.«is_element/2»
      cases found : mapLookup X q <;> simp [found]

    theorem bool_term (b : Bool) : (if b then Term.atom "false" else .atom "true") =
        if !b then .atom "true" else .atom "false" := by
      cases b <;> rfl

    theorem atom_member_field (n : String) (field : Option Term) (atomsX : ∀ w, field = some w → AtomField w) :
        «atom_member?/2» (.atom n) (field.getD (.atom "nil")) =
          .ok (if atomIn n field then .atom "true" else .atom "false") := by
      cases field with
      | none => rfl
      | some w =>
        obtain ⟨pos, S, rfl, -⟩ := atomsX w rfl
        rw [atomIn_field]
        cases pos <;> cases h : (mapLookup S (.atom n)).isSome <;>
          simp [«atom_member?/2», is_element_eq, h, Erlang.erlang.«not/1»]

    theorem or_else_bool (x y : Bool) :
        Lynx.Except.orElse (.ok (if x then Term.atom "true" else .atom "false"))
          (.ok (if y then Term.atom "true" else .atom "false")) Bool.true =
          .ok (if x || y then Term.atom "true" else .atom "false") := by
      cases x <;> cases y <;> rfl

    /-- Membership is `holds` on the fields of a type. -/
    theorem member_eq (value : Term) : ∃ k : Nat, (k = 0 ∨ ∃ i, k = 2 ^ i ∧ atomOf value = none) ∧
        ∀ X, Shaped X → «member?/2» value (.map X) =
          .ok (if holds k (atomOf value) X then .atom "true" else .atom "false") := by
      obtain ⟨k, kinded, single⟩ := kind_eq value
      refine ⟨k, single, fun X shaped => ?_⟩
      obtain ⟨bitsX, atomsX⟩ := shaped
      have bitmap : «bitmap_member?/2» value ((mapLookup X (.atom "bitmap")).getD (.integer 0)) =
          .ok (if bits X &&& k != 0 then .atom "true" else .atom "false") := by
        have field : (mapLookup X (.atom "bitmap")).getD (.integer 0) = .integer (bits X) := by
          cases found : mapLookup X (.atom "bitmap") with
          | none => simp [bits, found]
          | some w =>
            obtain ⟨b, rfl⟩ := bitsX w found
            simp [bits, found]
        rw [field]
        simp only [«bitmap_member?/2», kinded, Lynx.Except.ok_bind]
        show (Erlang.erlang.«band/2» (.integer (.ofNat (bits X))) (.integer (.ofNat k)) >>= _) = _
        by_cases zero : bits X &&& k = 0 <;> simp [Erlang.erlang.«band/2», Erlang.erlang.«/=/2», zero]
      have atom : «atom_member?/2» value ((mapLookup X (.atom "atom")).getD (.atom "nil")) =
          .ok (if (match atomOf value with | some n => atoms n X | none => false)
            then .atom "true" else .atom "false") := by
        cases value with
        | atom n => exact atom_member_field n _ atomsX
        | _ => simp [«atom_member?/2», atomOf]
      have fields : «member?/2» value (.map X) = Lynx.Except.orElse
          («bitmap_member?/2» value ((mapLookup X (.atom "bitmap")).getD (.integer 0)))
          («atom_member?/2» value ((mapLookup X (.atom "atom")).getD (.atom "nil"))) Bool.true := by
        simp only [«member?/2», Elixir.Map.«get/2», Elixir.Map.«get/3», getMapKeys_single]
        cases mapLookup X (.atom "bitmap") <;> cases mapLookup X (.atom "atom") <;> rfl
      rw [fields, bitmap, atom, or_else_bool]
      rfl
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

    theorem no_dynamic {X : List (Term × Term)} (valid : Valid X) : mapLookup X (.atom "dynamic") = none := by
      cases h : mapLookup X (.atom "dynamic") with
      | none => rfl
      | some w =>
        rcases valid.keys _ (by rw [h]; rfl) with bad | bad <;> simp only [Term.atom.injEq] at bad <;>
          exact absurd bad (by decide)

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

    theorem union_fields (depth : Nat) (L R : List (Term × Term)) (validL : Valid L) (validR : Valid R) :
        ∃ out, Elixir.Module.Types.Descr.«bare_union/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.map L) (.map R) = .ok (.map out) ∧
          Shaped out ∧ bits out = bits L ||| bits R ∧ ∀ n, atoms n out = (atoms n L || atoms n R) := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have calls : ∀ q x y, (q = .atom "bitmap" ∨ q = .atom "atom") → mapLookup L q = some x →
          mapLookup R q = some y →
          Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            q x y = .ok (g q x y) := by
        intro q x y key hx hy
        rcases key with rfl | rfl
        · obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hx
          obtain ⟨b₂, rfl, -⟩ := validR.bitmap y hy
          simp [g, Elixir.Module.Types.Descr.«bare_union/3», Erlang.erlang.«bor/2»]
        · obtain ⟨p₁, S₁, rfl, set₁⟩ := validL.atom x hx
          obtain ⟨p₂, S₂, rfl, set₂⟩ := validR.atom y hy
          obtain ⟨p, E, hE, -⟩ := atom_union p₁ S₁ p₂ S₂ set₁ set₂
          simp only [g, Elixir.Module.Types.Descr.«bare_union/3», hE]
      obtain ⟨out, run, look⟩ : ∃ out, Elixir.Module.Types.Descr.«bare_union/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map out) ∧
          ∀ name, mapLookup out (.atom name) =
            match mapLookup R (.atom name) with
            | some y => some (match mapLookup L (.atom name) with | some x => g (.atom name) x y | none => y)
            | none => mapLookup L (.atom name) := by
        unfold Elixir.Module.Types.Descr.«bare_union/2»
        simp [getMapKeys_single, Erlang.erlang.«==/2», no_dynamic validL, no_dynamic validR]
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
            rw [Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure, calls e.1 x e.2 (validR.keys e.1 (by simp [hy])) hx hy])
        refine ⟨out, by simpa using run, fun name => ?_⟩
        rw [look, find_atom]
        cases mapLookup R (.atom name) <;> rfl
      have bitmap : (mapLookup out (.atom "bitmap") = none ∧ bits L ||| bits R = 0) ∨
          mapLookup out (.atom "bitmap") = some (.integer ↑(bits L ||| bits R)) := by
        rw [look]
        cases hR : mapLookup R (.atom "bitmap") with
        | none =>
          cases hL : mapLookup L (.atom "bitmap") with
          | none => left; simp [bits, hL, hR]
          | some x =>
            obtain ⟨b, rfl, -⟩ := validL.bitmap x hL
            right; simp [bits, hL, hR]
        | some y =>
          obtain ⟨b₂, rfl, -⟩ := validR.bitmap y hR
          right
          cases hL : mapLookup L (.atom "bitmap") with
          | none => simp [bits, hL, hR]
          | some x =>
            obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hL
            simp [bits, hL, hR, g, Elixir.Module.Types.Descr.«bare_union/3», Erlang.erlang.«bor/2»]
      have atom : (∀ w, mapLookup out (.atom "atom") = some w → AtomField w) ∧
          ∀ n, atomIn n (mapLookup out (.atom "atom")) = (atoms n L || atoms n R) := by
        rw [look]
        cases hR : mapLookup R (.atom "atom") with
        | none =>
          cases hL : mapLookup L (.atom "atom") with
          | none => exact ⟨fun w found => by simp at found, fun n => by simp [atoms, atomIn, hL, hR]⟩
          | some x =>
            exact ⟨fun w found => by simp at found; exact found ▸ validL.atom x hL,
              fun n => by simp only [atoms, hL, hR]; cases atomIn n (some x) <;> rfl⟩
        | some y =>
          obtain ⟨p₂, S₂, rfl, set₂⟩ := validR.atom y hR
          cases hL : mapLookup L (.atom "atom") with
          | none =>
            exact ⟨fun w found => by simp at found; exact found ▸ validR.atom _ hR,
              fun n => by simp [atoms, atomIn, hL, hR]⟩
          | some x =>
            obtain ⟨p₁, S₁, rfl, set₁⟩ := validL.atom x hL
            obtain ⟨p, E, hE, setE, mE⟩ := atom_union p₁ S₁ p₂ S₂ set₁ set₂
            have union : g (.atom "atom") (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
                (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
                .tuple #[.atom (if p then "union" else "negation"), .map E] := by
              simp only [g, Elixir.Module.Types.Descr.«bare_union/3», hE]
            refine ⟨fun w found => ?_, fun n => ?_⟩
            · simp only [union, Option.some.injEq] at found
              exact ⟨p, E, found.symm, setE⟩
            simp only [union, atoms, hL, hR, atomIn_field, mE]
      refine ⟨out, run, ⟨fun w found => ?_, fun w found => ?_⟩, ?_, fun n => atom.2 n⟩
      · rcases bitmap with ⟨none, -⟩ | some
        · rw [none] at found; cases found
        · rw [some] at found; cases found; exact ⟨_, rfl⟩
      · exact atom.1 w found
      · rcases bitmap with ⟨none, zero⟩ | some
        · rw [show bits out = 0 by simp [bits, none], zero]
        · simp [bits, some]


    /-! Laws compare memberships as Booleans. -/

    theorem eq_bool (x y : Bool) :
        Erlang.erlang.«==/2» (if x then Term.atom "true" else .atom "false")
          (if y then Term.atom "true" else .atom "false") =
          .ok (if x == y then Term.atom "true" else .atom "false") := by
      cases x <;> cases y <;> simp [Erlang.erlang.«==/2»]

    theorem and_also_bool (x y : Bool) :
        Lynx.Except.andAlso (.ok (if x then Term.atom "true" else .atom "false"))
          (.ok (if y then Term.atom "true" else .atom "false")) Bool.true =
          .ok (if x && y then Term.atom "true" else .atom "false") := by
      cases x <;> cases y <;> rfl

    theorem not_bool (x : Bool) :
        Erlang.erlang.«not/1» (if x then Term.atom "true" else .atom "false") =
          .ok (if !x then Term.atom "true" else .atom "false") := by
      cases x <;> rfl

    theorem holds_union (k : Nat) (a : Option String) (out L R : List (Term × Term))
        (bitsOut : bits out = bits L ||| bits R) (atomsOut : ∀ n, atoms n out = (atoms n L || atoms n R)) :
        holds k a out = (holds k a L || holds k a R) := by
      have distrib : (bits L ||| bits R) &&& k = (bits L &&& k) ||| (bits R &&& k) :=
        Nat.and_or_distrib_right _ _ _
      have nonzero (x y : Nat) : (x ||| y != 0) = (x != 0 || y != 0) := by
        rw [Bool.eq_iff_iff]; simp [Nat.or_eq_zero_iff]; omega
      simp only [holds, bitsOut, distrib, nonzero]
      generalize (bits L &&& k != 0) = x
      generalize (bits R &&& k != 0) = y
      cases a with
      | none => cases x <;> cases y <;> rfl
      | some n =>
        simp only [atomsOut]
        cases x <;> cases y <;> cases atoms n L <;> cases atoms n R <;> rfl
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

    theorem intersection_fields (depth : Nat) (L R : List (Term × Term)) (validL : Valid L) (validR : Valid R) :
        ∃ out, Elixir.Module.Types.Descr.«bare_intersection/2»
            (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map out) ∧
          Shaped out ∧ bits out = bits L &&& bits R ∧ ∀ n, atoms n out = (atoms n L && atoms n R) := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have calls : ∀ q x y, (q = .atom "bitmap" ∨ q = .atom "atom") → mapLookup L q = some x →
          mapLookup R q = some y →
          Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            q x y = .ok (g q x y) := by
        intro q x y key hx hy
        rcases key with rfl | rfl
        · obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hx
          obtain ⟨b₂, rfl, -⟩ := validR.bitmap y hy
          simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», Erlang.erlang.«band/2»]
        · obtain ⟨p₁, S₁, rfl, set₁⟩ := validL.atom x hx
          obtain ⟨p₂, S₂, rfl, set₂⟩ := validR.atom y hy
          rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, -⟩ | ⟨hE, -⟩ <;>
            simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE]
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr" "bare_intersection" #[] L R g (by
          intro e me y hy
          have hx := mapLookup_of_mem_mapEntries me
          rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, calls e.1 e.2 y (validL.keys e.1 (by simp [hx])) hx hy])
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] I kept (by
          intro e _
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
      have run : Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map out) := by
        unfold Elixir.Module.Types.Descr.«bare_intersection/2»
        simp [getMapKeys_single, no_dynamic validL, no_dynamic validR]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runO]
      have look : ∀ name, mapLookup out (.atom name) =
          match mapLookup L (.atom name), mapLookup R (.atom name) with
          | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else none
          | _, _ => none := by
        intro name
        rw [lookO, find_atom, lookI, find_atom]
        cases mapLookup L (.atom name) <;> cases hR : mapLookup R (.atom name) <;> simp [hR]
      have bitmap : (mapLookup out (.atom "bitmap") = none ∧ bits L &&& bits R = 0) ∨
          mapLookup out (.atom "bitmap") = some (.integer ↑(bits L &&& bits R)) := by
        rw [look]
        cases hL : mapLookup L (.atom "bitmap") with
        | none => left; simp [bits, hL]
        | some x =>
          obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hL
          cases hR : mapLookup R (.atom "bitmap") with
          | none => left; simp [bits, hR]
          | some y =>
            obtain ⟨b₂, rfl, -⟩ := validR.bitmap y hR
            by_cases zero : b₁ &&& b₂ = 0 <;>
              simp [bits, hL, hR, g, Elixir.Module.Types.Descr.«bare_intersection/3», Erlang.erlang.«band/2»,
                kept, zero]
      have atom : (∀ w, mapLookup out (.atom "atom") = some w → AtomField w) ∧
          ∀ n, atomIn n (mapLookup out (.atom "atom")) = (atoms n L && atoms n R) := by
        rw [look]
        cases hL : mapLookup L (.atom "atom") with
        | none => exact ⟨fun w found => by simp at found, fun n => by simp [atoms, atomIn, hL]⟩
        | some x =>
          obtain ⟨p₁, S₁, rfl, set₁⟩ := validL.atom x hL
          cases hR : mapLookup R (.atom "atom") with
          | none => exact ⟨fun w found => by simp at found, fun n => by simp [atoms, atomIn, hR]⟩
          | some y =>
            obtain ⟨p₂, S₂, rfl, set₂⟩ := validR.atom y hR
            rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -, -, mE⟩ | ⟨hE, mE⟩
            · have inter : g (.atom "atom") (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
                  (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
                  .tuple #[.atom (if p then "union" else "negation"), .map E] := by
                simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE]
              have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) =
                  Bool.true := by
                simp [kept]
              simp only [inter, keep, ite_true]
              refine ⟨fun w found => ?_, fun n => ?_⟩
              · simp only [Option.some.injEq] at found
                exact ⟨p, E, found.symm, setE⟩
              · simp only [atoms, hL, hR, atomIn_field, mE]
            · have inter : g (.atom "atom") (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
                  (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .integer 0 := by
                simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE]
              have drop : kept (.atom "atom", .integer 0) = Bool.false := by simp [kept]
              simp only [inter, drop]
              refine ⟨fun w found => by simp at found, fun n => ?_⟩
              simp only [atoms, hL, hR, atomIn_field, mE]
              rfl
      refine ⟨out, run, ⟨fun w found => ?_, fun w found => atom.1 w found⟩, ?_, fun n => atom.2 n⟩
      · rcases bitmap with ⟨none, -⟩ | some
        · rw [none] at found; cases found
        · rw [some] at found; cases found; exact ⟨_, rfl⟩
      · rcases bitmap with ⟨none, zero⟩ | some
        · rw [show bits out = 0 by simp [bits, none], zero]
        · simp [bits, some]

    theorem holds_intersection (k : Nat) (a : Option String) (single : k = 0 ∨ ∃ i, k = 2 ^ i ∧ a = none)
        (out L R : List (Term × Term)) (bitsOut : bits out = bits L &&& bits R)
        (atomsOut : ∀ n, atoms n out = (atoms n L && atoms n R)) :
        holds k a out = (holds k a L && holds k a R) := by
      rcases single with rfl | ⟨i, rfl, rfl⟩
      · cases a with
        | none => simp [holds]
        | some n => simp [holds, atomsOut]
      · simp [holds, bitsOut, and_two_pow]
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

    theorem difference_step (depth : Nat) (g : Term → Term → Term → Term) (acc : List (Term × Term))
        (key v₂ : Term)
        (calls : ∀ v₁, mapLookup acc key = some v₁ →
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            key v₁ v₂ = .ok (g key v₁ v₂)) :
        Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
            (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[]) key v₂ (.map acc) = .ok (.map (differenceStep g acc (key, v₂))) := by
      unfold Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4»
      cases found : mapLookup acc key with
      | none => simp [getMapKeys_single, found, differenceStep]
      | some v₁ =>
        simp only [getMapKeys_single, found, Option.toList_some, Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure,
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
    theorem difference_fold (depth : Nat) (g : Term → Term → Term → Term) (es acc : List (Term × Term))
        (distinct : es.Pairwise (fun a b => exactCompare a.1 b.1 ≠ .eq))
        (calls : ∀ e ∈ es, ∀ v₁, mapLookup acc e.1 = some v₁ →
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            e.1 v₁ e.2 = .ok (g e.1 v₁ e.2)) :
        ∃ M, es.foldlM (fun acc entry =>
            (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
              (.function "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3
              #[.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[]]) #[entry.1, entry.2, acc] : Except Exception Term))
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
              #[.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[]]) #[e.1, e.2, .map acc] : Except Exception Term) =
            .ok (.map (differenceStep g acc e)) := by
          rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-dynamic_difference/3-fun-0-/3».pure,
            difference_step depth g acc e.1 e.2 (calls e (List.mem_cons_self ..))]
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
          p = (p₁ || !p₂) ∧
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
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun q => ?_⟩
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
          Erlang.erlang.«==/2»], setE, rfl, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun q => ?_⟩
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
            Erlang.erlang.«==/2», nonzero], setE, rfl, fun q => ?_⟩
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

    theorem difference_fields (depth : Nat) (L R : List (Term × Term)) (validL : Valid L) (validR : Valid R) :
        ∃ out, Elixir.Module.Types.Descr.«bare_difference/2»
            (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map L) (.map R) = .ok (.map out) ∧
          Shaped out ∧ bits out = bits L - (bits L &&& bits R) ∧
          ∀ n, atoms n out = (atoms n L && !atoms n R) := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have calls : ∀ q x y, (q = .atom "bitmap" ∨ q = .atom "atom") → mapLookup L q = some x →
          mapLookup R q = some y →
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            q x y = .ok (g q x y) := by
        intro q x y key hx hy
        rcases key with rfl | rfl
        · obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hx
          obtain ⟨b₂, rfl, -⟩ := validR.bitmap y hy
          simp [g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]
        · obtain ⟨p₁, S₁, rfl, set₁⟩ := validL.atom x hx
          obtain ⟨p₂, S₂, rfl, set₂⟩ := validR.atom y hy
          rcases atom_difference p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, -⟩ | ⟨hE, -⟩ <;>
            simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
      obtain ⟨out, fold, lookOut⟩ := difference_fold depth g (mapEntries R) L (mapEntries_distinct R) (by
        intro e member v₁ found
        have hy := mapLookup_of_mem_mapEntries member
        exact calls e.1 v₁ e.2 (validR.keys e.1 (by simp [hy])) found hy)
      have run : Elixir.Module.Types.Descr.«bare_difference/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map L) (.map R) = .ok (.map out) := by
        unfold Elixir.Module.Types.Descr.«bare_difference/2»
        simp [Erlang.erlang.«==/2»]
        by_cases emptyR : R = []
        · subst emptyR
          simpa using fold
        · simp only [emptyR, ite_false, unfold_map, static_map (no_dynamic validL), static_map (no_dynamic validR), Lynx.Except.ok_bind]
          unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
          simp [Erlang.erlang.«==/2», emptyR, Erlang.maps.«fold/3»]
          simpa using fold
      have look : ∀ name, mapLookup out (.atom name) =
          match mapLookup R (.atom name) with
          | some y => (mapLookup L (.atom name)).bind fun x =>
              if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else none
          | none => mapLookup L (.atom name) := by
        intro name
        rw [lookOut, find_atom]
        cases mapLookup R (.atom name) <;> rfl
      have bitmap : (mapLookup out (.atom "bitmap") = none ∧ bits L - (bits L &&& bits R) = 0) ∨
          mapLookup out (.atom "bitmap") = some (.integer ↑(bits L - (bits L &&& bits R))) := by
        rw [look]
        cases hR : mapLookup R (.atom "bitmap") with
        | none =>
          cases hL : mapLookup L (.atom "bitmap") with
          | none => left; simp [bits, hL]
          | some x =>
            obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hL
            right; simp [bits, hL, hR]
        | some y =>
          obtain ⟨b₂, rfl, -⟩ := validR.bitmap y hR
          cases hL : mapLookup L (.atom "bitmap") with
          | none => left; simp [bits, hL]
          | some x =>
            obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hL
            have le : b₁ &&& b₂ ≤ b₁ := Nat.and_le_left
            by_cases zero : b₁ - (b₁ &&& b₂) = 0
            · left
              simp [bits, hL, hR, g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», kept]
              omega
            · right
              simp [bits, hL, hR, g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», kept]
              omega
      have atom : (∀ w, mapLookup out (.atom "atom") = some w → AtomField w) ∧
          ∀ n, atomIn n (mapLookup out (.atom "atom")) = (atoms n L && !atoms n R) := by
        rw [look]
        cases hR : mapLookup R (.atom "atom") with
        | none =>
          refine ⟨fun w found => validL.atom w (by simpa using found), fun n => ?_⟩
          simp only [atoms, hR]
          cases atomIn n (mapLookup L (.atom "atom")) <;> rfl
        | some y =>
          obtain ⟨p₂, S₂, rfl, set₂⟩ := validR.atom y hR
          cases hL : mapLookup L (.atom "atom") with
          | none => exact ⟨fun w found => by simp at found, fun n => by simp [atoms, atomIn, hL]⟩
          | some x =>
            obtain ⟨p₁, S₁, rfl, set₁⟩ := validL.atom x hL
            rcases atom_difference p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -, mE⟩ | ⟨hE, mE⟩
            · have diff : g (.atom "atom") (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
                  (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
                  .tuple #[.atom (if p then "union" else "negation"), .map E] := by
                simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
              have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) =
                  Bool.true := by
                simp [kept]
              simp only [diff, keep, ite_true, Option.bind_some]
              refine ⟨fun w found => ?_, fun n => ?_⟩
              · simp only [Option.some.injEq] at found
                exact ⟨p, E, found.symm, setE⟩
              · simp only [atoms, hL, hR, atomIn_field, mE]
            · have diff : g (.atom "atom") (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
                  (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .integer 0 := by
                simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
              have drop : kept (.atom "atom", .integer 0) = Bool.false := by simp [kept]
              simp only [diff, drop, Option.bind_some]
              refine ⟨fun w found => by simp at found, fun n => ?_⟩
              simp only [atoms, hL, hR, atomIn_field, mE]
              rfl
      refine ⟨out, run, ⟨fun w found => ?_, fun w found => atom.1 w found⟩, ?_, fun n => atom.2 n⟩
      · rcases bitmap with ⟨none, -⟩ | some
        · rw [none] at found; cases found
        · rw [some] at found; cases found; exact ⟨_, rfl⟩
      · rcases bitmap with ⟨none, zero⟩ | some
        · rw [show bits out = 0 by simp [bits, none], zero]
        · simp [bits, some]

    theorem holds_difference (k : Nat) (a : Option String) (single : k = 0 ∨ ∃ i, k = 2 ^ i ∧ a = none)
        (out L R : List (Term × Term)) (bitsOut : bits out = bits L - (bits L &&& bits R))
        (atomsOut : ∀ n, atoms n out = (atoms n L && !atoms n R)) :
        holds k a out = (holds k a L && !holds k a R) := by
      rcases single with rfl | ⟨i, rfl, rfl⟩
      · cases a with
        | none => simp [holds]
        | some n => simp [holds, atomsOut]
      · simp [holds, bitsOut, and_two_pow, testBit_sub_and]

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

    # Lazy BDDs ordered by their literals: unions, removals, intersections, and
    # negations terminate and compute the propositional connectives, so a
    # BDD that no assignment of its literals satisfies has no line.
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

    /-! Unions. -/

    def UnionOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_union/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a || eval ρ b)

    def RemoveOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_remove/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)

    def RemoveBddOk (a b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_remove_bdd/2» a b = .ok r ∧
        (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)

    /-- Every pair of BDDs over the universe below the measure `n` unites and removes. -/
    def Below (U : List Term) (n : Nat) : Prop :=
      ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → UnionOk a b ∧ RemoveOk a b ∧ RemoveBddOk a b

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
        (ih : Below U (μ U a b)) : UnionOk a b := by
      by_cases same : exactCompare b a = .eq
      · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_⟩
        · unfold Elixir.Module.Types.Descr.«bdd_union/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [← eval_congr wb resp same]; simp
      by_cases ta : a = .atom "bdd_top"
      · subst ta
        refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases tb : b = .atom "bdd_top"
      · subst tb
        refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fa : a = .atom "bdd_bot"
      · subst fa
        refine ⟨b, ?_, fun ok _ wb => wb, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fb : b = .atom "bdd_bot"
      · subst fb
        refine ⟨a, ?_, fun ok wa _ => wa, fun ρ _ => by simp⟩
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
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := (ih c₁ b (hc.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)).2.1
        obtain ⟨r₂, run₂, keep₂, sem₂⟩ := (ih u₁ b (hu.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)).1
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := (ih d₁ b (hd.mono fun _ h => h.1) wb
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
        · obtain ⟨r, runr, keepr, semr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wb)
            (keep₂ _ (hu.mono fun _ h => h.1) wb)
            (lower (fun m ha' hb' => ⟨keep₁ _ (High.split split wa ha').1 hb', keep₂ _ (High.split split wa ha').2.1 hb'⟩)
              ⟨keep₁ _ Hc HB, keep₂ _ Hu HB⟩)).1
          refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_⟩
          · obtain ⟨oc, ou, -⟩ := split.children oka
            exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) okb) (keep₂ ok (ou.mono fun _ h => h.1) okb)
          · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wb) resp post
            have s₁ := sem₁ ρ resp
            have s₂ := sem₂ ρ resp
            have s₃ := sem₃ ρ resp
            rw [semr ρ resp, split.eval ρ, s₂]
            rw [← e₃] at s₁
            cases hB : eval ρ b <;> cases hl : ρ la <;> simp_all [Bool.or_comm, Bool.or_left_comm]
        · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
          refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_⟩
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
            obtain ⟨r, runr, keepr, semr⟩ := (ih (.atom "bdd_top") u₂ Bdd.top (hu.mono fun _ h => h.1)
              (lowerB (fun m _ hb' => ⟨Bdd.top, (High.split (Or.inl ⟨h₂, rfl⟩) wb hb').2.1⟩) ⟨Bdd.top, Hu⟩)).1
            refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok _ okb => ?_,
              fun ρ resp => ?_⟩
            · exact keepr ok Bdd.top ((Bdd.node_iff.mp okb).2.2.2.1.mono fun _ h => h.1)
            · rw [semr ρ resp]
              cases hl : ρ lb <;> simp [hl, sameLit ρ resp]
          · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok _ okb => ?_,
              fun ρ resp => ?_⟩
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
            obtain ⟨r, runr, keepr, semr⟩ := (ih (.atom "bdd_top") u₁ Bdd.top (hu.mono fun _ h => h.1)
              (lower (fun m ha' _ => ⟨Bdd.top, (High.split (Or.inl ⟨h₁, rfl⟩) wa ha').2.1⟩) ⟨Bdd.top, Hu⟩)).1
            refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka _ => ?_,
              fun ρ resp => ?_⟩
            · exact keepr ok Bdd.top ((Bdd.node_iff.mp oka).2.2.2.1.mono fun _ h => h.1)
            · rw [semr ρ resp]
              cases hl : ρ la <;> simp [hl, ← sameLit ρ resp]
          · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka _ => ?_,
              fun ρ resp => ?_⟩
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
          obtain ⟨r₁, run₁, keep₁, sem₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
            (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
              ⟨Hc₁, Hc₂.congr order⟩)).1
          obtain ⟨r₂, run₂, keep₂, sem₂⟩ := (ih u₁ u₂ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1)
            (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, (High.split splitB wb hb').2.1⟩)
              ⟨Hu₁, Hu₂.congr order⟩)).1
          obtain ⟨r₃, run₃, keep₃, sem₃⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
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
          · obtain ⟨r, runr, keepr, semr⟩ := (ih r₁ r₂ (keep₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
              (keep₂ _ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1))
              (lower (fun m ha' hb' => ⟨keep₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
                keep₂ _ (High.split splitA wa ha').2.1 (High.split splitB wb hb').2.1⟩)
                ⟨keep₁ _ Hc₁ (Hc₂.congr order), keep₂ _ Hu₁ (Hu₂.congr order)⟩)).1
            refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_,
              fun ρ resp => ?_⟩
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
              fun ρ resp => ?_⟩
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
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := (ih c₂ a (hc.mono fun _ h => h.1) wa
          (lowerB (fun m ha' hb' => ⟨(High.split split wb hb').1, ha'⟩) ⟨Hc, HA⟩)).2.1
        obtain ⟨r₂, run₂, keep₂, sem₂⟩ := (ih a u₂ wa (hu.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)).1
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := (ih d₂ a (hd.mono fun _ h => h.1) wa
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
        · obtain ⟨r, runr, keepr, semr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wa)
            (keep₂ _ wa (hu.mono fun _ h => h.1))
            (lowerB (fun m ha' hb' => ⟨keep₁ _ (High.split split wb hb').1 ha', keep₂ _ ha' (High.split split wb hb').2.1⟩)
              ⟨keep₁ _ Hc HA, keep₂ _ HA Hu⟩)).1
          refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_⟩
          · obtain ⟨oc, ou, -⟩ := split.children okb
            exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) oka) (keep₂ ok oka (ou.mono fun _ h => h.1))
          · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wa) resp post
            have s₁ := sem₁ ρ resp
            have s₂ := sem₂ ρ resp
            have s₃ := sem₃ ρ resp
            rw [semr ρ resp, split.eval ρ, s₂]
            rw [← e₃] at s₁
            cases hA : eval ρ a <;> cases hl : ρ lb <;> simp_all [Bool.or_comm, Bool.or_left_comm]
        · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
      · refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ resp => ?_⟩
        · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [eval_congr wb resp same]; simp
      rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₁, la, c₁, u₁, d₁, rfl⟩
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl⟩
        unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl⟩
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
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := (ih c₁ _ (hc₁.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, hb'⟩) ⟨Hc₁, HB⟩)).2.2
        obtain ⟨r₂, run₂, keep₂, sem₂⟩ := (ih u₁ _ (hu₁.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, hb'⟩) ⟨Hu₁, HB⟩)).2.2
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := (ih d₁ _ (hd₁.mono fun _ h => h.1) wb
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, hb'⟩) ⟨Hd₁, HB⟩)).2.2
        obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc₁ (raiseB wb))
          (keep₂ _ hu₁ (raiseB wb)) (keep₃ _ hd₁ (raiseB wb))
        refine ⟨.tuple #[.integer h₃, la, r₁, r₂, r₃], ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
        obtain ⟨x₁, runx₁, keepx₁, semx₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
            ⟨Hc₁, Hc₂.congr order⟩)).2.1
        obtain ⟨x₂, runx₂, keepx₂, semx₂⟩ := (ih x₁ u₂ (keepx₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
          (hu₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨keepx₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
            (High.split splitB wb hb').2.1⟩) ⟨keepx₁ _ Hc₁ (Hc₂.congr order), Hu₂.congr order⟩)).2.1
        obtain ⟨y₁, runy₁, keepy₁, semy₁⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, (High.split splitB wb hb').2.2⟩)
            ⟨Hd₁, Hd₂.congr order⟩)).2.1
        obtain ⟨y₂, runy₂, keepy₂, semy₂⟩ := (ih y₁ u₂ (keepy₁ _ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1))
          (hu₂.mono fun _ h => h.1)
          (lower (fun m ha' hb' => ⟨keepy₁ _ (High.split splitA wa ha').2.2 (High.split splitB wb hb').2.2,
            (High.split splitB wb hb').2.1⟩) ⟨keepy₁ _ Hd₁ (Hd₂.congr order), Hu₂.congr order⟩)).2.1
        have bx := keepx₂ _ (keepx₁ _ hc₁ (hc₂.congr order)) (hu₂.congr order)
        have byy := keepy₂ _ (keepy₁ _ hd₁ (hd₂.congr order)) (hu₂.congr order)
        obtain ⟨h₃, node⟩ := node_new la x₂ u₁ y₂ (head_leaf wa ha) bx hu₁ byy
        refine ⟨.tuple #[.integer h₃, la, x₂, u₁, y₂], ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
        obtain ⟨r, run, keep, sem⟩ := (ih _ u₂ wa (hu₂.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split splitB wb hb').2.1⟩) ⟨HA, Hu₂⟩)).2.1
        refine ⟨r, ?_, fun ok oka okb => keep ok oka ((splitB.children okb).2.1.mono fun _ h => h.1),
          fun ρ resp => ?_⟩
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
        (ih : Below U (μ U a b)) : RemoveOk a b := by
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp⟩
        simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
      · refine ⟨a, ?_, fun _ oka _ => oka, fun ρ _ => rfl⟩
        simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
      · -- removing a leaf
        have leafRun : Elixir.Module.Types.Descr.«bdd_remove/2» a (.tuple #[.integer k, x, y]) =
            Elixir.Module.Types.Descr.«bdd_remove_leaf/2» a (.tuple #[.integer k, x, y]) := by
          simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
        have fallback : ¬(∃ (h : Int) (la c u d : Term), a = .tuple #[.integer h, la, c, u, d] ∧
            exactCompare (.tuple #[.integer k, x, y]) la = .eq) → RemoveOk a (.tuple #[.integer k, x, y]) := by
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
          · refine ⟨.atom "bdd_bot", by rw [leafRun, run, if_pos same], fun _ _ _ => Bdd.bot, fun ρ resp => ?_⟩
            rw [eval_congr wb resp same]; simp
          · exact ⟨a, by rw [leafRun, run, if_neg same], fun _ oka _ => oka, fun ρ _ => rfl⟩
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
          obtain ⟨r₁, run₁, keep₁, sem₁⟩ := union_step U la u wl (hu.mono fun _ h => h.1)
            (ih.mono (μ_le fun m ha' _ => ⟨highLit ha', (High.split splitA wa ha').2.1⟩))
          have wr₁ := keep₁ _ wl (hu.mono fun _ h => h.1)
          obtain ⟨r₂, run₂, keep₂, sem₂⟩ := union_step U r₁ d wr₁ (hd.mono fun _ h => h.1)
            (ih.mono (μ_le fun m ha' _ =>
              ⟨keep₁ _ (highLit ha') (High.split splitA wa ha').2.1, (High.split splitA wa ha').2.2⟩))
          refine ⟨r₂, ?_, fun ok oka _ => ?_, fun ρ resp => ?_⟩
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
        obtain ⟨r, runr, keep, sem⟩ := remove_bdd_step U a _ wa wb ih
        exact ⟨r, by rw [run, runr], keep, sem⟩

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

    theorem union_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : UnionOk a b :=
      let U := lits a ++ lits b
      (below_all U _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
        (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)).1

    theorem remove_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : RemoveOk a b :=
      let U := lits a ++ lits b
      (below_all U _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
        (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)).2.1

    /-! Intersections. -/

    /-- Nodes whose constrained and dual branches are equal collapse into a union. -/
    theorem post_spec (lit r₁ r₂ r₃ : Term) (h : Int) {okU : Term → Prop}
        (w₁ : Bdd okU r₁) (w₂ : Bdd okU r₂) (w₃ : Bdd okU r₃) :
        ∃ r, (if exactCompare r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
            else .ok (.tuple #[.integer h, lit, r₁, r₂, r₃])) = .ok r ∧
          (∀ ok : Term → Prop, IsLeaf lit → ok lit → Bdd (Above ok lit) r₁ → Bdd (Above ok lit) r₂ →
            Bdd (Above ok lit) r₃ → Bdd ok r) ∧
          ∀ ρ, Resp ρ → eval ρ r = ((ρ lit && eval ρ r₁) || eval ρ r₂ || (!ρ lit && eval ρ r₃)) := by
      by_cases post : exactCompare r₃ r₁ = .eq
      · obtain ⟨r, run, keep, sem⟩ := union_ok w₁ w₂
        refine ⟨r, by rw [ite_eq_left_of_eq_true _ _ (eq_true post), run], fun ok _ _ o₁ o₂ _ =>
          keep ok (o₁.mono fun _ h => h.1) (o₂.mono fun _ h => h.1), fun ρ resp => ?_⟩
        rw [sem ρ resp, eval_congr w₃ resp post]
        cases ρ lit <;> cases eval ρ r₁ <;> simp
      · exact ⟨_, ite_eq_right_of_eq_false _ _ (eq_false post), fun ok leaf okl o₁ o₂ o₃ =>
          Bdd.node_iff.mpr ⟨leaf, okl, o₁, o₂, o₃⟩, fun ρ _ => eval_node ρ _ _ _ _ _⟩

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

    theorem inter_eq_spec {okU : Term → Prop} (cd₁ cd₂ u₁ u₂ : Term) (w₁ : Bdd okU cd₁) (w₂ : Bdd okU cd₂)
        (w₃ : Bdd okU u₁) (w₄ : Bdd okU u₂) (i₁ : InterOk cd₁ cd₂) (i₂ : InterOk cd₁ u₂) (i₃ : InterOk u₁ cd₂) :
        ∃ r, Elixir.Module.Types.Descr.«bdd_intersection_eq/4» cd₁ cd₂ u₁ u₂ = .ok r ∧
          (∀ ok, Bdd ok cd₁ → Bdd ok cd₂ → Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
          ∀ ρ, Resp ρ → eval ρ r = ((eval ρ cd₁ && eval ρ cd₂) || (eval ρ cd₁ && eval ρ u₂) ||
            (eval ρ u₁ && eval ρ cd₂)) := by
      obtain ⟨r₁, run₁, keep₁, sem₁⟩ := i₁
      obtain ⟨r₂, run₂, keep₂, sem₂⟩ := i₂
      obtain ⟨r₃, run₃, keep₃, sem₃⟩ := i₃
      by_cases top : r₁ = .atom "bdd_top"
      · subst top
        refine ⟨.atom "bdd_top", ?_, fun _ _ _ _ _ => Bdd.top, fun ρ resp => ?_⟩
        · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
          simp [run₁]
        · have := sem₁ ρ resp
          simp at this
          simp [this]
      · obtain ⟨r₄, run₄, keep₄, sem₄⟩ := union_ok (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂)
        obtain ⟨r, runr, keepr, semr⟩ := union_ok (keep₁ _ w₁ w₂) (keep₄ _ (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂))
        refine ⟨r, ?_, fun ok o₁ o₂ o₃ o₄ => keepr ok (keep₁ ok o₁ o₂)
          (keep₄ ok (keep₂ ok o₁ o₄) (keep₃ ok o₃ o₂)), fun ρ resp => ?_⟩
        · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
          simp only [run₁, Lynx.Except.ok_bind]
          simp [run₂, run₃, run₄, runr]
        · rw [semr ρ resp, sem₄ ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp]
          simp [Bool.or_assoc]

    def BelowI (U : List Term) (n : Nat) : Prop :=
      ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → InterOk a b

    theorem inter_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
        (ih : BelowI U (μ U a b)) : InterOk a b := by
      by_cases same : exactCompare b a = .eq
      · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_⟩
        · unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
          simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
        · rw [← eval_congr wb resp same]; simp
      by_cases ta : a = .atom "bdd_top"
      · subst ta
        refine ⟨b, ?_, fun ok _ okb => okb, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases tb : b = .atom "bdd_top"
      · subst tb
        refine ⟨a, ?_, fun ok oka _ => oka, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fa : a = .atom "bdd_bot"
      · subst fa
        refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp⟩
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», same]
      by_cases fb : b = .atom "bdd_bot"
      · subst fb
        refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp⟩
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
        obtain ⟨r, runr, keep, sem⟩ := post_spec la r₁ r₂ r₃ h₁ w₁ w₂ w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
          refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_⟩
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
          obtain ⟨r, runr, keep, sem⟩ := post_spec lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
          obtain ⟨r, runr, keep, sem⟩ := post_spec la r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
                High m x ∧ High m y) → InterOk x y :=
            fun wx wy hx hy mono => ih _ _ (U' wx) (U' wy) (lower mono ⟨hx, hy⟩)
          have bool : ∀ ρ, Resp ρ → ρ lb = ρ la := fun ρ resp => (sameLit ρ resp).symm
          by_cases su : exactCompare u₂ u₁ = .eq
          · obtain ⟨r₁, run₁, keep₁, sem₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
            obtain ⟨r₃, run₃, keep₃, sem₃⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
            have w₁ := keep₁ _ hc₁ hc₂
            have w₃ := keep₃ _ hd₁ hd₂
            obtain ⟨h₃, node⟩ := node_new la r₁ u₁ r₃ (head_leaf wa ha) w₁ hu₁ w₃
            obtain ⟨r, runr, keep, sem⟩ := post_spec la r₁ u₁ r₃ h₃ w₁ hu₁ w₃
            refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
              obtain ⟨i₁, ri₁, ki₁, si₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
              obtain ⟨i₂, ri₂, ki₂, si₂⟩ := pair hc₁ hu₂ Hc₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').2.1⟩
              obtain ⟨i₃, ri₃, ki₃, si₃⟩ := pair hu₁ hc₂ Hu₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').1⟩
              obtain ⟨r₁, run₁, keep₁, sem₁⟩ := inter_eq_spec c₁ c₂ u₁ u₂ hc₁ hc₂ hu₁ hu₂
                ⟨i₁, ri₁, ki₁, si₁⟩ ⟨i₂, ri₂, ki₂, si₂⟩ ⟨i₃, ri₃, ki₃, si₃⟩
              obtain ⟨r₂, run₂, keep₂, sem₂⟩ := pair hu₁ hu₂ Hu₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.1⟩
              obtain ⟨j₁, rj₁, kj₁, sj₁⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
              obtain ⟨j₂, rj₂, kj₂, sj₂⟩ := pair hd₁ hu₂ Hd₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.1⟩
              obtain ⟨j₃, rj₃, kj₃, sj₃⟩ := pair hu₁ hd₂ Hu₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.2⟩
              obtain ⟨r₃, run₃, keep₃, sem₃⟩ := inter_eq_spec d₁ d₂ u₁ u₂ hd₁ hd₂ hu₁ hu₂
                ⟨j₁, rj₁, kj₁, sj₁⟩ ⟨j₂, rj₂, kj₂, sj₂⟩ ⟨j₃, rj₃, kj₃, sj₃⟩
              have w₁ := keep₁ _ hc₁ hc₂ hu₁ hu₂
              have w₂ := keep₂ _ hu₁ hu₂
              have w₃ := keep₃ _ hd₁ hd₂ hu₁ hu₂
              obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
              obtain ⟨r, runr, keep, sem⟩ := post_spec la r₁ r₂ r₃ h₃ w₁ w₂ w₃
              refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
              obtain ⟨x, rx, kx, sx⟩ := union_ok hc₁ hu₁
              obtain ⟨y, ry, ky, sy⟩ := union_ok hc₂ hu₂
              obtain ⟨x', rx', kx', sx'⟩ := union_ok hd₁ hu₁
              obtain ⟨y', ry', ky', sy'⟩ := union_ok hd₂ hu₂
              obtain ⟨r₁, run₁, keep₁, sem₁⟩ := pair (kx _ hc₁ hu₁) (ky _ hc₂ hu₂) (kx _ Hc₁ Hu₁) (ky _ Hc₂ Hu₂)
                fun m ha' hb' => ⟨kx _ (mA m ha').1 (mA m ha').2.1, ky _ (mB m hb').1 (mB m hb').2.1⟩
              obtain ⟨r₃, run₃, keep₃, sem₃⟩ := pair (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂) (kx' _ Hd₁ Hu₁) (ky' _ Hd₂ Hu₂)
                fun m ha' hb' => ⟨kx' _ (mA m ha').2.2 (mA m ha').2.1, ky' _ (mB m hb').2.2 (mB m hb').2.1⟩
              have w₁ := keep₁ _ (kx _ hc₁ hu₁) (ky _ hc₂ hu₂)
              have w₃ := keep₃ _ (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂)
              obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
                (Bdd.bot (ok := fun _ => True)) w₃
              obtain ⟨r, runr, keep, sem⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
              refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := ih a c₂ wa (hc.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').1⟩) ⟨HA, Hc⟩)
        obtain ⟨r₂, run₂, keep₂, sem₂⟩ := ih a u₂ wa (hu.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := ih a d₂ wa (hd.mono fun _ h => h.1)
          (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.2⟩) ⟨HA, Hd⟩)
        have w₁ := keep₁ _ (raiseA wa) hc
        have w₂ := keep₂ _ (raiseA wa) hu
        have w₃ := keep₃ _ (raiseA wa) hd
        obtain ⟨h₁, node⟩ := node_new lb r₁ r₂ r₃ (head_leaf wb hb) w₁ w₂ w₃
        obtain ⟨r, runr, keep, sem⟩ := post_spec lb r₁ r₂ r₃ h₁ w₁ w₂ w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
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

    theorem inter_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : InterOk a b :=
      belowI_all (lits a ++ lits b) _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
        (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)

    /-! Negations. -/

    def NegOk (b : Term) : Prop :=
      ∃ r, Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok r ∧ (∀ ok, Bdd ok b → Bdd ok r) ∧
        ∀ ρ, Resp ρ → eval ρ r = !eval ρ b

    theorem neg_ok {ok₀ : Term → Prop} {b : Term} (wb : Bdd ok₀ b) : NegOk b := by
      refine Bdd.induction (P := fun _ b => NegOk b) ?_ ?_ ?_ ?_ ok₀ b wb
      · intro _
        exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.bot,
          fun ρ _ => by simp⟩
      · intro _
        exact ⟨.atom "bdd_top", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.top,
          fun ρ _ => by simp⟩
      · intro ok k x y okl
        obtain ⟨h, node⟩ := node_new (.tuple #[.integer k, x, y]) (.atom "bdd_bot") (.atom "bdd_bot")
          (.atom "bdd_top") ⟨k, x, y, rfl⟩ (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
          (Bdd.top (ok := fun _ => True))
        refine ⟨.tuple #[.integer h, .tuple #[.integer k, x, y], .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"],
          by simp [Elixir.Module.Types.Descr.«bdd_negation/1», node], fun ok' w => ?_, fun ρ _ => ?_⟩
        · exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, Bdd.leaf_iff.mp w, Bdd.bot, Bdd.bot, Bdd.top⟩
        · cases ρ (.tuple #[.integer k, x, y]) <;> simp
      · intro ok h lit c u d leaf okl hc hu hd ⟨nc, runc, keepc, semc⟩ ⟨nu, runu, keepu, semu⟩
          ⟨nd, rund, keepd, semd⟩
        have wnc := keepc _ hc
        have wnd := keepd _ hd
        obtain ⟨h₁, inner⟩ := node_new lit nc (.atom "bdd_bot") nd leaf wnc (Bdd.bot (ok := fun _ => True)) wnd
        have winner : Bdd ok (.tuple #[.integer h₁, lit, nc, .atom "bdd_bot", nd]) :=
          Bdd.node_iff.mpr ⟨leaf, okl, wnc, Bdd.bot, wnd⟩
        have wnu : Bdd ok nu := (keepu _ hu).mono fun _ h => h.1
        obtain ⟨i, runi, keepi, semi⟩ := inter_ok winner wnu
        have wi := keepi _ winner wnu
        -- the result before and after the final simplification
        have final : ∃ r, (∀ ok', Bdd ok' (.tuple #[.integer h, lit, c, u, d]) → Bdd ok' r) ∧
            (∀ ρ, Resp ρ → eval ρ r = eval ρ i) ∧
            Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, lit, c, u, d]) = .ok r := by
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
          · exact ⟨_, keepI, fun _ _ => rfl, base⟩
          · exact ⟨_, keepI, fun _ _ => rfl, base⟩
          · exact ⟨_, keepI, fun _ _ => rfl, base⟩
          · by_cases e : exactCompare d' c' = .eq
            · obtain ⟨-, -, wc', wu', wd'⟩ := Bdd.node_iff.mp wi
              obtain ⟨r, runr, keepr, semr⟩ := union_ok wu' wc'
              refine ⟨r, fun ok' w => ?_, fun ρ resp => ?_, by rw [base]; simp [e, runr]⟩
              · obtain ⟨-, -, oc', ou', -⟩ := Bdd.node_iff.mp (keepI ok' w)
                exact keepr ok' (ou'.mono fun _ h => h.1) (oc'.mono fun _ h => h.1)
              · rw [semr ρ resp, eval_node, eval_congr wd' resp e]
                cases ρ li <;> cases eval ρ c' <;> simp
            · exact ⟨_, keepI, fun _ _ => rfl, by rw [base]; simp [e]⟩
        obtain ⟨r, keepr, semr, runr⟩ := final
        refine ⟨r, runr, keepr, fun ρ resp => ?_⟩
        rw [semr ρ resp, semi ρ resp, eval_node, eval_node, semc ρ resp, semd ρ resp, semu ρ resp]
        cases ρ lit <;> cases eval ρ c <;> cases eval ρ u <;> cases eval ρ d <;> simp

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

    /-- Element types of tuples: static types of bitmaps, atoms, tuples, and lists, whose BDDs
    hold anything. -/
    structure Elem (X : List (Term × Term)) : Prop where
      keys : ∀ q, (mapLookup X q).isSome →
        q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "tuple" ∨ q = .atom "list"
      bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Int, w = .integer b
      atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
      tuple : ∀ w, mapLookup X (.atom "tuple") = some w → Bdd (fun _ => True) w
      list : ∀ w, mapLookup X (.atom "list") = some w → Bdd (fun _ => True) w

    def ElemTerm (e : Term) : Prop := e = .atom "term" ∨ ∃ X, e = .map X ∧ Elem X

    theorem Elem.static {X : List (Term × Term)} (valid : Elem X) : mapLookup X (.atom "dynamic") = Option.none := by
      cases h : mapLookup X (.atom "dynamic") with
      | none => rfl
      | some w =>
        rcases valid.keys _ (by rw [h]; rfl) with bad | bad | bad | bad <;> simp only [Term.atom.injEq] at bad <;>
          exact absurd bad (by decide)

    /-- BDD fields stay BDDs through their intersections. -/
    theorem bdd_field_inter {x y : Term} (wx : Bdd (fun _ => True) x) (wy : Bdd (fun _ => True) y)
        (f : Except Exception Term) (cases : f = .ok y ∨ f = .ok x ∨ f = Elixir.Module.Types.Descr.«bdd_intersection/2» x y) :
        ∃ r, f = .ok r ∧ Bdd (fun _ => True) r := by
      rcases cases with rfl | rfl | rfl
      · exact ⟨y, rfl, wy⟩
      · exact ⟨x, rfl, wx⟩
      · obtain ⟨r, run, keep, -⟩ := inter_ok wx wy
        exact ⟨r, run, keep _ wx wy⟩

    theorem tuple_inter_cases (x y : Term) :
        Elixir.Module.Types.Descr.«tuple_intersection/2» x y = .ok y ∨
          Elixir.Module.Types.Descr.«tuple_intersection/2» x y = .ok x ∨
          Elixir.Module.Types.Descr.«tuple_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
      split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

    theorem list_inter_cases (x y : Term) :
        Elixir.Module.Types.Descr.«list_intersection/2» x y = .ok y ∨
          Elixir.Module.Types.Descr.«list_intersection/2» x y = .ok x ∨
          Elixir.Module.Types.Descr.«list_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
      unfold Elixir.Module.Types.Descr.«list_intersection/2»
      split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

    /-- The shape of a field of an element type. -/
    def ElemField (q w : Term) : Prop :=
      (q = .atom "bitmap" ∧ ∃ b : Int, w = .integer b) ∨ (q = .atom "atom" ∧ AtomField w) ∨
        (q = .atom "tuple" ∧ Bdd (fun _ => True) w) ∨ (q = .atom "list" ∧ Bdd (fun _ => True) w)

    theorem Elem.field {X : List (Term × Term)} (valid : Elem X) {q w : Term} (h : mapLookup X q = some w) :
        ElemField q w := by
      rcases valid.keys q (by simp [h]) with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, valid.bitmap w h⟩
      · exact Or.inr (Or.inl ⟨rfl, valid.atom w h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, valid.tuple w h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, valid.list w h⟩))

    /-- Element types intersect into element types. -/
    theorem elem_inter_map (depth : Nat) (L R : List (Term × Term)) (vL : Elem L) (vR : Elem R) :
        ∃ out, Elixir.Module.Types.Descr.«bare_intersection/2»
            (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map out) ∧
          Elem out := by
      let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
        match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
          k₀ v₁ v₂ with
        | .ok w => w
        | .error _ => .nil
      have common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
          Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            q x y = .ok (g q x y) ∧ (kept (q, g q x y) = Bool.true → ElemField q (g q x y)) := by
        intro q x y hx hy
        rcases vL.field hx with ⟨rfl, b₁, rfl⟩ | ⟨rfl, ax⟩ | ⟨rfl, wx⟩ | ⟨rfl, wx⟩
        · obtain ⟨b₂, rfl⟩ := vR.bitmap y hy
          have run : Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
              (.atom "bitmap") (.integer b₁) (.integer b₂) = .ok (.integer (bandI b₁ b₂)) := by
            simp [Elixir.Module.Types.Descr.«bare_intersection/3»]
          exact ⟨by simp only [g, run], fun _ => by simp only [g, run]; exact Or.inl ⟨rfl, _, rfl⟩⟩
        · obtain ⟨p₁, S₁, rfl, set₁⟩ := ax
          obtain ⟨p₂, S₂, rfl, set₂⟩ := vR.atom y hy
          rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -⟩ | ⟨hE, -⟩
          · exact ⟨by simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE], fun _ => by
              simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE]
              exact Or.inr (Or.inl ⟨rfl, p, E, rfl, setE⟩)⟩
          · exact ⟨by simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE], fun k => by
              simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE, kept] at k⟩
        · obtain ⟨r, run, wr⟩ := bdd_field_inter wx (vR.tuple y hy) _ (tuple_inter_cases x y)
          have run' : Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
              (.atom "tuple") x y = .ok r := by simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]; exact run
          exact ⟨by simp only [g, run'], fun _ => by simp only [g, run']; exact Or.inr (Or.inr (Or.inl ⟨rfl, wr⟩))⟩
        · obtain ⟨r, run, wr⟩ := bdd_field_inter wx (vR.list y hy) _ (list_inter_cases x y)
          have run' : Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
              (.atom "list") x y = .ok r := by simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]; exact run
          exact ⟨by simp only [g, run'], fun _ => by simp only [g, run']; exact Or.inr (Or.inr (Or.inr ⟨rfl, wr⟩))⟩
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
      have field : ∀ q w, mapLookup out q = some w → ElemField q w := by
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
              rw [value] at shape
              rcases shape with ⟨key, s⟩ | ⟨key, s⟩ | ⟨key, s⟩ | ⟨key, s⟩ <;> rw [key] at qf <;>
                simp only [exactCompare_eq_atom] at qf <;> subst qf
              · exact Or.inl ⟨rfl, s⟩
              · exact Or.inr (Or.inl ⟨rfl, s⟩)
              · exact Or.inr (Or.inr (Or.inl ⟨rfl, s⟩))
              · exact Or.inr (Or.inr (Or.inr ⟨rfl, s⟩))
            · simp [k] at hw
      refine ⟨out, ?_, ⟨fun q some => ?_, fun w h => ?_, fun w h => ?_, fun w h => ?_, fun w h => ?_⟩⟩
      · have absent : mapLookup R (.atom "dynamic") = Option.none := vR.static
        unfold Elixir.Module.Types.Descr.«bare_intersection/2»
        simp [getMapKeys_single, vL.static, absent]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runO]
      · obtain ⟨w, h⟩ := Option.isSome_iff_exists.mp some
        rcases field q w h with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> simp [k]
      all_goals
        rcases field _ w h with ⟨k, s⟩ | ⟨k, s⟩ | ⟨k, s⟩ | ⟨k, s⟩ <;> simp at k <;> exact s

    theorem elem_inter (depth : Nat) {a b : Term} (ha : ElemTerm a) (hb : ElemTerm b) :
        ∃ e, Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) a b = .ok e ∧ ElemTerm e := by
      rcases ha with rfl | ⟨L, rfl, vL⟩
      · exact ⟨b, by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl, hb⟩
      rcases hb with rfl | ⟨R, rfl, vR⟩
      · exact ⟨.map L, by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl, Or.inr ⟨L, rfl, vL⟩⟩
      obtain ⟨out, run, vo⟩ := elem_inter_map depth L R vL vR
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

    theorem element_fields_spec (es : List (Term × Term))
        (valid : «element_fields?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
        ∀ p ∈ es, ElemField p.1 p.2 := by
      induction es with
      | nil => simp
      | cons e rest ih =>
        obtain ⟨k, w⟩ := e
        have both : ElemField k w ∧
            «element_fields?/1» (Term.list (rest.map fun e => .tuple #[e.1, e.2])) = .ok Term.true := by
          simp only [List.map_cons, Term.list] at valid
          unfold «element_fields?/1» at valid
          split at valid
          · rename_i bits fields heq
            simp at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            simp only [Term.true, Lynx.Except.andAlso_eq_true] at valid
            cases w <;> simp [Erlang.erlang.«is_integer/1»] at valid
            exact ⟨Or.inl ⟨rfl, _, rfl⟩, valid⟩
          · rename_i atoms fields heq
            simp at heq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
            simp only [Term.true, Lynx.Except.andAlso_eq_true] at valid
            rcases valid_fields [(.atom "atom", w)] (by simpa [Term.list] using valid.1) (.atom "atom", w)
              (by simp) with ⟨k, -⟩ | ⟨-, f⟩
            · simp at k
            · exact ⟨Or.inr (Or.inl ⟨rfl, f⟩), valid.2⟩
          · simp only [Lynx.Except.guard, Lynx.Except.tryWith] at valid
            split at valid
            · next member =>
              simp only [Term.true, Lynx.Except.andAlso_eq_true] at valid
              have w' := (any_bdd_spec _ w _ (Nat.le_refl _) valid.1).mono fun _ _ => trivial
              by_cases t : k = .atom "tuple"
              · exact ⟨Or.inr (Or.inr (Or.inl ⟨t, w'⟩)), valid.2⟩
              · by_cases l : k = .atom "list"
                · exact ⟨Or.inr (Or.inr (Or.inr ⟨l, w'⟩)), valid.2⟩
                · simp [isMember, t, l] at member
            · simp [Term.true] at valid
        intro p member
        rcases List.mem_cons.mp member with rfl | member
        · exact both.1
        · exact ih both.2 p member

    theorem element_spec {e : Term} (h : «element?/1» e = .ok Term.true) : ElemTerm e := by
      unfold «element?/1» at h
      split at h
      · exact Or.inl rfl
      · rename_i X
        simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at h
        have each := element_fields_spec (mapEntries X) h
        have entry (q w : Term) (lookup : mapLookup X q = some w) :
            ∃ p ∈ mapEntries X, exactCompare q p.1 = .eq ∧ p.2 = w :=
          lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
        have field : ∀ q w, mapLookup X q = some w → ElemField q w := by
          intro q w lookup
          obtain ⟨p, mp, qp, rfl⟩ := entry q w lookup
          rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
            simp only [exactCompare_eq_atom] at qp <;> subst qp
          · exact Or.inl ⟨rfl, f⟩
          · exact Or.inr (Or.inl ⟨rfl, f⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, f⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, f⟩))
        refine Or.inr ⟨X, rfl, ⟨fun q some => ?_, fun w h => ?_, fun w h => ?_, fun w h => ?_, fun w h => ?_⟩⟩
        · obtain ⟨w, h⟩ := Option.isSome_iff_exists.mp some
          rcases field q w h with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> simp [k]
        all_goals
          rcases field _ w h with ⟨k, s⟩ | ⟨k, s⟩ | ⟨k, s⟩ | ⟨k, s⟩ <;> simp at k <;> exact s
      · simp [Term.true] at h

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
          obtain ⟨nb, run, wnb, sem, leafless⟩ := leaf_difference (ok := TupleLit) ⟨61102469, _, _, rfl⟩
            ⟨k, _, _, rfl⟩ tuple_top_lit ⟨k, tag, ls, rfl, tags, elems⟩
          refine ⟨nb, ?_, fun _ => ?_⟩
          · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
            split
            · next _ _ e =>
              exfalso
              simp at e
              obtain ⟨-, rfl, hl⟩ := e
              exact notTopX ⟨_, by rw [hl]⟩
            · next _ _ e => exact (notSpecial _ e).elim
            · next _ _ e => simp at e
            · exact run
          · have wx' : Bdd TupleLit (.tuple #[.integer k, .atom tag, Term.list ls]) :=
              Bdd.leaf_iff.mpr ⟨k, tag, ls, rfl, tags, elems⟩
            obtain ⟨r, rr, kr, sr⟩ := inter_ok wx' wnb
            refine ⟨r, ?_, fun _ => tuple_empty_unsat (kr _ wx' wnb) (fun _ h => h) fun ρ resp => ?_⟩
            · rw [tuple_intersection_bdd notTop (fun k e => leafless _ _ _ e)]
              exact rr
            · rw [sr ρ resp, sem ρ resp]
              simp only [eval_leaf]
              cases ρ (.tuple #[.integer k, .atom tag, Term.list ls]) <;> simp
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

    /-- Flat types intersect into flat types. -/
    theorem flat_inter_map (depth : Nat) (L R : List (Term × Term)) (vL : Elem L) (vR : Elem R) :
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
        rcases vL.field hx with ⟨rfl, b₁, rfl⟩ | ⟨rfl, ax⟩ | ⟨rfl, wx⟩ | ⟨rfl, wx⟩
        · obtain ⟨b₂, rfl⟩ := vR.bitmap y hy
          have run : Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
              (.atom "bitmap") (.integer b₁) (.integer b₂) = .ok (.integer (bandI b₁ b₂)) := by
            simp [Elixir.Module.Types.Descr.«bare_intersection/3»]
          exact ⟨by simp only [g, run], fun _ => by simp only [g, run]; exact Or.inl ⟨rfl, _, rfl⟩⟩
        · obtain ⟨p₁, S₁, rfl, set₁⟩ := ax
          obtain ⟨p₂, S₂, rfl, set₂⟩ := vR.atom y hy
          rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -⟩ | ⟨hE, -⟩
          · exact ⟨by simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE], fun _ => by
              simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE]
              exact Or.inr (Or.inl ⟨rfl, p, E, rfl, setE⟩)⟩
          · exact ⟨by simp only [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE], fun k => by
              simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE, kept] at k⟩
        · obtain ⟨r, run, wr⟩ := bdd_field_inter wx (vR.tuple y hy) _ (tuple_inter_cases x y)
          have run' : Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
              (.atom "tuple") x y = .ok r := by simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]; exact run
          exact ⟨by simp only [g, run'], fun _ => by simp only [g, run']; exact Or.inr (Or.inr (Or.inl ⟨rfl, wr⟩))⟩
        · obtain ⟨r, run, wr⟩ := bdd_field_inter wx (vR.list y hy) _ (list_inter_cases x y)
          have run' : Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
              (.atom "list") x y = .ok r := by simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]; exact run
          exact ⟨by simp only [g, run'], fun _ => by simp only [g, run']; exact Or.inr (Or.inr (Or.inr ⟨rfl, wr⟩))⟩
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
              rcases shape with ⟨key, s⟩ | ⟨key, s⟩ | ⟨key, s⟩ | ⟨key, s⟩ <;> rw [key] at qf <;>
                simp only [exactCompare_eq_atom] at qf <;> subst qf
              · exact Or.inl ⟨rfl, s⟩
              · exact Or.inr (Or.inl ⟨rfl, s⟩)
              · exact Or.inr (Or.inr (Or.inl ⟨rfl, s⟩))
              · exact Or.inr (Or.inr (Or.inr ⟨rfl, s⟩))
            · simp [k] at hw
      refine ⟨out, ?_, ⟨fun q some => ?_, fun w h => ?_, fun w h => ?_, fun w h => ?_, fun w h => ?_⟩,
        fun q w h => (field q w h).2⟩
      · have absent : mapLookup R (.atom "dynamic") = Option.none := vR.static
        unfold Elixir.Module.Types.Descr.«bare_intersection/2»
        simp [getMapKeys_single, vL.static, absent]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
        simp [runI, runO]
      · obtain ⟨w, h⟩ := Option.isSome_iff_exists.mp some
        rcases (field q w h).1 with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> simp [k]
      all_goals
        rcases (field _ w h).1 with ⟨k, s⟩ | ⟨k, s⟩ | ⟨k, s⟩ | ⟨k, s⟩ <;> simp at k <;> exact s


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
      obtain ⟨out, run, vo, fromL⟩ := flat_inter_map depth L R vL.1 vR.1
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

    /-- Unsatisfiable map BDDs have no line, whatever the fields of their literals. -/
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

    def MapOk (t : Term) : Prop := MapLit t ∧ ¬IsTop t

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
      · have okx := Bdd.leaf_iff.mp wx
        obtain ⟨nb, run, wnb, sem, leafless⟩ := leaf_difference (ok := MapLit) ⟨61102469, _, _, rfl⟩
          ⟨k, _, _, rfl⟩ map_top_lit okx.1
        refine ⟨nb, ?_, fun _ => ?_⟩
        · unfold Elixir.Module.Types.Descr.«map_difference/2»
          split
          · next _ _ e => exact (notTop _ e).elim
          · next _ _ _ e => simp at e
          · exact run
        · have wx' : Bdd MapLit (.tuple #[.integer k, tg, l]) := Bdd.leaf_iff.mpr okx.1
          obtain ⟨r, rr, kr, sr⟩ := inter_ok wx' wnb
          refine ⟨r, ?_, fun _ => map_empty_unsat (kr _ wx' wnb) (fun _ h => h) fun ρ resp => ?_⟩
          · rw [map_intersection_bdd notTop (fun k e => leafless _ _ _ e)]
            exact rr
          · rw [sr ρ resp, sem ρ resp]
            simp only [eval_leaf]
            cases ρ (.tuple #[.integer k, tg, l]) <;> simp
      · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
        have wnb := keep _ wx
        refine ⟨nb, ?_, fun _ => ?_⟩
        · unfold Elixir.Module.Types.Descr.«map_difference/2»
          simp [run]
        · have wl : Bdd MapLit (.tuple #[.integer h, lit, c, u, d]) := wx.mono fun _ h => h.1
          obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
          refine ⟨r, ?_, fun _ => map_empty_unsat (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h) fun ρ resp => ?_⟩
          · rw [map_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
            exact rr
          · rw [sr ρ resp, sem ρ resp]
            cases eval ρ (.tuple #[.integer h, lit, c, u, d]) <;> rfl

    /-! Reading the map specification. -/

    theorem Valid.flat {X : List (Term × Term)} (valid : Valid X) : Flat X := by
      refine ⟨⟨fun q h => ?_, fun w h => ?_, valid.atom, fun w h => ?_, fun w h => ?_⟩, valid.keys⟩
      · rcases valid.keys q h with rfl | rfl <;> simp
      · obtain ⟨b, rfl, -⟩ := valid.bitmap w h; exact ⟨_, rfl⟩
      · rcases valid.keys _ (by rw [h]; rfl) with e | e <;> simp at e
      · rcases valid.keys _ (by rw [h]; rfl) with e | e <;> simp at e

    theorem field_type_spec {t : Term} (h : «field_type?/1» t = .ok Term.true) : FlatTerm t := by
      unfold «field_type?/1» at h
      split at h
      · exact Or.inl rfl
      · obtain ⟨X, rfl, valid⟩ := valid_map _ h
        exact Or.inr ⟨X, rfl, valid.flat⟩

    theorem map_fields_spec (fs : Term) (h : «map_fields?/1» fs = .ok Term.true) : Fields fs := by
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

    /-- What `negatable?/1` checks of a type. -/
    structure Negatable (X : List (Term × Term)) : Prop where
      keys : ∀ q, (mapLookup X q).isSome →
        q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨ q = .atom "list" ∨ q = .atom "tuple" ∨
          q = .atom "map"
      bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
      atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
      funs : ∀ w, mapLookup X (.atom "fun") = some w → FunField w
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
          (p.1 = .atom "atom" ∧ AtomField p.2) ∨ (p.1 = .atom "fun" ∧ FunField p.2) ∨
          (p.1 = .atom "list" ∧ ListField p.2) ∨ (p.1 = .atom "tuple" ∧ TupleField p.2) ∨
          (p.1 = .atom "map" ∧ MapField p.2) := by
      induction es with
      | nil => simp
      | cons e rest ih =>
        obtain ⟨k, w⟩ := e
        simp only [List.map_cons, Term.list, «negatable_fields?/1», Term.true, Lynx.Except.andAlso_eq_true] at valid
        have head : (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
            (k = .atom "atom" ∧ AtomField w) ∨ (k = .atom "fun" ∧ FunField w) ∨ (k = .atom "list" ∧ ListField w) ∨
            (k = .atom "tuple" ∧ TupleField w) ∨ (k = .atom "map" ∧ MapField w) := by
          have field := valid.1
          have fallback : «valid_fields?/1» (Term.list [.tuple #[k, w]]) = .ok Term.true →
              (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨ (k = .atom "atom" ∧ AtomField w) ∨
                (k = .atom "fun" ∧ FunField w) ∨ (k = .atom "list" ∧ ListField w) ∨
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
              cases arities <;> simp [Erlang.erlang.«is_map/1»] at field
              rename_i R
              by_cases u : tag = .atom "union"
              · exact ⟨Bool.true, R, by simp [u]⟩
              · by_cases n : tag = .atom "negation"
                · exact ⟨Bool.false, R, by simp [n]⟩
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
      refine ⟨X, rfl, ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_,
        fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_⟩⟩
      · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
        obtain ⟨p, mp, qp, -⟩ := entry q w lookup
        rcases each p mp with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> rw [k] at qp <;> simp [key qp]
      all_goals
        obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
        rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
          first | exact f | (simp at qp)

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
          rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure,
            keep_field])
      refine ⟨out, ?_, fun q w hw => ?_⟩
      · have absent : mapLookup R (.atom "dynamic") = Option.none := staticR
        unfold Elixir.Module.Types.Descr.«bare_intersection/2»
        simp [getMapKeys_single, validL.static, absent]
        unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
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
            MapCancel x y) := by
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
      obtain ⟨N, fold, lookN⟩ := difference_fold depth g (mapEntries X) T (mapEntries_distinct X) (by
        intro e member v₁ found
        have hy := mapLookup_of_mem_mapEntries member
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
        fun x y hX hN => ?_, fun x y hX hN => ?_⟩
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
        rcases atom_difference false [] pR SR noAtoms setR with ⟨p, E, hE, setE, tag, mE⟩ | ⟨hE, -⟩ <;>
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

    end Elixir.STTDescrProofsTest
    """

    law union_member(value, left, right),
      requires: valid?(left) and valid?(right),
      expects:
        member?(value, Descr.bare_union(left, right)) ==
          (member?(value, left) or member?(value, right)),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«union_member:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨L, rfl, validL⟩ := valid_map left requires.1
      obtain ⟨R, rfl, validR⟩ := valid_map right requires.2
      obtain ⟨k, -, member⟩ := member_eq value
      obtain ⟨out, run, shaped, bitsOut, atomsOut⟩ := union_fields 99 L R validL validR
      simp only [Lynx.apply_eq, «union_member:ensures/3», run, Lynx.Except.ok_bind,
        member _ validL.shaped, member _ validR.shaped, member _ shaped, or_else_bool, eq_bool,
        holds_union k _ out L R bitsOut atomsOut, BEq.rfl]
      rfl
      """

    law intersection_member(value, left, right),
      requires: valid?(left) and valid?(right),
      expects:
        member?(value, Descr.bare_intersection(left, right)) ==
          (member?(value, left) and member?(value, right)),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«intersection_member:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨L, rfl, validL⟩ := valid_map left requires.1
      obtain ⟨R, rfl, validR⟩ := valid_map right requires.2
      obtain ⟨k, single, member⟩ := member_eq value
      obtain ⟨out, run, shaped, bitsOut, atomsOut⟩ := intersection_fields 99 L R validL validR
      simp only [Lynx.apply_eq, «intersection_member:ensures/3», run, Lynx.Except.ok_bind,
        member _ validL.shaped, member _ validR.shaped, member _ shaped, and_also_bool, eq_bool,
        holds_intersection k _ single out L R bitsOut atomsOut, BEq.rfl]
      rfl
      """

    law difference_member(value, left, right),
      requires: valid?(left) and valid?(right),
      expects:
        member?(value, Descr.bare_difference(left, right)) ==
          (member?(value, left) and not member?(value, right)),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«difference_member:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨L, rfl, validL⟩ := valid_map left requires.1
      obtain ⟨R, rfl, validR⟩ := valid_map right requires.2
      obtain ⟨k, single, member⟩ := member_eq value
      obtain ⟨out, run, shaped, bitsOut, atomsOut⟩ := difference_fields 98 L R validL validR
      simp only [Lynx.apply_eq, «difference_member:ensures/3», run, Lynx.Except.ok_bind,
        member _ validL.shaped, member _ validR.shaped, member _ shaped, not_bool, and_also_bool, eq_bool,
        holds_difference k _ single out L R bitsOut atomsOut, BEq.rfl]
      rfl
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
      · obtain ⟨N, negation, static, bitmaps, atoms, funs, lists, tuples, maps⟩ := negation_fields 98 X valid empty
        obtain ⟨I, run, only⟩ := intersection_disjoint 99 X N valid static bitmaps atoms
          (fun x y hx hy => funs x y hx hy 99) lists tuples maps
        simp [negation, run, empty_gone 97 I only]
      """
  end
end
