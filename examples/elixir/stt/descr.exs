# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/stt/descr.exs
# Prove the set operations of Elixir's type system on static types of bitmaps and atoms.
# Checked against Elixir 1.21.0-dev (d17b3abe7), Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/module/types/descr.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
ExUnit.start()

defmodule STTDescrProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case
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

  laws "static" do
    # Elixir's default map field access falls back to a remote call on non-maps.
    cutoff &:elixir_erl_pass.no_parens_remote/2

    # Only bitmaps and atoms are modeled so far, so emptiness of the other
    # fields is cut off.
    cutoff &Descr.tuple_empty?/2
    cutoff &Descr.map_empty?/2
    cutoff &Descr.list_empty?/2
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
          ∀ q, (p == (mapLookup E q).isSome) =
            ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome))) ∨
        (Elixir.Module.Types.Descr.«atom_intersection/2»
              (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
              (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .ok (.integer 0) ∧
          ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) := by
      cases p₁ <;> cases p₂
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
        refine Or.inl ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE,
          Erlang.erlang.«==/2»], setE, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, fun q => ?_⟩
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
            Erlang.erlang.«==/2», nonzero], setE, fun q => ?_⟩
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
            Erlang.erlang.«==/2», nonzero], setE, fun q => ?_⟩
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
            rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, mE⟩ | ⟨hE, mE⟩
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
            Erlang.erlang.«==/2», nonzero], setE, fun q => ?_⟩
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
          Erlang.erlang.«==/2»], setE, fun q => ?_⟩
        rw [m]
        cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
      · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
        rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
        · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
            Erlang.erlang.«==/2», nonzero], setE, fun q => ?_⟩
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
            Erlang.erlang.«==/2», nonzero], setE, fun q => ?_⟩
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

    theorem static_map {X : List (Term × Term)} (valid : Valid X) :
        Erlang.erlang.«is_map_key/2» (.atom "dynamic") (.map X) = .ok (.atom "false") := by
      have absent : X.any (fun entry => exactCompare (.atom "dynamic") entry.1 == .eq) = Bool.false := by
        rw [Bool.eq_false_iff]
        intro present
        obtain ⟨entry, member, same⟩ := List.any_eq_true.mp present
        have := (mapLookup_isSome X (.atom "dynamic")).mpr ⟨entry, member, by simpa using same⟩
        rw [no_dynamic valid] at this
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
        · simp only [emptyR, ite_false, unfold_map, static_map validL, static_map validR, Lynx.Except.ok_bind]
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
            rcases atom_difference p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, mE⟩ | ⟨hE, mE⟩
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

    /-- The intersection with the empty type is empty. -/
    theorem intersection_none (depth : Nat) (X : List (Term × Term)) (valid : Valid X) :
        Elixir.Module.Types.Descr.«bare_intersection/2»
          (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map X) (.map []) = .ok (.map []) := by
      obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "bare_intersection" #[] X [] (fun _ _ _ => .nil) (by intro e _ y hy; simp [mapLookup] at hy)
      obtain rfl : I = [] := nil_of_lookup_none I fun q => by
        rw [lookI]
        cases (mapEntries X).find? (fun e => decide (exactCompare q e.1 = .eq)) <;> simp [mapLookup]
      obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
        "-symmetrical_intersection/3-fun-0-" #[] [] kept (by intro e member; simp at member)
      obtain rfl : out = [] := nil_of_lookup_none out fun q => by rw [lookO]; simp
      have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»
      simp [getMapKeys_single, no_dynamic valid, absent]
      unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
      simp [runI, runO]

    /-- The empty type is empty. -/
    theorem empty_none (d : Dispatcher) :
        Elixir.Module.Types.Descr.«empty?/1» d (.map []) = .ok Term.true := by
      simp only [Elixir.Module.Types.Descr.«empty?/1»]
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
      simp [getMapKeys_single, mapLookup, Erlang.erlang.«==/2», Term.true]

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
      requires: valid?(descr),
      expects: Descr.empty?(Descr.bare_intersection(descr, Descr.none())),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      simp only [«intersection_none_empty:requires/1»] at requires
      obtain ⟨X, rfl, valid⟩ := valid_map descr requires
      simp [Lynx.apply_eq, «intersection_none_empty:ensures/1», Elixir.Module.Types.Descr.«none/0»,
        intersection_none 99 X valid, empty_none]
      """
  end
end
