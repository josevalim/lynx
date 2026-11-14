# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/stt/descr.exs
# Prove the set operations of Elixir's type system, Module.Types.Descr.
#
# Laws:
#
#   * Empty type: a type meets none() in the empty type.
#   * Negation: a type does not meet its negation, and a type united with its negation
#     is the top type. A gradual type meets its negation in its dynamic part, so the
#     intersection is checked on its lower bound and the union on its upper bound.
#   * De Morgan: the negation of a union is the intersection of the negations. For the
#     optimized operations, so is the dual: the negation of an intersection is the
#     union of the negations.
#   * Bounds: intersections are included in their arguments, and unions include them.
#   * Agreement: the plain and optimized unions, intersections, differences, and
#     negations are equal.
#   * Distributivity: plain intersections distribute over plain unions.
#   * Function arity: the top function type of each arity is the arrow from that many
#     arguments of none() to term().
#   * Compatibility: a type is compatible with another when its static part is included
#     in the dynamic part of the other and the two meet.
#   * Order: subtyping is reflexive and transitive, two types are equal when each is a
#     subtype of the other, and two types are disjoint when their intersection is empty.
#   * Lattice: unions and intersections are commutative, associative, and idempotent,
#     absorb each other, and unions distribute over intersections. A type is a subtype
#     of another when their union is the other, and when their intersection is the first.
#   * Difference: for static types, a type is a subtype of another when their difference is
#     empty, a type is the union of its difference with another type and its intersection
#     with it, a difference is disjoint from the type it removes, and negating a type twice
#     gives it back.
#   * Tuples: fetching an index of a static type of tuples gives the least type including
#     the values of its tuples there, and :badindex exactly when one of them is too short.
#     Inserting a non-empty type at an index and fetching that index gives the type back,
#     and deleting that index gives the tuples back.
#   * Maps: fetching a key of a static type of maps gives the least type including the
#     values of its maps there, and :badkey exactly when one of them lacks the key.
#     Getting the keys of given atoms and kinds of keys gives the least type including
#     the values of its maps at those keys, :error exactly when none of them holds such
#     a key, and :badmap exactly for types other than non-empty types of maps. Getting
#     a single atom key agrees with fetching it. Converting a static type of maps to lists
#     lists every key and value of its maps, for atom keys and keys of each kind, with
#     values only from its maps; its lists hold the empty list exactly when the type holds
#     the empty map, and are only the empty list exactly when all its maps are empty.
#     Constructing maps from pairs of static types holds, at each atom key, the type and
#     optional flag of the last pair of the key, or else the optional values of the atom
#     domain, and at the keys of each kind the union of the domain pairs naming it, or
#     else any value for open maps and none for closed ones, all of them least. Closed
#     maps are open maps, and the empty map is the closed map of no pairs.
#
# The negation, De Morgan, and bounds laws hold for both the plain operations and the
# optimized ones the type checker uses.
#
# Types:
#
#   * The empty type law holds for any map, valid type or not.
#   * The other laws need the invariants Descr maintains, and cover the top type and the
#     types of bitmaps, atoms, functions, lists, tuples, and maps. Lists, tuples, maps,
#     maps with domains, and functions nest types at any depth: each law takes the
#     depth as an input.
#   * Gradual types, whose dynamic part includes their static part, for both parts.
#   * The recursive type t = nil or {term(), t}, as a Descr node wherever types nest.
#
# Function types are modeled as sets of functions, whose arguments and returns are nested
# types. The plain negation and De Morgan laws also hold for static types whose function
# types hold any literals, modeled as Boolean combinations of arrows.
#
# Checked against Elixir 1.21.0-dev (9636feee7), Erlang/OTP 29.1.2.
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

  # The top type and types of bitmaps, atoms, functions, lists, tuples, and maps. Function
  # types are unions or negations of maps from arities to BDDs, whose literals are not
  # inspected. List elements and tails, tuple elements, map fields, and the arguments and
  # returns of nested functions nest types of bitmaps, atoms, functions, lists, tuples, and
  # maps, at most `depth` levels deep, and the recursive node `node` below, given as
  # `{depth, node}`. The laws take any depth as an input, so they hold for types of every depth.
  def depth?(depth), do: is_integer(depth) and depth >= 0

  # The recursive node of the laws: a recursive tuple, t = nil or {term(), t}, as
  # Descr.recursive/1 builds it from the generator below.
  def tuple_list(recur),
    do: Descr.bare_union(Descr.atom([nil]), Descr.tuple([Descr.term(), recur.(:t)]))

  def recursive_node?({id, %{t: {id, generator}}, generator}) when is_reference(id),
    do: generator === &__MODULE__.tuple_list/1

  def recursive_node?(_node), do: false

  def negatable?(:term, _depth), do: true
  def negatable?(descr, depth) when is_map(descr), do: negatable_fields?(:maps.to_list(descr), depth)
  def negatable?(_descr, _depth), do: false

  defp negatable_fields?([field | fields], depth),
    do: negatable_field?(field, depth) and negatable_fields?(fields, depth)

  defp negatable_fields?([], _depth), do: true

  defp negatable_field?({:fun, {tag, arities}}, _depth) when tag in [:union, :negation],
    do: is_map(arities) and arity_bdds?(:maps.to_list(arities))

  defp negatable_field?(field, depth), do: nested_field?(field, depth)

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

  # Nested types: the top type, the recursive node, valid types, or types of bitmaps, atoms,
  # functions, lists, tuples, and maps whose contents nest at most `depth - 1` levels. The
  # depth comes with the recursive node the types may hold, as `{depth, node}`.
  defp nested?(:term, _depth), do: true

  defp nested?({_, _, _} = other, {_depth, node}) when other === node,
    do: recursive_node?(other)

  defp nested?(type, {0, _node}), do: valid?(type)

  defp nested?(type, {depth, node}) when is_map(type),
    do: nested_fields?(:maps.to_list(type), {depth - 1, node})

  defp nested?(_type, _depth), do: false

  defp nested_fields?([field | fields], depth),
    do: nested_field?(field, depth) and nested_fields?(fields, depth)

  defp nested_fields?([], _depth), do: true

  defp nested_field?({:fun, {tag, arities}}, depth) when tag in [:union, :negation],
    do: is_map(arities) and fun_arities?(:maps.to_list(arities), depth)

  defp nested_field?({:list, bdd}, depth), do: list_bdd?(bdd, depth)
  defp nested_field?({:tuple, bdd}, depth), do: tuple_bdd?(bdd, depth)
  defp nested_field?({:map, bdd}, depth), do: map_bdd?(bdd, depth)
  defp nested_field?(field, _depth), do: valid_fields?([field])

  # Function types map arities to BDDs of function literals ordered by Erlang's
  # term order, whose arguments, as many as their arity, and return types are
  # nested types.
  defp fun_arities?([{arity, bdd} | arities], depth),
    do: is_integer(arity) and fun_bdd?(bdd, arity, :bottom, depth) and fun_arities?(arities, depth)

  defp fun_arities?([], _depth), do: true

  defp fun_bdd?(:bdd_top, _arity, _lower, _depth), do: true
  defp fun_bdd?(:bdd_bot, _arity, _lower, _depth), do: true
  defp fun_bdd?({_, _, _} = leaf, arity, lower, depth), do: fun_literal?(leaf, arity, lower, depth)

  defp fun_bdd?({hash, lit, c, u, d}, arity, lower, depth),
    do:
      is_integer(hash) and fun_literal?(lit, arity, lower, depth) and fun_bdd?(c, arity, lit, depth) and
        fun_bdd?(u, arity, lit, depth) and fun_bdd?(d, arity, lit, depth)

  defp fun_bdd?(_bdd, _arity, _lower, _depth), do: false

  defp fun_literal?({key, args, return} = lit, arity, lower, depth),
    do:
      is_integer(key) and lit > lower and elements?(args, depth) and length(args) == arity and
        nested?(return, depth)

  defp fun_literal?(_lit, _arity, _lower, _depth), do: false

  # List types are all non-empty lists, or BDDs of other list literals ordered
  # by Erlang's term order, whose element and tail types are nested types. Atoms
  # precede the tuples of literals.
  defp list_bdd?({key, :term, :term}, _depth), do: is_integer(key)
  defp list_bdd?(bdd, depth), do: ordered_bdd?(bdd, :bottom, depth)

  defp ordered_bdd?(:bdd_top, _lower, _depth), do: true
  defp ordered_bdd?(:bdd_bot, _lower, _depth), do: true
  defp ordered_bdd?({_, _, _} = leaf, lower, depth), do: list_literal?(leaf, lower, depth)

  defp ordered_bdd?({hash, lit, c, u, d}, lower, depth),
    do:
      is_integer(hash) and list_literal?(lit, lower, depth) and ordered_bdd?(c, lit, depth) and
        ordered_bdd?(u, lit, depth) and ordered_bdd?(d, lit, depth)

  defp ordered_bdd?(_bdd, _lower, _depth), do: false

  defp list_literal?({key, list, last} = lit, lower, depth),
    do:
      is_integer(key) and lit > lower and not (list == :term and last == :term) and
        nested?(list, depth) and nested?(last, depth)

  defp list_literal?(_lit, _lower, _depth), do: false

  # Tuple types are all tuples, or BDDs of other tuple literals ordered by
  # Erlang's term order, whose elements are nested types.
  defp tuple_bdd?({key, :open, []}, _depth), do: is_integer(key)
  defp tuple_bdd?(bdd, depth), do: ordered_tuple_bdd?(bdd, :bottom, depth)

  defp ordered_tuple_bdd?(:bdd_top, _lower, _depth), do: true
  defp ordered_tuple_bdd?(:bdd_bot, _lower, _depth), do: true
  defp ordered_tuple_bdd?({_, _, _} = leaf, lower, depth), do: tuple_literal?(leaf, lower, depth)

  defp ordered_tuple_bdd?({hash, lit, c, u, d}, lower, depth),
    do:
      is_integer(hash) and tuple_literal?(lit, lower, depth) and ordered_tuple_bdd?(c, lit, depth) and
        ordered_tuple_bdd?(u, lit, depth) and ordered_tuple_bdd?(d, lit, depth)

  defp ordered_tuple_bdd?(_bdd, _lower, _depth), do: false

  defp tuple_literal?({key, tag, elements} = lit, lower, depth) when tag in [:open, :closed],
    do:
      is_integer(key) and lit > lower and not (tag == :open and elements == []) and
        elements?(elements, depth)

  defp tuple_literal?(_lit, _lower, _depth), do: false

  defp elements?([element | elements], depth), do: nested?(element, depth) and elements?(elements, depth)
  defp elements?([], _depth), do: true
  defp elements?(_elements, _depth), do: false

  # Map types are all maps, or BDDs of other map literals ordered by Erlang's term order.
  # Their literals are open maps, closed maps, or maps with domains, the types of the values
  # of each kind of keys, and their fields and domains hold nested types.
  defp map_bdd?({key, :open, []}, _depth), do: is_integer(key)
  defp map_bdd?(bdd, depth), do: ordered_map_bdd?(bdd, :bottom, depth)

  defp ordered_map_bdd?(:bdd_top, _lower, _depth), do: true
  defp ordered_map_bdd?(:bdd_bot, _lower, _depth), do: true
  defp ordered_map_bdd?({_, _, _} = leaf, lower, depth), do: map_literal?(leaf, lower, depth)

  defp ordered_map_bdd?({hash, lit, c, u, d}, lower, depth),
    do:
      is_integer(hash) and map_literal?(lit, lower, depth) and ordered_map_bdd?(c, lit, depth) and
        ordered_map_bdd?(u, lit, depth) and ordered_map_bdd?(d, lit, depth)

  defp ordered_map_bdd?(_bdd, _lower, _depth), do: false

  defp map_literal?({key, tag, fields} = lit, lower, depth),
    do:
      is_integer(key) and lit > lower and map_tag?(tag, depth) and
        not (tag == :open and fields == []) and map_fields?(fields, depth)

  defp map_literal?(_lit, _lower, _depth), do: false

  defp map_tag?(tag, _depth) when tag in [:open, :closed], do: true
  defp map_tag?(domains, depth), do: map_domains?(domains, depth)

  defp map_domains?([{_kind, type} | domains], depth),
    do: nested?(type, depth) and map_domains?(domains, depth)

  defp map_domains?([], _depth), do: true
  defp map_domains?(_domains, _depth), do: false

  defp map_fields?([{_key, {type, optional?}} | fields], depth),
    do: is_boolean(optional?) and nested?(type, depth) and map_fields?(fields, depth)

  defp map_fields?([], _depth), do: true
  defp map_fields?(_fields, _depth), do: false

  # Any type: the top type or a map of fields, whose dynamic part, if any,
  # is the top type or a map. The fields may hold anything.
  def descr?(:term), do: true
  def descr?(%{dynamic: dynamic}), do: dynamic == :term or is_map(dynamic)
  def descr?(descr), do: is_map(descr)

  defp sorted_keys?([{key, _} | [{next, _} | _] = fields]),
    do: is_atom(key) and key < next and sorted_keys?(fields)

  defp sorted_keys?([{key, _}]), do: is_atom(key)
  defp sorted_keys?(_fields), do: true

  # Types of the laws on optimized operations: the top type, or negatable types whose tuple
  # and map literals are keyed as Descr keys them at every depth, so closed literals sort
  # before open ones: closed literals have negative keys, open ones other than the top
  # literals and those with domains have non-negative keys, and map literals have atom keys
  # in order and domains of the kinds Descr knows in order. Function types inside other
  # types have arities that are natural numbers, at least one when they are unions, and keyed
  # arguments and returns. The depth comes with the recursive node, as `{depth, node}`.
  def opt_negatable?(:term, _depth), do: true

  def opt_negatable?(descr, {depth, _node} = nested),
    do: negatable?(descr, nested) and keyed_fields?(:maps.to_list(descr), depth, false)

  defp arrows?(%{fun: fun}, {depth, _node} = nested),
    do: nested_field?({:fun, fun}, nested) and keyed_fields?([{:fun, fun}], depth, true)

  defp arrows?(_descr, _nested), do: true

  # Static types of the laws: the types above whose function types are arrows between nested types.
  def arrows_static?(descr, nested), do: opt_negatable?(descr, nested) and arrows?(descr, nested)

  # Gradual types of the laws: static types, or a static part and a dynamic part of those types, where the dynamic
  # part includes the static part, as Descr maintains. Inclusion is checked with Descr.
  def arrows_gradual?(%{dynamic: dynamic} = descr, nested) do
    static = Map.delete(descr, :dynamic)

    arrows_static?(static, nested) and arrows_static?(dynamic, nested) and
      Descr.empty?(Descr.bare_difference(static, dynamic))
  end

  def arrows_gradual?(descr, nested), do: arrows_static?(descr, nested)

  defp keyed?(:term, _depth), do: true
  defp keyed?({_, _, _}, _depth), do: true
  defp keyed?(_descr, 0), do: true
  defp keyed?(descr, depth), do: keyed_fields?(:maps.to_list(descr), depth - 1, true)

  defp keyed_fields?([{:fun, {tag, arities}} | fields], depth, true) when is_map(arities),
    do:
      (tag == :negation or map_size(arities) > 0) and keyed_arities?(:maps.to_list(arities), depth) and
        keyed_fields?(fields, depth, true)

  defp keyed_fields?([{:fun, _fun} | _fields], _depth, true), do: false

  defp keyed_fields?([{:tuple, bdd} | fields], depth, element?),
    do: keyed_tuple_bdd?(bdd, depth) and keyed_fields?(fields, depth, element?)

  defp keyed_fields?([{:map, bdd} | fields], depth, element?),
    do: keyed_map_bdd?(bdd, depth) and keyed_fields?(fields, depth, element?)

  defp keyed_fields?([{:list, bdd} | fields], depth, element?),
    do: keyed_list_bdd?(bdd, depth) and keyed_fields?(fields, depth, element?)

  defp keyed_fields?([_field | fields], depth, element?), do: keyed_fields?(fields, depth, element?)
  defp keyed_fields?([], _depth, _element?), do: true
  defp keyed_fields?(_fields, _depth, _element?), do: false

  defp keyed_tuple_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_tuple_bdd?(lit, depth) and keyed_tuple_bdd?(c, depth) and keyed_tuple_bdd?(u, depth) and
        keyed_tuple_bdd?(d, depth)

  defp keyed_tuple_bdd?({key, :closed, elements}, depth),
    do: key < 0 and keyed_elements?(elements, depth)

  defp keyed_tuple_bdd?({key, _tag, elements}, depth),
    do: (elements == [] or key >= 0) and keyed_elements?(elements, depth)

  defp keyed_tuple_bdd?(_bdd, _depth), do: true

  defp keyed_elements?([element | elements], depth),
    do: keyed?(element, depth) and keyed_elements?(elements, depth)

  defp keyed_elements?([], _depth), do: true
  defp keyed_elements?(_elements, _depth), do: false

  defp keyed_map_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_map_bdd?(lit, depth) and keyed_map_bdd?(c, depth) and keyed_map_bdd?(u, depth) and
        keyed_map_bdd?(d, depth)

  defp keyed_map_bdd?({key, :closed, fields}, depth),
    do: key < 0 and sorted_keys?(fields) and keyed_values?(fields, depth)

  defp keyed_map_bdd?({key, domains, fields}, depth) when is_list(domains),
    do:
      key >= 0 and domain_kinds?(domains) and keyed_domains?(domains, depth) and sorted_keys?(fields) and
        keyed_values?(fields, depth)

  defp keyed_map_bdd?({key, _tag, fields}, depth),
    do: (fields == [] or key >= 0) and sorted_keys?(fields) and keyed_values?(fields, depth)

  defp keyed_map_bdd?(_bdd, _depth), do: true

  defp keyed_values?([{_key, {type, _optional?}} | fields], depth),
    do: keyed?(type, depth) and keyed_values?(fields, depth)

  defp keyed_values?([], _depth), do: true
  defp keyed_values?(_fields, _depth), do: false

  defp domain_kinds?([{kind, _} | [{next, _} | _] = domains]),
    do: domain_kind?(kind) and kind < next and domain_kinds?(domains)

  defp domain_kinds?([{kind, _}]), do: domain_kind?(kind)
  defp domain_kinds?(_domains), do: true

  defp domain_kind?(kind)
       when kind in [:atom, :binary, :bitstring_no_binary, :float, :fun, :integer] or
              kind in [:list, :map, :pid, :port, :reference, :tuple],
       do: true

  defp domain_kind?(_kind), do: false

  defp keyed_domains?([{_kind, type} | domains], depth),
    do: keyed?(type, depth) and keyed_domains?(domains, depth)

  defp keyed_domains?([], _depth), do: true
  defp keyed_domains?(_domains, _depth), do: false

  # Function types inside other types have arities that are natural numbers, at least one when
  # they are unions, and keyed arguments and returns.
  defp keyed_arities?([{arity, bdd} | arities], depth),
    do: is_integer(arity) and arity >= 0 and keyed_fun_bdd?(bdd, depth) and keyed_arities?(arities, depth)

  defp keyed_arities?([], _depth), do: true
  defp keyed_arities?(_arities, _depth), do: false

  defp keyed_fun_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_fun_bdd?(lit, depth) and keyed_fun_bdd?(c, depth) and keyed_fun_bdd?(u, depth) and
        keyed_fun_bdd?(d, depth)

  defp keyed_fun_bdd?({_key, args, return}, depth), do: keyed_elements?(args, depth) and keyed?(return, depth)
  defp keyed_fun_bdd?(_bdd, _depth), do: true

  defp keyed_list_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_list_bdd?(lit, depth) and keyed_list_bdd?(c, depth) and keyed_list_bdd?(u, depth) and
        keyed_list_bdd?(d, depth)

  defp keyed_list_bdd?({_key, list, last}, depth), do: keyed?(list, depth) and keyed?(last, depth)
  defp keyed_list_bdd?(_bdd, _depth), do: true

  # Keys of map types, as lists of atoms and of kinds of keys that map domains name.
  def keys?(atoms, kinds), do: atom_list?(atoms) and kind_list?(kinds)

  defp atom_list?([atom | atoms]), do: is_atom(atom) and atom_list?(atoms)
  defp atom_list?(atoms), do: atoms == []

  defp kind_list?([kind | kinds]), do: domain_kind?(kind) and kind_list?(kinds)
  defp kind_list?(kinds), do: kinds == []

  # The type of the keys of the given atoms and kinds.
  def key_type([], kinds), do: kinds_type(kinds, Descr.none())
  def key_type(atoms, kinds), do: kinds_type(kinds, Descr.atom(atoms))

  defp kinds_type([kind | kinds], acc), do: kinds_type(kinds, Descr.bare_union(kind_type(kind), acc))
  defp kinds_type([], acc), do: acc

  defp kind_type(:atom), do: Descr.atom()
  defp kind_type(:binary), do: Descr.binary()
  defp kind_type(:bitstring_no_binary), do: Descr.bitstring_no_binary()
  defp kind_type(:float), do: Descr.float()
  defp kind_type(:fun), do: Descr.fun()
  defp kind_type(:integer), do: Descr.integer()
  defp kind_type(:list), do: Descr.bare_union(Descr.empty_list(), Descr.non_empty_list(Descr.term(), Descr.term()))
  defp kind_type(:map), do: Descr.open_map()
  defp kind_type(:pid), do: Descr.pid()
  defp kind_type(:port), do: Descr.port()
  defp kind_type(:reference), do: Descr.reference()
  defp kind_type(:tuple), do: Descr.tuple()

  # Maps whose keys of the given atoms and kinds hold values of a type: the open maps
  # holding them at each of those keys.
  def keys_hold(atoms, kinds, value), do: kinds_hold(kinds, value, atoms_hold(atoms, value, Descr.open_map()))

  defp atoms_hold([atom | atoms], value, acc),
    do: atoms_hold(atoms, value, Descr.bare_intersection(acc, Descr.open_map([{atom, {value, true}}])))

  defp atoms_hold([], _value, acc), do: acc

  defp kinds_hold([kind | kinds], value, acc),
    do: kinds_hold(kinds, value, Descr.bare_intersection(acc, Descr.open_map([{[kind], value}])))

  defp kinds_hold([], _value, acc), do: acc

  # Pairs of map constructors: atom keys with types and optional flags, and lists of kinds of keys
  # with types, all of them static types of the given nesting.
  def map_pairs?([{key, {value, optional?}} | pairs], nested) when is_atom(key) and is_boolean(optional?),
    do: arrows_static?(value, nested) and map_pairs?(pairs, nested)

  def map_pairs?([{kinds, value} | pairs], nested) when is_list(kinds),
    do: kind_list?(kinds) and arrows_static?(value, nested) and map_pairs?(pairs, nested)

  def map_pairs?(pairs, _nested), do: pairs == []

  # The map constructors of open and closed maps.
  def construct(:open, pairs), do: Descr.open_map(pairs)
  def construct(:closed, pairs), do: Descr.closed_map(pairs)

  # The field a constructed map holds at an atom key: that of the last pair of the key, or the
  # optional values of the atom domain.
  def atom_field(tag, pairs, key) do
    case :lists.keyfind(key, 1, :lists.reverse(pairs)) do
      {^key, field} -> field
      false -> {domain_value(tag, pairs, :atom), true}
    end
  end

  # The values a constructed map holds at the keys of a kind: the union of the types of the pairs
  # naming the kind, or any value for open maps and none for closed ones.
  def domain_value(tag, pairs, kind), do: domain_value(pairs, kind, tag_value(tag), false)

  defp domain_value([{kinds, value} | pairs], kind, acc, found?) when is_list(kinds) do
    case kind_in?(kinds, kind) do
      true when found? -> domain_value(pairs, kind, Descr.bare_union(acc, value), true)
      true -> domain_value(pairs, kind, value, true)
      false -> domain_value(pairs, kind, acc, found?)
    end
  end

  defp domain_value([_pair | pairs], kind, acc, found?), do: domain_value(pairs, kind, acc, found?)
  defp domain_value([], _kind, acc, _found?), do: acc

  defp kind_in?([kind | kinds], other), do: kind == other or kind_in?(kinds, other)
  defp kind_in?([], _other), do: false

  defp tag_value(:open), do: Descr.term()
  defp tag_value(:closed), do: Descr.none()

  laws "static" do
    # Elixir's default map field access falls back to a remote call on non-maps.
    cutoff &:elixir_erl_pass.no_parens_remote/2

    # Lines with negative tuple or map literals are not modeled, so their
    # emptiness is cut off.

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
    termination_suffix &Descr.upper_bound/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.lower_bound/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_seen?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_union/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_difference/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_intersection/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_difference/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_map_difference_strategy/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:orddict.merge/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fields_merge_with_defaults/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.duplicate/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_map_union_strategy/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_tuple_fuse_elements/4, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_tuple_union_leaf/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_difference_subtype?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.iterator_empty_difference_subtype?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fun_line_empty?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.dynamic/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_fetch/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_fetch_key/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_get/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_split_keys_and_domains/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.to_domain_keys/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:sets.fold_1/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_to_list/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.ukeymerge3_1/11, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.rukeymerge3_1/11, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.umergel/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.ukeymergel/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fields_put_all_new/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_elim_sizes/4, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_delete_at/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_insert_at/3, ~LEAN"partial_fixpoint", recur: true
    # Nested types are finite, so their specification terminates.
    termination_suffix &__MODULE__.nested?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &__MODULE__.keyed?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &__MODULE__.sorted_keys?/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &__MODULE__.domain_kinds?/1, ~LEAN"partial_fixpoint", recur: true

    # Valid types hold a non-empty bitmap and atom types of version 2 sets.
    postlude "descr/valid_types.lean"

    # Unions merge fields with maps:merge_with/3.
    postlude "descr/union_fields.lean"

    # Intersections intersect fields with maps:intersect_with/3 and drop empty ones.
    postlude "descr/intersection_fields.lean"

    # Differences fold over the fields of the right type and drop empty ones.
    postlude "descr/difference_fields.lean"

    # The empty type is the empty map, and intersecting with it empties a type.
    postlude "descr/empty_type.lean"

    # A function type and its negation hold the same BDDs for each arity, whose
    # differences are bottom, so their intersection drops every arity.
    postlude "descr/function_negation.lean"

    # Lazy BDDs ordered by their literals: unions, removals, intersections,
    # negations, and differences terminate and compute the propositional
    # connectives, so a BDD that no assignment of its literals satisfies has no line.
    postlude "descr/bdd_connectives.lean"

    # Tuple types are the top tuple literal or ordered BDDs of other tuple literals,
    # whose elements are types of bitmaps, atoms, tuples, and lists. Lines of
    # tuples intersect these elements, which stay such types, and what remains
    # of a tuple type and its negation has no line, except for the empty tuple,
    # whose negation holds tuples of other sizes.
    postlude "descr/tuple_negation.lean"

    # Map types are the top map literal or ordered BDDs of other map literals,
    # open or closed maps whose fields hold types of bitmaps and atoms. Lines of
    # maps intersect these fields, whose emptiness is immediate, and what remains
    # of a map type and its negation has no line.
    postlude "descr/map_negation.lean"

    # List types are the top list literal or ordered BDDs of other list literals,
    # so negations hold the same literals and the list intersection shortcuts
    # never apply. What remains of a list type and its negation has no line.
    postlude "descr/list_negation.lean"

    # Negations are differences from the top type, which no type intersects.
    postlude "descr/negation_intersection.lean"

    # The optimized operations compute the same negations of bitmaps, atoms, functions,
    # lists, and tuples, while open maps of one field negate to open maps of one field.
    # Their intersections fall back to BDD intersections, since the negation of a BDD
    # node is never a leaf, or intersect literals whose fields do not meet.
    postlude "descr/opt_negation_intersection.lean"

    # The top type is a subtype of a type united with its negation: each field of the top
    # type, minus what the type and its negation unite into at that field, is empty.
    # Propositional BDD unions are tautologies, while `{}` and its negation `{term, ...}`
    # are checked as concrete tuple lines.
    postlude "descr/union_negation_top.lean"

    # Optimized unions of a type with its optimized negation fuse open maps of a single
    # field into one, except for `:__struct__` keys, which only fuse when one side is a
    # subtype. Basic types, whose fields are non-empty bitmaps, atoms, or the top function,
    # list, tuple, and map types, compute set operations, so the fused fields and the map
    # lines of both single field maps can be checked directly.
    postlude "descr/opt_union_negation.lean"

    # De Morgan's law for the plain operations. Each field denotes a propositional predicate:
    # bitmaps their bits, atoms their members, functions their BDDs per arity, and lists,
    # tuples, and maps their BDDs. Unions, intersections, and negations compute the
    # connectives, under valuations that some tuple realizes for tuple literals, since the
    # negation of `{}` is `{term, ...}`. A type whose fields hold no more than another's is
    # its subtype, since tuple lines that no realizable valuation satisfies are empty.
    postlude "descr/plain_de_morgan.lean"
    postlude "descr/recursive_node.lean"
    postlude "descr/element_values.lean"
    postlude "descr/basic_values.lean"
    postlude "descr/open_map_leaves.lean"
    postlude "descr/basic_subtype_sound.lean"
    postlude "descr/tuple_opt_union_literals.lean"
    postlude "descr/tuple_fuse_flat.lean"
    postlude "descr/tuple_negation_flat.lean"
    postlude "descr/opt_fields_values.lean"
    postlude "descr/compare_lt_trans.lean"
    postlude "descr/opt_union_element_top.lean"
    postlude "descr/tuple3_eq.lean"
    postlude "descr/opt_intersection_basic.lean"
    postlude "descr/map_opt_negation_values.lean"
    postlude "descr/map_opt_intersection_negation.lean"
    postlude "descr/bdd_line_valuations.lean"
    postlude "descr/tuple_opt_intersection_values.lean"
    postlude "descr/bdd_compare_differences.lean"
    postlude "descr/element_disjoint.lean"
    postlude "descr/list_differences_values.lean"
    postlude "descr/flat_field_differences.lean"
    postlude "descr/flat_differences.lean"
    postlude "descr/sorted_keys.lean"
    postlude "descr/literal_heights.lean"
    postlude "descr/flat_elements.lean"
    postlude "descr/tuple_opt_union_elements.lean"
    postlude "descr/tuple_fuse_elements.lean"
    postlude "descr/tuple_opt_intersection_elements.lean"
    postlude "descr/tuple_differences_values.lean"
    postlude "descr/tuple_emptiness_sound.lean"
    postlude "descr/node_tuple_fields.lean"
    postlude "descr/tuple_emptiness_exact.lean"
    postlude "descr/tuple_heights.lean"
    postlude "descr/structural_kinds.lean"
    postlude "descr/list_emptiness_sound.lean"
    postlude "descr/list_emptiness_exact.lean"
    postlude "descr/list_plain_operations.lean"
    postlude "descr/list_opt_union_intersection.lean"
    postlude "descr/list_opt_difference.lean"
    postlude "descr/list_kind.lean"
    postlude "descr/kind_fields.lean"
    postlude "descr/kind_operations.lean"
    postlude "descr/kind_emptiness.lean"
    postlude "descr/kind_congruence.lean"
    postlude "descr/kind_subtype_disjoint.lean"
    postlude "descr/value_maps.lean"
    postlude "descr/map_line_completeness.lean"
    postlude "descr/map_literal_intersections.lean"
    postlude "descr/map_bdd_emptiness.lean"
    postlude "descr/map_opt_union_literals.lean"
    postlude "descr/map_opt_union_types.lean"
    postlude "descr/map_opt_intersection_elements.lean"
    postlude "descr/map_opt_negation_elements.lean"
    postlude "descr/map_opt_difference_strategy.lean"
    postlude "descr/map_differences_values.lean"
    postlude "descr/map_opt_difference_literals.lean"
    postlude "descr/map_emptiness_sound_fields.lean"
    postlude "descr/map_emptiness_sound.lean"
    postlude "descr/map_emptiness_exact.lean"
    postlude "descr/map_heights.lean"
    postlude "descr/map_field_elements.lean"
    postlude "descr/map_kind.lean"
    postlude "descr/bottom_level.lean"
    postlude "descr/function_values.lean"
    postlude "descr/term_list_positions.lean"
    postlude "descr/phi_terms.lean"
    postlude "descr/phi_cache.lean"
    postlude "descr/phi_skip.lean"
    postlude "descr/phi_empty_sets.lean"
    postlude "descr/phi_positive_arrows.lean"
    postlude "descr/phi_run.lean"
    postlude "descr/arrow_application.lean"
    postlude "descr/function_checks.lean"
    postlude "descr/function_type_values.lean"
    postlude "descr/element_top_function.lean"
    postlude "descr/function_element_types.lean"
    postlude "descr/top_type_operands.lean"
    postlude "descr/next_level_elements.lean"
    postlude "descr/next_level_fuse.lean"
    postlude "descr/function_check_elements.lean"
    postlude "descr/level_step.lean"
    postlude "descr/node_elements.lean"
    postlude "descr/levels.lean"
    postlude "descr/empty_no_points.lean"
    postlude "descr/top_level_types.lean"
    postlude "descr/keyed_elements.lean"
    postlude "descr/top_type_levels.lean"
    postlude "descr/keyed_specification.lean"
    postlude "descr/plain_top_laws.lean"
    postlude "descr/merge_fields.lean"
    postlude "descr/gradual_types.lean"
    postlude "descr/gradual_unions.lean"
    postlude "descr/gradual_intersections.lean"
    postlude "descr/gradual_differences.lean"
    postlude "descr/gradual_negations.lean"
    postlude "descr/gradual_subtype_complete.lean"
    postlude "descr/gradual_laws.lean"
    postlude "descr/top_level_emptiness_sound.lean"
    postlude "descr/gradual_negation_bounds.lean"

    # Compatibility only checks emptiness, inclusion, and disjointness of the bounds of gradual types, which are
    # exact on the element types of the next level, whose function types are the top one.
    postlude "descr/gradual_compatibility.lean"
    postlude "descr/arrow_subtype_order.lean"
    postlude "descr/arrow_union_intersection.lean"
    postlude "descr/arrow_difference_negation.lean"
    postlude "descr/tuple_fetch_elements.lean"
    postlude "descr/tuple_fetch_lines.lean"
    postlude "descr/tuple_fetch.lean"
    postlude "descr/map_split_key.lean"
    postlude "descr/map_move_key.lean"
    postlude "descr/map_lines.lean"
    postlude "descr/map_split_pairs.lean"
    postlude "descr/map_pop_key.lean"
    postlude "descr/map_fetch.lean"
    postlude "descr/tuple_insert_elements.lean"
    postlude "descr/tuple_positive_literals.lean"
    postlude "descr/tuple_insert.lean"
    postlude "descr/tuple_insert_at.lean"
    postlude "descr/tuple_delete.lean"

    # The top function type of an arity is the arrow from that many arguments of none() to term():
    # removing the arrow leaves a line whose only negative literal is the arrow itself, which phi covers.
    postlude "descr/function_arity.lean"
    postlude "descr/map_get_keys.lean"
    postlude "descr/map_set_key.lean"
    postlude "descr/map_split_keys.lean"
    postlude "descr/map_static_get.lean"
    postlude "descr/map_get.lean"
    postlude "descr/bitmap_key_kinds.lean"
    postlude "descr/point_key_kinds.lean"
    postlude "descr/map_union_points.lean"
    postlude "descr/key_types.lean"
    postlude "descr/lists_sort_compare.lean"
    postlude "descr/lists_sort_merges.lean"
    postlude "descr/lists_ukeymerge2.lean"
    postlude "descr/lists_ukeymerge3.lean"
    postlude "descr/lists_rukeymerge.lean"
    postlude "descr/lists_ukeymergel.lean"
    postlude "descr/lists_ukeysort_1.lean"
    postlude "descr/lists_ukeysort_2.lean"
    postlude "descr/lists_ukeysort.lean"
    postlude "descr/lists_umerge.lean"
    postlude "descr/lists_rumerge.lean"
    postlude "descr/lists_umergel.lean"
    postlude "descr/lists_usort_1.lean"
    postlude "descr/lists_usort_2.lean"
    postlude "descr/lists_usort.lean"
    postlude "descr/open_map_domain.lean"
    postlude "descr/maps_of_points.lean"
    postlude "descr/open_map_subtype.lean"
    postlude "descr/tuple_list_constructors.lean"
    postlude "descr/points_above.lean"
    postlude "descr/map_line_pairs.lean"
    postlude "descr/single_atom.lean"
    postlude "descr/map_swap_keys.lean"
    postlude "descr/optional_fields.lean"
    postlude "descr/map_dnf_nonempty.lean"
    postlude "descr/map_to_list.lean"
    postlude "descr/map_to_list_pairs.lean"
    postlude "descr/key_sorted_lists.lean"
    postlude "descr/map_pairs_fold.lean"
    postlude "descr/map_descr_pairs.lean"
    postlude "descr/map_constructor_values.lean"
    postlude "descr/map_constructor_run.lean"
    postlude "descr/open_map_atom_key.lean"

    law intersection_none_empty(descr),
      requires: descr?(descr),
      expects: Descr.empty?(Descr.bare_intersection(descr, Descr.none())),
      proof: ~LEAN"""
      -- The proofs run from a depth of 100 on.
      refine ⟨100, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le' deep
      open Lynx Lynx.Term in
      simp only [«intersection_none_empty:requires/1»] at requires
      simp only [Lynx.apply_eq, «intersection_none_empty:ensures/1», Elixir.Module.Types.Descr.«none/0»]
      cases descr with
      | map X =>
        cases dynamic : mapLookup X (.atom "dynamic") with
        | none => simp [intersection_none_static (δ + 99) X dynamic, empty_none]
        | some Dy =>
          have inner : Dy = .atom "term" ∨ ∃ Y, Dy = .map Y := by
            simp [«descr?/1», getMapKeys_single, dynamic, Erlang.erlang.«==/2», Erlang.erlang.«is_map/1»] at requires
            cases Dy <;> simp_all
          simp [intersection_none_dynamic (δ + 99) X Dy dynamic inner, empty_none]
      | atom name =>
        by_cases top : name = "term"
        · subst top
          unfold Elixir.Module.Types.Descr.«bare_intersection/2»
          simp [empty_none]
        · simp [«descr?/1», top, Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      | _ => simp [«descr?/1», Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      """

    law intersection_negation_empty(descr, depth, node),
      requires: (negatable?(descr, {depth, node}) or arrows_gradual?(descr, {depth, node})) and depth?(depth),
      expects: Descr.empty?(Descr.lower_bound(Descr.bare_intersection(descr, Descr.bare_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_negation_empty:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_negation_empty:requires/3», Term.true, Lynx.Except.orElse_eq_true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      simp only [Lynx.apply_eq, «intersection_negation_empty:ensures/3»]
      rcases requires with static | ⟨-, gradual⟩
      · rcases Nest.negatable_cases node d descr (by simpa [Term.true] using static) with rfl | ⟨X, rfl, valid⟩
        · simp [negation_term_none, inter_term_left, Nest.lower_bound_run, Nest.lower, Nest.rmDyn, empty_none]
        obtain ⟨ops, -, -, -, -⟩ := closed_ok node d
        replace valid := valid.mono (nest_closed node d)
        by_cases empty : X = []
        · subst empty
          have negation : Elixir.Module.Types.Descr.«bare_negation/1»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) = .ok (.atom "term") := by
            simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
            unfold Elixir.Module.Types.Descr.«bare_difference/2»
            simp [Erlang.erlang.«==/2»]
          have intersection : Elixir.Module.Types.Descr.«bare_intersection/2»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) (.atom "term") = .ok (.map []) := by
            unfold Elixir.Module.Types.Descr.«bare_intersection/2»
            rfl
          simp [negation, intersection, Nest.lower_bound_run, Nest.lower, Nest.rmDyn, empty_none]
        · obtain ⟨N, negation, static, bitmaps, atoms, funs, lists, tuples, maps, -⟩ :=
            negation_fields ops (δ + 98) X valid empty
          obtain ⟨I, run, only⟩ := intersection_disjoint (δ + 99) X N valid static bitmaps atoms
            (fun x y hx hy => funs x y hx hy (δ + 99)) lists tuples maps
          have staticI : mapLookup I (.atom "dynamic") = Option.none := by
            cases h : mapLookup I (.atom "dynamic") with
            | none => rfl
            | some w => rcases only _ _ h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> simp at e
          simp [negation, run, Nest.lower_bound_run, Nest.lower, Nest.rmDyn_static staticI,
            empty_gone (m := δ + 100) (by omega) I only]
      · have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr gradual
        obtain ⟨n, i, r₁, r₂, r₃, eq⟩ := Nest.gd_inter_neg_lower t (m := δ + 100) (by rw [Nest.level_K]; omega)
        simp [r₁, r₂, r₃, eq]
      """

    law opt_intersection_negation_empty(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.empty?(Descr.lower_bound(Descr.opt_intersection(descr, Descr.opt_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_intersection_negation_empty:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_intersection_negation_empty:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr requires
      obtain ⟨n, i, r₁, r₂, r₃, eq⟩ := Nest.gd_opt_inter_neg_lower t (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_intersection_negation_empty:ensures/3»]
      simp [r₁, r₂, r₃, eq]
      """

    law union_negation_term(descr, depth, node),
      requires: (negatable?(descr, {depth, node}) or arrows_gradual?(descr, {depth, node})) and depth?(depth),
      expects: Descr.subtype?(Descr.term(), Descr.upper_bound(Descr.bare_union(descr, Descr.bare_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_negation_term:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_negation_term:requires/3», Term.true, Lynx.Except.orElse_eq_true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      simp only [Lynx.apply_eq, «union_negation_term:ensures/3»]
      rcases requires with static | ⟨-, gradual⟩
      · rcases Nest.negatable_cases node d descr (by simpa [Term.true] using static) with rfl | ⟨X, rfl, valid⟩
        · simp [Elixir.Module.Types.Descr.«term/0», negation_term_none, union_term_l, Nest.upper_bound_term,
            Nest.sub_term_term]
        obtain ⟨ops, -, -, -, -⟩ := closed_ok node d
        replace valid := valid.mono (nest_closed node d)
        by_cases empty : X = []
        · subst empty
          have negation : Elixir.Module.Types.Descr.«bare_negation/1»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) = .ok (.atom "term") := by
            simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
            unfold Elixir.Module.Types.Descr.«bare_difference/2»
            simp [Erlang.erlang.«==/2»]
          have union : Elixir.Module.Types.Descr.«bare_union/2»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) (.atom "term") = .ok (.atom "term") := by
            unfold Elixir.Module.Types.Descr.«bare_union/2»
            rfl
          simp [Elixir.Module.Types.Descr.«term/0», negation, union, Nest.upper_bound_term, Nest.sub_term_term]
        · obtain ⟨N, U, negation, union, staticU, sub⟩ := union_negation_covers δ ops (by omega) X valid empty
          simp [Elixir.Module.Types.Descr.«term/0», negation, union, Nest.upper_bound_static staticU, sub]
      · have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr gradual
        obtain ⟨n, u, r₁, r₂, r₃, sub⟩ := Nest.gd_union_neg_upper t (m := δ + 100) (by rw [Nest.level_K]; omega)
        simp [Elixir.Module.Types.Descr.«term/0», r₁, r₂, r₃, sub]
      """

    law opt_union_negation_term(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(Descr.term(), Descr.upper_bound(Descr.opt_union(descr, Descr.opt_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_union_negation_term:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_union_negation_term:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr requires
      obtain ⟨n, u, r₁, r₂, r₃, sub⟩ := Nest.gd_opt_union_neg_upper t (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_union_negation_term:ensures/3»]
      simp [Elixir.Module.Types.Descr.«term/0», r₁, r₂, r₃, sub]
      """

    law de_morgan_union(left, right, depth, node),
      requires:
        ((negatable?(left, {depth, node}) and negatable?(right, {depth, node})) or
           (arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}))) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_negation(Descr.bare_union(left, right)),
          Descr.bare_intersection(Descr.bare_negation(left), Descr.bare_negation(right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «de_morgan_union:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «de_morgan_union:requires/4», Term.true, Lynx.Except.orElse_eq_true,
        Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      simp only [Lynx.apply_eq, «de_morgan_union:ensures/4»]
      rcases requires with ⟨sl, sr⟩ | ⟨-, gl, gr⟩
      · exact de_morgan_union_any δ (by omega) (Nest.negatable_cases node d left (by simpa [Term.true] using sl))
          (Nest.negatable_cases node d right (by simpa [Term.true] using sr))
      · have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left gl
        have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right gr
        obtain ⟨u, x, nl, nr, y, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
          Nest.gd_de_morgan_union tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
        simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_de_morgan_union(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.opt_negation(Descr.opt_union(left, right)),
          Descr.opt_intersection(Descr.opt_negation(left), Descr.opt_negation(right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_de_morgan_union:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_de_morgan_union:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, x, nl, nr, y, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
        Nest.gd_opt_de_morgan_union tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_de_morgan_union:ensures/4»]
      simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_de_morgan_intersection(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.opt_negation(Descr.opt_intersection(left, right)),
          Descr.opt_union(Descr.opt_negation(left), Descr.opt_negation(right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_de_morgan_intersection:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_de_morgan_intersection:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, x, nl, nr, y, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
        Nest.gd_opt_de_morgan_inter tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_de_morgan_intersection:ensures/4»]
      simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_intersection_subtype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(Descr.opt_intersection(left, right), left) and
          Descr.subtype?(Descr.opt_intersection(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_intersection_subtype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_intersection_subtype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, r₁, s₁, s₂⟩ := Nest.gd_opt_inter_sub tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_intersection_subtype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law opt_union_supertype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(left, Descr.opt_union(left, right)) and
          Descr.subtype?(right, Descr.opt_union(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_union_supertype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_union_supertype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, r₁, s₁, s₂⟩ := Nest.gd_opt_union_sup tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_union_supertype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law intersection_subtype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(Descr.bare_intersection(left, right), left) and
          Descr.subtype?(Descr.bare_intersection(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_subtype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_subtype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, r₁, s₁, s₂⟩ := Nest.gd_inter_sub tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «intersection_subtype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law union_supertype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(left, Descr.bare_union(left, right)) and
          Descr.subtype?(right, Descr.bare_union(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_supertype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_supertype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, r₁, s₁, s₂⟩ := Nest.gd_union_sup tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «union_supertype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law opt_union_equal(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(Descr.bare_union(left, right), Descr.opt_union(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_union_equal:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_union_equal:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, w, r₁, r₂, eq⟩ := Nest.gd_union_equal tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_union_equal:ensures/4»]
      simp [r₁, r₂, eq]
      """

    law opt_intersection_equal(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(Descr.bare_intersection(left, right), Descr.opt_intersection(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_intersection_equal:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_intersection_equal:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, j, r₁, r₂, eq⟩ := Nest.gd_inter_equal tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_intersection_equal:ensures/4»]
      simp [r₁, r₂, eq]
      """

    law intersection_union_distributive(descr, left, right, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_intersection(descr, Descr.bare_union(left, right)),
          Descr.bare_union(Descr.bare_intersection(descr, left), Descr.bare_intersection(descr, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_union_distributive:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_union_distributive:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tT := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr (by simpa [Term.true] using requires.1.1)
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1.2)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, x, y, z, w, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
        Nest.gd_distrib tT tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «intersection_union_distributive:ensures/5»]
      simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_negation_equal(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_negation(descr), Descr.opt_negation(descr)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_negation_equal:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_negation_equal:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr requires
      obtain ⟨x, y, r₁, r₂, eq⟩ := Nest.gd_neg_equal t (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_negation_equal:ensures/3»]
      simp [r₁, r₂, eq]
      """

    law opt_difference_equal(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_difference(left, right), Descr.opt_difference(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_difference_equal:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_difference_equal:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨x, y, r₁, r₂, eq⟩ := Nest.gd_diff_equal tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_difference_equal:ensures/4»]
      simp [r₁, r₂, eq]
      """

    law fun_arity_equal(arity),
      requires: is_integer(arity) and arity >= 0,
      expects: Descr.equal?(Descr.fun(arity), Descr.fun(:lists.duplicate(arity, Descr.none()), Descr.term())),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      obtain ⟨n, rfl⟩ : ∃ n : Nat, arity = .integer n := by
        simp only [«fun_arity_equal:requires/1»] at requires
        cases arity <;> simp [Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true, Erlang.erlang.«>=/2»,
          Int.isGE_compare] at requires
        rename_i z
        exact ⟨z.toNat, by simp only [Term.integer.injEq]; omega⟩
      -- The proofs run from a depth of 100 on.
      refine ⟨100, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le' deep
      obtain ⟨right, run, eq⟩ := fun_arity_equal_run n (δ + 100) (by omega)
      simp only [Lynx.apply_eq, «fun_arity_equal:ensures/1»]
      simp [fun_arity_run, Elixir.Module.Types.Descr.«none/0», dup_nat, Elixir.Module.Types.Descr.«term/0», run, eq,
        Term.true]
      """

    law compatible_bounds(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.compatible?(left, right) ==
          (Descr.subtype?(Descr.lower_bound(left), Descr.upper_bound(right)) and not Descr.disjoint?(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «compatible_bounds:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «compatible_bounds:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      obtain ⟨gl, ll, ul⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (by rw [Nest.level_K]; omega) requires.1
      obtain ⟨gr, -, ur⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (by rw [Nest.level_K]; omega) requires.2
      obtain ⟨b, r₁, r₂⟩ := Nest.gd_compatible gl gr ll ul ur (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «compatible_bounds:ensures/4»]
      simp [r₁, Nest.lower_bound_run gl.shape, Nest.upper_bound_run gr.ub, r₂, Erlang.erlang.«==/2», Term.true]
      """

    law subtype_reflexive(descr),
      requires: descr?(descr),
      expects: Descr.subtype?(descr, descr),
      proof: ~LEAN"""
      -- The proofs run from a depth of 1 on.
      refine ⟨1, fun depth _ => ?_⟩
      open Lynx Lynx.Term in
      simp only [«subtype_reflexive:requires/1»] at requires
      simp only [Lynx.apply_eq, «subtype_reflexive:ensures/1»]
      cases descr with
      | map X => simp [Nest.subtype_refl _ (Or.inr ⟨X, rfl⟩), Term.true]
      | atom name =>
        by_cases top : name = "term"
        · subst top; simp [Nest.subtype_refl _ (Or.inl rfl), Term.true]
        · simp [«descr?/1», top, Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      | _ => simp [«descr?/1», Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      """

    law subtype_transitive(left, middle, right, depth, node),
      requires:
        arrows_gradual?(left, {depth, node}) and arrows_gradual?(middle, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        not (Descr.subtype?(left, middle) and Descr.subtype?(middle, right)) or Descr.subtype?(left, right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «subtype_transitive:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «subtype_transitive:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨ga, la, ua⟩ := Nest.arrows_gradual_ok hK requires.1.1
      obtain ⟨gb, lb, ub⟩ := Nest.arrows_gradual_ok hK requires.1.2
      obtain ⟨gc, lc, uc⟩ := Nest.arrows_gradual_ok hK requires.2
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rw [Lynx.apply_eq, «subtype_transitive:ensures/5», Nest.gd_sub ga gb la ua lb ub hm, Nest.gd_sub gb gc lb ub lc uc hm,
        Nest.gd_sub ga gc la ua lc uc hm]
      by_cases h₁ : Nest.SubN node d (Nest.lower left) (Nest.lower middle) ∧
          Nest.SubN node d (Nest.upper left) (Nest.upper middle)
      · by_cases h₂ : Nest.SubN node d (Nest.lower middle) (Nest.lower right) ∧
            Nest.SubN node d (Nest.upper middle) (Nest.upper right)
        · have h₃ : Nest.SubN node d (Nest.lower left) (Nest.lower right) ∧
              Nest.SubN node d (Nest.upper left) (Nest.upper right) :=
            ⟨fun v h => h₂.1 v (h₁.1 v h), fun v h => h₂.2 v (h₁.2 v h)⟩
          simp [Nest.bp_true.mpr h₁, Nest.bp_true.mpr h₂, Nest.bp_true.mpr h₃, boolAtom, Lynx.Except.andAlso]
        · simp [Nest.bp_true.mpr h₁, Nest.bp_false.mpr h₂, boolAtom, Lynx.Except.andAlso]
      · simp [Nest.bp_false.mpr h₁, boolAtom, Lynx.Except.andAlso]
      """

    law equal_subtype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(left, right) == (Descr.subtype?(left, right) and Descr.subtype?(right, left)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «equal_subtype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «equal_subtype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨gl, ll, ul⟩ := Nest.arrows_gradual_ok hK requires.1
      obtain ⟨gr, lr, ur⟩ := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨s₁, s₂, r₁, r₂, r₃⟩ := Nest.gd_equal gl gr ll ul lr ur (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «equal_subtype:ensures/4»]
      cases s₁ <;> cases s₂ <;> simp [r₁, r₂, r₃, boolAtom, Lynx.Except.andAlso, Erlang.erlang.«==/2», Term.true]
      """

    law disjoint_empty(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.disjoint?(left, right) == Descr.empty?(Descr.bare_intersection(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «disjoint_empty:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «disjoint_empty:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨gl, -, ul⟩ := Nest.arrows_gradual_ok hK requires.1
      obtain ⟨gr, -, ur⟩ := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c, s, run, r₁, r₂⟩ := Nest.gd_disj_empty gl gr ul ur (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «disjoint_empty:ensures/4»]
      cases s <;> simp [run, r₁, r₂, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law union_commutative(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_union(left, right), Descr.bare_union(right, left)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_commutative:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_commutative:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union gr gl hm
      have eq := Nest.gd_eq_true g₁ g₂ (m := δ + 100) (by omega) (fun v => by rw [l₁, l₂]; exact or_comm)
        (fun v => by rw [u₁, u₂]; exact or_comm)
      simp only [Lynx.apply_eq, «union_commutative:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law intersection_commutative(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_intersection(left, right), Descr.bare_intersection(right, left)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_commutative:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_commutative:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_inter gr gl hm
      have eq := Nest.gd_eq_true g₁ g₂ (m := δ + 100) (by omega) (fun v => by rw [l₁, l₂]; exact and_comm)
        (fun v => by rw [u₁, u₂]; exact and_comm)
      simp only [Lynx.apply_eq, «intersection_commutative:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law union_associative(left, middle, right, depth, node),
      requires:
        arrows_gradual?(left, {depth, node}) and arrows_gradual?(middle, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_union(Descr.bare_union(left, middle), right),
          Descr.bare_union(left, Descr.bare_union(middle, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_associative:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_associative:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1.1
      have gm : Nest.GD node d middle := Nest.arrows_gradual_ok hK requires.1.2
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gl gm hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union g₁ gr hm
      obtain ⟨c₃, r₃, g₃, l₃, u₃⟩ := Nest.gd_union gm gr hm
      obtain ⟨c₄, r₄, g₄, l₄, u₄⟩ := Nest.gd_union gl g₃ hm
      have eq := Nest.gd_eq_true g₂ g₄ (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁, l₄, l₃]; exact or_assoc)
        (fun v => by rw [u₂, u₁, u₄, u₃]; exact or_assoc)
      simp only [Lynx.apply_eq, «union_associative:ensures/5»]
      simp [r₁, r₂, r₃, r₄, eq, Term.true]
      """

    law intersection_associative(left, middle, right, depth, node),
      requires:
        arrows_gradual?(left, {depth, node}) and arrows_gradual?(middle, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_intersection(Descr.bare_intersection(left, middle), right),
          Descr.bare_intersection(left, Descr.bare_intersection(middle, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_associative:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_associative:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1.1
      have gm : Nest.GD node d middle := Nest.arrows_gradual_ok hK requires.1.2
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gm hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_inter g₁ gr hm
      obtain ⟨c₃, r₃, g₃, l₃, u₃⟩ := Nest.gd_inter gm gr hm
      obtain ⟨c₄, r₄, g₄, l₄, u₄⟩ := Nest.gd_inter gl g₃ hm
      have eq := Nest.gd_eq_true g₂ g₄ (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁, l₄, l₃]; exact and_assoc)
        (fun v => by rw [u₂, u₁, u₄, u₃]; exact and_assoc)
      simp only [Lynx.apply_eq, «intersection_associative:ensures/5»]
      simp [r₁, r₂, r₃, r₄, eq, Term.true]
      """

    law union_idempotent(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_union(descr, descr), descr),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_idempotent:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_idempotent:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gd : Nest.GD node d descr := Nest.arrows_gradual_ok hK requires
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gd gd hm
      have eq := Nest.gd_eq_true g₁ gd (m := δ + 100) (by omega) (fun v => by rw [l₁]; exact or_self_iff)
        (fun v => by rw [u₁]; exact or_self_iff)
      simp only [Lynx.apply_eq, «union_idempotent:ensures/3»]
      simp [r₁, eq, Term.true]
      """

    law intersection_idempotent(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_intersection(descr, descr), descr),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_idempotent:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_idempotent:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gd : Nest.GD node d descr := Nest.arrows_gradual_ok hK requires
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gd gd hm
      have eq := Nest.gd_eq_true g₁ gd (m := δ + 100) (by omega) (fun v => by rw [l₁]; exact and_self_iff)
        (fun v => by rw [u₁]; exact and_self_iff)
      simp only [Lynx.apply_eq, «intersection_idempotent:ensures/3»]
      simp [r₁, eq, Term.true]
      """

    law union_absorption(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_union(left, Descr.bare_intersection(left, right)), left),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_absorption:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_absorption:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union gl g₁ hm
      have eq := Nest.gd_eq_true g₂ gl (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁]; exact ⟨fun h => h.elim id And.left, Or.inl⟩)
        (fun v => by rw [u₂, u₁]; exact ⟨fun h => h.elim id And.left, Or.inl⟩)
      simp only [Lynx.apply_eq, «union_absorption:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law intersection_absorption(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_intersection(left, Descr.bare_union(left, right)), left),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_absorption:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_absorption:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_inter gl g₁ hm
      have eq := Nest.gd_eq_true g₂ gl (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁]; exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩)
        (fun v => by rw [u₂, u₁]; exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩)
      simp only [Lynx.apply_eq, «intersection_absorption:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law union_intersection_distributive(descr, left, right, depth, node),
      requires:
        arrows_gradual?(descr, {depth, node}) and arrows_gradual?(left, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_union(descr, Descr.bare_intersection(left, right)),
          Descr.bare_intersection(Descr.bare_union(descr, left), Descr.bare_union(descr, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_intersection_distributive:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_intersection_distributive:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gd : Nest.GD node d descr := Nest.arrows_gradual_ok hK requires.1.1
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1.2
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union gd g₁ hm
      obtain ⟨c₃, r₃, g₃, l₃, u₃⟩ := Nest.gd_union gd gl hm
      obtain ⟨c₄, r₄, g₄, l₄, u₄⟩ := Nest.gd_union gd gr hm
      obtain ⟨c₅, r₅, g₅, l₅, u₅⟩ := Nest.gd_inter g₃ g₄ hm
      have eq := Nest.gd_eq_true g₂ g₅ (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁, l₅, l₃, l₄]; exact or_and_left)
        (fun v => by rw [u₂, u₁, u₅, u₃, u₄]; exact or_and_left)
      simp only [Lynx.apply_eq, «union_intersection_distributive:ensures/5»]
      simp [r₁, r₂, r₃, r₄, r₅, eq, Term.true]
      """

    law subtype_union(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(left, right) == Descr.equal?(Descr.bare_union(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «subtype_union:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «subtype_union:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c, s, r₁, r₂, r₃⟩ := Nest.gd_sub_union gl gr hm
      simp only [Lynx.apply_eq, «subtype_union:ensures/4»]
      cases s <;> simp [r₁, r₂, r₃, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law subtype_intersection(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(left, right) == Descr.equal?(Descr.bare_intersection(left, right), left),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «subtype_intersection:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «subtype_intersection:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c, s, r₁, r₂, r₃⟩ := Nest.gd_sub_inter gl gr hm
      simp only [Lynx.apply_eq, «subtype_intersection:ensures/4»]
      cases s <;> simp [r₁, r₂, r₃, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law subtype_difference(left, right, depth, node),
      requires: arrows_static?(left, {depth, node}) and arrows_static?(right, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(left, right) == Descr.empty?(Descr.bare_difference(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«subtype_difference:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dl := Nest.arrows_static_ok requires.1
      have dr := Nest.arrows_static_ok requires.2
      obtain ⟨c, s, r₁, r₂, r₃⟩ := Nest.next_sub_diff dl dr hm
      simp only [Lynx.apply_eq, «subtype_difference:ensures/4»]
      cases s <;> simp [r₁, r₂, r₃, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law difference_partition(left, right, depth, node),
      requires: arrows_static?(left, {depth, node}) and arrows_static?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_union(Descr.bare_difference(left, right), Descr.bare_intersection(left, right)),
          left
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«difference_partition:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dl := Nest.arrows_static_ok requires.1
      have dr := Nest.arrows_static_ok requires.2
      have ef := Nest.ef_next node d
      obtain ⟨c₁, d₁, r₁, s₁, -⟩ := ef.diff dl dr
      obtain ⟨c₂, d₂, r₂, s₂, -⟩ := ef.inter dl dr
      obtain ⟨c₃, d₃, r₃, s₃, -⟩ := ef.union d₁ d₂
      have eq := Nest.next_eq_true d₃ dl hm fun v => by
        rw [s₃, s₁, s₂]
        exact ⟨fun h => h.elim And.left And.left, fun h => (Classical.em _).elim (fun h' => Or.inr ⟨h, h'⟩)
          fun h' => Or.inl ⟨h, h'⟩⟩
      simp only [Lynx.apply_eq, «difference_partition:ensures/4»]
      simp [r₁ _ hm, r₂ _ (by omega), r₃ _ hm, eq, Term.true]
      """

    law difference_disjoint(left, right, depth, node),
      requires: arrows_static?(left, {depth, node}) and arrows_static?(right, {depth, node}) and depth?(depth),
      expects: Descr.disjoint?(Descr.bare_difference(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«difference_disjoint:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dl := Nest.arrows_static_ok requires.1
      have dr := Nest.arrows_static_ok requires.2
      obtain ⟨c, dc, run, sem, -⟩ := (Nest.ef_next node d).diff dl dr
      have disj := Nest.next_disj dc dr hm
      rw [Nest.bp_true.mpr fun v h₁ h₂ => ((sem v).mp h₁).2 h₂] at disj
      simp only [Lynx.apply_eq, «difference_disjoint:ensures/4»]
      simp [run _ hm, disj, Term.true]
      """

    law negation_involutive(descr, depth, node),
      requires: arrows_static?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_negation(Descr.bare_negation(descr)), descr),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«negation_involutive:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dd := Nest.arrows_static_ok requires
      obtain ⟨c₁, r₁, d₁, s₁⟩ := Nest.next_neg dd hm
      obtain ⟨c₂, r₂, d₂, s₂⟩ := Nest.next_neg d₁ hm
      have eq := Nest.next_eq_true d₂ dd hm fun v => by rw [s₂, s₁]; exact Classical.not_not
      simp only [Lynx.apply_eq, «negation_involutive:ensures/3»]
      simp [r₁, r₂, eq, Term.true]
      """

    law tuple_fetch_sound(tuple, index, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and
          match?({false, _}, Descr.tuple_fetch(tuple, index)),
      expects:
        Descr.subtype?(
          tuple,
          Descr.open_tuple(:lists.duplicate(index, Descr.term()) ++ [elem(Descr.tuple_fetch(tuple, index), 1)])
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_fetch_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_fetch_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨hs, -⟩, hi⟩, hf⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      by_cases neg : z < 0
      · rw [Nest.fetch_neg _ _ neg] at hf; simp at hf
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, only, long, s₁, -⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      have hl : ∀ x ∈ List.replicate i (.atom "term") ++ [e], (Nest.level node d).E x := by
        intro x mx
        rcases List.mem_append.mp mx with mx | mx
        · rw [List.eq_of_mem_replicate mx]; exact (Nest.level node d).ef.term
        · simp at mx; subst mx; exact he
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate i (.atom "term") ++ [e])
        fun x mx => (Nest.level node d).ef.static (hl x mx)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) _ from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (only.1 v hv)
        rw [hw X] at hv
        rw [hw, Nest.tt_open_at he i k]
        have lw := long w hv
        have split : w = w.take i ++ w[i] :: w.drop (i + 1) := by simp
        refine ⟨w.take i, w[i], w.drop (i + 1), split, List.length_take_of_le (Nat.le_of_lt lw),
          s₁ (w.take i) w[i] (w.drop (i + 1)) (List.length_take_of_le (Nat.le_of_lt lw)) ?_⟩
        rw [← split]; exact hv)] at sub
      simp only [Lynx.apply_eq, «tuple_fetch_sound:ensures/4»]
      simp only [Elixir.Module.Types.Descr.«term/0», dup_nat, run, Lynx.Except.ok_bind]
      simp [Erlang.erlang.«element/2»]
      rw [append_list, Lynx.Except.ok_bind, rot, Lynx.Except.ok_bind, sub]
      rfl
      """

    law tuple_fetch_least(tuple, index, element, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(element, {depth, node}) and depth?(depth) and
          is_integer(index) and match?({false, _}, Descr.tuple_fetch(tuple, index)) and
          Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index, Descr.term()) ++ [element])),
      expects: Descr.subtype?(elem(Descr.tuple_fetch(tuple, index), 1), element),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the element `d`, so the proofs run from the bound of level `d + 1`
      -- on, and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_fetch_least:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_fetch_least:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hf⟩, hsub⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have del : (Nest.level node (d + 1)).E element := Or.inl (Nest.arrows_static_ok hel)
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      by_cases neg : z < 0
      · rw [Nest.fetch_neg _ _ neg] at hf; simp at hf
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, -, -, -, s₂⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      have hl : ∀ x ∈ List.replicate i (.atom "term") ++ [element], (Nest.level node (d + 1)).E x := by
        intro x mx
        rcases List.mem_append.mp mx with mx | mx
        · rw [List.eq_of_mem_replicate mx]; exact (Nest.level node (d + 1)).ef.term
        · simp at mx; subst mx; exact del
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate i (.atom "term") ++ [element])
        fun x mx => (Nest.level node (d + 1)).ef.static (hl x mx)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, dup_nat, Lynx.Except.ok_bind] at hsub
      rw [append_list, Lynx.Except.ok_bind, rot, Lynx.Except.ok_bind, sub, Except.ok.injEq] at hsub
      have incl := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have sem : ∀ y, (Nest.level node (d + 1)).den e y → (Nest.level node (d + 1)).den element y := by
        intro y hy
        obtain ⟨v₁, v₂, len, hw⟩ := s₂ y hy
        have := incl _ ((Nest.denD_tpt _).mpr hw)
        rw [Nest.denD_tpt, Nest.tt_open_at del i k] at this
        obtain ⟨w₁, y', w₂, ew, lw, hy'⟩ := this
        obtain ⟨-, e₂⟩ := List.append_inj ew (by omega)
        simp only [List.cons.injEq] at e₂
        rw [e₂.1]; exact hy'
      simp only [Lynx.apply_eq, «tuple_fetch_least:ensures/5»]
      simp [run, Erlang.erlang.«element/2», (Nest.level node (d + 1)).ef.subc he del sem (δ + 100) (by rw [Nest.level_K]; omega),
        Lynx.Term.true]
      """

    law tuple_fetch_badindex(tuple, index, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and index >= 0 and
          Descr.subtype?(tuple, Descr.tuple()) and not Descr.empty?(tuple),
      expects:
        (Descr.tuple_fetch(tuple, index) == :badindex) ==
          not Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term()))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_fetch_badindex:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_fetch_badindex:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨⟨hs, -⟩, hi⟩, hnn⟩, htup⟩, hne⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := by
        refine ⟨z.toNat, ?_⟩
        by_cases neg : z < 0
        · simp [Erlang.erlang.«>=/2», Int.isGE_compare, neg] at hnn
        · omega
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.tupleTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«tuple/0» =
        .ok (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT] at htup
      rw [Except.ok.injEq] at htup
      have onlyT := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) htup)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.tupleTop_den Nest.bitPt).mp (onlyT Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node d, Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.TOnly node d X := by
        refine ⟨fun v hv => (Nest.tupleTop_den v).mp (onlyT v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_tuple v ((Nest.tupleTop_den v).mp (onlyT v hv))
        exact ⟨w, (hw X).mp hv⟩
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate (i + 1) (.atom "term"))
        fun x mx => by rw [List.eq_of_mem_replicate mx]; exact Or.inl rfl
      have hl : ∀ x ∈ List.replicate (i + 1) (.atom "term"), (Nest.level node d).E x := by
        intro x mx; rw [List.eq_of_mem_replicate mx]; exact (Nest.level node d).ef.term
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      have subIff : Nest.SubN node d (.map X)
          (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Lynx.Term.list (List.replicate (i + 1) (.atom "term"))])]) ↔ ∀ w, Nest.TT node d X w → i + 1 ≤ w.length := by
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_tpt w).mpr hw)
          rwa [Nest.denD_tpt, Nest.tt_open] at this
        · intro h v hv
          obtain ⟨w, hw⟩ := Nest.pt_tuple v (only.1 v hv)
          rw [hw X] at hv
          rw [hw, Nest.tt_open]
          exact h w hv
      have dup' : Erlang.lists.«duplicate/2» (.integer ((i : Int) + 1)) (.atom "term") =
          .ok (Lynx.Term.list (List.replicate (i + 1) (.atom "term"))) := by simpa using dup_nat (.atom "term") (i + 1)
      obtain ⟨res, run, ⟨-, nonly⟩ | ⟨rfl, -, w, hw, len⟩ | ⟨e, rfl, -, -, long, -, -⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · exact absurd only nonly
      · rw [Nest.bp_false.mpr fun h => by have := (subIff.mp h) w hw; omega] at sub
        simp only [Lynx.apply_eq, «tuple_fetch_badindex:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      · rw [Nest.bp_true.mpr (subIff.mpr fun w hw => long w hw)] at sub
        simp only [Lynx.apply_eq, «tuple_fetch_badindex:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law map_fetch_key_sound(map, key, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and is_atom(key) and
          match?({false, _}, Descr.map_fetch_key(map, key)),
      expects: Descr.subtype?(map, Descr.open_map([{key, {elem(Descr.map_fetch_key(map, key), 1), false}}])),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_fetch_key_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_fetch_key_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨hs, -⟩, hi⟩, hf⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_map_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, only, s₁, -⟩⟩ :=
        Nest.fetch_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node d).ef.static he) (δ + 99)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req he) key))
        (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) _ from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_map v (only.1 v hv)
        rw [hw X] at hv
        rw [hw, Nest.mt_open_at he a k]
        exact s₁ w hv)] at sub
      simp only [Lynx.apply_eq, «map_fetch_key_sound:ensures/4»]
      simp [run, Erlang.erlang.«element/2», rom, sub, Lynx.Term.true]
      """

    law map_fetch_key_least(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and match?({false, _}, Descr.map_fetch_key(map, key)) and
          Descr.subtype?(map, Descr.open_map([{key, {value, false}}])),
      expects: Descr.subtype?(elem(Descr.map_fetch_key(map, key), 1), value),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_fetch_key_least:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_fetch_key_least:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hf⟩, hsub⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have del : (Nest.level node (d + 1)).E value := Or.inl (Nest.arrows_static_ok hel)
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_map_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, -, -, s₂⟩⟩ :=
        Nest.fetch_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node (d + 1)).ef.static del) (δ + 99)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req del) key))
        (m := δ + 100) (by omega)
      rw [rom, Lynx.Except.ok_bind, sub, Except.ok.injEq] at hsub
      have incl := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have sem : ∀ x, (Nest.level node (d + 1)).den e x → (Nest.level node (d + 1)).den value x := by
        intro x hx
        obtain ⟨w, hw, wa⟩ := s₂ x hx
        have := incl _ ((Nest.denD_mpt w).mpr hw)
        rw [Nest.denD_mpt, Nest.mt_open_at del a k] at this
        obtain ⟨x', wa', hx'⟩ := this
        rw [wa] at wa'
        cases wa'
        exact hx'
      simp only [Lynx.apply_eq, «map_fetch_key_least:ensures/5»]
      simp [run, Erlang.erlang.«element/2», (Nest.level node (d + 1)).ef.subc he del sem (δ + 100) (by rw [Nest.level_K]; omega),
        Lynx.Term.true]
      """

    law map_fetch_key_badkey(map, key, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and is_atom(key) and
          Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map),
      expects:
        (Descr.map_fetch_key(map, key) == :badkey) ==
          not Descr.subtype?(map, Descr.open_map([{key, {Descr.term(), false}}])),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_fetch_key_badkey:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_fetch_key_badkey:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hi⟩, hmap⟩, hne⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«open_map/0» =
        .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT,
        Except.ok.injEq] at hmap
      have onlyM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hmap)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.mapTop_den Nest.bitPt).mp (onlyM Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node d, Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.MOnly node d X := by
        refine ⟨fun v hv => (Nest.mapTop_den v).mp (onlyM v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_map v ((Nest.mapTop_den v).mp (onlyM v hv))
        exact ⟨w, (hw X).mp hv⟩
      have hterm : (Nest.level node d).E (.atom "term") := (Nest.level node d).ef.term
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node d).ef.static hterm) (δ + 99)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req hterm) key))
        (m := δ + 100) (by omega)
      have subIff : Nest.SubN node d (.map X)
          (.map [(.atom "map", .tuple #[.integer k, .atom "open",
            fieldsTerm [(.atom a, .tuple #[.atom "term", .atom "false"])]])]) ↔
          ∀ w, Nest.MT node d X w → w (.atom a) ≠ none := by
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_mpt w).mpr hw)
          rw [Nest.denD_mpt, Nest.mt_open_at hterm a k] at this
          obtain ⟨x, wa, -⟩ := this
          rw [wa]; simp
        · intro h v hv
          obtain ⟨w, hw⟩ := Nest.pt_map v (only.1 v hv)
          rw [hw X] at hv
          rw [hw, Nest.mt_open_at hterm a k]
          cases wa : w (.atom a) with
          | none => exact absurd wa (h w hv)
          | some x => exact ⟨x, rfl, (Nest.level node d).ef.den_term x⟩
      obtain ⟨res, run, ⟨-, nonly⟩ | ⟨rfl, -, w, hw, wa⟩ | ⟨e, rfl, -, -, s₁, -⟩⟩ :=
        Nest.fetch_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      · exact absurd only nonly
      · rw [Nest.bp_false.mpr fun h => (subIff.mp h) w hw wa] at sub
        simp only [Lynx.apply_eq, «map_fetch_key_badkey:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», rom, sub, Erlang.erlang.«not/1», Lynx.Term.true]
      · rw [Nest.bp_true.mpr (subIff.mpr fun w hw => by obtain ⟨x, wa, -⟩ := s₁ w hw; rw [wa]; simp)] at sub
        simp only [Lynx.apply_eq, «map_fetch_key_badkey:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», rom, sub, Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law tuple_insert_fetch(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and not Descr.empty?(value) and is_map(Descr.tuple_insert_at(tuple, index, value)),
      expects:
        match?({false, _}, Descr.tuple_fetch(Descr.tuple_insert_at(tuple, index, value), index)) and
          Descr.equal?(elem(Descr.tuple_fetch(Descr.tuple_insert_at(tuple, index, value), index), 1), value),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_fetch:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_fetch:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.insert_at_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · rw [Nest.insert_at_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rw [Nest.insert_at_static _ _ _ sx] at hmap
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
          (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, longX, dY, onlyY, ttY⟩ := Nest.insert_tuple (Or.inr ⟨X, rfl, sX⟩) del i hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The inserted type holds a tuple.
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have lw := longX w₀ hw₀
      have hY : Nest.TT node (d + 1) Y (w₀.take i ++ y₀ :: w₀.drop i) :=
        (ttY _).mpr ⟨w₀.take i, y₀, w₀.drop i, rfl, by simp; omega, hy₀, by simpa using hw₀⟩
      obtain ⟨res, fetch, ⟨rfl, nonly⟩ | ⟨rfl, -, w, hw, len⟩ | ⟨e, rfl, he, -, -, s₁, s₂⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d + 1) dY i hm
      · exact absurd ⟨onlyY, _, hY⟩ nonly
      · obtain ⟨w₁, y, w₂, rfl, l₁, -, -⟩ := (ttY w).mp hw
        simp at len; omega
      have sem : ∀ y, (Nest.level node (d + 1)).den e y ↔ (Nest.level node (d + 1)).den value y := by
        intro y
        constructor
        · intro hy
          obtain ⟨v₁, v₂, len, h⟩ := s₂ y hy
          obtain ⟨w₁, y', w₂, ew, l₁, hy', -⟩ := (ttY _).mp h
          obtain ⟨-, e₂⟩ := List.append_inj ew (by omega)
          simp only [List.cons.injEq] at e₂
          rw [e₂.1]; exact hy'
        · intro hy
          exact s₁ (w₀.take i) y (w₀.drop i) (by simp; omega)
            ((ttY _).mpr ⟨w₀.take i, y, w₀.drop i, rfl, by simp; omega, hy, by simpa using hw₀⟩)
      simp only [Lynx.apply_eq, «tuple_insert_fetch:ensures/5», Nest.insert_at_static _ _ _ sx, run, Lynx.Except.ok_bind,
        fetch]
      simp [Erlang.erlang.«element/2», Nest.elem_equal (Nest.level node (d + 1)).ef he del sem (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      """

    law tuple_insert_delete(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and not Descr.empty?(value) and is_map(Descr.tuple_insert_at(tuple, index, value)),
      expects: Descr.equal?(Descr.tuple_delete_at(Descr.tuple_insert_at(tuple, index, value), index), tuple),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_delete:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_delete:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.insert_at_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · rw [Nest.insert_at_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rw [Nest.insert_at_static _ _ _ sx] at hmap
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
          (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, longX, dY, onlyY, ttY⟩ := Nest.insert_tuple (Or.inr ⟨X, rfl, sX⟩) del i hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The inserted type holds only tuples, longer than the index.
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have lw := longX w₀ hw₀
      have hY : Nest.TT node (d + 1) Y (w₀.take i ++ y₀ :: w₀.drop i) :=
        (ttY _).mpr ⟨w₀.take i, y₀, w₀.drop i, rfl, by simp; omega, hy₀, by simpa using hw₀⟩
      have longY : ∀ w, Nest.TT node (d + 1) Y w → i < w.length := fun w hw => by
        obtain ⟨w₁, y, w₂, rfl, l₁, -, -⟩ := (ttY w).mp hw
        simp; omega
      obtain ⟨r, del, tr, sr⟩ := Nest.delete_tuple dY ⟨onlyY, _, hY⟩ i longY hm
      have dZ : Nest.DE (Nest.level node (d + 1)).E (.map [(.atom "tuple", r)]) :=
        Or.inr ⟨_, rfl, Nest.descrC_put Nest.descrC_nil tr⟩
      have same : ∀ v : Nest.PN node (d + 1), Nest.denD (.map [(.atom "tuple", r)]) v ↔ Nest.denD (.map X) v := by
        intro v
        by_cases h : v.1.1 = "tuple"
        · obtain ⟨w, hw⟩ := Nest.pt_tuple v h
          rw [hw, hw]
          have ttZ : Nest.TT node (d + 1) [(.atom "tuple", r)] w ↔
              Nest.denTF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den r w = Bool.true := by
            simp [Nest.TT, Lynx.Term.mapLookup]
          rw [ttZ, sr]
          constructor
          · rintro ⟨v₁, y, v₂, rfl, l₁, h⟩
            obtain ⟨w₁, y', w₂, e, l₁', -, hx⟩ := (ttY _).mp h
            obtain ⟨e₁, e₂⟩ := List.append_inj e (by omega)
            simp only [List.cons.injEq] at e₂
            rw [e₁, e₂.2]; exact hx
          · intro h
            have lw := longX w h
            refine ⟨w.take i, y₀, w.drop i, by simp, by simp; omega, (ttY _).mpr ⟨w.take i, y₀, w.drop i, rfl, by simp; omega,
              hy₀, by simpa using h⟩⟩
        · constructor
          · intro hv
            rw [Nest.denD_map] at hv
            simp [Lynx.Term.mapLookup, h, Elixir.STTDescrProofsTest.dn_none] at hv
          · intro hv
            exact absurd (onlyX.1 v hv) h
      simp only [Lynx.apply_eq, «tuple_insert_delete:ensures/5», Nest.insert_at_static _ _ _ sx, run, Lynx.Except.ok_bind, del]
      rw [Nest.next_eq_true dZ (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) same]
      rfl
      """
    law map_get_fetch_key(map, key, depth, node),
      requires: arrows_static?(map, {depth, node}) and depth?(depth) and is_atom(key),
      expects:
        (case {Descr.map_get(map, Descr.atom([key])), Descr.map_fetch_key(map, key)} do
           {{:ok, got}, {_, fetched}} -> Descr.equal?(got, fetched)
           {{:ok, _}, :badkey} -> not Descr.subtype?(map, Descr.open_map([{key, {Descr.term(), false}}]))
           {:error, :badkey} -> true
           {:badmap, :badmap} -> true
           _ -> false
         end),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      simp only [«map_get_fetch_key:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨hs, hd⟩, hi⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d) [.atom a] [] (by simp) (by simp)
        (m := δ + 100) (by omega)
      have rA : Elixir.Module.Types.Descr.«atom/1» (Lynx.Term.list [.atom a]) = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«atom/1» (Lynx.Term.list [.atom a]) with
        | error e => simp [«key_type/2», Lynx.Term.list, h] at rY
        | ok r =>
          simp only [Lynx.Term.list] at h
          simp [«key_type/2», «kinds_type/2», Lynx.Term.list, h] at rY
          rw [rY]
      have keyA : ∀ κ, Nest.SplitKey rs neg ds κ ↔ κ = .atom a := fun κ => by
        rw [sk]
        cases κ with
        | atom s => simp [Nest.KeysOf]
        | dom k i => simp [Nest.KeysOf]
      have hterm : (Nest.level node d).E (.atom "term") := (Nest.level node d).ef.term
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node d).ef.static hterm) (δ + 99)
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · simp only [Lynx.apply_eq, «map_get_fetch_key:ensures/4»]
        simp [rA, Nest.get_map_term, Nest.fetch_map_term, Lynx.Term.true]
      obtain ⟨gres, grun, ⟨rfl, gnon⟩ | ⟨rfl, gonly, gnone⟩ | ⟨T, rfl, hT, gonly, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      all_goals obtain ⟨fres, frun, ⟨rfl, fnon⟩ | ⟨rfl, fonly, w₀, hw₀, wa⟩ | ⟨e, rfl, he, fonly, s₁, s₂⟩⟩ :=
        Nest.fetch_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      all_goals simp only [Lynx.apply_eq, «map_get_fetch_key:ensures/4»]
      · simp [rA, grun, frun, Lynx.Term.true]
      · exact absurd fonly gnon
      · exact absurd fonly gnon
      · exact absurd gonly fnon
      · simp [rA, grun, frun, Lynx.Term.true]
      · obtain ⟨w, hw⟩ := gonly.2
        obtain ⟨x, hx, -⟩ := s₁ w hw
        rw [gnone w hw _ ((keyA _).mpr rfl)] at hx; cases hx
      · exact absurd gonly fnon
      · -- An optional key: some map lacks it.
        have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩)
          (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req hterm) key)) (m := δ + 100) (by omega)
        rw [Nest.bp_false.mpr fun h => by
          have := h _ ((Nest.denD_mpt w₀).mpr hw₀)
          rw [Nest.denD_mpt, Nest.mt_open_at hterm a k] at this
          obtain ⟨x, wa', -⟩ := this
          rw [wa] at wa'; cases wa'] at sub
        simp [rA, grun, frun, Elixir.Module.Types.Descr.«term/0», rom, sub, Erlang.erlang.«not/1», Lynx.Term.true]
      · have sem : ∀ x, (Nest.level node d).den T x ↔ (Nest.level node d).den e x := fun x => by
          rw [sT]
          constructor
          · rintro ⟨w, hw, κ, hκ, wκ⟩
            obtain rfl := (keyA κ).mp hκ
            obtain ⟨x', wa, hx'⟩ := s₁ w hw
            rw [wκ] at wa; cases wa; exact hx'
          · intro hx
            obtain ⟨w, hw, wa⟩ := s₂ x hx
            exact ⟨w, hw, .atom a, (keyA _).mpr rfl, wa⟩
        simp [rA, grun, frun, Nest.elem_equal (Nest.level node d).ef hT he sem (m := δ + 100)
          (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      """

    law map_get_sound(map, atoms, kinds, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and keys?(atoms, kinds) and
          match?({:ok, _}, Descr.map_get(map, key_type(atoms, kinds))),
      expects: Descr.subtype?(map, keys_hold(atoms, kinds, elem(Descr.map_get(map, key_type(atoms, kinds)), 1))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_get_sound:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_get_sound:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨hs, -⟩, hk⟩, hg⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d) as ks ha hks (m := δ + 100) (by omega)
      rw [rY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.get_map_term] at hg; simp at hg
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨T, rfl, hT, only, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      obtain ⟨H, rH, dH, -, sH⟩ := Nest.keys_hold_run (t := node) (n := d) as ks ha hks
        ((Nest.level node d).ef.static hT) hT (m := δ + 100) (by omega)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dH (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) H from fun p hp => by
        obtain ⟨w, hw⟩ := Nest.pt_map p (only.1 p hp)
        rw [sH p w hw]
        intro κ hκ
        cases e : w κ with
        | none => exact Or.inl rfl
        | some x => exact Or.inr ⟨x, rfl, (sT x).mpr ⟨w, (hw X).mp hp, κ, (sk κ).mpr hκ, e⟩⟩)] at sub
      simp only [Lynx.apply_eq, «map_get_sound:ensures/5»]
      simp [rY, run, Erlang.erlang.«element/2», rH, sub, Lynx.Term.true]
      """

    law map_get_least(map, atoms, kinds, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          keys?(atoms, kinds) and match?({:ok, _}, Descr.map_get(map, key_type(atoms, kinds))) and
          Descr.subtype?(map, keys_hold(atoms, kinds, value)),
      expects: Descr.subtype?(elem(Descr.map_get(map, key_type(atoms, kinds)), 1), value),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_get_least:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_get_least:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hs, hel⟩, -⟩, hk⟩, hg⟩, hsub⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d + 1) as ks ha hks (m := δ + 100)
        (by omega)
      rw [rY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.get_map_term] at hg; simp at hg
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨T, rfl, hT, only, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      obtain ⟨H, rH, dH, -, sH⟩ := Nest.keys_hold_run (t := node) (n := d + 1) as ks ha hks
        ((Nest.level node (d + 1)).ef.static del) del (m := δ + 100) (by omega)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dH (m := δ + 100) (by omega)
      rw [rH, Lynx.Except.ok_bind, sub, Except.ok.injEq] at hsub
      have incl := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have sem : ∀ x, (Nest.level node (d + 1)).den T x → (Nest.level node (d + 1)).den value x := by
        intro x hx
        obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        have := (sH _ w (Nest.mapOf_mpt w)).mp (incl _ ((Nest.denD_mpt w).mpr hw)) κ ((sk κ).mp hκ)
        rw [wκ] at this
        rcases this with h | ⟨x', e, h⟩
        · cases h
        · cases e; exact h
      simp only [Lynx.apply_eq, «map_get_least:ensures/6»]
      simp [rY, run, Erlang.erlang.«element/2»,
        (Nest.level node (d + 1)).ef.subc hT del sem (δ + 100) (by rw [Nest.level_K]; omega), Lynx.Term.true]
      """

    law map_get_error(map, atoms, kinds, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and keys?(atoms, kinds) and
          Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map),
      expects:
        (Descr.map_get(map, key_type(atoms, kinds)) == :error) ==
          Descr.subtype?(map, keys_hold(atoms, kinds, Descr.none())),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_get_error:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_get_error:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hk⟩, hmap⟩, hne⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«open_map/0» =
        .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT,
        Except.ok.injEq] at hmap
      have onlyM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hmap)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.mapTop_den Nest.bitPt).mp (onlyM Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node d, Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.MOnly node d X := by
        refine ⟨fun v hv => (Nest.mapTop_den v).mp (onlyM v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_map v ((Nest.mapTop_den v).mp (onlyM v hv))
        exact ⟨w, (hw X).mp hv⟩
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d) as ks ha hks (m := δ + 100) (by omega)
      have hn := (Nest.level node d).ef.none
      obtain ⟨H, rH, dH, -, sH⟩ := Nest.keys_hold_run (t := node) (n := d) as ks ha hks
        ((Nest.level node d).ef.static hn) hn (m := δ + 100) (by omega)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dH (m := δ + 100) (by omega)
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨rfl, -, none⟩ | ⟨T, rfl, -, -, ⟨x, hx⟩, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · exact absurd only nonly
      · rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) H from fun p hp => by
          obtain ⟨w, hw⟩ := Nest.pt_map p (only.1 p hp)
          rw [sH p w hw]
          exact fun κ hκ => Or.inl (none w ((hw X).mp hp) κ ((sk κ).mpr hκ)))] at sub
        simp only [Lynx.apply_eq, «map_get_error:ensures/5»]
        simp [rY, run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«none/0», rH, sub, Lynx.Term.true]
      · obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        rw [Nest.bp_false.mpr fun h => by
          have := (sH _ w (Nest.mapOf_mpt w)).mp (h _ ((Nest.denD_mpt w).mpr hw)) κ ((sk κ).mp hκ)
          rw [wκ] at this
          rcases this with h' | ⟨x', e, h'⟩
          · cases h'
          · exact (Nest.level node d).ef.den_none x' h'] at sub
        simp only [Lynx.apply_eq, «map_get_error:ensures/5»]
        simp [rY, run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«none/0», rH, sub, Lynx.Term.true]
      """

    law map_get_badmap(map, atoms, kinds, depth, node),
      requires: arrows_static?(map, {depth, node}) and depth?(depth) and keys?(atoms, kinds),
      expects:
        (Descr.map_get(map, key_type(atoms, kinds)) == :badmap) ==
          not (Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      simp only [«map_get_badmap:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨hs, hd⟩, hk⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, -⟩ := Nest.key_split (t := node) (n := d) as ks ha hks (m := δ + 100) (by omega)
      have dt := Nest.arrows_static_ok hs
      have top : Elixir.Module.Types.Descr.«open_map/0» =
          .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) := rfl
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.bp_false.mpr fun h => by
          have := (Nest.mapTop_den Nest.bitPt).mp (h Nest.bitPt (Nest.denD_term _))
          simp [Nest.bitPt] at this] at sT
        simp only [Lynx.apply_eq, «map_get_badmap:ensures/5»]
        simp [rY, Nest.get_map_term, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨rfl, only, -⟩ | ⟨T, rfl, -, only, -⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · rw [Nest.monly_iff] at nonly
        simp only [Lynx.apply_eq, «map_get_badmap:ensures/5»]
        by_cases h : Nest.SubN node d (.map X) (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
        · rw [Nest.bp_true.mpr h] at sT
          rw [Nest.bp_true.mpr (Classical.not_not.mp fun h' => nonly ⟨h, h'⟩)] at ne
          simp [rY, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
        · rw [Nest.bp_false.mpr h] at sT
          simp [rY, run, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      all_goals
        obtain ⟨h₁, h₂⟩ := Nest.monly_iff.mp only
        rw [Nest.bp_true.mpr h₁] at sT
        rw [Nest.bp_false.mpr h₂] at ne
        simp only [Lynx.apply_eq, «map_get_badmap:ensures/5»]
        simp [rY, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
      """
    law map_to_list_atom(map, key, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and is_atom(key) and
          match?({:ok, _}, Descr.map_to_list(map)) and match?({:ok, _}, Descr.map_get(map, Descr.atom([key]))),
      expects:
        Descr.subtype?(
          Descr.non_empty_list(Descr.tuple([Descr.atom([key]), elem(Descr.map_get(map, Descr.atom([key])), 1)])),
          elem(Descr.map_to_list(map), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_atom:requires/4», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_atom:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hi⟩, hl⟩, hg⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d + 1) [.atom a] [] (by simp) (by simp)
        (m := δ + 100) (by rw [Nest.level_K]; omega)
      have eY : Nest.atomT a = .map Y := by
        have := Nest.atom_one a
        simp only [Lynx.Term.list] at this
        simpa [«key_type/2», «kinds_type/2», Lynx.Term.list, this] using rY
      rw [Nest.atom_one, eY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨T, rfl, hT, -, ⟨x₀, hx₀⟩, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (by omega) rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      have keyA : ∀ κ, Nest.SplitKey rs neg ds κ ↔ κ = .atom a := fun κ => by
        rw [sk]
        cases κ with
        | atom s => simp [Nest.KeysOf]
        | dom k i => simp [Nest.KeysOf]
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨-, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      obtain ⟨P, rP, dP, sP⟩ := Nest.pair_run (t := node) (n := d + 1) (Or.inl (Nest.atomT_de a)) hT (Nest.atomT_static a)
        ((Nest.level node (d + 1)).ef.static hT)
      have incl : ∀ y : Nest.PN node (d + 1), Nest.denD P y → Nest.denD inner y := by
        intro y hy
        obtain ⟨w', hw', k, x, rfl, hk, hx⟩ := (sP y).mp hy
        obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        obtain rfl := (keyA κ).mp hκ
        exact (Nest.same_tuple dI hw').mpr (sI.1 w ((mt w).mp hw) a x wκ k hk)
      obtain ⟨k', rlist, rnel⟩ := Nest.list_run ((Nest.ef_next node (d + 1)).static dP) (δ + 100)
      have one := Nest.atom_one a
      simp only [Lynx.Term.list] at one
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, -⟩
      · exfalso
        have k₀ : (Nest.level node (d + 1)).den (Nest.atomT a) (Nest.aPt (t := node) (n := d) (.atom a)) :=
          (Nest.den_succ (Nest.atomT_de a) _).mpr ((Nest.atomT_den a _).mpr ⟨rfl, rfl⟩)
        exact emp _ (incl _ ((sP _).mpr (Nest.pairPt_tpt k₀ hx₀)))
      have sub := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de Bool.false k' dP) (Nest.lTy_de nil k dI)
        (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (Nest.nel_sub dP dI incl nil k k')] at sub
      simp only [Lynx.apply_eq, «map_to_list_atom:ensures/4»]
      rw [eY] at rP
      have e : Nest.lTy Bool.false k' P = .map [(.atom "list", .tuple #[.integer k', P, Nest.nilT])] := rfl
      rw [e] at sub
      simp [one, eY, run, Erlang.erlang.«element/2», rP, rnel, Nest.tolist_one, runL, sub, Lynx.Term.true]
      """

    law map_to_list_kind(map, kind, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and keys?([], [kind]) and kind != :atom and
          match?({:ok, _}, Descr.map_to_list(map)) and match?({:ok, _}, Descr.map_get(map, key_type([], [kind]))),
      expects:
        Descr.subtype?(
          Descr.non_empty_list(Descr.tuple([key_type([], [kind]), elem(Descr.map_get(map, key_type([], [kind])), 1)])),
          elem(Descr.map_to_list(map), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_kind:requires/4», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_kind:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hs, -⟩, hk⟩, hne⟩, hl⟩, hg⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨as, ks, eas, eks, -, hks⟩ := Nest.keys_ok hk
      have eas := list_inj (l := []) eas
      subst eas
      have eks := list_inj eks
      subst eks
      obtain ⟨kd, mkd, rfl⟩ := hks _ List.mem_cons_self
      have nkd : kd ≠ "atom" := fun e => by subst e; simp [Erlang.erlang.«/=/2»] at hne
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d + 1) [] [.atom kd] (by simp)
        (by simpa using mkd) (m := δ + 100) (by rw [Nest.level_K]; omega)
      obtain ⟨Y₁, rY₁, hY⟩ := Nest.key_type_run (t := node) (n := d) [] [.atom kd] (by simp) (by simpa using mkd)
        (m := δ + 100) (by rw [Nest.level_K]; omega)
      rw [rY] at rY₁
      cases rY₁
      have nil : Lynx.Term.nil = Lynx.Term.list [] := rfl
      rw [← nil] at rY
      rw [rY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨T, rfl, hT, -, ⟨x₀, hx₀⟩, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (by omega) rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      have keyK : ∀ κ, Nest.SplitKey rs neg ds κ ↔ ∃ kk i, κ = .dom kk i ∧ Nest.domKind kk = kd := fun κ => by
        rw [sk]
        cases κ with
        | atom s => simp [Nest.KeysOf, Ne.symm nkd]
        | dom kk i => simp [Nest.KeysOf]
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨-, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      have kY : ∀ k : Nest.PN node d, Nest.denD (.map Y) k → Nest.ptKind k = kd := by
        intro k hk
        by_cases ka : k.1.1 = "atom"
        · have := (hY.atoms k.1.2.2.1).mp ((Nest.denD_atom_pt ka).mp hk)
          simp at this
          exact absurd this.symm nkd
        · simpa using hY.kinds k hk ka
      obtain ⟨P, rP, dP, sP⟩ := Nest.pair_run (t := node) (n := d + 1) (Or.inl hY.de) hT
        (Or.inr (Or.inl ⟨_, rfl, (Nest.de_map hY.de).static⟩)) ((Nest.level node (d + 1)).ef.static hT)
      have incl : ∀ y : Nest.PN node (d + 1), Nest.denD P y → Nest.denD inner y := by
        intro y hy
        obtain ⟨w', hw', k, x, rfl, hk, hx⟩ := (sP y).mp hy
        obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        obtain ⟨kk, i, rfl, hkk⟩ := (keyK κ).mp hκ
        exact (Nest.same_tuple dI hw').mpr (sI.2.1 w ((mt w).mp hw) kk i x wκ k
          (by rw [hkk]; exact kY _ ((Nest.den_succ hY.de _).mp hk)))
      obtain ⟨k', rlist, rnel⟩ := Nest.list_run ((Nest.ef_next node (d + 1)).static dP) (δ + 100)
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, -⟩
      · exfalso
        obtain ⟨v, hv, pv⟩ := hY.wit kd (by simp) nkd
        exact emp _ (incl _ ((sP _).mpr (Nest.pairPt_tpt ((Nest.den_succ hY.de v).mpr hv) hx₀)))
      have sub := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de Bool.false k' dP) (Nest.lTy_de nil k dI)
        (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (Nest.nel_sub dP dI incl nil k k')] at sub
      have e : Nest.lTy Bool.false k' P = .map [(.atom "list", .tuple #[.integer k', P, Nest.nilT])] := rfl
      rw [e] at sub
      simp only [Lynx.apply_eq, «map_to_list_kind:ensures/4»]
      simp [rY, run, Erlang.erlang.«element/2», rP, rnel, Nest.tolist_one, runL, sub, Lynx.Term.true]
      """

    law map_to_list_values(map, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and match?({:ok, _}, Descr.map_to_list(map)) and
          match?({:ok, _}, Descr.map_get(map, Descr.term())),
      expects:
        Descr.subtype?(
          elem(Descr.map_to_list(map), 1),
          Descr.list(Descr.tuple([Descr.term(), elem(Descr.map_get(map, Descr.term()), 1)]))
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_values:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_values:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨hs, -⟩, hl⟩, hg⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨only, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      -- The values of the pairs are values of the maps.
      have tm : Elixir.Module.Types.Descr.«term/0» = .ok (.atom "term") := rfl
      rw [tm, Lynx.Except.ok_bind] at hg
      obtain ⟨rs, neg, ds, rS, ok, allK⟩ := Nest.term_split (t := node) (n := d + 1) (m := δ + 99)
        (by rw [Nest.level_K]; omega)
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨T, rfl, hT, -, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (by omega) rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      obtain ⟨P, rP, dP, sP⟩ := Nest.pair_run (t := node) (n := d + 1) (Nest.level node (d + 1)).ef.term hT (Or.inl rfl)
        ((Nest.level node (d + 1)).ef.static hT)
      have incl : ∀ y : Nest.PN node (d + 1), Nest.denD inner y → Nest.denD P y := by
        intro y hy
        obtain ⟨w', hw', k, x, rfl, w, hw, κ, wκ⟩ := sI.2.2 y hy
        exact (sP y).mpr ⟨[k, x], hw', k, x, rfl, (Nest.level node (d + 1)).ef.den_term k,
          (sT x).mpr ⟨w, (mt w).mpr hw, κ, allK κ, wκ⟩⟩
      obtain ⟨k', rlist, -⟩ := Nest.list_run ((Nest.ef_next node (d + 1)).static dP) (δ + 100)
      have e : Elixir.Module.Types.Descr.«list/1» (D (δ + 100)) P = .ok (Nest.lTy Bool.true k' P) := rlist
      have dQ := Nest.lTy_de Bool.true k' dP
      rcases hL with ⟨rfl, -⟩ | ⟨nil, k, rfl, -⟩
      · have sub := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de dQ (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (Nest.nilT_sub_true dP k')] at sub
        simp only [Lynx.apply_eq, «map_to_list_values:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», tm, run, rP, e, sub, Lynx.Term.true]
      · have sub := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de nil k dI) dQ (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (Nest.lTy_mono dI dP incl (fun _ => rfl) k k')] at sub
        simp only [Lynx.apply_eq, «map_to_list_values:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», tm, run, rP, e, sub, Lynx.Term.true]
      """

    law map_to_list_empty(map, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and match?({:ok, _}, Descr.map_to_list(map)),
      expects:
        Descr.subtype?(elem(Descr.map_to_list(map), 1), Descr.empty_list()) ==
          Descr.subtype?(map, Descr.empty_map()),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_empty:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_empty:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨hs, -⟩, hl⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨only, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      -- Maps of the type are all empty exactly when it lists no pairs.
      have subE := Nest.next_sub (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) Nest.emptyMap_de (m := δ + 100) (by omega)
      have allE : Nest.SubN node (d + 1) (.map X) Nest.emptyMapT ↔ ∀ p : Nest.PN node (d + 1), ¬Nest.denD inner p := by
        rw [Nest.inner_empty_iff sI]
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_mpt w).mpr ((mt w).mpr hw))
          rwa [Nest.emptyMapT, Nest.denD_mpt, Nest.mt_emptyMap] at this
        · intro h q hq
          obtain ⟨w, hw⟩ := Nest.pt_map q (only.1 q hq)
          rw [Nest.emptyMapT, hw, Nest.mt_emptyMap]
          exact h w ((mt w).mp ((hw X).mp hq))
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, -⟩
      · have subL := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de Nest.nilT_de (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (show Nest.SubN node (d + 2) Nest.nilT Nest.nilT from fun q hq => hq)] at subL
        rw [Nest.bp_true.mpr (allE.mpr emp)] at subE
        simp only [Lynx.apply_eq, «map_to_list_empty:ensures/3»]
        have el : Elixir.Module.Types.Descr.«empty_list/0» = .ok Nest.nilT := rfl
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, subE, Erlang.erlang.«==/2»,
          Lynx.Term.true]
      · have subL := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de nil k dI) Nest.nilT_de (m := δ + 100) (by omega)
        have el : Elixir.Module.Types.Descr.«empty_list/0» = .ok Nest.nilT := rfl
        rw [Nest.bp_congr ((Nest.lTy_nil_sub dI nil k).trans allE.symm)] at subL
        simp only [Lynx.apply_eq, «map_to_list_empty:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, subE, Erlang.erlang.«==/2»,
          Lynx.Term.true]
      """

    law map_to_list_nil(map, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and match?({:ok, _}, Descr.map_to_list(map)),
      expects:
        Descr.subtype?(Descr.empty_list(), elem(Descr.map_to_list(map), 1)) ==
          not Descr.disjoint?(map, Descr.empty_map()),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_nil:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_nil:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨hs, -⟩, hl⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨only, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      -- Lists of the type hold the empty list exactly when the type holds the empty map.
      have dis := Nest.next_disj (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) Nest.emptyMap_de (m := δ + 100) (by omega)
      have holds : (¬∀ v : Nest.PN node (d + 1), Nest.denD (.map X) v → Nest.denD Nest.emptyMapT v → False) ↔
          Nest.MT node (d + 1) X Nest.wNone := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := Classical.not_forall.mp h
          obtain ⟨hx, he⟩ := Classical.not_imp.mp hv
          have he := Classical.not_imp.mp he |>.1
          obtain ⟨w, hw⟩ := Nest.pt_map v (only.1 v hx)
          rw [Nest.emptyMapT, hw, Nest.mt_emptyMap] at he
          subst he
          exact (hw X).mp hx
        · intro h h'
          exact h' _ ((Nest.denD_mpt _).mpr h) ((Nest.denD_mpt _).mpr ((Nest.mt_emptyMap _).mpr rfl))
      have el : Elixir.Module.Types.Descr.«empty_list/0» = .ok Nest.nilT := rfl
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, hnil⟩
      · have subL := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de Nest.nilT_de (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (show Nest.SubN node (d + 2) Nest.nilT Nest.nilT from fun q hq => hq)] at subL
        have e := (Nest.inner_empty_iff sI).mp emp
        obtain ⟨w, hw⟩ := only.2
        have hn : Nest.MT node (d + 1) X Nest.wNone := by rw [← e w ((mt w).mp hw)]; exact hw
        rw [Nest.bp_false.mpr (fun h => holds.mpr hn h)] at dis
        simp only [Lynx.apply_eq, «map_to_list_nil:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, dis, Erlang.erlang.«not/1»,
          Erlang.erlang.«==/2», Lynx.Term.true]
      · have subL := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de (Nest.lTy_de nil k dI) (m := δ + 100) (by omega)
        rw [Nest.bp_congr ((Nest.nilT_sub_lTy dI nil k).trans hnil)] at subL
        simp only [Lynx.apply_eq, «map_to_list_nil:ensures/3»]
        by_cases hn : Nest.MT node (d + 1) X Nest.wNone
        · rw [Nest.bp_true.mpr hn] at subL
          rw [Nest.bp_false.mpr (fun h => holds.mpr hn h)] at dis
          simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, dis, Erlang.erlang.«not/1»,
            Erlang.erlang.«==/2», Lynx.Term.true]
        · rw [Nest.bp_false.mpr hn] at subL
          rw [Nest.bp_true.mpr (Classical.not_not.mp fun h => hn (holds.mp h))] at dis
          simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, dis, Erlang.erlang.«not/1»,
            Erlang.erlang.«==/2», Lynx.Term.true]
      """

    law map_to_list_badmap(map, depth, node),
      requires: arrows_static?(map, {depth + 1, node}) and depth?(depth),
      expects:
        (Descr.map_to_list(map) == :badmap) ==
          not (Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map)),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, so the proofs run from the bound of level `d + 1` on.
      simp only [«map_to_list_badmap:requires/3», Lynx.Term.true] at requires
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at requires; cases requires
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨hs, hd⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      simp only [Erlang.erlang.«+/2_integers», Except.ok.injEq] at hp
      subst hp
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      refine ⟨100 + 24 * (d + 1), fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dt := Nest.arrows_static_ok hs
      have top : Elixir.Module.Types.Descr.«open_map/0» =
          .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) := rfl
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.bp_false.mpr fun h => by
          have := (Nest.mapTop_den Nest.bitPt).mp (h Nest.bitPt (Nest.denD_term _))
          simp [Nest.bitPt] at this] at sT
        simp only [Lynx.apply_eq, «map_to_list_badmap:ensures/3»]
        simp [Nest.tolist_one, Nest.tolist_term, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨only, b, inner, L, -, rfl, -⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm
      · rw [Nest.monly_iff] at nonly
        simp only [Lynx.apply_eq, «map_to_list_badmap:ensures/3»]
        by_cases h : Nest.SubN node (d + 1) (.map X) (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
        · rw [Nest.bp_true.mpr h] at sT
          rw [Nest.bp_true.mpr (Classical.not_not.mp fun h' => nonly ⟨h, h'⟩)] at ne
          simp [Nest.tolist_one, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
        · rw [Nest.bp_false.mpr h] at sT
          simp [Nest.tolist_one, run, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      · obtain ⟨h₁, h₂⟩ := Nest.monly_iff.mp only
        rw [Nest.bp_true.mpr h₁] at sT
        rw [Nest.bp_false.mpr h₂] at ne
        simp only [Lynx.apply_eq, «map_to_list_badmap:ensures/3»]
        simp [Nest.tolist_one, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law map_constructor_closed_open(pairs, depth, node),
      requires: map_pairs?(pairs, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(Descr.closed_map(pairs), Descr.open_map(pairs)),
      proof: ~LEAN"""
      simp only [«map_constructor_closed_open:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨hp, hd⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      refine ⟨(Nest.level node (d + 1)).K + 26, fun depth' deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_closed_open_core hfs (by omega) _ _
      """

    law map_constructor_empty(),
      expects: Descr.equal?(Descr.empty_map(), Descr.closed_map([])),
      proof: ~LEAN"""
      refine ⟨(Nest.level (.atom "term") 0).K + 26, fun depth deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth = m + 1 := ⟨depth - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_empty_core (t := .atom "term") (n := 0) (by omega)
      """

    law map_constructor_atom(tag, pairs, key, depth, node),
      requires: tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and depth?(depth) and is_atom(key),
      expects: Descr.subtype?(construct(tag, pairs), Descr.open_map([{key, atom_field(tag, pairs, key)}])),
      proof: ~LEAN"""
      simp only [«map_constructor_atom:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true, Except.ok.injEq]
        at requires
      obtain ⟨⟨⟨ht, hp⟩, hd⟩, hk⟩ := requires
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨k, rfl⟩ := Nest.is_atom_true hk
      refine ⟨(Nest.level node (d + 1)).K + 26, fun depth' deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_atom_core hs hfs k (by omega) _ _
      """

    law map_constructor_atom_least(tag, pairs, key, value, optional, depth, node),
      requires:
        tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and arrows_static?(value, {depth, node}) and
          depth?(depth) and is_atom(key) and is_boolean(optional) and not Descr.empty?(construct(tag, pairs)) and
          Descr.subtype?(construct(tag, pairs), Descr.open_map([{key, {value, optional}}])),
      expects:
        Descr.subtype?(elem(atom_field(tag, pairs, key), 0), value) and
          (optional or not elem(atom_field(tag, pairs, key), 1)),
      proof: ~LEAN"""
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_constructor_atom_least:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Except.ok.injEq] at checked
      obtain ⟨⟨⟨⟨⟨⟨⟨ht, hp⟩, hv⟩, hd⟩, hk⟩, ho⟩, -⟩, -⟩ := checked
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨k, rfl⟩ := Nest.is_atom_true hk
      obtain ⟨o, rfl⟩ := Nest.is_boolean_true ho
      have ev : (Nest.level node (d + 1)).E value := Or.inl (Nest.arrows_static_ok hv)
      refine ⟨max bound ((Nest.level node (d + 1)).K + 26), fun depth' deep => ?_⟩
      obtain ⟨hb, hm⟩ := Nat.max_le.mp deep
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      have r := requires (m + 1) hb
      simp only [Lynx.apply_eq, «map_constructor_atom_least:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true]
        at r
      obtain ⟨⟨-, r1⟩, r2⟩ := r
      simp only [Lynx.apply_eq]
      exact Nest.ctor_atom_least_core hs hfs k ev o (by omega) r1 r2 _ _
      """

    law map_constructor_kind(tag, pairs, kind, depth, node),
      requires:
        tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and depth?(depth) and keys?([], [kind]) and
          kind != :atom,
      expects: Descr.subtype?(construct(tag, pairs), Descr.open_map([{[kind], domain_value(tag, pairs, kind)}])),
      proof: ~LEAN"""
      simp only [«map_constructor_kind:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true, Except.ok.injEq]
        at requires
      obtain ⟨⟨⟨⟨ht, hp⟩, hd⟩, hk⟩, hn⟩ := requires
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨-, ks, -, e, -, hks⟩ := Nest.keys_ok hk
      obtain rfl := list_inj e
      obtain ⟨k, mk, rfl⟩ := hks kind (by simp)
      refine ⟨(Nest.level node (d + 1)).K + 26, fun depth' deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_kind_core hs hfs mk (Nest.ne_atom_ok hn) (by omega) _ _
      """

    law map_constructor_kind_least(tag, pairs, kind, value, depth, node),
      requires:
        tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and arrows_static?(value, {depth, node}) and
          depth?(depth) and keys?([], [kind]) and kind != :atom and not Descr.empty?(construct(tag, pairs)) and
          Descr.subtype?(construct(tag, pairs), Descr.open_map([{[kind], value}])),
      expects: Descr.subtype?(domain_value(tag, pairs, kind), value),
      proof: ~LEAN"""
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_constructor_kind_least:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Except.ok.injEq] at checked
      obtain ⟨⟨⟨⟨⟨⟨⟨ht, hp⟩, hv⟩, hd⟩, hk⟩, hn⟩, -⟩, -⟩ := checked
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨-, ks, -, e, -, hks⟩ := Nest.keys_ok hk
      obtain rfl := list_inj e
      obtain ⟨k, mk, rfl⟩ := hks kind (by simp)
      have ev : (Nest.level node (d + 1)).E value := Or.inl (Nest.arrows_static_ok hv)
      refine ⟨max bound ((Nest.level node (d + 1)).K + 26), fun depth' deep => ?_⟩
      obtain ⟨hb, hm⟩ := Nat.max_le.mp deep
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      have r := requires (m + 1) hb
      simp only [Lynx.apply_eq, «map_constructor_kind_least:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true]
        at r
      obtain ⟨⟨-, r1⟩, r2⟩ := r
      simp only [Lynx.apply_eq]
      exact Nest.ctor_kind_least_core hs hfs mk (Nest.ne_atom_ok hn) ev (by omega) r1 r2 _ _
      """
  end
end
