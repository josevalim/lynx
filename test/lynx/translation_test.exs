defmodule Lynx.TranslationTest do
  use ExUnit.Case, async: true

  alias Lynx.Translation

  test "clusters cycles separately and emits dependencies before callers" do
    core =
      cerl("""
      -module(example).
      -export([caller/1, identity/1, self/1]).

      caller(X) ->
          Y = odd(X),
          Z = first(Y),
          Z + even(X).
      odd([]) -> false;
      odd([_ | Xs]) -> even(Xs).
      even([]) -> true;
      even([_ | Xs]) -> odd(Xs).
      first([]) -> 0;
      first([_ | Xs]) -> second(Xs).
      second([]) -> 1;
      second([_ | Xs]) -> third(Xs).
      third([]) -> 2;
      third([_ | Xs]) -> first(Xs).
      identity(X) -> X.
      self(X) -> self(X).
      """)

    assert %{example: commands} =
             Translation.new()
             |> Translation.add(core, [{:caller, 1}, {:identity, 1}, {:self, 1}])
             |> Translation.assemble()

    groups =
      Enum.map(commands, fn %{"expr" => expr} ->
        case expr do
          %{"kind" => "mutual", "defs" => defs} -> Enum.map(defs, & &1["name"])
          %{"kind" => "def", "name" => name} -> [name]
        end
      end)

    assert Enum.sort(groups) == [
             ["caller_1"],
             ["even_1", "odd_1"],
             ["first_1", "second_1", "third_1"],
             ["identity_1"],
             ["self_1"]
           ]

    caller = Enum.find_index(groups, &("caller_1" in &1))
    assert Enum.find_index(groups, &("odd_1" in &1)) < caller
    assert Enum.find_index(groups, &("first_1" in &1)) < caller
  end

  test "only translates requested roots" do
    core =
      cerl("""
      -module(example).
      -export([identity/1]).
      identity(X) -> X.
      """)

    assert %{example: []} =
             Translation.new() |> Translation.add(core, []) |> Translation.assemble()
  end

  test "propagates unsupported Core from an exported function" do
    core =
      cerl("""
      -module(example).
      -export([entry/1]).
      entry(X) -> erlang:abs(X).
      """)

    assert {:unsupported_core, text} = Translation.add(Translation.new(), core, [{:entry, 1}])
    assert text =~ "call 'erlang':'abs'"
  end

  test "accumulates roots across modules and reuses each module's translations" do
    first =
      cerl("""
      -module(first).
      -export([entry/1, extra/1]).
      entry(X) -> helper(X).
      helper(X) -> X.
      extra(_) -> 1.
      """)

    second =
      cerl("""
      -module(second).
      -export([entry/1]).
      entry(_) -> 2.
      """)

    initial = Translation.new() |> Translation.add(first, [{:entry, 1}])
    assert Enum.sort(Map.keys(initial.modules.first)) == [{:entry, 1}, {:helper, 1}]

    translation =
      initial
      |> Translation.add(second, [{:entry, 1}])
      |> Translation.add(first, [{:extra, 1}])

    assert Map.take(translation.modules.first, Map.keys(initial.modules.first)) ==
             initial.modules.first

    assert Enum.sort(Map.keys(translation.modules.first)) ==
             [{:entry, 1}, {:extra, 1}, {:helper, 1}]

    assert Map.keys(translation.modules.second) == [{:entry, 1}]
    assert Translation.add(translation, first, [{:entry, 1}]) == translation

    assert %{first: first_commands, second: second_commands} = Translation.assemble(translation)
    assert Enum.map(first_commands, & &1["expr"]["name"]) == ["extra_1", "helper_1", "entry_1"]
    assert Enum.map(second_commands, & &1["expr"]["name"]) == ["entry_1"]
    assert Translation.assemble(Translation.new()) == %{}
  end

  defp cerl(source) do
    forms =
      {String.to_charlist(source), 1}
      |> Stream.unfold(fn {chars, line} ->
        result =
          case :erl_scan.tokens([], chars, line) do
            {:more, continuation} -> :erl_scan.tokens(continuation, :eof, line)
            done -> done
          end

        case result do
          {:done, {:eof, _}, _} ->
            nil

          {:done, {:ok, tokens, next_line}, rest} ->
            assert {:ok, form} = :erl_parse.parse_form(tokens)
            {form, {rest, next_line}}
        end
      end)
      |> Enum.to_list()

    assert {:ok, core, _warnings} = :v3_core.module(forms, [])
    core
  end
end
