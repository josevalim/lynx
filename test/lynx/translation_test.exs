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

    assert [%{"module" => "example", "contents" => commands}] =
             Translation.new([{"example.erl", core}])
             |> Translation.add(:example, [{:caller, 1}, {:identity, 1}, {:self, 1}])
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

    assert [%{"module" => "example", "contents" => []}] =
             Translation.new([{"example.erl", core}])
             |> Translation.add(:example, [])
             |> Translation.assemble()
  end

  test "propagates unsupported Core from an exported function" do
    core =
      cerl("""
      -module(example).
      -export([entry/1]).
      entry(X) -> erlang:abs(X).
      """)

    assert {:unsupported_core, text} =
             Translation.add(Translation.new([{"example.erl", core}]), :example, [{:entry, 1}])

    assert text =~ "call 'erlang':'abs'"
  end

  test "follows remote calls and orders external modules before callers" do
    caller =
      cerl("""
      -module(a_caller).
      -export([entry/1, identity/1]).
      entry(X) -> helper(X).
      helper(X) -> z_dependency:entry(X).
      identity(X) -> X.
      """)

    dependency =
      cerl("""
      -module(z_dependency).
      -export([entry/1]).
      entry(X) -> X.
      """)

    translation =
      Translation.new([{"caller.erl", caller}, {"dependency.erl", dependency}])
      |> Translation.add(:a_caller, [{:identity, 1}])
      |> Translation.add(:a_caller, [{:entry, 1}])

    assert Translation.add(translation, :a_caller, [{:entry, 1}]) == translation
    assert translation.modules.z_dependency.translations == %{}

    assert [
             %{
               "module" => "z_dependency",
               "file" => "dependency.erl",
               "imports" => [],
               "contents" => [dependency]
             },
             %{"module" => "a_caller", "file" => "caller.erl", "imports" => ["z_dependency"]}
           ] = Translation.assemble(translation)

    assert dependency["expr"]["name"] == "entry_1"

    assert_raise KeyError, fn ->
      Translation.new([{"caller.erl", caller}])
      |> Translation.add(:a_caller, [{:entry, 1}])
      |> Translation.assemble()
    end

    assert_raise KeyError, fn -> Translation.new([]) |> Translation.add(:missing, []) end
  end

  test "translates qualified calls to the current module as local calls" do
    core =
      cerl("""
      -module(example).
      -export([entry/1, helper/1]).
      entry(X) -> example:helper(X).
      helper([]) -> 0;
      helper([_ | Xs]) -> example:helper(Xs).
      """)

    translation =
      Translation.new([{"example.erl", core}]) |> Translation.add(:example, [{:entry, 1}])

    functions = translation.modules.example.translations
    assert functions[{:entry, 1}].local_calls == [{:helper, 1}]
    assert functions[{:entry, 1}].external_calls == []
    assert functions[{:helper, 1}].local_calls == []
    assert functions[{:helper, 1}].external_calls == []
    json = JSON.encode!(functions[{:entry, 1}].translation)
    assert json =~ ~s("name":"helper_1")
    refute json =~ "example.helper_1"

    assert [%{"imports" => [], "contents" => commands}] = Translation.assemble(translation)
    assert Enum.map(commands, & &1["expr"]["name"]) == ["helper_1", "entry_1"]
  end

  test "rejects cycles between modules during assembly" do
    first =
      cerl("""
      -module(first).
      -export([entry/1]).
      entry(X) -> second:entry(X).
      """)

    second =
      cerl("""
      -module(second).
      -export([entry/1]).
      entry(X) -> first:entry(X).
      """)

    translation =
      Translation.new([{"first.erl", first}, {"second.erl", second}])
      |> Translation.add(:first, [{:entry, 1}])

    assert_raise ArgumentError, "found cycle during topsort", fn ->
      Translation.assemble(translation)
    end
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
