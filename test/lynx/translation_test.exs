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

    assert [%{"module" => "Erlang.example", "contents" => commands}] =
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
             ["«caller/1»"],
             ["«even/1»", "«odd/1»"],
             ["«first/1»", "«second/1»", "«third/1»"],
             ["«identity/1»"],
             ["«self/1»"]
           ]

    caller = Enum.find_index(groups, &("«caller/1»" in &1))
    assert Enum.find_index(groups, &("«odd/1»" in &1)) < caller
    assert Enum.find_index(groups, &("«first/1»" in &1)) < caller
  end

  test "only translates requested roots" do
    core =
      cerl("""
      -module(example).
      -export([identity/1]).
      identity(X) -> X.
      """)

    assert [%{"module" => "Erlang.example", "contents" => []}] =
             Translation.new([{"example.erl", core}])
             |> Translation.add(:example, [])
             |> Translation.assemble()
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
    assert Map.keys(translation.modules.z_dependency.translations) == [{:entry, 1}]
    assert translation.external_calls == %{a_caller: MapSet.new([:z_dependency])}
    assert translation.stack == []

    assert [
             %{
               "module" => "Erlang.z_dependency",
               "file" => "dependency.erl",
               "imports" => [],
               "contents" => [dependency]
             },
             %{
               "module" => "Erlang.a_caller",
               "file" => "caller.erl",
               "imports" => ["Erlang.z_dependency"]
             }
           ] = Translation.assemble(translation)

    assert dependency["expr"]["name"] == "«entry/1»"
  end

  test "keeps Elixir namespaces in module names and imports" do
    caller =
      cerl("""
      -module(caller).
      -export([entry/1]).
      entry(X) -> 'Elixir.Foo.Bar':entry(X).
      """)

    dependency =
      cerl("""
      -module('Elixir.Foo.Bar').
      -export([entry/1]).
      entry(X) -> X.
      """)

    files =
      Translation.new([{"caller.erl", caller}, {"bar.ex", dependency}])
      |> Translation.add(:caller, [{:entry, 1}])
      |> Translation.assemble()

    assert [
             %{"module" => "Elixir.Foo.Bar", "imports" => []},
             %{"module" => "Erlang.caller", "imports" => ["Elixir.Foo.Bar"]}
           ] = files
  end

  test "imports runtime functions without requiring their Core definitions" do
    core =
      cerl("""
      -module(example).
      -export([entry/1]).
      entry(X) -> maps:put(key, X + 1, maps:new()).
      """)

    translation =
      Translation.new([{"example.erl", core}])
      |> Translation.add(:example, [{:entry, 1}])

    assert Map.keys(translation.modules) == [:example]
    assert translation.external_calls == %{example: MapSet.new([:erlang, :maps])}

    assert [%{"imports" => ["Erlang.erlang", "Erlang.maps"], "contents" => [_]}] =
             Translation.assemble(translation)
  end

  test "propagates impurity through recursive groups and their callers only" do
    core =
      cerl("""
      -module(example).
      -export([entry/1, pure/1, later/1]).
      entry(X) -> first(X).
      first([]) -> erlang:get(key);
      first([_ | Xs]) -> second(Xs).
      second([]) -> 0;
      second([_ | Xs]) -> first(Xs).
      pure(X) -> X + 1.
      later(X) -> entry(X).
      """)

    for roots <- [[{:entry, 1}, {:pure, 1}], [{:pure, 1}, {:entry, 1}]] do
      translation = Translation.new([{"example.erl", core}]) |> Translation.add(:example, roots)
      translation = Translation.add(translation, :example, [{:later, 1}])
      functions = translation.modules.example.translations

      assert functions[{:pure, 1}].pure
      for name <- [:entry, :first, :second, :later], do: refute(functions[{name, 1}].pure)
      assert Translation.add(translation, :example, roots) == translation

      assert [%{"contents" => contents}] = Translation.assemble(translation)
      assert Enum.count(contents, &(&1["kind"] == "command")) == 1
      assert Enum.any?(contents, &(&1["kind"] == "mutual"))
    end
  end

  test "tracks purity per function across remote and local call chains" do
    caller =
      cerl("""
      -module(caller).
      -export([pure/1, impure/1]).
      pure(X) -> middle:pure(X).
      impure(X) -> middle:impure(X).
      """)

    middle =
      cerl("""
      -module(middle).
      -export([pure/1, impure/1]).
      pure(X) -> dependency:pure(X).
      impure(X) -> helper(X).
      helper(X) -> dependency:impure(X).
      """)

    dependency =
      cerl("""
      -module(dependency).
      -export([pure/1, impure/1]).
      pure(X) -> X + 1.
      impure(X) -> erlang:get(X).
      """)

    translation =
      Translation.new([
        {"caller.erl", caller},
        {"middle.erl", middle},
        {"dependency.erl", dependency}
      ])
      |> Translation.add(:caller, [{:impure, 1}])
      |> Translation.add(:caller, [{:pure, 1}])

    for module <- [:caller, :middle, :dependency] do
      assert translation.modules[module].translations[{:pure, 1}].pure
      refute translation.modules[module].translations[{:impure, 1}].pure
    end

    for %{"contents" => contents} <- Translation.assemble(translation) do
      assert Enum.any?(
               contents,
               &match?(%{"name" => "lynx_pure", "expr" => %{"name" => "«pure/1»"}}, &1)
             )

      assert Enum.any?(contents, &match?(%{"kind" => "def", "name" => "«impure/1»"}, &1))
    end
  end

  test "imports a module BIF if used" do
    lists =
      cerl("""
      -module(lists).
      -export([sum/1, reverse/2]).
      sum([]) -> 0;
      sum([X | Xs]) -> X + sum(Xs).
      reverse(_, _) -> erlang:nif_error(undef).
      """)

    caller =
      cerl("""
      -module(caller).
      -export([sum/1, reverse/1]).
      sum(X) -> lists:sum(X).
      reverse(X) -> lists:reverse(X, []).
      """)

    translation = Translation.new([{"lists.erl", lists}, {"caller.erl", caller}])

    sum_only = Translation.add(translation, :caller, [{:sum, 1}])
    assert sum_only.builtin_modules == %{erlang: true}

    assert [
             %{"module" => "Erlang.lists", "imports" => ["Erlang.erlang"]},
             %{"module" => "Erlang.caller", "imports" => ["Erlang.lists"]}
           ] = Translation.assemble(sum_only)

    for roots <- [[{:sum, 1}, {:reverse, 1}], [{:reverse, 1}, {:sum, 1}]] do
      mixed =
        Enum.reduce(roots, translation, fn root, acc -> Translation.add(acc, :caller, [root]) end)

      assert mixed.builtin_modules == %{erlang: true, lists: true}
      assert Map.keys(mixed.modules.lists.translations) == [{:sum, 1}]

      assert [
               %{
                 "module" => "Erlang.lists",
                 "imports" => ["Erlang.erlang", "Erlang.lists"],
                 "contents" => [%{"expr" => %{"name" => "«sum/1»"}}]
               },
               %{"module" => "Erlang.caller", "imports" => ["Erlang.lists"]}
             ] = Translation.assemble(mixed)
    end
  end

  test "qualified self calls resolve builtins before local definitions" do
    lists =
      cerl("""
      -module(lists).
      -export([reverse/1, reverse/2]).
      reverse(X) -> lists:reverse(X, []).
      reverse(_, _) -> erlang:nif_error(undef).
      """)

    translation =
      Translation.new([{"lists.erl", lists}]) |> Translation.add(:lists, [{:reverse, 1}])

    assert translation.builtin_modules == %{lists: true}
    assert translation.external_calls == %{}
    assert Map.keys(translation.modules.lists.translations) == [{:reverse, 1}]
    assert translation.modules.lists.translations[{:reverse, 1}].pure
    assert translation.modules.lists.translations[{:reverse, 1}].local_calls == []

    assert [%{"imports" => ["Erlang.lists"], "contents" => [definition]}] =
             Translation.assemble(translation)

    assert JSON.encode!(definition) =~ "Erlang.lists.«reverse/2»"
  end

  @tag :tmp_dir
  test "loads modules from code path", %{tmp_dir: tmp_dir} do
    {_beam, source} =
      write_beam(
        :lynx_lookup_root,
        """
        -export([entry/1]).
        entry(X) -> X.
        """,
        tmp_dir
      )

    assert [%{"module" => "Erlang.lynx_lookup_root", "file" => ^source, "contents" => [_]}] =
             Translation.new([])
             |> Translation.add(:lynx_lookup_root, [{:entry, 1}])
             |> Translation.assemble()
  end

  describe "errors" do
    @tag :tmp_dir
    test "reports missing debug information at the caller", %{tmp_dir: tmp_dir} do
      write_beam(
        :lynx_lookup_no_debug,
        """
        -export([entry/1]).
        entry(X) -> X.
        """,
        tmp_dir,
        [:no_debug_info]
      )

      caller =
        cerl("""
        -module(caller).
        -export([entry/1]).
        -file("lookup_caller.erl", 1).
        entry(X) -> lynx_lookup_no_debug:entry(X).
        """)

      error =
        assert_raise CompileError, fn ->
          Translation.new([{"caller.erl", caller}]) |> Translation.add(:caller, [{:entry, 1}])
        end

      assert error.file == "lookup_caller.erl"
      assert error.line == 4
      assert error.description =~ "debug information"
      assert error.description =~ ":lynx_lookup_no_debug"
    end

    @tag :tmp_dir
    test "reports invalid BEAM files at the caller", %{tmp_dir: tmp_dir} do
      File.write!(Path.join(tmp_dir, "lynx_lookup_invalid.beam"), "not a BEAM")
      add_code_path(tmp_dir)

      caller =
        cerl("""
        -module(caller).
        -export([entry/1]).
        entry(X) -> lynx_lookup_invalid:entry(X).
        """)

      error =
        assert_raise CompileError, fn ->
          Translation.new([{"caller.erl", caller}]) |> Translation.add(:caller, [{:entry, 1}])
        end

      assert error.file == "caller.erl"
      assert error.line == 3
      assert error.description =~ "cannot read BEAM for :lynx_lookup_invalid"
    end

    test "does not skip a runtime function with the wrong arity" do
      core =
        cerl("""
        -module(example).
        -export([entry/1]).
        entry(X) -> maps:new(X).
        """)

      assert_raise CompileError, "example.erl:3: undefined function :maps.new/1", fn ->
        Translation.new([{"example.erl", core}]) |> Translation.add(:example, [{:entry, 1}])
      end
    end

    test "raises on unsupported Core" do
      core =
        cerl("""
        -module(example).
        -export([entry/1]).
        entry(X) -> {ok, X}.
        """)

      error =
        assert_raise CompileError, fn ->
          Translation.add(Translation.new([{"example.erl", core}]), :example, [{:entry, 1}])
        end

      assert error.file == "example.erl"
      assert error.line == 3
      assert Exception.message(error) =~ "example.erl:3: unsupported Core expression:"
      assert error.description =~ "'ok'"
    end

    test "validates remote modules" do
      caller =
        cerl("""
        -module(a_caller).
        -export([entry/1]).
        entry(X) -> z_dependency:entry(X).
        """)

      assert_raise CompileError,
                   "caller.erl:3: unknown module :z_dependency",
                   fn ->
                     Translation.new([{"caller.erl", caller}])
                     |> Translation.add(:a_caller, [{:entry, 1}])
                   end
    end

    test "validates remote functions" do
      caller =
        cerl("""
        -module(caller).
        -export([entry/1]).
        entry(X) -> other:entry(X).
        """)

      missing =
        cerl("""
        -module(other).
        -export([different/1]).
        different(X) -> X.
        """)

      assert_raise CompileError, "caller.erl:3: undefined function :other.entry/1", fn ->
        Translation.new([{"caller.erl", caller}, {"other.erl", missing}])
        |> Translation.add(:caller, [{:entry, 1}])
      end
    end

    test "rejects cycles between modules during translation" do
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

      assert_raise CompileError,
                   "second.erl:3: cyclic module call to :first.entry/1 (:first -> :second -> :first)",
                   fn ->
                     Translation.new([{"first.erl", first}, {"second.erl", second}])
                     |> Translation.add(:first, [{:entry, 1}])
                   end
    end

    # Regression: `?MODULE:missing(X)` used to crash the translator with an
    # internal `badkey` error instead of reporting the undefined function.
    test "validates qualified calls to the current module" do
      core =
        cerl("""
        -module(example).
        -export([entry/1]).
        entry(X) -> example:missing(X).
        """)

      assert_raise CompileError, "example.erl:3: undefined function :example.missing/1", fn ->
        Translation.new([{"example.erl", core}]) |> Translation.add(:example, [{:entry, 1}])
      end
    end

    # Regression: calling a fun held in a variable, `F(X)`, used to crash the
    # translator with an internal `badkey` error.
    test "reports applications of fun variables as unsupported Core" do
      core =
        cerl("""
        -module(example).
        -export([entry/1]).
        entry(F) -> F(1).
        """)

      error =
        assert_raise CompileError, fn ->
          Translation.new([{"example.erl", core}]) |> Translation.add(:example, [{:entry, 1}])
        end

      assert error.line == 3
      assert error.description =~ "unsupported Core expression:"
      assert error.description =~ "apply"
    end

    # Regression: a clause with a guard used to crash while formatting the
    # error message, because Core pretty-printing cannot print a bare clause.
    test "reports unsupported guards without crashing" do
      core =
        cerl("""
        -module(example).
        -export([entry/1]).
        entry(X) when X > 0 -> X.
        """)

      error =
        assert_raise CompileError, fn ->
          Translation.new([{"example.erl", core}]) |> Translation.add(:example, [{:entry, 1}])
        end

      assert error.line == 3
      assert error.description =~ "unsupported Core expression:"
      assert error.description =~ "'>'"
    end

    # Regression: runtime functions whose Lean signature is not
    # `Term -> ... -> Result` (they need the function table or thunks) were
    # listed as builtins, so the translator emitted ill-typed Lean.
    test "does not call runtime functions that need more than terms" do
      for {call, name} <- [
            {"erlang:spawn(X)", "spawn/1"},
            {"erlang:apply(X, [])", "apply/2"},
            {"erlang:'andalso'(X, X)", "andalso/2"}
          ] do
        core =
          cerl("""
          -module(example).
          -export([entry/1]).
          entry(X) -> #{call}.
          """)

        assert_raise CompileError, ~r/:erlang/, fn ->
          Translation.new([{"example.erl", core}]) |> Translation.add(:example, [{:entry, 1}])
        end

        refute name in Map.keys(
                 JSON.decode!(File.read!(Path.expand("../../Lean/modules.json", __DIR__)))[
                   "erlang"
                 ]
               )
      end
    end

    test "uses the file directive for unknown remote module errors" do
      core =
        cerl("""
        -module(example).
        -export([entry/1]).
        -file("foo", 1).
        entry(X) -> missing:entry(X).
        """)

      error =
        assert_raise CompileError, "foo:4: unknown module :missing", fn ->
          Translation.new([{"example.erl", core}]) |> Translation.add(:example, [{:entry, 1}])
        end

      assert error.file == "foo"
      assert error.line == 4
    end
  end

  defp write_beam(module, body, directory, options \\ [:debug_info]) do
    source = Path.join(directory, "#{module}.erl")
    beam = Path.join(directory, "#{module}.beam")
    File.write!(source, "-module(#{module}).\n" <> body)
    assert {:ok, ^module, binary} = :compile.file(String.to_charlist(source), [:binary | options])
    File.write!(beam, binary)
    add_code_path(directory)
    {beam, source}
  end

  defp add_code_path(directory) do
    path = String.to_charlist(directory)
    assert :code.add_patha(path) == true
    on_exit(fn -> :code.del_path(path) end)
  end

  defp cerl(source) do
    forms =
      {String.to_charlist(source), {1, 1}}
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
