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
             Translation.new()
             |> Translation.add({"example.erl", core})
             |> Translation.translate(:example, [{:caller, 1}, {:identity, 1}, {:self, 1}])
             |> Translation.assemble()

    groups =
      Enum.map(commands, fn expr ->
        case expr do
          %{"kind" => "mutual", "defs" => defs} -> Enum.map(defs, & &1["name"])
          %{"kind" => "def", "name" => name} -> [name]
        end
      end)

    assert Enum.sort(groups) == [
             ["caller"],
             ["first", "second", "third"],
             ["identity"],
             ["odd", "even"],
             ["self"]
           ]

    caller = Enum.find_index(groups, &("caller" in &1))
    assert Enum.find_index(groups, &("odd" in &1)) < caller
    assert Enum.find_index(groups, &("first" in &1)) < caller
  end

  test "only translates requested roots" do
    core =
      cerl("""
      -module(example).
      -export([identity/1]).
      identity(X) -> X.
      """)

    assert [%{"module" => "Erlang.example", "contents" => []}] =
             Translation.new()
             |> Translation.add({"example.erl", core})
             |> Translation.translate(:example, [])
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
      Translation.new()
      |> Translation.add({"caller.erl", caller})
      |> Translation.add({"dependency.erl", dependency})
      |> Translation.translate(:a_caller, [{:identity, 1}])
      |> Translation.translate(:a_caller, [{:entry, 1}])

    assert Translation.translate(translation, :a_caller, [{:entry, 1}]) == translation
    assert Map.keys(translation.modules.z_dependency.translations) == [{:entry, 1}]
    assert translation.external_calls == %{a_caller: MapSet.new([:z_dependency])}
    assert translation.stack == []

    assert [
             %{
               "module" => "Erlang.z_dependency",
               "cache_key" => <<_::binary-size(64)>>,
               "file" => "dependency.erl",
               "imports" => [],
               "contents" => [%{"name" => "entry", "pure" => true}]
             },
             %{
               "module" => "Erlang.a_caller",
               "cache_key" => <<_::binary-size(64)>>,
               "file" => "caller.erl",
               "imports" => ["Erlang.z_dependency"]
             }
           ] = Translation.assemble(translation)
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
      Translation.new()
      |> Translation.add({"caller.erl", caller})
      |> Translation.add({"bar.ex", dependency})
      |> Translation.translate(:caller, [{:entry, 1}])
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
      entry(X) -> maps:put(key, X + 1, maps:merge(X, X)).
      """)

    translation =
      Translation.new()
      |> Translation.add({"example.erl", core})
      |> Translation.translate(:example, [{:entry, 1}])

    assert Map.keys(translation.modules) == [:example]
    assert translation.external_calls == %{example: MapSet.new([:erlang, :maps])}

    assert [%{"imports" => ["Erlang.erlang", "Erlang.maps"], "contents" => [_]}] =
             Translation.assemble(translation)
  end

  test "translates laws and recursively includes both predicates' callees" do
    core =
      cerl(~S"""
      -module(example).
      -export([allowed/1, identity_ensures/1]).
      -law #{name => {identity_law, [value]}, requires => allowed, ensures => identity_ensures}.
      -proof <<"rfl">>.
      identity_ensures(X) -> identity(X) == X.
      allowed(_) -> true.
      identity(X) -> X.
      """)

    translation =
      Translation.new()
      |> Translation.add({"example.erl", core})
      |> Translation.translate(:example, [{:identity_law, 1}])

    assert {:law, _} = translation.modules.example.definitions[{:identity_law, 1}]

    assert Enum.sort(Map.keys(translation.modules.example.translations)) ==
             [{:allowed, 1}, {:identity, 1}, {:identity_ensures, 1}, {:identity_law, 1}]

    assert [
             %{
               "contents" => [
                 %{"name" => "allowed"},
                 %{"name" => "identity"},
                 %{"name" => "identity_ensures"},
                 %{
                   "kind" => "theorem",
                   "name" => "identity_law",
                   "params" => ["value"],
                   "requires" => "allowed",
                   "ensures" => "identity_ensures",
                   "proof" => %{"source" => "rfl", "indentation" => 0, "span" => [5]}
                 } = law
               ]
             }
           ] = Translation.assemble(translation)

    refute Map.has_key?(law, "pure")
  end

  test "raises CompileError with source annotations for invalid law attributes" do
    core =
      cerl(~S"""
      -module(example).
      -law #{name => {entry, [x]}, ensures => expected}.
      -other value.
      -export([expected/1]).
      expected(_) -> true.
      """)

    assert_raise CompileError, "example.erl:2: proof must immediately follow law", fn ->
      Translation.new() |> Translation.add({"example.erl", core})
    end
  end

  test "raises CompileError at a non-binary proof attribute" do
    core =
      cerl(~S"""
      -module(example).
      -law #{name => {entry, [x]}, ensures => expected}.
      -proof "rfl".
      -export([expected/1]).
      expected(_) -> true.
      """)

    assert_raise CompileError, "example.erl:3: proof must be a binary", fn ->
      Translation.new() |> Translation.add({"example.erl", core})
    end
  end

  test "translates a law with omitted requires" do
    core =
      cerl(~S"""
      -module(example).
      -law #{name => {entry, [x]}, ensures => expected}.
      -proof <<"rfl">>.
      -export([expected/1]).
      expected(_) -> true.
      """)

    translation =
      Translation.new()
      |> Translation.add({"example.erl", core})
      |> Translation.translate(:example, [{:entry, 1}])

    assert [%{"contents" => [%{"name" => "expected"}, law]}] = Translation.assemble(translation)

    assert law == %{
             "kind" => "theorem",
             "name" => "entry",
             "params" => ["x"],
             "ensures" => "expected",
             "proof" => %{"source" => "rfl", "indentation" => 0, "span" => [4]},
             "span" => [2, 2]
           }
  end

  test "verify selects all declared laws and skips unrelated exports" do
    core =
      cerl(~S"""
      -module(example).
      -export([unused/1]).
      -law #{name => {first, [x]}, ensures => expected}.
      -proof <<"rfl">>.
      -law #{name => {second, [y]}, ensures => expected}.
      -proof <<"rfl">>.
      expected(_) -> true.
      unused(X) -> {unsupported, X}.
      """)

    translation =
      Translation.new() |> Translation.add({"example.erl", core}) |> Translation.verify(:example)

    assert %{
             {:expected, 1} => %{},
             {:first, 1} => %{},
             {:second, 1} => %{}
           } = translation.modules.example.translations

    refute Map.has_key?(translation.modules.example.translations, {:unused, 1})

    selected =
      Translation.new()
      |> Translation.add({"example.erl", core})
      |> Translation.verify(:example, [{:second, 1}])

    assert Map.keys(selected.modules.example.translations) |> Enum.sort() ==
             [{:expected, 1}, {:second, 1}]

    assert_raise CompileError, ~r/does not declare law/, fn ->
      Translation.new()
      |> Translation.add({"example.erl", core})
      |> Translation.verify(:example, [{:unused, 1}])
    end
  end

  test "verify raises when a module declares no laws" do
    core =
      cerl("""
      -module(example).
      -export([truth/0]).
      truth() -> true.
      """)

    translation = Translation.new() |> Translation.add({"example.erl", core})

    error =
      assert_raise CompileError, ~r/module :example declares no laws/, fn ->
        Translation.verify(translation, :example)
      end

    assert error.file == "example.erl"

    assert [%{"contents" => [_]}] =
             translation
             |> Translation.translate(:example, [{:truth, 0}])
             |> Translation.assemble()
  end

  test "keeps explicit apply when its argument list is dynamic" do
    core =
      cerl("""
      -module(example).
      -export([entry/2]).
      entry(F, Args) -> erlang:apply(F, Args).
      """)

    translation =
      Translation.new()
      |> Translation.add({"example.erl", core})
      |> Translation.translate(:example, [{:entry, 2}])

    assert %{
             pure: false,
             translation: %{
               "body" => %{
                 "kind" => "remote_call",
                 "module" => "Erlang.erlang",
                 "name" => "apply"
               }
             }
           } = translation.modules.example.translations[{:entry, 2}]

    assert translation.builtin_modules == %{erlang: true}
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
      translation =
        Translation.new()
        |> Translation.add({"example.erl", core})
        |> Translation.translate(:example, roots)

      translation = Translation.translate(translation, :example, [{:later, 1}])
      functions = translation.modules.example.translations

      assert %{pure: true} = functions[{:pure, 1}]

      for name <- [:entry, :first, :second, :later],
          do: assert(%{pure: false} = functions[{name, 1}])

      assert Translation.translate(translation, :example, roots) == translation

      assert [%{"contents" => contents}] = Translation.assemble(translation)
      assert Enum.count(contents, & &1["pure"]) == 1
      assert Enum.any?(contents, &(&1["kind"] == "mutual"))

      for %{"kind" => "mutual", "pure" => pure, "defs" => defs} <- contents do
        assert Enum.all?(defs, &(&1["pure"] == pure))
      end
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
      Translation.new()
      |> Translation.add({"caller.erl", caller})
      |> Translation.add({"middle.erl", middle})
      |> Translation.add({"dependency.erl", dependency})
      |> Translation.translate(:caller, [{:impure, 1}])
      |> Translation.translate(:caller, [{:pure, 1}])

    for module <- [:caller, :middle, :dependency] do
      assert %{
               {:pure, 1} => %{pure: true},
               {:impure, 1} => %{pure: false}
             } = translation.modules[module].translations
    end

    for %{"contents" => contents} <- Translation.assemble(translation) do
      assert Enum.any?(
               contents,
               &match?(%{"kind" => "def", "name" => "pure", "pure" => true}, &1)
             )

      assert Enum.any?(contents, &match?(%{"kind" => "def", "name" => "impure"}, &1))
    end
  end

  test "dynamic application makes local, remote, and recursive callers impure" do
    dependency =
      cerl("""
      -module(dependency).
      -export([entry/1]).
      entry(F) -> X = dynamic(F), Y = explicit(X), first(Y).
      dynamic(F) -> F(7, F).
      explicit(F) -> erlang:apply(F, [7, F]).
      zero(F) -> F().
      first([]) -> second([]);
      first(F) -> zero(F).
      second(F) -> first(F).
      """)

    for {body, caller_imports} <- [
          {"dependency:entry(F)", [:dependency]},
          {"X = erlang:get(key), dependency:entry(X)", [:dependency, :erlang]},
          {"X = dependency:entry(F), erlang:get(X)", [:dependency, :erlang]}
        ] do
      caller =
        cerl("""
        -module(caller).
        -export([entry/1, pure/1]).
        entry(F) -> helper(F).
        helper(F) -> #{body}.
        pure(X) -> X.
        """)

      base =
        Translation.new()
        |> Translation.add({"caller.erl", caller})
        |> Translation.add({"dependency.erl", dependency})

      dependency_only = Translation.translate(base, :dependency, [{:entry, 1}])

      for %{"contents" => contents} <- Translation.assemble(dependency_only) do
        assert Enum.all?(contents, &(&1["kind"] in ["def", "mutual"]))
      end

      translation = Translation.translate(dependency_only, :caller, [{:entry, 1}, {:pure, 1}])
      direct = Translation.translate(base, :caller, [{:entry, 1}, {:pure, 1}])
      assert Translation.assemble(translation) == Translation.assemble(direct)

      for name <- [:entry, :helper] do
        assert %{pure: false} = translation.modules.caller.translations[{name, 1}]
      end

      for {_, definition} <- translation.modules.dependency.translations do
        assert %{pure: false} = definition
      end

      assert translation.builtin_modules ==
               if(:erlang in caller_imports, do: %{erlang: true}, else: %{})

      assert translation.external_calls == %{caller: MapSet.new(caller_imports)}

      functions = translation.modules.dependency.translations

      for name <- [:dynamic, :explicit, :zero] do
        assert %{local_calls: []} = functions[{name, 1}]
      end

      for name <- [:dynamic, :explicit] do
        assert %{
                 "body" => %{
                   "kind" => "fun_call",
                   "function" => %{"kind" => "var", "name" => 0},
                   "args" => [
                     %{"kind" => "integer", "value" => 7},
                     %{"kind" => "var", "name" => 0}
                   ]
                 }
               } = functions[{name, 1}].translation
      end

      assert %{
               "body" => %{
                 "kind" => "fun_call",
                 "function" => %{"kind" => "var", "name" => 0},
                 "args" => []
               }
             } = functions[{:zero, 1}].translation

      files = Translation.assemble(translation)

      commands =
        for %{"contents" => contents} <- files,
            %{"pure" => true} = command <- contents,
            do: command

      assert [%{"kind" => "def", "name" => "pure", "pure" => true}] = commands
    end
  end

  test "generates a function table with stable IDs across modules and incremental roots" do
    caller =
      cerl("""
      -module(caller).
      -export([entry/1, extra/1, again/0]).
      entry(X) -> F = fun local/1, G = dependency:entry(F), fun(Y) -> G(X + Y) end.
      local(X) -> X.
      extra(X) -> fun() -> erlang:get(X) end.
      again() -> fun local/1.
      """)

    dependency =
      cerl("""
      -module(dependency).
      -export([entry/1]).
      entry(F) -> G = fun local/1, fun(X) -> F(G(X)) end.
      local(X) -> X + 1.
      """)

    translation =
      Translation.new()
      |> Translation.add({"caller.erl", caller})
      |> Translation.add({"dependency.erl", dependency})
      |> Translation.translate(:caller, [{:entry, 1}])

    assert %{
             {:caller, {:local, 1}} => %{id: 0, captures: []},
             {:dependency, {:local, 1}} => %{id: 1, captures: []},
             2 => %{
               id: 2,
               module: :dependency,
               name: {:"$lynx_fun_2", 3},
               arity: 1,
               captures: [_, _]
             },
             3 => %{id: 3, module: :caller, name: {:"$lynx_fun_3", 3}, arity: 1, captures: [_, _]}
           } = translation.funs

    assert map_size(translation.funs) == 4

    assert Translation.translate(translation, :caller, [{:entry, 1}]) == translation

    updated = Translation.translate(translation, :caller, [{:again, 0}, {:extra, 1}])
    assert map_size(updated.funs) == 5
    assert Map.take(updated.funs, Map.keys(translation.funs)) == translation.funs

    assert %{id: 4, module: :caller, name: {:"$lynx_fun_4", 1}, arity: 0, captures: [_]} =
             updated.funs[4]

    assert %{pure: true, local_calls: []} = updated.modules.caller.translations[{:extra, 1}]
    assert %{pure: false} = updated.modules.caller.translations[{:"$lynx_fun_4", 1}]
    assert %{pure: false} = updated.modules.dependency.translations[{:"$lynx_fun_2", 3}]

    assert %{
             "body" => %{"kind" => "return", "value" => function}
           } =
             updated.modules.caller.translations[{:again, 0}].translation

    assert %{"kind" => "function", "id" => 0, "arity" => 1, "captures" => []} = function

    files = Translation.assemble(updated)

    assert %{
             "module" => "Erlang.program",
             "contents" => [
               %{"kind" => "fun_table", "entries" => entries} =
                 table
             ]
           } = List.last(files)

    refute Map.has_key?(table, "pure")

    %{"contents" => contents} = Enum.find(files, &(&1["module"] == "Erlang.caller"))

    assert Enum.any?(
             contents,
             &match?(%{"kind" => "def", "name" => "extra", "pure" => true}, &1)
           )

    assert Enum.map(entries, fn %{
                                  "body" => %{
                                    "kind" => "remote_call",
                                    "module" => module,
                                    "name" => name
                                  }
                                } ->
             {module, name}
           end) == [
             {"Erlang.caller", "local"},
             {"Erlang.dependency", "local"},
             {"Erlang.dependency", "$lynx_fun_2"},
             {"Erlang.caller", "$lynx_fun_3"},
             {"Erlang.caller", "$lynx_fun_4"}
           ]

    assert Enum.map(entries, & &1["pure"]) == [true, true, false, false, false]
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

    translation =
      Translation.new()
      |> Translation.add({"lists.erl", lists})
      |> Translation.add({"caller.erl", caller})

    sum_only = Translation.translate(translation, :caller, [{:sum, 1}])
    assert sum_only.builtin_modules == %{erlang: true}

    assert [
             %{"module" => "Erlang.lists", "imports" => ["Erlang.erlang"]},
             %{"module" => "Erlang.caller", "imports" => ["Erlang.lists"]}
           ] = Translation.assemble(sum_only)

    for roots <- [[{:sum, 1}, {:reverse, 1}], [{:reverse, 1}, {:sum, 1}]] do
      mixed =
        Enum.reduce(roots, translation, fn root, acc ->
          Translation.translate(acc, :caller, [root])
        end)

      assert mixed.builtin_modules == %{erlang: true, lists: true}
      assert Map.keys(mixed.modules.lists.translations) == [{:sum, 1}]

      assert [
               %{
                 "module" => "Erlang.lists",
                 "imports" => ["Erlang.erlang", "Erlang.lists"],
                 "contents" => [%{"name" => "sum", "pure" => true}]
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
      Translation.new()
      |> Translation.add({"lists.erl", lists})
      |> Translation.translate(:lists, [{:reverse, 1}])

    assert translation.builtin_modules == %{lists: true}
    assert translation.external_calls == %{}
    assert Map.keys(translation.modules.lists.translations) == [{:reverse, 1}]

    assert %{pure: true, local_calls: []} =
             translation.modules.lists.translations[{:reverse, 1}]

    assert [%{"imports" => ["Erlang.lists"], "contents" => [definition]}] =
             Translation.assemble(translation)

    assert %{"body" => call} = definition
    assert %{"kind" => "remote_call", "module" => "Erlang.lists", "name" => "reverse"} = call
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
             Translation.new()
             |> Translation.translate(:lynx_lookup_root, [{:entry, 1}])
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
          Translation.new()
          |> Translation.add({"caller.erl", caller})
          |> Translation.translate(:caller, [{:entry, 1}])
        end

      assert %CompileError{file: "lookup_caller.erl", line: 4} = error
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
          Translation.new()
          |> Translation.add({"caller.erl", caller})
          |> Translation.translate(:caller, [{:entry, 1}])
        end

      assert %CompileError{file: "caller.erl", line: 3} = error
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
        Translation.new()
        |> Translation.add({"example.erl", core})
        |> Translation.translate(:example, [{:entry, 1}])
      end
    end

    test "raises on unsupported Core" do
      core =
        cerl("""
        -module(example).
        -export([entry/1]).
        entry(X) -> 1.5.
        """)

      error =
        assert_raise CompileError, fn ->
          Translation.translate(
            Translation.new() |> Translation.add({"example.erl", core}),
            :example,
            [{:entry, 1}]
          )
        end

      assert %CompileError{file: "example.erl", line: 3} = error
      assert Exception.message(error) =~ "example.erl:3: unsupported Core expression:"
      assert error.description =~ "unsupported Core expression:"
      assert error.description =~ "1.5"
    end

    test "falls back to the function line for compiler-generated NIF primops" do
      core =
        cerl("""
        -module(example).
        -export([entry/0]).
        entry() -> erlang:load_nif("example_nif", 0).
        """)

      error =
        assert_raise CompileError, fn ->
          Translation.new()
          |> Translation.add({"example.erl", core})
          |> Translation.translate(:example, [{:entry, 0}])
        end

      assert %CompileError{file: "example.erl", line: 3} = error

      assert error.description ==
               "unsupported Core expression:\n    \n    primop 'nif_start'\n        ()"
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
                     Translation.new()
                     |> Translation.add({"caller.erl", caller})
                     |> Translation.translate(:a_caller, [{:entry, 1}])
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
        Translation.new()
        |> Translation.add({"caller.erl", caller})
        |> Translation.add({"other.erl", missing})
        |> Translation.translate(:caller, [{:entry, 1}])
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
                     Translation.new()
                     |> Translation.add({"first.erl", first})
                     |> Translation.add({"second.erl", second})
                     |> Translation.translate(:first, [{:entry, 1}])
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
          Translation.new()
          |> Translation.add({"example.erl", core})
          |> Translation.translate(:example, [{:entry, 1}])
        end

      assert %CompileError{file: "foo", line: 4} = error
    end
  end

  describe "cache" do
    @describetag :cache
    @describetag :tmp_dir

    test "reuses verified files and invalidates dependents when their input changes", %{
      tmp_dir: cache_dir
    } do
      dependent =
        cerl("""
        -module(cached_dependent).
        -export([ensures/0]).
        -law \#{name => {law, []}, ensures => ensures}.
        -proof ~"rfl".
        ensures() -> cached_source:value().
        """)

      unrelated =
        cerl("""
        -module(cached_unrelated).
        -export([value/0]).
        value() -> true.
        """)

      assemble = fn value ->
        source =
          cerl("""
          -module(cached_source).
          -export([value/0]).
          value() -> #{value}.
          """)

        Translation.new()
        |> Translation.add({"source.erl", source})
        |> Translation.add({"dependent.erl", dependent})
        |> Translation.add({"unrelated.erl", unrelated})
        |> Translation.verify(:cached_dependent)
        |> Translation.translate(:cached_unrelated, [{:value, 0}])
        |> Translation.assemble()
      end

      files = assemble.(true)

      request = %{
        "command" => "verify",
        "version" => "1.0",
        "cache_dir" => cache_dir,
        "files" => files
      }

      lean_dir = Path.expand("../../Lean", __DIR__)
      cold = Lynx.Commands.runner!(lean_dir, request)
      assert [_, cold_unrelated, _] = cold
      assert Enum.all?(cold, &match?(%{"status" => "ok", "cached" => false}, &1))

      changed = assemble.(false)
      assert [source, unrelated, dependent] = files
      assert [changed_source, ^unrelated, changed_dependent] = changed
      refute source["cache_key"] == changed_source["cache_key"]
      refute dependent["cache_key"] == changed_dependent["cache_key"]
      changed_request = Map.put(request, "files", changed)

      assert [
               %{"status" => "ok", "cached" => false},
               %{"status" => "ok", "cached" => true} = warm_unrelated,
               %{"status" => "error", "cached" => false}
             ] = Lynx.Commands.runner!(lean_dir, changed_request)

      assert Map.drop(cold_unrelated, ["cached", "time_ms"]) ==
               Map.drop(warm_unrelated, ["cached", "time_ms"])

      # Failed proofs must not leave reusable artifacts on disk.
      assert Path.wildcard(
               Path.join([cache_dir, "lean-*", changed_dependent["cache_key"], "result.json"])
             ) == []
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

    assert {:ok, _module, core, _warnings} =
             :compile.forms(forms, [:to_core, :return_errors, :return_warnings])

    core
  end
end
