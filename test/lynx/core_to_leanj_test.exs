defmodule Lynx.CoreToLeanjTest do
  use ExUnit.Case, async: true

  test "translates Core values into separate match expressions and patterns" do
    body =
      :cerl.c_case(:cerl.c_values([:cerl.c_var(0), :cerl.c_nil()]), [
        :cerl.c_clause([:cerl.c_var(:X), :cerl.c_nil()], :cerl.c_var(:X))
      ])

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))

    assert %{
             "body" => %{
               "kind" => "match",
               "expressions" => [
                 %{"kind" => "var", "name" => 0},
                 %{"kind" => "nil"}
               ],
               "cases" => [
                 %{
                   "patterns" => [
                     %{"kind" => "var", "name" => "X"},
                     %{"kind" => "nil"}
                   ]
                 }
               ]
             }
           } = functions[{:entry, 1}].translation
  end

  test "recursively translates reachable callees and keeps each function's calls separate" do
    body =
      :cerl.c_let(
        [:cerl.c_var(:Y)],
        call(:odd),
        :cerl.c_case(:cerl.c_var(:Y), [
          :cerl.c_clause([:cerl.c_nil()], call(:helper)),
          :cerl.c_clause([:cerl.c_var(:Other)], call(:even))
        ])
      )

    definitions =
      definitions([
        definition(:entry, body),
        definition(:odd, call(:even)),
        definition(:even, call(:odd)),
        definition(:helper, call(:helper)),
        definition(:unused, unsupported_call())
      ])

    assert {:ok, functions, []} = translate(definitions)

    assert Enum.sort(Map.keys(functions)) == [{:entry, 1}, {:even, 1}, {:helper, 1}, {:odd, 1}]
    assert Enum.sort(functions[{:entry, 1}].local_calls) == [{:even, 1}, {:helper, 1}, {:odd, 1}]

    assert %{
             {:odd, 1} => %{local_calls: [{:even, 1}]},
             {:even, 1} => %{local_calls: [{:odd, 1}]},
             {:helper, 1} => %{local_calls: []}
           } = functions

    for {{name, 1}, %{translation: translation}} <- functions do
      expected = Atom.to_string(name)
      assert %{"kind" => "def", "name" => ^expected} = translation
    end
  end

  test "threads the remote callback context through local functions and reuses translations" do
    remote = fn module ->
      :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])
    end

    definitions =
      definitions([
        definition(:entry, :cerl.c_let([:cerl.c_var(:Y)], call(:first), call(:second))),
        definition(:first, remote.(:one)),
        definition(:second, remote.(:two))
      ])

    assert {:ok, functions, calls} = translate(definitions)

    assert calls == [{:two, :entry, 1, []}, {:one, :entry, 1, []}]
    assert Enum.sort(functions[{:entry, 1}].local_calls) == [{:first, 1}, {:second, 1}]

    assert %{
             {:first, 1} => %{local_calls: []},
             {:second, 1} => %{local_calls: []}
           } = functions

    assert {:ok, ^functions, []} = translate(definitions, functions)
  end

  test "translates qualified calls to the current module as local calls" do
    qualified = :cerl.c_call(:cerl.c_atom(:example), :cerl.c_atom(:helper), [:cerl.c_var(0)])
    definitions = definitions([definition(:entry, qualified), definition(:helper, qualified)])

    assert {:ok, functions, []} = translate(definitions)

    assert Enum.sort(Map.keys(functions)) == [{:entry, 1}, {:helper, 1}]

    assert %{
             {:entry, 1} => %{local_calls: [{:helper, 1}]},
             {:helper, 1} => %{local_calls: []}
           } = functions

    for name <- [:entry, :helper] do
      assert %{"body" => %{"kind" => "local_call", "name" => "helper"}} =
               functions[{name, 1}].translation
    end
  end

  test "passes raw file and position annotations to remote calls" do
    body =
      :cerl.ann_c_call(
        [{:file, ~c"foo"}, {7, 3}],
        :cerl.c_atom(:other),
        :cerl.c_atom(:entry),
        [:cerl.c_var(0)]
      )

    assert {:ok, _, [{:other, :entry, 1, [{:file, ~c"foo"}, {7, 3}]}]} =
             translate(definitions([definition(:entry, body)]))
  end

  test "qualifies remote modules and preserves raw function names" do
    for {module, expected} <- [
          {:other, "Erlang.other"},
          {Foo.Bar, "Elixir.Foo.Bar"}
        ] do
      body = :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])

      assert {:ok, functions, [{^module, :entry, 1, []}]} =
               translate(definitions([definition(:entry, body)]))

      assert %{"body" => %{"kind" => "remote_call", "module" => ^expected, "name" => "entry"}} =
               functions[{:entry, 1}].translation
    end
  end

  test "accumulates remote impurity without leaking it between functions" do
    remote = fn module ->
      :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])
    end

    defs =
      definitions([
        definition(:entry, :cerl.c_let([:cerl.c_var(:Y)], remote.(:impure), call(:helper))),
        definition(:helper, remote.(:pure))
      ])

    assert {:ok, functions, calls} = translate(defs, %{}, %{{:impure, :entry, 1} => false})

    assert %{
             {:entry, 1} => %{pure: false},
             {:helper, 1} => %{pure: true}
           } = functions

    assert calls == [{:pure, :entry, 1, []}, {:impure, :entry, 1, []}]
  end

  test "extracts paired law attributes and calls their ordinary predicate helpers" do
    core =
      :cerl.c_module(
        :cerl.c_atom(:example),
        [],
        [
          {:cerl.c_atom(:law),
           :cerl.ann_abstract([10], [
             %{name: {:entry, [:x]}, requires: :requirement, ensures: :expected, indentation: 4}
           ])},
          {:cerl.c_atom(:proof), :cerl.ann_abstract([11], ["rfl"])}
        ],
        [definition(:requirement, :cerl.c_atom(true)), definition(:expected, :cerl.c_atom(true))]
      )

    definitions = :lynx_core_to_leanj.to_definitions(core)
    assert {:law, _} = definitions[{:entry, 1}]
    assert {:function, _} = definitions[{:requirement, 1}]
    assert {:ok, functions, []} = translate(definitions)
    assert Enum.sort(functions[{:entry, 1}].local_calls) == [{:expected, 1}, {:requirement, 1}]

    assert %{
             "kind" => "theorem",
             "name" => "entry",
             "span" => [10],
             "params" => ["x"],
             "requires" => "requirement",
             "ensures" => "expected",
             "proof" => %{"source" => "rfl", "indentation" => 4, "span" => [12]}
           } == functions[{:entry, 1}].translation
  end

  describe "to_definition" do
    test "extracts ordinary functions and ignores unrelated attributes" do
      defs = [definition(:entry, :cerl.c_atom(true))]
      [{_, fun}] = defs
      core = core([attribute(:other, [:value], [2])], defs)
      assert %{{:entry, 1} => {:function, ^fun}} = :lynx_core_to_leanj.to_definitions(core)
    end

    test "extracts a law with optional requires and a binary proof" do
      core = law_core(%{name: {:entry, [:x]}, ensures: :expected}, ["exact hé"])

      assert %{
               {:entry, 1} => {:law, law},
               {:expected, 1} => {:function, _}
             } = :lynx_core_to_leanj.to_definitions(core)

      assert law == %{
               name: {:entry, [:x]},
               ensures: :expected,
               anno: [10],
               proof: %{"source" => "exact hé", "indentation" => 0, "span" => [12]}
             }
    end

    test "extracts multiple paired laws with a binary proof and explicit indentation" do
      law = %{name: {:entry, [:x]}, requires: :requirement, ensures: :expected, indentation: 4}
      core = law_core(law, ["rfl"])

      attrs =
        :cerl.module_attrs(core) ++
          [
            attribute(:law, [%{name: {:second, [:b, :a]}, ensures: :expected}], [14]),
            attribute(:proof, ["rfl"], [{15, 8}])
          ]

      core = core(attrs, :cerl.module_defs(core))

      assert %{
               {:entry, 1} =>
                 {:law,
                  %{
                    requires: :requirement,
                    proof: %{"source" => "rfl", "indentation" => 4, "span" => [12]}
                  }},
               {:second, 2} => {:law, %{name: {:second, [:b, :a]}, proof: %{"span" => [16]}}}
             } = :lynx_core_to_leanj.to_definitions(core)
    end

    test "reports missing or misplaced proofs at the offending attribute" do
      law = attribute(:law, [%{name: {:entry, [:x]}, ensures: :expected}], [10])
      proof = attribute(:proof, ["rfl"], [11])
      other = attribute(:other, [:value], [12])

      for attrs <- [[law], [law, other, proof]] do
        assert {:error, [10], "proof must immediately follow law"} ==
                 :lynx_core_to_leanj.to_definitions(core(attrs))
      end

      assert {:error, [11], "proof without preceding law"} ==
               :lynx_core_to_leanj.to_definitions(core([proof]))
    end

    test "reports malformed law descriptors with their original annotations" do
      anno = [{:file, ~c"law.erl"}, {10, 2}]
      reason = "law must contain name {atom, parameters} and ensures function name"

      for law <- [
            %{},
            %{name: {:entry, [:x]}},
            %{name: {:entry, -1}, ensures: :expected},
            %{name: {:entry, 1}, ensures: :expected},
            %{name: {"entry", [:x]}, ensures: :expected},
            %{name: {:entry, [:x]}, ensures: "expected"}
          ] do
        core = core([attribute(:law, [law], anno), attribute(:proof, ["rfl"], [11])])
        assert {:error, ^anno, ^reason} = :lynx_core_to_leanj.to_definitions(core)
      end
    end

    test "requires unique atom parameter names" do
      for {params, reason} <- [
            {["x"], "law parameters must be atoms"},
            {[:x, :x], "law parameters must be unique"}
          ] do
        assert {:error, [10], ^reason} =
                 :lynx_core_to_leanj.to_definitions(
                   law_core(%{name: {:entry, params}, ensures: :expected})
                 )
      end
    end

    test "validates requires names and indentation" do
      for {extra, reason} <- [
            {%{requires: "requirement"}, "law requires must be a function name"},
            {%{indentation: -1}, "law indentation must be a nonnegative integer"},
            {%{indentation: 1.5}, "law indentation must be a nonnegative integer"}
          ] do
        law = Map.merge(%{name: {:entry, [:x]}, ensures: :expected}, extra)
        assert {:error, [10], ^reason} = :lynx_core_to_leanj.to_definitions(law_core(law))
      end
    end

    test "requires binary proofs and reports errors at the proof attribute" do
      for proof <- [~c"rfl", [:not_text], [42]] do
        assert {:error, [11], "proof must be a binary"} ==
                 :lynx_core_to_leanj.to_definitions(
                   law_core(%{name: {:entry, [:x]}, ensures: :expected}, proof)
                 )
      end
    end

    test "a law replaces an ordinary function with the same name and arity" do
      original = law_core(%{name: {:entry, [:x]}, ensures: :expected})

      core =
        core(
          :cerl.module_attrs(original),
          [definition(:entry, :cerl.c_atom(true)) | :cerl.module_defs(original)]
        )

      assert %{{:entry, 1} => {:law, %{ensures: :expected}}} =
               :lynx_core_to_leanj.to_definitions(core)
    end
  end

  test "returns annotated binary reasons for unsupported Core during translation" do
    anno = [{:file, ~c"example.erl"}, {7, 3}]
    body = :cerl.ann_c_tuple(anno, [:cerl.c_atom(:ok), :cerl.c_var(0)])
    assert {:error, ^anno, reason} = translate(definitions([definition(:entry, body)]))
    assert reason =~ "unsupported Core expression:"
    assert reason =~ "'ok'"
  end

  test "translates laws without a requires helper" do
    definitions =
      :lynx_core_to_leanj.to_definitions(law_core(%{name: {:entry, [:x]}, ensures: :expected}))

    assert {:ok, %{{:entry, 1} => %{local_calls: [{:expected, 1}], translation: law}}, []} =
             translate(definitions)

    assert law == %{
             "kind" => "theorem",
             "name" => "entry",
             "params" => ["x"],
             "span" => [10],
             "ensures" => "expected",
             "proof" => %{"source" => "rfl", "indentation" => 0, "span" => [12]}
           }
  end

  defp core(attrs, defs \\ []), do: :cerl.c_module(:cerl.c_atom(:example), [], attrs, defs)
  defp attribute(name, value, anno), do: {:cerl.c_atom(name), :cerl.ann_abstract(anno, value)}

  defp law_core(law, proof \\ ["rfl"]) do
    core(
      [attribute(:law, [law], [10]), attribute(:proof, proof, [11])],
      [definition(:requirement, :cerl.c_atom(true)), definition(:expected, :cerl.c_atom(true))]
    )
  end

  defp translate(definitions, translated \\ %{}, pure \\ %{}) do
    callback = fn calls, module, function, arity, span_anno, funs ->
      if module == :example do
        :local
      else
        pure = Map.get(pure, {module, function, arity}, true)
        {pure, funs, [{module, function, arity, span_anno} | calls]}
      end
    end

    case :lynx_core_to_leanj.translate(
           :example,
           definitions,
           [{:entry, 1}],
           translated,
           %{},
           {[], callback}
         ) do
      {:ok, functions, _funs, calls} -> {:ok, functions, calls}
      {:error, _, _} = error -> error
    end
  end

  defp definitions(defs) do
    defs
    |> then(&:cerl.c_module(:cerl.c_atom(:example), [], &1))
    |> :lynx_core_to_leanj.to_definitions()
  end

  defp definition(name, body), do: {:cerl.c_fname(name, 1), :cerl.c_fun([:cerl.c_var(0)], body)}
  defp call(name), do: :cerl.c_apply(:cerl.c_fname(name, 1), [:cerl.c_var(0)])

  defp unsupported_call,
    do: :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:abs), [:cerl.c_int(-1)])
end
