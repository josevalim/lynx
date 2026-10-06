defmodule Lynx.CoreToLeanjTest do
  use ExUnit.Case, async: true

  test "allocates distinct generated message binders for timeout-only receives" do
    receive_after = fn action ->
      loop = :cerl.c_fname(:receive_loop, 0)
      expired = :cerl.c_var(:expired)

      wait =
        :cerl.c_let(
          [expired],
          :cerl.c_primop(:cerl.c_atom(:recv_wait_timeout), [:cerl.c_int(0)]),
          :cerl.c_case(expired, [
            :cerl.c_clause([:cerl.c_atom(true)], action),
            :cerl.c_clause([:cerl.c_atom(false)], :cerl.c_apply(loop, []))
          ])
        )

      :cerl.c_letrec([{loop, :cerl.c_fun([], wait)}], :cerl.c_apply(loop, []))
    end

    body =
      :cerl.c_seq(
        receive_after.(:cerl.c_atom(:ok)),
        receive_after.(:cerl.c_atom(:done))
      )

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))
    assert functions[{:entry, 1}].pure == false

    assert %{
             "body" => %{
               "kind" => "bind",
               "computation" => %{
                 "kind" => "receive",
                 "message" => %{"name" => %{"generated" => 0}},
                 "cases" => []
               },
               "body" => %{
                 "kind" => "receive",
                 "message" => %{"name" => %{"generated" => 1}},
                 "cases" => []
               }
             }
           } = functions[{:entry, 1}].translation
  end

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

  test "translates map construction" do
    key = :cerl.c_var(0)

    body =
      :cerl.c_map([
        :cerl.c_map_pair(key, :cerl.c_int(1)),
        :cerl.c_map_pair(key, :cerl.c_var(0))
      ])

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))
    assert functions[{:entry, 1}].pure

    assert %{
             "kind" => "return",
             "values" => [%{"kind" => "map", "entries" => [first, last]}]
           } = functions[{:entry, 1}].translation["body"]

    assert last["key"] == first["key"]
    assert last["value"] == %{"kind" => "var", "name" => 0, "span" => []}
    assert first["value"] == %{"kind" => "integer", "value" => 1, "span" => []}
  end

  test "marks fallthrough solely from whether the Core guard is literally true" do
    guards = [
      :cerl.c_atom(true),
      :cerl.c_atom(false),
      :cerl.c_var(0),
      :cerl.c_seq(:cerl.c_atom(:ok), :cerl.c_atom(true))
    ]

    body =
      :cerl.c_case(
        :cerl.c_var(0),
        Enum.map(guards, fn guard ->
          :cerl.c_clause([:cerl.c_var(:X)], guard, :cerl.c_var(:X))
        end)
      )

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))
    cases = functions[{:entry, 1}].translation["body"]["cases"]
    assert Enum.map(cases, & &1["nest"]) == [false, true, true, true]
    refute Map.has_key?(hd(cases), "guard")
    assert Enum.all?(tl(cases), &Map.has_key?(&1, "guard"))
  end

  test "translates zero and multiple Core try values" do
    x = :cerl.c_var(:x)
    a = :cerl.c_var(:a)
    b = :cerl.c_var(:b)
    evars = Enum.map([:class, :reason, :trace], &:cerl.c_var/1)
    empty = :cerl.c_var({:empty, 0})
    pair = :cerl.c_var({:pair, 1})
    bound = :cerl.c_var({:bound, 1})
    empty_bound = :cerl.c_var({:empty_bound, 0})
    matched = :cerl.c_var({:matched, 1})
    returned = :cerl.c_values([x, :cerl.c_atom(:second)])

    protected =
      :cerl.c_try(
        returned,
        [a, b],
        :cerl.c_values([b, a]),
        evars,
        :cerl.c_values([:cerl.c_atom(:caught), :cerl.c_atom(:caught)])
      )

    core =
      :cerl.c_module(:cerl.c_atom(:core_try), [empty, pair, bound, empty_bound, matched], [], [
        {empty,
         :cerl.c_fun(
           [],
           :cerl.c_try(
             :cerl.c_values([]),
             [],
             :cerl.c_atom(:empty),
             Enum.take(evars, 2),
             :cerl.c_atom(:caught)
           )
         )},
        {pair,
         :cerl.c_fun(
           [x],
           :cerl.c_try(returned, [a, b], :cerl.c_tuple([b, a]), evars, :cerl.c_atom(:caught))
         )},
        {bound, :cerl.c_fun([x], :cerl.c_let([a, b], protected, :cerl.c_tuple([a, b])))},
        {empty_bound, :cerl.c_fun([], :cerl.c_let([], :cerl.c_values([]), :cerl.c_atom(:empty)))},
        {matched,
         :cerl.c_fun(
           [x],
           :cerl.c_case(protected, [
             :cerl.c_clause([a, b], :cerl.c_tuple([a, b]))
           ])
         )}
      ])

    roots = [{:empty, 0}, {:pair, 1}, {:bound, 1}, {:empty_bound, 0}, {:matched, 1}]
    callback = fn _, _, _, _, _, _ -> flunk("unexpected remote call") end

    assert {:ok, functions, %{}, []} =
             :lynx_core_to_leanj.translate(
               :core_try,
               :lynx_core_to_leanj.to_definitions(core),
               roots,
               %{},
               %{},
               {[], callback}
             )

    by_name =
      Map.new(functions, fn {{name, _}, function} ->
        {Atom.to_string(name), function.translation}
      end)

    assert %{
             "kind" => "try",
             "vars" => [],
             "computation" => %{"kind" => "return", "values" => []},
             "exception_vars" => [_, _]
           } = by_name["empty"]["body"]

    assert %{
             "kind" => "try",
             "vars" => [_, _],
             "computation" => %{"kind" => "return", "values" => [_, _]},
             "exception_vars" => [_, _, _]
           } = by_name["pair"]["body"]

    assert %{
             "kind" => "bind",
             "vars" => [],
             "computation" => %{"kind" => "return", "values" => []}
           } = by_name["empty_bound"]["body"]

    assert %{
             "kind" => "bind",
             "vars" => [_, _],
             "computation" => %{
               "kind" => "try",
               "computation" => %{"kind" => "return", "values" => [_, _]}
             }
           } = by_name["bound"]["body"]

    assert %{
             "kind" => "bind",
             "vars" => [left, right],
             "body" => %{"kind" => "match", "expressions" => [left, right]}
           } = by_name["matched"]["body"]
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

  test "lowers a case input computation to a bind followed by a match" do
    input = :cerl.c_call(:cerl.c_atom(:other), :cerl.c_atom(:entry), [:cerl.c_var(0)])

    body =
      :cerl.c_case(input, [
        :cerl.c_clause([:cerl.c_atom(true)], :cerl.c_var(0)),
        :cerl.c_clause([:cerl.c_var(:Other)], :cerl.c_atom(false))
      ])

    defs = definitions([definition(:entry, body)])

    assert {:ok, functions, [{:other, :entry, 1, []}]} =
             translate(defs, %{}, %{{:other, :entry, 1} => false})

    assert %{pure: false, local_calls: [], translation: translation} =
             functions[{:entry, 1}]

    assert %{
             "body" => %{
               "kind" => "bind",
               "vars" => [%{"kind" => "var", "name" => name}],
               "computation" => %{"kind" => "remote_call", "name" => "entry"},
               "body" => %{
                 "kind" => "match",
                 "expressions" => [%{"kind" => "var", "name" => name}],
                 "cases" => [_, _]
               }
             }
           } = translation

    assert name == %{"generated" => 0}
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
             %{name: {:entry, [:x]}, requires: :requirement, ensures: :expected}
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
             "proof" => %{"source" => "rfl", "indentation" => 0, "span" => [12]}
           } == functions[{:entry, 1}].translation
  end

  test "uses the law's explicit span instead of the Core attribute's annotations" do
    for {span, expected} <- [{40, [40]}, {{40, 9}, [40, 9]}] do
      definitions =
        law_core(%{name: {:entry, [:x]}, ensures: :expected, span: span})
        |> :lynx_core_to_leanj.to_definitions()

      assert {:ok, functions, []} = translate(definitions)

      assert %{"span" => ^expected, "proof" => %{"span" => [12]}} =
               functions[{:entry, 1}].translation
    end
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

    test "extracts multiple paired laws with binary proofs" do
      law = %{name: {:entry, [:x]}, requires: :requirement, ensures: :expected}
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
                    proof: %{"source" => "rfl", "indentation" => 0, "span" => [12]}
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

    test "validates requires names" do
      law = %{name: {:entry, [:x]}, ensures: :expected, requires: "requirement"}

      assert {:error, [10], "law requires must be a function name"} =
               :lynx_core_to_leanj.to_definitions(law_core(law))
    end

    test "reports invalid law spans at the Core attribute" do
      law = %{name: {:entry, [:x]}, ensures: :expected, span: {40, 0}}

      assert {:error, [10], "law span must be a line or {line, column}"} =
               :lynx_core_to_leanj.to_definitions(law_core(law))
    end

    test "extracts embedded proof metadata with tuple and integer spans" do
      for {span, expected} <- [{{12, 9}, [12, 9]}, {12, [12]}] do
        law = %{
          name: {:entry, [:x]},
          ensures: :expected,
          proof: %{source: "rfl", indentation: 4, span: span}
        }

        core = core([attribute(:law, [law], [10])])

        assert %{
                 {:entry, 1} =>
                   {:law, %{proof: %{"source" => "rfl", "indentation" => 4, "span" => ^expected}}}
               } =
                 :lynx_core_to_leanj.to_definitions(core)
      end
    end

    test "reports invalid embedded proof metadata at the law attribute" do
      for {extra, reason} <- [
            {%{source: ~c"rfl"},
             "embedded proof requires a binary, nonnegative indentation and span"},
            {%{indentation: -1},
             "embedded proof requires a binary, nonnegative indentation and span"},
            {%{span: {12, 0}}, "embedded proof span must be a line or {line, column}"}
          ] do
        law = %{
          name: {:entry, [:x]},
          ensures: :expected,
          proof: Map.merge(%{source: "rfl", indentation: 0, span: 12}, extra)
        }

        assert {:error, [10], ^reason} =
                 :lynx_core_to_leanj.to_definitions(core([attribute(:law, [law], [10])]))
      end
    end

    test "rejects embedded proof metadata at the law root" do
      law = %{name: {:entry, [:x]}, ensures: :expected, proof: "rfl", indentation: 0, span: 12}

      assert {:error, [10], "embedded proof requires a binary, nonnegative indentation and span"} =
               :lynx_core_to_leanj.to_definitions(core([attribute(:law, [law], [10])]))
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
    body = :cerl.ann_abstract(anno, 1.5)
    assert {:error, ^anno, reason} = translate(definitions([definition(:entry, body)]))
    assert reason =~ "unsupported Core expression:"
    assert reason =~ "1.5"
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
