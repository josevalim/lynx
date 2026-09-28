defmodule Lynx.CoreToLeanjTest do
  use ExUnit.Case, async: true

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
    assert functions[{:odd, 1}].local_calls == [{:even, 1}]
    assert functions[{:even, 1}].local_calls == [{:odd, 1}]
    assert functions[{:helper, 1}].local_calls == []

    for {{name, 1}, %{translation: translation}} <- functions do
      assert %{"kind" => "def", "name" => translated_name} = translation
      assert translated_name == "«#{name}/1»"
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
    assert functions[{:first, 1}].local_calls == []
    assert functions[{:second, 1}].local_calls == []

    assert {:ok, ^functions, []} = translate(definitions, functions)
  end

  test "translates qualified calls to the current module as local calls" do
    qualified = :cerl.c_call(:cerl.c_atom(:example), :cerl.c_atom(:helper), [:cerl.c_var(0)])
    definitions = definitions([definition(:entry, qualified), definition(:helper, qualified)])

    assert {:ok, functions, []} = translate(definitions)

    assert Enum.sort(Map.keys(functions)) == [{:entry, 1}, {:helper, 1}]
    assert functions[{:entry, 1}].local_calls == [{:helper, 1}]
    assert functions[{:helper, 1}].local_calls == []

    for name <- [:entry, :helper] do
      assert functions[{name, 1}].translation["body"]["function"]["name"] == "«helper/1»"
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

    assert {:ok, _, [{:other, :entry, 1, span_anno}]} =
             translate(definitions([definition(:entry, body)]))

    assert span_anno == [{:file, ~c"foo"}, {7, 3}]
  end

  test "qualifies remote function names with Erlang and Elixir namespaces" do
    for {module, expected} <- [
          {:other, "Erlang.other.«entry/1»"},
          {Foo.Bar, "Elixir.Foo.Bar.«entry/1»"}
        ] do
      body = :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])

      assert {:ok, functions, [{^module, :entry, 1, []}]} =
               translate(definitions([definition(:entry, body)]))

      assert functions[{:entry, 1}].translation["body"]["function"]["name"] == expected
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
    refute functions[{:entry, 1}].pure
    assert functions[{:helper, 1}].pure
    assert calls == [{:pure, :entry, 1, []}, {:impure, :entry, 1, []}]
  end

  defp translate(definitions, translated \\ %{}, purity \\ %{}) do
    callback = fn calls, module, function, arity, span_anno ->
      pure = Map.get(purity, {module, function, arity}, true)
      {:ok, pure, [{module, function, arity, span_anno} | calls]}
    end

    :lynx_core_to_leanj.translate(
      :example,
      definitions,
      [{:entry, 1}],
      translated,
      {[], callback}
    )
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
