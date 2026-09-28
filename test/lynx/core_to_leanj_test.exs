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

    assert {:ok, functions} = :lynx_core_to_leanj.translate(definitions, [{:entry, 1}], %{})
    assert Enum.sort(Map.keys(functions)) == [{:entry, 1}, {:even, 1}, {:helper, 1}, {:odd, 1}]
    assert Enum.sort(functions[{:entry, 1}].local_calls) == [{:even, 1}, {:helper, 1}, {:odd, 1}]
    assert functions[{:odd, 1}].local_calls == [{:even, 1}]
    assert functions[{:even, 1}].local_calls == [{:odd, 1}]
    assert functions[{:helper, 1}].local_calls == []

    for {{name, 1}, %{translation: translation}} <- functions do
      assert %{"kind" => "def", "name" => translated_name} = translation
      assert translated_name == "#{name}_1"
    end
  end

  test "extends an existing map with additional roots" do
    definitions =
      definitions([
        definition(:odd, call(:even)),
        definition(:even, call(:odd)),
        definition(:identity, :cerl.c_var(0))
      ])

    assert {:ok, initial} = :lynx_core_to_leanj.translate(definitions, [{:odd, 1}], %{})
    assert map_size(initial) == 2

    assert {:ok, extended} =
             :lynx_core_to_leanj.translate(definitions, [{:identity, 1}, {:odd, 1}], initial)

    assert map_size(extended) == 3
    assert Map.take(extended, Map.keys(initial)) == initial
    assert {:ok, ^extended} = :lynx_core_to_leanj.translate(definitions, [], extended)
  end

  test "returns unsupported Core from a reachable callee as printable text" do
    definitions =
      definitions([definition(:entry, call(:helper)), definition(:helper, unsupported_call())])

    assert {:unsupported_core, text} =
             :lynx_core_to_leanj.translate(definitions, [{:entry, 1}], %{})

    assert is_binary(text)
    assert String.valid?(text)
    assert text =~ "call 'erlang':'abs'"
    assert text =~ "-1"
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
