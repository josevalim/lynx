defmodule Lynx.CoreToLeanjTest do
  use ExUnit.Case, async: true

  test "clusters cycles separately and emits dependencies before callers" do
    body =
      :cerl.c_let(
        [:cerl.c_var(:Y)],
        call(:odd),
        :cerl.c_case(:cerl.c_var(:Y), [
          :cerl.c_clause([:cerl.c_nil()], call(:first)),
          :cerl.c_clause([:cerl.c_var(:Other)], call(:even))
        ])
      )

    core =
      :cerl.c_module(:cerl.c_atom(:example), [], [
        definition(:caller, body),
        definition(:odd, call(:even)),
        definition(:even, call(:odd)),
        definition(:first, call(:second)),
        definition(:second, call(:third)),
        definition(:third, call(:first)),
        definition(:identity, :cerl.c_var(0)),
        definition(:self, call(:self))
      ])

    assert {:ok, commands} = :lynx_core_to_leanj.translate(core)

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

  test "ignores generated module_info definitions" do
    core =
      :cerl.c_module(:cerl.c_atom(:example), [], [
        {:cerl.c_fname(:module_info, 0), :cerl.c_fun([], :cerl.c_atom(:unused))},
        definition(:module_info, :cerl.c_var(0))
      ])

    assert {:ok, []} = :lynx_core_to_leanj.translate(core)
  end

  test "returns unsupported Core as printable text" do
    call = :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:abs), [:cerl.c_int(-1)])

    core =
      :cerl.c_module(:cerl.c_atom(:example), [], [
        {:cerl.c_fname(:example, 0), :cerl.c_fun([], call)}
      ])

    assert {:unsupported_core, text} = :lynx_core_to_leanj.translate(core)
    assert is_binary(text)
    assert String.valid?(text)
    assert text =~ "call 'erlang':'abs'"
    assert text =~ "-1"
  end

  defp definition(name, body), do: {:cerl.c_fname(name, 1), :cerl.c_fun([:cerl.c_var(0)], body)}
  defp call(name), do: :cerl.c_apply(:cerl.c_fname(name, 1), [:cerl.c_var(0)])
end
