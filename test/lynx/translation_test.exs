defmodule Lynx.TranslationTest do
  use ExUnit.Case, async: true

  alias Lynx.Translation

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
      :cerl.c_module(
        :cerl.c_atom(:example),
        Enum.map([:caller, :identity, :self], &:cerl.c_fname(&1, 1)),
        [
          definition(:caller, body),
          definition(:odd, call(:even)),
          definition(:even, call(:odd)),
          definition(:first, call(:second)),
          definition(:second, call(:third)),
          definition(:third, call(:first)),
          definition(:identity, :cerl.c_var(0)),
          definition(:self, call(:self))
        ]
      )

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
      :cerl.c_module(
        :cerl.c_atom(:example),
        [:cerl.c_fname(:module_info, 0), :cerl.c_fname(:module_info, 1)],
        [
          {:cerl.c_fname(:module_info, 0), :cerl.c_fun([], :cerl.c_atom(:unused))},
          definition(:module_info, :cerl.c_var(0))
        ]
      )

    assert %{example: []} =
             Translation.new() |> Translation.add(core, []) |> Translation.assemble()
  end

  test "propagates unsupported Core from an exported function" do
    call = :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:abs), [:cerl.c_int(-1)])

    core =
      :cerl.c_module(:cerl.c_atom(:example), [:cerl.c_fname(:entry, 1)], [
        definition(:entry, call)
      ])

    assert {:unsupported_core, text} = Translation.add(Translation.new(), core, [{:entry, 1}])
    assert text =~ "call 'erlang':'abs'"
  end

  test "accumulates roots across modules and reuses each module's translations" do
    first =
      :cerl.c_module(:cerl.c_atom(:first), [], [
        definition(:entry, call(:helper)),
        definition(:helper, :cerl.c_var(0)),
        definition(:extra, :cerl.c_int(1))
      ])

    second =
      :cerl.c_module(:cerl.c_atom(:second), [], [
        definition(:entry, :cerl.c_int(2))
      ])

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

  defp definition(name, body), do: {:cerl.c_fname(name, 1), :cerl.c_fun([:cerl.c_var(0)], body)}
  defp call(name), do: :cerl.c_apply(:cerl.c_fname(name, 1), [:cerl.c_var(0)])
end
