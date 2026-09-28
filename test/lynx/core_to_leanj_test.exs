defmodule Lynx.CoreToLeanjTest do
  use ExUnit.Case, async: true

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
end
