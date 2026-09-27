defmodule Lynx.CoreToLeanjTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @fixtures_dir Path.expand("../fixtures/translations", __DIR__)
  @source "../test/fixtures/translations/sum.erl"

  @tag timeout: to_timeout(minute: 10)
  test "translates sum from Erlang debug info to verified Lean source" do
    # Keep compilation and Core extraction here until there is a translation pipeline.
    # The source annotation is relative to the Lean project, where the runner executes.
    assert {:ok, :sum, beam} =
             :compile.file(String.to_charlist(Path.join(@fixtures_dir, "sum.erl")), [
               :binary,
               :debug_info,
               :return_errors,
               {:source, String.to_charlist(@source)}
             ])

    assert {:ok, {:sum, [debug_info: {:debug_info_v1, backend, data}]}} =
             :beam_lib.chunks(beam, [:debug_info])

    assert {:ok, core} = backend.debug_info(:core_v1, :sum, data, [])
    assert {:ok, commands} = :lynx_core_to_leanj.translate(core)

    request = %{
      "version" => "1.0",
      "files" => %{@source => commands}
    }

    assert request == JSON.decode!(File.read!(Path.join(@fixtures_dir, "sum.json")))
    json = JSON.encode!(request)

    assert Lynx.Commands.runner!(@lean_dir, "render", json) == %{
             "status" => "ok",
             "files" => %{@source => File.read!(Path.join(@fixtures_dir, "sum.lean"))}
           }

    assert Lynx.Commands.runner!(@lean_dir, "verify", json) == %{
             "status" => "ok",
             "diagnostics" => []
           }
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
end
