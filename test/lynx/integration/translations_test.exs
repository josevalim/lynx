defmodule Lynx.Integration.TranslationTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../../Lean", __DIR__)
  @translations_dir Path.expand("../../fixtures/translations", __DIR__)

  @tag timeout: to_timeout(minute: 10)
  test "translates all Erlang fixtures to verified Lean source" do
    fixtures = Path.wildcard(Path.join(@translations_dir, "*.erl"))
    assert fixtures != []

    for fixture <- fixtures do
      source = "../test/fixtures/translations/#{Path.basename(fixture)}"

      # Keep compilation and Core extraction here until there is a translation pipeline.
      # The source annotation is relative to the Lean project, where the runner executes.
      assert {:ok, module, beam} =
               :compile.file(String.to_charlist(fixture), [
                 :binary,
                 :debug_info,
                 :return_errors,
                 {:source, String.to_charlist(source)}
               ])

      assert {:ok, {^module, [debug_info: {:debug_info_v1, backend, data}]}} =
               :beam_lib.chunks(beam, [:debug_info])

      assert {:ok, core} = backend.debug_info(:core_v1, module, data, [])
      assert {:ok, commands} = :lynx_core_to_leanj.translate(core)

      request = %{"version" => "1.0", "files" => %{source => commands}}

      assert request == JSON.decode!(File.read!(Path.rootname(fixture) <> ".json")),
             "translated output does not match #{fixture}"

      json = JSON.encode!(request)
      expected = File.read!(Path.rootname(fixture) <> ".lean")

      assert Lynx.Commands.runner!(@lean_dir, "render", json) == %{
               "status" => "ok",
               "files" => %{source => expected}
             },
             "rendered output does not match #{fixture}"
  end
end
