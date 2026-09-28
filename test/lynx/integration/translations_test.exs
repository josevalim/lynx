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

      {module, core} = core(fixture, source)

      exports =
        core
        |> :cerl.module_exports()
        |> Enum.map(&:cerl.var_name/1)
        |> Kernel.--([{:module_info, 0}, {:module_info, 1}])

      files =
        Lynx.Translation.new([{source, core}])
        |> Lynx.Translation.add(module, exports)
        |> Lynx.Translation.assemble()

      request = %{"version" => "1.0", "files" => files}

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
end
