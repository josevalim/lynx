defmodule Lynx.Integration.TranslationTest do
  use ExUnit.Case

  @lean_dir Path.expand("../../../Lean", __DIR__)
  @translations_dir Path.expand("../../fixtures/translations", __DIR__)

  @tag timeout: to_timeout(minute: 10)
  test "translates all Erlang fixtures to verified Lean source" do
    fixtures = Path.wildcard(Path.join(@translations_dir, "*.erl"))
    assert fixtures != []

    Enum.each(fixtures, fn fixture ->
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

      expected =
        Map.new(files, fn file ->
          suffix = if file["module"] == "Erlang.program", do: ".program.lean", else: ".lean"
          {file["file"], File.read!(Path.rootname(fixture) <> suffix)}
        end)

      rendered = Lynx.Commands.runner!(@lean_dir, Map.put(request, "command", "render"))

      assert rendered == %{"status" => "ok", "files" => expected},
             "rendered output does not match #{fixture}"
    end)
  end

  defp core(fixture, source) do
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
    {module, core}
  end
end
