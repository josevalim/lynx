defmodule Lynx.Integration.TranslationTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../../Lean", __DIR__)
  @translations_dir Path.expand("../../fixtures/translations", __DIR__)

  for fixture <- Path.wildcard(Path.join(@translations_dir, "*.erl")) do
    @tag timeout: to_timeout(minute: 10)
    test "translates #{Path.basename(fixture)}" do
      check_translation(unquote(fixture))
    end
  end

  defp check_translation(fixture) do
    source = "../test/fixtures/translations/#{Path.basename(fixture)}"
    {module, core} = core(fixture, source)

    exports =
      core
      |> :cerl.module_exports()
      |> Enum.map(&:cerl.var_name/1)
      |> Kernel.--([{:module_info, 0}, {:module_info, 1}])

    laws = for {name, {:law, _}} <- :lynx_core_to_leanj.to_definitions(core), do: name

    files =
      Lynx.Translation.new([{source, core}])
      |> Lynx.Translation.add(module, exports ++ laws)
      |> Lynx.Translation.assemble()

    assert %{"version" => "1.0", "files" => expected_files} =
             JSON.decode!(File.read!(Path.rootname(fixture) <> ".json"))

    assert length(files) == length(expected_files)

    for {left_file, right_file} <- Enum.zip(files, expected_files) do
      assert left_file == right_file
    end

    expected =
      Map.new(files, fn file ->
        suffix =
          if file["module"] == "Erlang." <> Path.basename(fixture, Path.extname(fixture)) do
            ".lean"
          else
            "." <> file["module"] <> ".lean"
          end

        {file["file"], File.read!(Path.rootname(fixture) <> suffix)}
      end)

    request = %{"command" => "render", "version" => "1.0", "files" => files}
    assert %{"status" => "ok", "files" => rendered} = Lynx.Commands.runner!(@lean_dir, request)
    assert map_size(rendered) == map_size(expected)

    for {path, right_file} <- expected do
      assert %{^path => left_file} = rendered
      assert left_file == right_file
    end
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
