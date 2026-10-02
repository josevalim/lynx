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

    laws =
      for {key, value} <- :cerl.module_attrs(core),
          :cerl.atom_val(key) == :law,
          %{name: {name, params}} <- :cerl.concrete(value),
          do: {name, length(params)}

    files =
      Lynx.Translation.new([{source, core}])
      |> Lynx.Translation.add(module, exports ++ laws)
      |> Lynx.Translation.assemble()

    assert %{"version" => "1.0", "files" => expected_files} =
             JSON.decode!(File.read!(Path.rootname(fixture) <> ".json"))

    assert length(files) == length(expected_files)

    for {left_file, right_file} <- Enum.zip(files, expected_files) do
      # OTP dependencies have version-specific source locations.
      {left_file, right_file} =
        if left_file["file"] == source do
          {left_file, right_file}
        else
          {without_spans(left_file), without_spans(right_file)}
        end

      left_file = Map.drop(left_file, ["file", "cache_key"])
      right_file = Map.drop(right_file, ["file", "cache_key"])
      assert left_file == right_file
    end

    request = %{"command" => "verify", "version" => "1.0", "files" => files}
    updates = Lynx.Commands.runner!(@lean_dir, request)
    assert length(updates) == length(files)

    for {file, update} <- Enum.zip(files, updates) do
      assert %{
               "status" => "ok",
               "module" => module,
               "source" => left_file,
               "time_ms" => elapsed,
               "diagnostics" => []
             } = update

      assert module == file["module"]
      assert is_integer(elapsed) and elapsed >= 0
      path = Path.rootname(fixture) <> "." <> module <> ".lean"
      right_file = File.read!(path)
      assert left_file == right_file
    end
  end

  defp without_spans(value) when is_map(value) do
    value
    |> Map.delete("span")
    |> Map.new(fn {key, value} -> {key, without_spans(value)} end)
  end

  defp without_spans(value) when is_list(value),
    do: Enum.map(value, &without_spans/1)

  defp without_spans(value), do: value

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
