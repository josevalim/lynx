# Run from the project root:
#   mix run test/fixtures/translations/regenerate.exs json
#   mix run test/fixtures/translations/regenerate.exs lean
defmodule Lynx.Fixtures.Regenerate do
  @lean_dir Path.expand("../../../Lean", __DIR__)

  def run(["json"]) do
    for fixture <- Path.wildcard(Path.join(__DIR__, "*.erl")) do
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

      write(
        Path.rootname(fixture) <> ".json",
        JSON.encode!(%{"version" => "1.0", "files" => files}) <> "\n"
      )
    end
  end

  def run(["lean"]) do
    case Lynx.Commands.lake(@lean_dir, ["build", "Lynx", "Erlang"]) do
      {0, _output} -> :ok
      {_status, output} -> Mix.raise("cannot build the Lean runtime:\n#{output}")
    end

    for fixture <- Path.wildcard(Path.join(__DIR__, "*.json")) do
      request = fixture |> File.read!() |> JSON.decode!() |> Map.put("command", "render")
      %{"status" => "ok", "files" => sources} = Lynx.Commands.runner!(@lean_dir, request)

      for file <- request["files"] do
        suffix =
          cond do
            file["module"] == "Erlang." <> Path.basename(fixture, Path.extname(fixture)) ->
              ".lean"

            true ->
              "." <> file["module"] <> ".lean"
          end

        write(Path.rootname(fixture) <> suffix, Map.fetch!(sources, file["file"]))
      end
    end
  end

  def run(_), do: Mix.raise("usage: mix run test/fixtures/translations/regenerate.exs json|lean")

  defp core(fixture, source) do
    {:ok, module, beam} =
      :compile.file(String.to_charlist(fixture), [
        :binary,
        :debug_info,
        :return_errors,
        {:source, String.to_charlist(source)}
      ])

    {:ok, {^module, [debug_info: {:debug_info_v1, backend, data}]}} =
      :beam_lib.chunks(beam, [:debug_info])

    {:ok, core} = backend.debug_info(:core_v1, module, data, [])
    {module, core}
  end

  defp write(path, content) do
    File.write!(path, content)
    IO.puts("Updated #{Path.basename(path)}")
  end
end

Lynx.Fixtures.Regenerate.run(System.argv())
