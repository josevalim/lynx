defmodule Lynx.Integration.TranslationTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../../Lean", __DIR__)
  @translations_dir Path.expand("../../fixtures/translations", __DIR__)

  @tag timeout: to_timeout(minute: 10)
  test "translates all Erlang fixtures to verified Lean source" do
    fixtures = Path.wildcard(Path.join(@translations_dir, "*.erl"))
    assert fixtures != []

    fixtures
    |> Task.async_stream(
      fn fixture ->
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

        expected = File.read!(Path.rootname(fixture) <> ".lean")
        rendered = Lynx.RunnerPool.command(@lean_dir, Map.put(request, "command", "render"))

        assert rendered == %{"status" => "ok", "files" => %{source => expected}},
               "rendered output does not match #{fixture}"
      end,
      ordered: false,
      timeout: :infinity
    )
    |> Stream.run()
  end

  @tag :tmp_dir
  test "translated closures retain the captures of each instance", %{tmp_dir: tmp_dir} do
    source =
      @translations_dir
      |> Path.join("functions.lean")
      |> File.read!()
      |> String.replace("import Erlang.erlang", """
      import Erlang.erlang
      import all Erlang.erlang.Fun
      import all Erlang.erlang.Guards
      import all Lynx.Term
      import all Lynx.Term.DataTypes
      """)

    checks = """
    example : Erlang.functions.«run/1» (.integer 5) = .ok (.integer 24) := by rfl
    example : Erlang.functions.«run/1» (.integer 11) = .ok (.integer 36) := by rfl
    """

    file = Path.join(tmp_dir, "Closures.lean")
    File.write!(file, source <> "\n" <> checks)

    {output, status} =
      System.cmd("lake", ["env", "lean", file], cd: @lean_dir, stderr_to_stdout: true)

    assert status == 0, output
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
