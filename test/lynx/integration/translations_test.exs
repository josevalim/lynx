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

        expected =
          Map.new(files, fn file ->
            suffix = if file["generated"], do: ".program.lean", else: ".lean"
            {file["file"], File.read!(Path.rootname(fixture) <> suffix)}
          end)

        rendered = Lynx.RunnerPool.command(@lean_dir, Map.put(request, "command", "render"))

        assert rendered == %{"status" => "ok", "files" => expected},
               "rendered output does not match #{fixture}"
      end,
      ordered: false,
      timeout: :infinity
    )
    |> Stream.run()
  end

  @tag :tmp_dir
  test "executes captured closures and spawned functions", %{tmp_dir: tmp_dir} do
    for {fixture, checks} <- [
          {"functions",
           """
           example : Lynx.run (Erlang.functions.«run/1» (.integer 5)) [] Lynx.Program.functions =
             .ok (.integer 24) {} := by cbv
           example : Lynx.run (Erlang.functions.«run/1» (.integer 11)) [] Lynx.Program.functions =
             .ok (.integer 36) {} := by cbv
           """},
          {"spawning",
           """
           example : Lynx.run (Erlang.spawning.«run/1» (.integer 7)) [.swap 2] Lynx.Program.functions =
             .ok (.pid 2) { pidCounter := 2, currentProcess.mailbox := [.integer 7] } := by cbv
           """}
        ] do
      source =
        @translations_dir
        |> Path.join(fixture <> ".lean")
        |> File.read!()
        |> String.replace("import Erlang.erlang", """
        import Erlang.erlang
        import all Erlang.erlang.Fun
        import all Erlang.erlang.Guards
        import all Erlang.erlang.Process
        import all Lynx.Term
        import all Lynx.Term.Dispatch
        import all Lynx.Term.Runner
        import all Lynx.Term.DataTypes
        """)

      program =
        @translations_dir
        |> Path.join(fixture <> ".program.lean")
        |> File.read!()
        |> String.replace(~r/^module\n|^(?:public )?import .*\n/m, "")

      file = Path.join(tmp_dir, fixture <> ".lean")
      File.write!(file, source <> "\n" <> program <> "\n" <> checks)

      {output, status} =
        System.cmd("lake", ["env", "lean", file], cd: @lean_dir, stderr_to_stdout: true)

      assert status == 0, output
    end
  end

  @tag :tmp_dir
  test "builds a program table after modules that call back into their caller", %{
    tmp_dir: tmp_dir
  } do
    cores =
      for {module, body} <- [
            {:dispatch_a, "entry(X) -> F = fun(Y) -> X + Y end, dispatch_b:invoke(F, 7)."},
            {:dispatch_b, "invoke(F, X) -> apply(F, [X])."}
          ] do
        exports = if module == :dispatch_a, do: "entry/1", else: "invoke/2"
        file = Path.join(tmp_dir, "#{module}.erl")
        File.write!(file, "-module(#{module}).\n-export([#{exports}]).\n#{body}\n")
        {^module, core} = core(file, file)
        {file, core}
      end

    files =
      Lynx.Translation.new(cores)
      |> Lynx.Translation.add(:dispatch_a, [{:entry, 1}])
      |> Lynx.Translation.assemble()

    assert [
             %{"module" => "Erlang.dispatch_b", "imports" => ["Erlang.erlang"]},
             %{
               "module" => "Erlang.dispatch_a",
               "imports" => ["Erlang.dispatch_b", "Erlang.erlang"]
             },
             %{"module" => "Lynx.Program", "generated" => true}
           ] = files

    request = %{"version" => "1.0", "files" => files}

    assert %{"status" => "ok", "diagnostics" => []} =
             Lynx.RunnerPool.command(@lean_dir, Map.put(request, "command", "verify"))

    assert %{"status" => "ok", "files" => rendered} =
             Lynx.RunnerPool.command(@lean_dir, Map.put(request, "command", "render"))

    # Lean selects a search root per package, so share its compiled runtime
    # artifacts with the generated Erlang and Lynx modules in this test root.
    library = Path.join(@lean_dir, ".lake/build/lib/lean")

    for entry <- File.ls!(library) do
      source = Path.join(library, entry)
      target = Path.join(tmp_dir, entry)

      if entry in ["Erlang", "Lynx"] do
        File.mkdir_p!(target)

        for child <- File.ls!(source) do
          File.ln_s!(Path.join(source, child), Path.join(target, child))
        end
      else
        File.ln_s!(source, target)
      end
    end

    for file <- files do
      target = Path.join(tmp_dir, String.replace(file["module"], ".", "/"))
      File.mkdir_p!(Path.dirname(target))
      source = Map.fetch!(rendered, file["file"])

      source =
        if file["generated"] do
          source
          |> String.replace("import Erlang.", "import all Erlang.")
          |> String.replace("public import Lynx", """
          public import Lynx
          import all Lynx.Term
          import all Lynx.Term.DataTypes
          import all Lynx.Term.Dispatch
          import all Lynx.Term.Runner
          import all Erlang.erlang.Guards
          import all Erlang.erlang.Fun
          """)
          |> Kernel.<>("""

          example : Lynx.run (Erlang.dispatch_a.«entry/1» (.integer 5)) [] Lynx.Program.functions =
            .ok (.integer 12) {} := by cbv
          """)
        else
          source
        end

      File.write!(target <> ".lean", source)

      {output, status} =
        System.cmd("lean", ["--root", tmp_dir, "-o", target <> ".olean", target <> ".lean"],
          cd: @lean_dir,
          env: [{"LEAN_PATH", tmp_dir <> ":" <> Path.join(@lean_dir, ".lake/build/lib/lean")}],
          stderr_to_stdout: true
        )

      assert status == 0, output
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
