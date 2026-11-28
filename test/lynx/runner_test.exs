defmodule Lynx.RunnerTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @translations_dir Path.expand("../fixtures/translations", __DIR__)
  @literal_erl "../test/fixtures/translations/literal.erl"
  @moduletag timeout: to_timeout(minute: 10)

  @tag :tmp_dir
  test "only exposes declared imports and their dependencies", %{tmp_dir: tmp_dir} do
    calls = [
      definition("source", call("Erlang.maps", "value")),
      definition("runtime", call("Erlang.maps", "new"))
    ]

    files = [
      file(@literal_erl, "Erlang.maps", [definition("value", call("Erlang.maps", "new"))], [
        "Erlang.maps"
      ]),
      file(@literal_erl, "Elixir.Undeclared", calls),
      file(@literal_erl, "Elixir.Declared", calls, ["Erlang.maps"])
    ]

    assert [
             %{status: :ok, diagnostics: []},
             %{status: :error, diagnostics: [source, runtime]},
             %{status: :ok, diagnostics: []}
           ] = Lynx.Commands.verify!(@lean_dir, files, debug_dir: tmp_dir)

    assert File.read!(Path.join(tmp_dir, "Erlang/maps.lean")) =~
             "public import Lynx.Modules.Erlang.maps"

    assert File.read!(Path.join(tmp_dir, "Elixir/Declared.lean")) =~ "public import Erlang.maps"

    assert %{
             file: @literal_erl,
             module: "Elixir.Undeclared",
             declaration: "source/0",
             severity: :error,
             line: 4,
             column: 15
           } = source

    assert source.message =~ "Unknown identifier `Erlang.maps.«value/0»`"
    assert %{module: "Elixir.Undeclared", declaration: "runtime/0"} = runtime
    assert runtime.message =~ "Unknown identifier `Erlang.maps.«new/0»`"
  end

  @tag :tmp_dir
  test "exports verified declarations only when every file verifies", %{tmp_dir: tmp_dir} do
    files = [file(@literal_erl, "Elixir.Exported", [definition("value", success())])]
    path = Path.join([tmp_dir, "nested", "export.ndjson"])

    assert [%{status: :ok}] = Lynx.Commands.verify!(@lean_dir, files, export: path)
    [metadata | records] = path |> File.read!() |> String.split("\n", trim: true)
    assert %{"meta" => %{"lean" => %{"version" => _}}} = JSON.decode!(metadata)
    assert Enum.any?(records, &match?(%{"str" => %{"str" => "value/0"}}, JSON.decode!(&1)))

    File.rm!(path)

    assert [%{status: :error}] =
             Lynx.Commands.verify!(@lean_dir, files, options: [maxRecDepth: 1], export: path)

    refute File.exists?(path)
  end

  @tag :tmp_dir
  test "writes compiled modules next to their sources in olean mode", %{tmp_dir: tmp_dir} do
    files = [file(@literal_erl, "Elixir.Debugged", [definition("value", success())])]

    assert [%{status: :ok}] =
             Lynx.Commands.verify!(@lean_dir, files, debug_dir: tmp_dir, debug: :olean)

    assert File.exists?(Path.join(tmp_dir, "Elixir/Debugged.lean"))
    assert File.exists?(Path.join(tmp_dir, "Elixir/Debugged.olean"))
  end

  @tag :tmp_dir
  test "renders preludes with the imports they elaborate with", %{tmp_dir: tmp_dir} do
    prelude =
      write_modules(tmp_dir, "prelude", %{
        "Rendered.lean" => """
        module
        public import Lynx.Modules.Erlang.maps

        @[expose] public section

        def value := @Erlang.maps.«new/0»
        """
      })

    debug_dir = Path.join(tmp_dir, "debug")

    assert [%{status: :ok, module: "Rendered", file: file}] =
             Lynx.Commands.verify!(@lean_dir, [],
               prelude: prelude,
               debug_dir: debug_dir,
               debug: :lean
             )

    assert file == Path.join(prelude, "Rendered.lean")

    assert File.read!(Path.join(debug_dir, "Rendered.lean")) == """
           module
           public import Lynx.Modules.Erlang.maps
           public import Lynx
           import Lynx.Runner.Elab

           @[expose] public section

           def value := @Erlang.maps.«new/0»
           """
  end

  @tag :tmp_dir
  test "sets Lean options in translated modules and caches them separately", %{tmp_dir: tmp_dir} do
    files = [file(@literal_erl, "Elixir.Options", [definition("value", success())])]
    cache = Path.join(tmp_dir, "cache")

    assert [%{status: :ok, cached: false}] = Lynx.Commands.verify!(@lean_dir, files, cache: cache)

    assert [%{status: :error, cached: false}] =
             Lynx.Commands.verify!(@lean_dir, files,
               options: [maxRecDepth: 1],
               debug_dir: tmp_dir,
               cache: cache
             )

    assert File.read!(Path.join(tmp_dir, "Elixir/Options.lean")) =~ "set_option maxRecDepth 1"
    assert [%{status: :ok, cached: true}] = Lynx.Commands.verify!(@lean_dir, files, cache: cache)
  end

  @tag :tmp_dir
  test "imports both dependency branches and theorems from their shared dependency", %{
    tmp_dir: tmp_dir
  } do
    contents = [
      definition("ensures", success()),
      theorem("law", "exact Elixir.Source.«law/0»")
    ]

    files = [
      file(@literal_erl, "Elixir.Source", [
        definition("ensures", success()),
        theorem("law", "rfl")
      ]),
      file(@literal_erl, "Elixir.Left", contents, ["Elixir.Source"]),
      file(@literal_erl, "Elixir.Right", contents, ["Elixir.Source"]),
      file(
        @literal_erl,
        "Elixir.Join",
        [
          definition("ensures", success()),
          theorem("left", "exact Elixir.Left.«law/0»"),
          theorem("right", "exact Elixir.Right.«law/0»"),
          theorem("source", "exact Elixir.Source.«law/0»")
        ],
        ["Elixir.Left", "Elixir.Right"]
      )
    ]

    reports = Lynx.Commands.verify!(@lean_dir, files, cache: tmp_dir)

    assert [
             %{
               status: :ok,
               module: "Elixir.Source",
               cached: false,
               diagnostics: []
             },
             %{
               status: :ok,
               module: "Elixir.Left",
               cached: false,
               diagnostics: []
             },
             %{status: :ok, module: "Elixir.Right", diagnostics: []},
             %{status: :ok, module: "Elixir.Join", diagnostics: []}
           ] = reports

    assert [%{name: "left/0"}, %{name: "right/0"}, %{name: "source/0"}] =
             List.last(reports).theorems

    for report <- reports do
      for theorem <- report.theorems do
        # Laws elaborate in parallel, so only each one is bounded by its module.
        assert is_integer(theorem.time_ms) and theorem.time_ms in 0..report.time_ms
      end
    end

    assert Enum.all?(Lynx.Commands.verify!(@lean_dir, files, cache: tmp_dir), fn report ->
             report.cached and report.theorems == []
           end)
  end

  test "skips dependents of failed modules and continues verifying unrelated files" do
    files = [
      file(@literal_erl, "Elixir.Failed", [
        definition("value", %{
          "kind" => "return",
          "span" => [4, 15],
          "values" => [%{"kind" => "var", "name" => "missing", "span" => [4, 15]}]
        })
      ]),
      file(@literal_erl, "Elixir.Unrelated", [definition("value", success())]),
      file(
        @literal_erl,
        "Elixir.Dependent",
        [definition("value", call("Elixir.Failed", "value"))],
        ["Elixir.Failed"]
      )
    ]

    assert [
             %{status: :error, module: "Elixir.Failed", diagnostics: [failed]},
             %{status: :ok, module: "Elixir.Unrelated", diagnostics: []},
             %{
               status: :skipped,
               module: "Elixir.Dependent",
               diagnostics: [dependent]
             }
           ] = Lynx.Commands.verify!(@lean_dir, files)

    assert failed.message =~ "Unknown identifier `vmissing`"

    assert dependent == %{
             file: @literal_erl,
             module: "Elixir.Dependent",
             declaration: nil,
             severity: :error,
             message: "import 'Elixir.Failed' must precede this file and verify successfully"
           }
  end

  test "function table purity metadata is checked rather than trusted" do
    %{"files" => files} = JSON.decode!(File.read!(Path.join(@translations_dir, "functions.json")))
    [source_file, table_file] = files
    [table] = table_file["contents"]
    entries = table["entries"]
    entry = Enum.find(entries, &(&1["body"]["name"] == "remember"))
    assert %{"purity" => "sequential"} = entry

    # Only the effectful callee and its falsely pure entry are needed here;
    # the translation integration test verifies the complete function table.
    source_file =
      Map.update!(
        source_file,
        "contents",
        &Enum.filter(&1, fn defn -> defn["name"] == "remember" end)
      )

    # Purity metadata only decides how calls are embedded. Claiming that an
    # effectful callee is pure omits the dispatcher it receives, a type error.
    wrong_entry =
      entry
      |> Map.put("purity", "pure")
      |> put_in(["body", "purity"], "pure")

    wrong_table = Map.put(table, "entries", [wrong_entry])
    wrong_file = Map.update!(source_file, "contents", &(&1 ++ [wrong_table]))

    assert [
             %{status: :error, diagnostics: diagnostics}
           ] = Lynx.Commands.verify!(@lean_dir, [wrong_file])

    assert Enum.any?(diagnostics, fn diagnostic ->
             diagnostic.severity == :error and diagnostic.module == source_file["module"] and
               diagnostic.message =~ "expected to have type\n  Lynx.Dispatcher"
           end)
  end

  @tag :tmp_dir
  test "orders directory modules by their imports around translated files and laws", %{
    tmp_dir: tmp_dir
  } do
    # Modules that import others sort after them, though their paths sort first.
    prelude =
      write_modules(tmp_dir, "prelude", %{
        "Tactics.lean" => """
        module
        public import Zeta.Base
        public section
        macro "finish" : tactic => `(tactic| rfl)
        """,
        "Zeta/Base.lean" => """
        module
        public import Lynx
        public section
        theorem base : True := trivial
        """
      })

    postlude =
      write_modules(tmp_dir, "postlude", %{
        "Shared.lean" => """
        module
        public import Zeta.Later
        public section
        theorem shared : True := later
        """,
        "Zeta/Later.lean" => """
        module
        public import Elixir.Ordered
        public section
        theorem later : True := trivial
        """
      })

    # Laws come last, whatever their input order, and import every postlude, while
    # translated files import every prelude.
    files = [
      file(@literal_erl, "Elixir.Ordered.laws", [
        definition("ensures", success()),
        theorem("law", "have := shared; finish")
      ]),
      file(@literal_erl, "Elixir.Ordered", [definition("value", success())])
    ]

    assert [
             %{status: :ok, module: "Zeta.Base"},
             %{status: :ok, module: "Tactics"},
             %{status: :ok, module: "Elixir.Ordered"},
             %{status: :ok, module: "Zeta.Later"},
             %{status: :ok, module: "Shared"},
             %{status: :ok, module: "Elixir.Ordered.laws", diagnostics: []}
           ] = Lynx.Commands.verify!(@lean_dir, files, prelude: prelude, postlude: postlude)
  end

  @tag :tmp_dir
  test "rejects directory modules that cannot be ordered or named", %{tmp_dir: tmp_dir} do
    header = "module\npublic import Lynx\n"
    files = [file(@literal_erl, "Elixir.Named", [definition("value", success())])]

    cycle =
      write_modules(tmp_dir, "cycle", %{
        "A.lean" => header <> "import B\n",
        "B.lean" => header <> "import A\n"
      })

    assert_raise RuntimeError, ~r/modules import each other in a cycle: A, B/, fn ->
      Lynx.Commands.verify!(@lean_dir, files, postlude: cycle)
    end

    early = write_modules(tmp_dir, "early", %{"Early.lean" => header <> "import Elixir.Named\n"})

    assert_raise RuntimeError, ~r/preludes verify first, so they cannot import Elixir.Named/, fn ->
      Lynx.Commands.verify!(@lean_dir, files, prelude: early)
    end

    for {name, path} <- [{"clash", "Elixir/Named.lean"}, {"runtime", "Lynx.lean"}] do
      dir = write_modules(tmp_dir, name, %{path => header})

      assert_raise RuntimeError, ~r/is already defined/, fn ->
        Lynx.Commands.verify!(@lean_dir, files, postlude: dir)
      end
    end

    for path <- ["Not.Plain.lean", "my-file.lean", "1st/File.lean"] do
      dir = write_modules(tmp_dir, "names", %{path => header})

      assert_raise RuntimeError, ~r/module paths must be Lean identifiers/, fn ->
        Lynx.Commands.verify!(@lean_dir, files, postlude: dir)
      end

      File.rm_rf!(dir)
    end

    laws = [
      file(@literal_erl, "Elixir.Named.laws", [
        definition("ensures", success()),
        theorem("law", "rfl")
      ])
    ]

    late = write_modules(tmp_dir, "late", %{"Late.lean" => header <> "import Elixir.Named.laws\n"})

    assert_raise RuntimeError, ~r/postludes cannot import Elixir.Named.laws/, fn ->
      Lynx.Commands.verify!(@lean_dir, laws, postlude: late)
    end
  end

  @tag :tmp_dir
  test "skips hidden files and fails alone a module whose header cannot be imported", %{
    tmp_dir: tmp_dir
  } do
    header = "module\npublic import Lynx\n"

    postlude =
      write_modules(tmp_dir, "postlude", %{
        ".#Editing.lean" => "not Lean",
        "Missing.lean" => header <> "import Not.A.Module\n",
        "Dependent.lean" => header <> "import Missing\n",
        "Fine.lean" => header
      })

    files = [file(@literal_erl, "Elixir.Alone", [definition("value", success())])]

    assert [
             %{module: "Elixir.Alone", status: :ok},
             %{module: "Fine", status: :ok},
             %{module: "Missing", status: :error, diagnostics: [%{message: message}]},
             %{module: "Dependent", status: :skipped}
           ] = Lynx.Commands.verify!(@lean_dir, files, postlude: postlude)

    assert message =~ "unknown module prefix 'Not'"
  end

  @tag :tmp_dir
  test "verifies again only the modules that import a changed module", %{tmp_dir: tmp_dir} do
    source = fn name, body ->
      "module\npublic import Elixir.Keyed\npublic section\ntheorem #{name} : True := #{body}\n"
    end

    files = [
      file(@literal_erl, "Elixir.Keyed", [definition("value", success())]),
      file(@literal_erl, "Elixir.Keyed.laws", [
        definition("ensures", success()),
        theorem("law", "rfl")
      ])
    ]

    write = fn body ->
      write_modules(tmp_dir, "postlude", %{
        "Stable.lean" => source.("stable", "trivial"),
        "Edited.lean" => source.("edited", body)
      })
    end

    cache = Path.join(tmp_dir, "cache")
    verify = &Lynx.Commands.verify!(@lean_dir, files, postlude: &1, cache: cache)

    assert Enum.all?(verify.(write.("trivial")), &match?(%{status: :ok, cached: false}, &1))

    assert [
             %{module: "Elixir.Keyed", cached: true},
             %{module: "Edited", cached: false},
             %{module: "Stable", cached: true},
             %{module: "Elixir.Keyed.laws", cached: false}
           ] = verify.(write.("True.intro"))

    assert Enum.all?(verify.(write.("True.intro")), & &1.cached)

    # A prelude reaches every translated file, so changing it verifies all of them again.
    prelude = fn body ->
      write_modules(tmp_dir, "prelude", %{"Base.lean" => "module\npublic import Lynx\n" <> body})
    end

    postlude = write.("True.intro")
    verify = &Lynx.Commands.verify!(@lean_dir, files, prelude: &1, postlude: postlude, cache: cache)
    assert [%{module: "Base"} | _] = verify.(prelude.(""))
    assert Enum.all?(verify.(prelude.("")), & &1.cached)
    assert Enum.all?(verify.(prelude.("-- changed\n")), &(not &1.cached))
  end

  describe "errors" do
    test "rejects unsupported versions before reading files" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, %{"command" => "verify", "version" => "2.0"})
        end

      assert error.message == "unsupported version"
    end

    test "rejects missing files" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, %{"command" => "verify", "version" => "1.0"})
        end

      assert error.message =~ "files"
    end

    test "rejects invalid instructions" do
      files = [file(@literal_erl, "Erlang.literal", [%{"kind" => "unknown", "span" => []}])]

      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.verify!(@lean_dir, files)
        end

      assert error.message =~ @literal_erl
      assert error.message =~ "unsupported command kind 'unknown'"
    end

    test "rejects non-finite exponents and oversized float fractions" do
      for {field, value, message} <- [
            {"exponent", 2047, "float exponent must be less than 2047"},
            {"exponent", 2048, "float exponent must be less than 2047"},
            {"fraction", 4_503_599_627_370_496, "float fraction must be less than 2^52"}
          ] do
        literal =
          %{
            "kind" => "float",
            "negative" => false,
            "exponent" => 0,
            "fraction" => 0,
            "span" => []
          }
          |> Map.put(field, value)

        body = %{"kind" => "return", "values" => [literal], "span" => []}
        files = [file(@literal_erl, "Erlang.literal", [definition("invalid", body)])]

        error = assert_raise RuntimeError, fn -> Lynx.Commands.verify!(@lean_dir, files) end
        assert error.message =~ message
      end
    end
  end

  defp definition(name, body, purity \\ "pure") do
    %{
      "kind" => "def",
      "name" => name,
      "params" => [],
      "purity" => purity,
      "span" => [4, 1],
      "body" => body
    }
  end

  defp success do
    %{
      "kind" => "return",
      "span" => [],
      "values" => [%{"kind" => "atom", "value" => "true", "span" => []}]
    }
  end

  defp call(module, name, purity \\ "pure") do
    %{
      "kind" => "remote_call",
      "module" => module,
      "name" => name,
      "args" => [],
      "purity" => purity,
      "span" => [4, 15]
    }
  end

  defp theorem(name, proof, purity \\ "pure") do
    %{
      "kind" => "theorem",
      "name" => name,
      "params" => [],
      "ensures" => "ensures",
      "ensures_purity" => purity,
      "span" => [4, 1],
      "proof" => %{"source" => proof, "indentation" => 0, "span" => [4, 15]}
    }
  end

  defp file(path, module, contents, imports \\ []) do
    %{"file" => path, "module" => module, "contents" => contents, "imports" => imports}
  end

  defp write_modules(tmp_dir, name, modules) do
    dir = Path.join(tmp_dir, name)

    for {path, source} <- modules do
      path = Path.join(dir, path)
      File.mkdir_p!(Path.dirname(path))
      File.write!(path, source)
    end

    dir
  end
end

defmodule Lynx.RunnerDiagnosticsTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @literal_erl "../test/fixtures/translations/literal.erl"
  @moduletag timeout: to_timeout(minute: 10)

  @header "module\npublic import Lynx\npublic section\n"

  @tag :tmp_dir
  test "checks prelude imports, caching, source locations, and proof axioms", %{tmp_dir: tmp_dir} do
    # The header imports a runtime module the declarations refer to.
    prelude =
      write_modules(tmp_dir, "cached", %{
        "Elaborators.lean" =>
          "module\npublic import Lynx.Modules.Erlang.erlang\npublic section\n" <>
            "def runtimeCall := @Erlang.erlang.«is_atom/1»\n" <>
            "open Lean Elab Tactic\n" <>
            "elab \"custom_finish\" : tactic => do evalTactic (← `(tactic| rfl))\n"
      })

    files = [
      file(@literal_erl, "Elixir.CustomClient", [
        definition("ensures", success()),
        theorem("law", "custom_finish")
      ])
    ]

    cache = Path.join(tmp_dir, "cache")

    for cached <- [false, true] do
      assert [%{status: :ok, cached: ^cached}, %{status: :ok, cached: ^cached}] =
               Lynx.Commands.verify!(@lean_dir, files, prelude: prelude, cache: cache)
    end

    broken =
      write_modules(tmp_dir, "broken", %{
        "Broken.lean" => @header <> "open Lean Elab Tactic\nelab \"broken\" : tactic => missing\n"
      })

    assert [%{status: :error, diagnostics: [error]}] =
             Lynx.Commands.verify!(@lean_dir, [], prelude: broken)

    assert %{
             file: file,
             declaration: nil,
             line: 5,
             column: 27,
             message: "Unknown identifier `missing`"
           } = error

    assert file == Path.join(broken, "Broken.lean")

    untrusted =
      write_modules(tmp_dir, "untrusted", %{
        "Untrusted.lean" =>
          @header <>
            "open Lean Elab Tactic\n" <>
            "elab \"untrusted\" : tactic => do evalTactic (← `(tactic| sorry))\n"
      })

    client =
      file(@literal_erl, "Elixir.UntrustedClient", [
        definition("ensures", success()),
        theorem("law", "untrusted")
      ])

    assert [%{status: :ok}, %{status: :error, diagnostics: diagnostics}] =
             Lynx.Commands.verify!(@lean_dir, [client], prelude: untrusted)

    assert Enum.any?(diagnostics, &(&1.message =~ "unexpected axiom: sorryAx"))

    headless =
      write_modules(tmp_dir, "headless", %{"Headless.lean" => "theorem truth : True := trivial\n"})

    assert [
             %{
               status: :error,
               diagnostics: [
                 %{message: "a prelude or postlude file must begin with a module header"}
               ]
             }
           ] = Lynx.Commands.verify!(@lean_dir, [], prelude: headless)
  end

  @tag :tmp_dir
  test "reports failed proofs of a prelude, elaborated in parallel", %{tmp_dir: tmp_dir} do
    prelude =
      write_modules(tmp_dir, "parallel", %{
        "Parallel.lean" =>
          @header <>
            "theorem first : 1 = 2 := by decide\ntheorem fine : 1 = 1 := rfl\n" <>
            "theorem second : 1 = 1 := fine\ntheorem third : 2 = 3 := by decide\n"
      })

    assert [%{status: :error, diagnostics: diagnostics}] =
             Lynx.Commands.verify!(@lean_dir, [], prelude: prelude)

    assert [first, third] = Enum.sort_by(diagnostics, & &1.line)
    assert %{line: 4, message: "Tactic `decide` proved" <> _} = first
    assert %{line: 7, message: "Tactic `decide` proved" <> _} = third
  end

  test "reports expected and actual values for expects" do
    receive_body = fn timeout ->
      %{
        "kind" => "receive",
        "message" => %{"kind" => "var", "name" => %{"generated" => 0}, "span" => []},
        "cases" => [],
        "timeout" => timeout,
        "after" => success(),
        "span" => []
      }
    end

    infinite = receive_body.(%{"kind" => "atom", "value" => "infinity", "span" => []})
    finite = receive_body.(%{"kind" => "integer", "value" => 10, "span" => []})
    zero = receive_body.(%{"kind" => "integer", "value" => 0, "span" => []})
    invalid = receive_body.(%{"kind" => "atom", "value" => "invalid", "span" => []})

    effect = %{
      "kind" => "bind",
      "vars" => [%{"kind" => "wildcard", "span" => []}],
      "computation" => call("Erlang.erlang", "self", "sequential"),
      "body" => infinite,
      "span" => []
    }

    false_body = put_in(success(), ["values", Access.at(0), "value"], "false")
    proof = "simp [«ensures/0», Lynx.Result.receiveWith, Lynx.ReceiveTimeout.ofTerm]"

    cases = [
      {"Infinite", infinite, "ReceiveTimeout.infinity"},
      {"Finite", finite, "ReceiveTimeout.finite"},
      {"Zero", zero, "ReceiveTimeout.immediate"},
      {"Invalid", invalid, "timeout_value"},
      {"Effect", effect, "Result.get"},
      {"False", false_body, ~s(Term.atom "false")},
      {"Success", success(), ~s(Term.atom "true")}
    ]

    files =
      for {name, body, _actual} <- cases do
        file(
          @literal_erl,
          "Elixir.#{name}",
          [
            definition("ensures", body, "concurrent"),
            theorem(
              "law",
              if(name == "Success", do: "fail \"deliberate failure\"", else: proof),
              "concurrent"
            )
          ],
          ["Erlang.erlang"]
        )
      end

    reports = Lynx.Commands.verify!(@lean_dir, files)

    for {report, {_name, _body, actual}} <- Enum.zip(reports, cases) do
      assert report.status == :error
      assert [diagnostic] = Enum.filter(report.diagnostics, &(&1.severity == :error))
      assert diagnostic.declaration == "law/0"
      assert diagnostic.message =~ "Expectation (definitionally reduced):"
      assert [expected, got] = String.split(diagnostic.message, "got:      ", parts: 2)
      assert expected =~ "Outcome.ok"
      assert expected =~ ~s(Term.atom "true")
      assert got =~ actual
      refute diagnostic.message =~ "Deadlock:"
      refute diagnostic.message =~ "Requires (definitionally reduced):"
    end
  end

  test "reports expected and actual values for requires" do
    false_body = put_in(success(), ["values", Access.at(0), "value"], "false")

    files =
      for {name, requirement} <- [
            {"FalseRequirement", false_body},
            {"TrueRequirement", success()}
          ] do
        law =
          Map.merge(theorem("law", "fail \"deliberate failure\"", "sequential"), %{
            "requires" => "requires",
            "requires_purity" => "sequential"
          })

        file(@literal_erl, "Elixir.#{name}", [
          definition("requires", requirement, "sequential"),
          definition("ensures", false_body, "sequential"),
          law
        ])
      end

    reports = Lynx.Commands.verify!(@lean_dir, files)

    for {report, actual} <- Enum.zip(reports, ["false", "true"]) do
      assert report.status == :error
      assert [diagnostic] = report.diagnostics
      assert diagnostic.message =~ "deliberate failure"

      assert [expectation, requirement] =
               String.split(
                 diagnostic.message,
                 "Requires (definitionally reduced):",
                 parts: 2
               )

      assert expectation =~ ~s(Term.atom "false")
      assert [expected, got] = String.split(requirement, "got:      ", parts: 2)
      assert expected =~ ~s(Term.atom "true")
      assert got =~ ~s(Term.atom "#{actual}")
    end
  end

  test "reports function elaboration errors at the inherited node location" do
    files = [
      file(@literal_erl, "Erlang.literal", [
        %{
          "kind" => "def",
          "name" => "broken",
          "params" => [],
          "purity" => "sequential",
          "span" => [4, 1],
          "body" => %{
            "kind" => "return",
            "span" => [4, 15],
            "values" => [%{"kind" => "var", "name" => "missing", "span" => []}]
          }
        }
      ])
    ]

    assert [%{status: :error, diagnostics: [diagnostic]}] =
             Lynx.Commands.verify!(@lean_dir, files)

    assert diagnostic == %{
             file: @literal_erl,
             module: "Erlang.literal",
             declaration: "broken/0",
             severity: :error,
             line: 4,
             column: 15,
             message: "Unknown identifier `vmissing`"
           }
  end

  test "reports type errors when generated match patterns do not match the expression type" do
    path = "invalid_match.erl"

    files = [
      file(
        path,
        "Erlang.invalid_match",
        [
          definition(
            "broken",
            %{
              "kind" => "match",
              "span" => [3, 1],
              "expressions" => [
                %{
                  "kind" => "remote_call",
                  "module" => "Erlang.erlang",
                  "name" => "+",
                  "args" => [
                    %{"kind" => "integer", "value" => 1, "span" => [3, 10]},
                    %{"kind" => "integer", "value" => 2, "span" => [3, 14]}
                  ],
                  "purity" => "pure",
                  "span" => [3, 8]
                }
              ],
              "cases" => [
                %{
                  "patterns" => [%{"kind" => "integer", "value" => 3, "span" => [4, 5]}],
                  "body" => success(),
                  "span" => [4, 1]
                }
              ]
            },
            "sequential"
          )
        ],
        ["Erlang.erlang"]
      )
    ]

    assert [%{status: :error, diagnostics: [diagnostic]}] =
             Lynx.Commands.verify!(@lean_dir, files)

    assert %{
             file: ^path,
             module: "Erlang.invalid_match",
             declaration: "broken/0",
             severity: :error,
             line: 4,
             column: 5,
             message: message
           } =
             diagnostic

    assert message ==
             String.trim_trailing("""
             Type mismatch
               Lynx.Term.integer 3
             has type
               Lynx.Term
             of sort `Type` but is expected to have type
               Lynx.Result
             of sort `Type 1`
             """)
  end

  test "reports proof elaboration errors with Unicode and the supplied location precision" do
    path = "proofs.ex"
    proof = "have h₀ : True := by trivial\nexact (let hé := True; missing)\n"

    laws =
      for {name, span} <- [
            {"columns", [10, 7]},
            {"line", [20]},
            {"unknown", []}
          ] do
        %{
          "kind" => "theorem",
          "name" => name,
          "params" => [],
          "ensures" => "ensures",
          "ensures_purity" => "sequential",
          "span" => [],
          "proof" => %{"source" => proof, "indentation" => 4, "span" => span}
        }
      end

    files = [
      file(path, "Elixir.Precision", [definition("ensures", success(), "sequential") | laws])
    ]

    assert [%{status: :error, diagnostics: diagnostics}] =
             Lynx.Commands.verify!(@lean_dir, files)

    for diagnostic <- diagnostics do
      assert diagnostic.message =~ "Expectation (definitionally reduced):"
      assert diagnostic.message =~ "expected:"
      assert diagnostic.message =~ "got:"
      assert diagnostic.message =~ ~s(Term.atom "true")
      assert String.ends_with?(diagnostic.message, "Unknown identifier `missing`")
    end

    assert Enum.map(diagnostics, &Map.delete(&1, :message)) == [
             %{
               file: path,
               module: "Elixir.Precision",
               declaration: "columns/0",
               severity: :error,
               line: 11,
               column: 28
             },
             %{
               file: path,
               module: "Elixir.Precision",
               declaration: "line/0",
               severity: :error,
               line: 21
             },
             %{
               file: path,
               module: "Elixir.Precision",
               declaration: "unknown/0",
               severity: :error
             }
           ]
  end

  test "reports termination suffix errors at their original file and position" do
    argument = %{"kind" => "var", "name" => 0, "span" => []}

    elaboration =
      definition(
        "broken",
        %{
          "kind" => "remote_call",
          "module" => "Erlang.suffix_elaboration",
          "name" => "broken",
          "args" => [argument],
          "purity" => "sequential",
          "span" => []
        },
        "sequential"
      )
      |> Map.put("params", [argument])
      |> Map.put("termination_suffix", %{
        "source" => "partial_fixpoint monotonicity by\n  exact (let hé := True; missing)\n",
        "file" => "suffixes.exs",
        "span" => [10, 7],
        "indentation" => 4
      })

    parsing =
      definition("broken", success(), "sequential")
      |> Map.put("termination_suffix", %{
        "source" => "termination_by )",
        "file" => "suffixes.exs",
        "span" => [20, 7],
        "indentation" => 4
      })

    assert [
             %{
               status: :error,
               diagnostics: [
                 %{
                   file: "suffixes.exs",
                   module: "Erlang.suffix_elaboration",
                   declaration: "broken/1",
                   severity: :error,
                   line: 11,
                   column: 30,
                   message: "Unknown identifier `missing`"
                 }
               ]
             },
             %{
               status: :error,
               diagnostics: [
                 %{
                   file: "suffixes.exs",
                   module: "Erlang.suffix_parsing",
                   declaration: "broken/0",
                   severity: :error,
                   line: 20,
                   column: 22,
                   message: "expected term"
                 }
               ]
             }
           ] =
             Lynx.Commands.verify!(@lean_dir, [
               file(@literal_erl, "Erlang.suffix_elaboration", [elaboration]),
               file(@literal_erl, "Erlang.suffix_parsing", [parsing])
             ])
  end

  test "reports proof parsing errors with the supplied location precision" do
    path = "syntax.ex"

    laws =
      for {name, span} <- [{"columns", [10, 7]}, {"line", [20]}, {"unknown", []}] do
        %{
          "kind" => "theorem",
          "name" => name,
          "params" => [],
          "ensures" => "ensures",
          "ensures_purity" => "sequential",
          "span" => [],
          "proof" => %{"source" => "exact )", "indentation" => 4, "span" => span}
        }
      end

    files = [file(path, "Elixir.Syntax", [definition("ensures", success()) | laws])]

    assert [%{status: :error, diagnostics: diagnostics}] =
             Lynx.Commands.verify!(@lean_dir, files)

    assert diagnostics == [
             %{
               file: path,
               severity: :error,
               line: 10,
               column: 13,
               module: "Elixir.Syntax",
               declaration: "columns/0",
               message: "expected term"
             },
             %{
               file: path,
               severity: :error,
               line: 20,
               module: "Elixir.Syntax",
               declaration: "line/0",
               message: "expected term"
             },
             %{
               file: path,
               severity: :error,
               module: "Elixir.Syntax",
               declaration: "unknown/0",
               message: "expected term"
             }
           ]
  end

  test "identifies the theorem and unexpected axiom when proof auditing fails" do
    path = "axioms.ex"

    files = [
      file(path, "Elixir.Axioms", [
        definition("ensures", success()),
        theorem("valid", "rfl"),
        theorem("untrusted", "sorry")
      ])
    ]

    assert [
             %{
               status: :error,
               diagnostics: [
                 %{
                   severity: :warning,
                   module: "Elixir.Axioms",
                   declaration: "untrusted/0"
                 },
                 %{severity: :error} = diagnostic
               ]
             }
           ] = Lynx.Commands.verify!(@lean_dir, files)

    assert diagnostic == %{
             file: path,
             severity: :error,
             line: 4,
             column: 15,
             module: "Elixir.Axioms",
             declaration: "untrusted/0",
             message: "unexpected axiom: sorryAx"
           }
  end

  defp definition(name, body, purity \\ "pure") do
    %{
      "kind" => "def",
      "name" => name,
      "params" => [],
      "purity" => purity,
      "span" => [4, 1],
      "body" => body
    }
  end

  defp success do
    %{
      "kind" => "return",
      "span" => [],
      "values" => [%{"kind" => "atom", "value" => "true", "span" => []}]
    }
  end

  defp call(module, name, purity) do
    %{
      "kind" => "remote_call",
      "module" => module,
      "name" => name,
      "args" => [],
      "purity" => purity,
      "span" => [4, 15]
    }
  end

  defp theorem(name, proof, purity \\ "pure") do
    %{
      "kind" => "theorem",
      "name" => name,
      "params" => [],
      "ensures" => "ensures",
      "ensures_purity" => purity,
      "span" => [4, 1],
      "proof" => %{"source" => proof, "indentation" => 0, "span" => [4, 15]}
    }
  end

  defp file(path, module, contents, imports \\ []) do
    %{"file" => path, "module" => module, "contents" => contents, "imports" => imports}
  end

  defp write_modules(tmp_dir, name, modules) do
    dir = Path.join(tmp_dir, name)

    for {path, source} <- modules do
      path = Path.join(dir, path)
      File.mkdir_p!(Path.dirname(path))
      File.write!(path, source)
    end

    dir
  end
end
