defmodule Lynx.RunnerTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @translations_dir Path.expand("../fixtures/translations", __DIR__)
  @literal_erl "../test/fixtures/translations/literal.erl"
  @moduletag timeout: to_timeout(minute: 10)

  test "only exposes declared imports and their dependencies" do
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
             %{status: :ok, source: runtime_source, diagnostics: []},
             %{status: :error, diagnostics: [source, runtime]},
             %{status: :ok, source: translated_source, diagnostics: []}
           ] = Lynx.Commands.verify!(@lean_dir, files)

    assert runtime_source =~ "public import Lynx.Modules.Erlang.maps"
    assert translated_source =~ "public import Erlang.maps"

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

  test "imports both dependency branches and theorems from their shared dependency" do
    contents = [definition("ensures", success()), theorem("law", "exact Elixir.Source.«law/0»")]

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

    files =
      Enum.map(files, fn file ->
        # Keep the first verification uncached across repeated test runs.
        key = :crypto.strong_rand_bytes(32) |> Base.encode16(case: :lower)
        Map.put(file, "cache_key", key)
      end)

    reports = Lynx.Commands.verify!(@lean_dir, files)

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
        assert is_integer(theorem.time_ms) and theorem.time_ms >= 0
      end

      assert Enum.sum(Enum.map(report.theorems, & &1.time_ms)) <= report.time_ms
    end

    assert Enum.all?(Lynx.Commands.verify!(@lean_dir, files), fn report ->
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
    [source_file, table_file] = Enum.map(files, &Map.delete(&1, "cache_key"))
    [table] = table_file["contents"]
    entries = table["entries"]
    entry = Enum.find(entries, &(&1["body"]["name"] == "remember"))
    assert %{"pure" => false} = entry

    # Only the effectful callee and its falsely pure entry are needed here;
    # the translation integration test verifies the complete function table.
    source_file =
      Map.update!(
        source_file,
        "contents",
        &Enum.filter(&1, fn defn -> defn["name"] == "remember" end)
      )

    wrong_table = Map.put(table, "entries", [Map.put(entry, "pure", true)])
    wrong_file = Map.update!(source_file, "contents", &(&1 ++ [wrong_table]))

    assert [
             %{status: :error, diagnostics: diagnostics}
           ] = Lynx.Commands.verify!(@lean_dir, [wrong_file])

    assert Enum.any?(diagnostics, fn diagnostic ->
             diagnostic.severity == :error and
               diagnostic.module == source_file["module"] and
               diagnostic.declaration == "fun_table_apply_0_bind" and
               (diagnostic.message =~ "IsPure" or
                  diagnostic.message =~ "simp` made no progress")
           end)
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
  end

  defp definition(name, body) do
    %{
      "kind" => "def",
      "name" => name,
      "params" => [],
      "pure" => false,
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

  defp call(module, name) do
    %{
      "kind" => "remote_call",
      "module" => module,
      "name" => name,
      "args" => [],
      "span" => [4, 15]
    }
  end

  defp theorem(name, proof) do
    %{
      "kind" => "theorem",
      "name" => name,
      "params" => [],
      "ensures" => "ensures",
      "span" => [4, 1],
      "proof" => %{"source" => proof, "indentation" => 0, "span" => [4, 15]}
    }
  end

  defp file(path, module, contents, imports \\ []) do
    %{"file" => path, "module" => module, "contents" => contents, "imports" => imports}
  end
end

defmodule Lynx.RunnerDiagnosticsTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @literal_erl "../test/fixtures/translations/literal.erl"
  @moduletag timeout: to_timeout(minute: 10)

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
      "computation" => call("Erlang.erlang", "self"),
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
            definition("ensures", body),
            theorem(
              "law",
              if(name == "Success", do: "fail \"deliberate failure\"", else: proof)
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
      assert expected =~ "Result.ok"
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
        law = Map.put(theorem("law", "fail \"deliberate failure\""), "requires", "requires")

        file(@literal_erl, "Elixir.#{name}", [
          definition("requires", requirement),
          definition("ensures", false_body),
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
                 "Requires (definitionally reduced):", parts: 2)

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
          "pure" => false,
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
          definition("broken", %{
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
          })
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
          "span" => [],
          "proof" => %{"source" => proof, "indentation" => 4, "span" => span}
        }
      end

    files = [file(path, "Elixir.Precision", [definition("ensures", success()) | laws])]

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

  test "reports proof parsing errors with the supplied location precision" do
    path = "syntax.ex"

    laws =
      for {name, span} <- [{"columns", [10, 7]}, {"line", [20]}, {"unknown", []}] do
        %{
          "kind" => "theorem",
          "name" => name,
          "params" => [],
          "ensures" => "ensures",
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

  defp definition(name, body) do
    %{
      "kind" => "def",
      "name" => name,
      "params" => [],
      "pure" => false,
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

  defp call(module, name) do
    %{
      "kind" => "remote_call",
      "module" => module,
      "name" => name,
      "args" => [],
      "span" => [4, 15]
    }
  end

  defp theorem(name, proof) do
    %{
      "kind" => "theorem",
      "name" => name,
      "params" => [],
      "ensures" => "ensures",
      "span" => [4, 1],
      "proof" => %{"source" => proof, "indentation" => 0, "span" => [4, 15]}
    }
  end

  defp file(path, module, contents, imports \\ []) do
    %{"file" => path, "module" => module, "contents" => contents, "imports" => imports}
  end
end
