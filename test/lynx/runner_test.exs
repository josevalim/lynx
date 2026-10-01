defmodule Lynx.RunnerTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @translations_dir Path.expand("../fixtures/translations", __DIR__)
  @literal_erl "../test/fixtures/translations/literal.erl"
  @moduletag timeout: to_timeout(minute: 10)

  test "only exposes declared imports and their dependencies" do
    calls = [
      definition("source", call("Elixir.Source", "value")),
      definition("runtime", call("Erlang.maps", "new"))
    ]

    request = %{
      "command" => "verify",
      "version" => "1.0",
      "files" => [
        file(@literal_erl, "Elixir.Source", [definition("value", call("Erlang.maps", "new"))], [
          "Erlang.maps"
        ]),
        file(@literal_erl, "Elixir.Undeclared", calls),
        file(@literal_erl, "Elixir.Declared", calls, ["Elixir.Source"])
      ]
    }

    assert [
             %{"status" => "ok", "diagnostics" => []},
             %{"status" => "error", "diagnostics" => [source, runtime]},
             %{"status" => "ok", "diagnostics" => []}
           ] = Lynx.Commands.runner!(@lean_dir, request)

    assert %{"file" => @literal_erl, "kind" => "error", "line" => 4, "column" => 15} = source
    assert source["message"] =~ "Unknown identifier `Elixir.Source.«value/0»`"
    assert runtime["message"] =~ "Unknown identifier `Erlang.maps.«new/0»`"
  end

  test "imports both dependency branches and theorems from their shared dependency" do
    contents = [definition("ensures", success()), theorem("law", "exact Elixir.Source.«law/0»")]

    request = %{
      "command" => "verify",
      "version" => "1.0",
      "files" => [
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
    }

    assert [
             %{"status" => "ok", "module" => "Elixir.Source", "diagnostics" => []},
             %{"status" => "ok", "module" => "Elixir.Left", "diagnostics" => []},
             %{"status" => "ok", "module" => "Elixir.Right", "diagnostics" => []},
             %{"status" => "ok", "module" => "Elixir.Join", "diagnostics" => []}
           ] = Lynx.Commands.runner!(@lean_dir, request)
  end

  test "skips dependents of failed modules and continues verifying unrelated files" do
    request = %{
      "command" => "verify",
      "version" => "1.0",
      "files" => [
        file(@literal_erl, "Elixir.Failed", [
          definition("value", %{
            "kind" => "return",
            "span" => [4, 15],
            "value" => %{"kind" => "var", "name" => "missing", "span" => [4, 15]}
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
    }

    assert [
             %{"status" => "error", "module" => "Elixir.Failed", "diagnostics" => [failed]},
             %{"status" => "ok", "module" => "Elixir.Unrelated", "diagnostics" => []},
             %{
               "status" => "skipped",
               "module" => "Elixir.Dependent",
               "diagnostics" => [dependent]
             }
           ] = Lynx.Commands.runner!(@lean_dir, request)

    assert failed["message"] =~ "Unknown identifier `vmissing`"

    assert dependent == %{
             "file" => @literal_erl,
             "kind" => "error",
             "message" => "import 'Elixir.Failed' must precede this file and verify successfully"
           }
  end

  test "function table purity metadata is checked rather than trusted" do
    request = fixture_request(Path.join(@translations_dir, "functions.json"), "verify")
    table_file = List.last(request["files"])
    [table] = table_file["contents"]
    entries = table["entries"]
    index = Enum.find_index(entries, &(&1["body"]["name"] == "remember"))
    assert %{"pure" => false} = Enum.at(entries, index)

    wrong_entries = List.update_at(entries, index, &Map.put(&1, "pure", true))
    wrong_table = Map.put(table, "entries", wrong_entries)
    wrong_file = Map.put(table_file, "contents", [wrong_table])
    wrong_request = Map.put(request, "files", Enum.drop(request["files"], -1) ++ [wrong_file])

    assert [
             %{"status" => "ok", "diagnostics" => []},
             %{"status" => "error", "diagnostics" => diagnostics}
           ] = Lynx.Commands.runner!(@lean_dir, wrong_request)

    assert Enum.any?(diagnostics, fn diagnostic ->
             diagnostic["kind"] == "error" and
               (diagnostic["message"] =~ "IsPure" or
                  diagnostic["message"] =~ "simp` made no progress")
           end)
  end

  describe "diagnostics" do
    test "reports function elaboration errors at the inherited node location" do
      request = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [
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
                "value" => %{"kind" => "var", "name" => "missing", "span" => []}
              }
            }
          ])
        ]
      }

      assert [%{"status" => "error", "diagnostics" => [diagnostic]}] =
               Lynx.Commands.runner!(@lean_dir, request)

      assert diagnostic == %{
               "file" => @literal_erl,
               "kind" => "error",
               "line" => 4,
               "column" => 15,
               "message" => "Unknown identifier `vmissing`"
             }
    end

    test "reports type errors when generated match patterns do not match the expression type" do
      path = "invalid_match.erl"

      request = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [
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
      }

      assert [%{"status" => "error", "diagnostics" => [diagnostic]}] =
               Lynx.Commands.runner!(@lean_dir, request)

      assert %{
               "file" => ^path,
               "kind" => "error",
               "line" => 4,
               "column" => 5,
               "message" => message
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

      request = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [file(path, "Elixir.Precision", [definition("ensures", success()) | laws])]
      }

      assert [%{"status" => "error", "diagnostics" => diagnostics}] =
               Lynx.Commands.runner!(@lean_dir, request)

      assert diagnostics == [
               %{
                 "file" => path,
                 "kind" => "error",
                 "line" => 11,
                 "column" => 28,
                 "message" => "Unknown identifier `missing`"
               },
               %{
                 "file" => path,
                 "kind" => "error",
                 "line" => 21,
                 "message" => "Unknown identifier `missing`"
               },
               %{"file" => path, "kind" => "error", "message" => "Unknown identifier `missing`"}
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

      request = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [file(path, "Elixir.Syntax", [definition("ensures", success()) | laws])]
      }

      assert [%{"status" => "error", "diagnostics" => diagnostics}] =
               Lynx.Commands.runner!(@lean_dir, request)

      assert diagnostics == [
               %{
                 "file" => path,
                 "kind" => "error",
                 "line" => 10,
                 "column" => 13,
                 "message" => "expected term"
               },
               %{"file" => path, "kind" => "error", "line" => 20, "message" => "expected term"},
               %{"file" => path, "kind" => "error", "message" => "expected term"}
             ]
    end
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
      invalid = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [file(@literal_erl, "Erlang.literal", [%{"kind" => "unknown", "span" => []}])]
      }

      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, invalid)
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
      "value" => %{"kind" => "atom", "value" => "true", "span" => []}
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

  defp fixture_request(path, command) do
    path
    |> File.read!()
    |> JSON.decode!()
    |> Map.put("command", command)
  end
end
