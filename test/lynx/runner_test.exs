defmodule Lynx.RunnerTest do
  use ExUnit.Case

  @lean_dir Path.expand("../../Lean", __DIR__)
  @translations_dir Path.expand("../fixtures/translations", __DIR__)
  @literal_erl "../test/fixtures/translations/literal.erl"
  @moduletag timeout: to_timeout(minute: 10)

  test "runs successive commands in independent processes" do
    render = %{"command" => "render", "version" => "1.0", "files" => []}
    verify = %{"command" => "verify", "version" => "1.0", "files" => []}
    invalid = %{"command" => "unknown", "version" => "1.0"}

    assert Lynx.Commands.runner!(@lean_dir, render) == %{"status" => "ok", "files" => %{}}

    assert_raise RuntimeError, "unsupported runner command 'unknown'", fn ->
      Lynx.Commands.runner!(@lean_dir, invalid)
    end

    assert Lynx.Commands.runner!(@lean_dir, verify) == %{
             "status" => "ok",
             "diagnostics" => []
           }

    assert {:links, links} = Process.info(self(), :links)
    refute Enum.any?(links, &is_port/1)
  end

  describe "render" do
    test "rejects unsupported versions before reading files" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, %{"command" => "render", "version" => "2.0"})
        end

      assert error.message == "unsupported version"
    end
  end

  describe "verify" do
    test "verifies all translation fixtures" do
      fixtures = Path.wildcard(Path.join(@translations_dir, "*.json"))
      assert fixtures != []

      Enum.each(fixtures, fn fixture ->
        assert Lynx.Commands.runner!(@lean_dir, fixture_request(fixture, "verify")) ==
                 %{"status" => "ok", "diagnostics" => []},
               "verification failed for #{fixture}"
      end)
    end

    test "reports verification errors with source diagnostics" do
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
                "value" => %{"kind" => "var", "name" => "missing", "span" => [4, 15]}
              }
            }
          ])
        ]
      }

      assert %{"status" => "error", "diagnostics" => [diagnostic]} =
               Lynx.Commands.runner!(@lean_dir, request)

      assert %{"file" => @literal_erl, "kind" => "error", "line" => 4, "column" => 15} =
               diagnostic

      assert diagnostic["message"] =~ "Unknown identifier"
    end

    @tag :tmp_dir
    test "reports embedded proof errors with source diagnostics", %{tmp_dir: tmp_dir} do
      path = Path.join(tmp_dir, "law.ex")

      File.write!(path, ~S'''
      defmodule Example do
        law example do
          ~LEAN"""
          have hé : True := by trivial
          exact missing
          """
        end
      end
      ''')

      request = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [
          file(path, "Elixir.Example", [
            %{
              "kind" => "def",
              "name" => "ensures",
              "params" => [],
              "pure" => true,
              "span" => [],
              "body" => %{
                "kind" => "return",
                "span" => [],
                "value" => %{"kind" => "atom", "value" => "true", "span" => []}
              }
            },
            %{
              "kind" => "theorem",
              "name" => "example",
              "arity" => 0,
              "span" => [2, 3],
              "ensures" => "ensures",
              "proof" => %{
                "span" => [4, 5],
                "indentation" => 4,
                "source" => "have hé : True := by trivial\nexact missing\n"
              }
            }
          ])
        ]
      }

      assert Lynx.Commands.runner!(@lean_dir, request) == %{
               "status" => "error",
               "diagnostics" => [
                 %{
                   "file" => path,
                   "kind" => "error",
                   "line" => 5,
                   "column" => 11,
                   "message" => "Unknown identifier `missing`"
                 }
               ]
             }
    end

    test "function table purity metadata is checked rather than trusted" do
      request = fixture_request(Path.join(@translations_dir, "functions.json"), "verify")
      table_file = List.last(request["files"])
      [table] = table_file["contents"]
      entries = table["entries"]
      assert Enum.frequencies_by(entries, & &1["pure"]) == %{true => 3, false => 2}

      for {entry, index} <- Enum.with_index(entries), entry["pure"] == false do
        wrong_entries = List.update_at(entries, index, &Map.put(&1, "pure", true))
        wrong_table = Map.put(table, "entries", wrong_entries)
        wrong_file = Map.put(table_file, "contents", [wrong_table])
        wrong_request = Map.put(request, "files", Enum.drop(request["files"], -1) ++ [wrong_file])

        assert %{"status" => "error", "diagnostics" => diagnostics} =
                 Lynx.Commands.runner!(@lean_dir, wrong_request)

        assert Enum.any?(diagnostics, fn diagnostic ->
                 diagnostic["kind"] == "error" and
                   (diagnostic["message"] =~ "IsPure" or
                      diagnostic["message"] =~ "simp` made no progress")
               end)
      end
    end

    test "rejects missing files" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, %{"command" => "verify", "version" => "1.0"})
        end

      assert error.message =~ "files"
    end

    test "verifies without source files and identifies unavailable source in errors" do
      path = "../test/fixtures/translations/missing.erl"

      request = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [file(path, "Erlang.missing", [])]
      }

      assert Lynx.Commands.runner!(@lean_dir, request) == %{"status" => "ok", "diagnostics" => []}

      broken = %{
        "kind" => "def",
        "name" => "broken",
        "params" => [],
        "pure" => false,
        "span" => [20, 7],
        "body" => %{
          "kind" => "return",
          "span" => [],
          "value" => %{"kind" => "var", "name" => "missing", "span" => []}
        }
      }

      request = Map.put(request, "files", [file(path, "Erlang.missing", [broken])])

      assert %{"status" => "error", "diagnostics" => [diagnostic]} =
               Lynx.Commands.runner!(@lean_dir, request)

      assert %{"line" => 20, "column" => 7, "kind" => "error"} = diagnostic
      assert diagnostic["message"] =~ "source not available"
    end
  end

  test "rejects invalid instructions" do
    invalid = %{
      "command" => "render",
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
