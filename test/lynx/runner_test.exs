defmodule Lynx.RunnerTest do
  use ExUnit.Case

  @lean_dir Path.expand("../../Lean", __DIR__)
  @translations_dir Path.expand("../fixtures/translations", __DIR__)
  @literal_erl "../test/fixtures/translations/literal.erl"
  @literal_json Path.join(@translations_dir, "literal.json")
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
      request =
        @literal_json
        |> File.read!()
        |> String.replace("Lynx.Term.integer", "Lynx.Term.unknown")
        |> JSON.decode!()
        |> Map.put("command", "verify")

      assert %{"status" => "error", "diagnostics" => diagnostics} =
               Lynx.Commands.runner!(@lean_dir, request)

      assert Enum.any?(diagnostics, fn diagnostic ->
               diagnostic["file"] == @literal_erl and diagnostic["kind"] == "error" and
                 diagnostic["line"] == 4 and diagnostic["column"] == 15
             end)
    end

    test "rejects missing files" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, %{"command" => "verify", "version" => "1.0"})
        end

      assert error.message =~ "files"
    end

    test "rejects missing source files" do
      missing = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [file("../test/fixtures/translations/missing.erl", "missing", [])]
      }

      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, missing)
        end

      assert error.message =~ "missing.erl"
    end
  end

  test "rejects invalid instructions" do
    invalid = %{
      "command" => "render",
      "version" => "1.0",
      "files" => [file(@literal_erl, "literal", [%{"kind" => "unknown", "span" => []}])]
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
