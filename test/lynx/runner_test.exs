defmodule Lynx.RunnerTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @translations_dir Path.expand("../fixtures/translations", __DIR__)
  @sum_erl "../test/fixtures/translations/sum.erl"
  @sum_json Path.join(@translations_dir, "sum.json")

  @moduletag timeout: to_timeout(minute: 10)

  test "one runner handles successive commands and continues after a failed request" do
    lake = System.find_executable("lake")

    port =
      Port.open(
        {:spawn_executable, String.to_charlist(lake)},
        [
          :binary,
          :exit_status,
          :use_stdio,
          :hide,
          {:line, 1_000_000},
          cd: @lean_dir,
          args: ["env", "lean", "--run", Path.join(@lean_dir, "Lynx/Runner.lean")]
        ]
      )

    try do
      assert request(port, %{"command" => "unknown", "version" => "1.0"}) == %{
               "status" => "failure",
               "message" => "unsupported runner command 'unknown'"
             }

      assert request(port, %{"command" => "verify", "version" => "2.0"}) == %{
               "status" => "failure",
               "message" => "unsupported version"
             }

      assert %{"status" => "failure", "message" => missing_files} =
               request(port, %{"command" => "verify", "version" => "1.0"})

      assert missing_files =~ "files"

      fixture = JSON.decode!(File.read!(@sum_json))

      assert request(port, Map.put(fixture, "command", "verify")) == %{
               "status" => "ok",
               "diagnostics" => []
             }

      assert %{"status" => "ok", "files" => files} =
               request(port, Map.put(fixture, "command", "render"))

      assert Map.has_key?(files, @sum_erl)
    after
      Port.close(port)
    end
  end

  describe "render" do
    test "rejects malformed JSON" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, "{")
        end

      assert error.message == "offset 2: unexpected end of input"
    end
  end

  describe "verify" do
    test "verifies all translation fixtures" do
      fixtures = Path.wildcard(Path.join(@translations_dir, "*.json"))
      assert fixtures != []

      for fixture <- fixtures do
        assert Lynx.Commands.runner!(@lean_dir, fixture_request(fixture, "verify")) ==
                 %{"status" => "ok", "diagnostics" => []},
               "verification failed for #{fixture}"
      end
    end

    test "reports verification errors with source diagnostics" do
      request =
        @sum_json
        |> fixture_request("verify")
        |> String.replace("Erlang.erlang.«+/2»", "Erlang.erlang.«unknown/2»")

      assert %{"status" => "error", "diagnostics" => diagnostics} =
               Lynx.Commands.runner!(@lean_dir, request)

      assert Enum.any?(diagnostics, fn diagnostic ->
               diagnostic["file"] == @sum_erl and diagnostic["kind"] == "error" and
                 diagnostic["line"] == 4 and diagnostic["column"] == 20
             end)
    end

    test "rejects malformed JSON" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, "{")
        end

      assert error.message == "offset 2: unexpected end of input"
    end

    test "rejects missing source files" do
      missing = %{
        "command" => "verify",
        "version" => "1.0",
        "files" => [file("../test/fixtures/translations/missing.erl", "missing", [])]
      }

      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, JSON.encode!(missing))
        end

      assert error.message =~ "missing.erl"
    end
  end

  test "rejects empty mutual blocks and non-definition members" do
    for {defs, message} <- [
          {[], "mutual requires at least one definition"},
          {[%{"kind" => "mutual", "span" => [], "defs" => []}],
           "mutual requires def declarations"}
        ] do
      request = %{
        "command" => "render",
        "version" => "1.0",
        "files" => [file(@sum_erl, "sum", [%{"kind" => "mutual", "span" => [], "defs" => defs}])]
      }

      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, JSON.encode!(request))
        end

      assert error.message =~ message
    end
  end

  test "rejects invalid instructions" do
    invalid = %{
      "command" => "render",
      "version" => "1.0",
      "files" => [file(@sum_erl, "sum", [%{"kind" => "unknown", "span" => []}])]
    }

    error =
      assert_raise RuntimeError, fn ->
        Lynx.Commands.runner!(@lean_dir, JSON.encode!(invalid))
      end

    assert error.message =~ @sum_erl
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
    |> JSON.encode!()
  end

  defp request(port, value) do
    Port.command(port, JSON.encode!(value) <> "\n")
    response(port, "")
  end

  defp response(port, output) do
    receive do
      {^port, {:data, {:eol, data}}} ->
        JSON.decode!(output <> data)

      {^port, {:data, {:noeol, data}}} ->
        response(port, output <> data)

      {^port, {:exit_status, status}} ->
        flunk("runner exited before responding with status #{status}")
    end
  end
end
