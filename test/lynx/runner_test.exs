defmodule Lynx.RunnerTest do
  use ExUnit.Case, async: true

  @lean_dir Path.expand("../../Lean", __DIR__)
  @translations_dir Path.expand("../fixtures/translations", __DIR__)
  @sum_erl "../test/fixtures/translations/sum.erl"
  @sum_json Path.join(@translations_dir, "sum.json")

  @moduletag timeout: to_timeout(minute: 10)

  describe "render" do
    test "renders all translation fixtures as Lean source" do
      fixtures = Path.wildcard(Path.join(@translations_dir, "*.json"))
      assert fixtures != []

      for fixture <- fixtures do
        response = Lynx.Commands.runner!(@lean_dir, "render", File.read!(fixture))
        source = "../test/fixtures/translations/#{Path.basename(fixture, ".json")}.erl"
        expected = File.read!(Path.rootname(fixture) <> ".lean")

        assert response == %{"status" => "ok", "files" => %{source => expected}},
               "rendered output does not match #{fixture}"
      end
    end

    test "rejects malformed JSON" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, "render", "{")
        end

      assert error.message == "offset 2: unexpected end of input"
    end
  end

  describe "verify" do
    test "verifies valid instructions" do
      request = File.read!(@sum_json)

      assert %{"status" => "ok", "diagnostics" => []} =
               Lynx.Commands.runner!(@lean_dir, "verify", request)
    end

    test "reports verification errors with source diagnostics" do
      request =
        @sum_json
        |> File.read!()
        |> String.replace("Lynx.Modules.Erlang.add_2", "Lynx.Modules.Erlang.unknown_2")

      assert %{"status" => "error", "diagnostics" => diagnostics} =
               Lynx.Commands.runner!(@lean_dir, "verify", request)

      assert Enum.any?(diagnostics, fn diagnostic ->
               diagnostic["file"] == @sum_erl and diagnostic["kind"] == "error" and
                 diagnostic["line"] == 4 and diagnostic["column"] == 18
             end)
    end

    test "rejects malformed JSON" do
      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, "verify", "{")
        end

      assert error.message == "offset 2: unexpected end of input"
    end

    # TODO: pass the file as part of the json input
    test "rejects missing source files" do
      missing = %{
        "version" => "1.0",
        "files" => %{"../test/fixtures/translations/missing.erl" => []}
      }

      error =
        assert_raise RuntimeError, fn ->
          Lynx.Commands.runner!(@lean_dir, "verify", JSON.encode!(missing))
        end

      assert error.message =~ "missing.erl"
    end
  end

  test "rejects invalid instructions" do
    invalid = %{
      "version" => "1.0",
      "files" => %{@sum_erl => [%{"kind" => "unknown", "span" => []}]}
    }

    error =
      assert_raise RuntimeError, fn ->
        Lynx.Commands.runner!(@lean_dir, "render", JSON.encode!(invalid))
      end

    assert error.message =~ @sum_erl
    assert error.message =~ "unsupported command kind 'unknown'"
  end
end
