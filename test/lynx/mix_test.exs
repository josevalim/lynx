defmodule Lynx.MixTest do
  use ExUnit.Case, async: true

  @moduletag :tmp_dir
  @root Path.expand("../..", __DIR__)

  setup %{tmp_dir: tmp_dir} do
    File.cp!(Path.join(@root, "mix.exs"), Path.join(tmp_dir, "mix.exs"))
    File.mkdir_p!(Path.join(tmp_dir, "lib"))
    File.cp!(Path.join(@root, "lib/lynx.ex"), Path.join(tmp_dir, "lib/lynx.ex"))
    :ok
  end

  test "module help works before compilation without building Lean", %{tmp_dir: tmp_dir} do
    for _ <- 1..2 do
      assert {output, 0} = mix_help(tmp_dir, "Lynx")
      assert output =~ "Write proofs about Erlang/Elixir programs using Lean."
      assert output =~ "Writing proofs"
      refute output =~ "Could not load module"
      refute output =~ "warning:"
    end

    assert Path.wildcard(Path.join(tmp_dir, "_build/**/*.beam")) == [
             Path.join(tmp_dir, "_build/lib/lynx/ebin/Elixir.Lynx.beam")
           ]
  end

  test "other help requests keep their normal behavior", %{tmp_dir: tmp_dir} do
    assert {output, 0} = mix_help(tmp_dir, "compile")
    assert output =~ "mix compile"

    assert {output, 0} = mix_help(tmp_dir, [])
    assert output =~ "mix help"

    assert {output, 0} = mix_help(tmp_dir, "--names")
    assert "compile" in String.split(output, "\n")
    refute File.exists?(Path.join(tmp_dir, "_build"))
  end

  defp mix_help(dir, args) do
    System.cmd(System.find_executable("mix"), ["help" | List.wrap(args)],
      cd: dir,
      stderr_to_stdout: true,
      env: [
        {"MIX_ENV", "dev"},
        {"MIX_BUILD_PATH", Path.join(dir, "_build")}
      ]
    )
  end
end
