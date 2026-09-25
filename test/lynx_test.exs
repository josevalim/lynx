defmodule LynxTest do
  use ExUnit.Case
  doctest Lynx

  @tag :tmp_dir
  @tag timeout: to_timeout(minute: 10)
  test "verifies translated Erlang in a Lean project with Lynx as a dependency", %{
    tmp_dir: tmp_dir
  } do
    lake = System.find_executable("lake") || flunk("lake must be installed and available on PATH")
    lean_dir = Path.expand("../Lean", __DIR__)

    File.cp!(Path.join(lean_dir, "lean-toolchain"), Path.join(tmp_dir, "lean-toolchain"))

    File.write!(Path.join(tmp_dir, "lakefile.toml"), """
    name = "TranslationTest"
    version = "0.1.0"
    defaultTargets = ["TranslationTest"]

    [[require]]
    name = "Lynx"
    path = #{inspect(lean_dir)}

    [[lean_lib]]
    name = "TranslationTest"
    """)

    File.write!(Path.join(tmp_dir, "TranslationTest.lean"), """
    module
    import Lynx
    """)

    {output, status} = System.cmd(lake, ["build"], cd: tmp_dir, stderr_to_stdout: true)
    assert status == 0, "lake build failed with exit status #{status}:\n#{output}"

    fixture_dir = Path.join(lean_dir, "LynxTest/Frontend")
    source_dir = Path.join(tmp_dir, "LynxTest/Frontend")
    File.mkdir_p!(source_dir)
    File.cp!(Path.join(fixture_dir, "sum.erl"), Path.join(source_dir, "sum.erl"))
    File.cp!(Path.join(fixture_dir, "sum.json"), Path.join(tmp_dir, "request.json"))

    # System.cmd/3 has no stdin option. Pass arguments separately to the shell
    # and redirect the request file so the frontend receives stdin followed by EOF.
    {output, status} =
      System.cmd(
        "sh",
        [
          "-c",
          ~s(exec "$@" < request.json),
          "frontend",
          lake,
          "env",
          "lean",
          "--run",
          Path.join(lean_dir, "Lynx/Frontend.lean"),
          "verify"
        ],
        cd: tmp_dir,
        stderr_to_stdout: true
      )

    assert status == 0, "frontend verification failed with exit status #{status}:\n#{output}"
    assert JSON.decode!(output) == %{"status" => "ok", "diagnostics" => []}
  end
end
