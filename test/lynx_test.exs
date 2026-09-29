defmodule LynxTest do
  use ExUnit.Case, async: true

  @tag :tmp_dir
  @tag timeout: to_timeout(minute: 10)
  test "builds new lean project with lynx dependency", %{tmp_dir: tmp_dir} do
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

    {status, output} = Lynx.Commands.lake(tmp_dir, ["build"])
    assert status == 0, "lake build failed with exit status #{status}:\n#{output}"
  end
end
