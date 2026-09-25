defmodule LynxTest do
  use ExUnit.Case
  doctest Lynx

  @tag timeout: to_timeout(minute: 10)
  test "Lean builds and tests pass" do
    lake = System.find_executable("lake") || flunk("lake must be installed and available on PATH")
    lean_dir = Path.expand("../Lean", __DIR__)

    for command <- ["build", "test"] do
      {output, status} = System.cmd(lake, [command], cd: lean_dir, stderr_to_stdout: true)
      assert status == 0, "lake #{command} failed with exit status #{status}:\n#{output}"
    end
  end
end
