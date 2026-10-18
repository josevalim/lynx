defmodule Lynx.LeanTest do
  use ExUnit.Case, async: true

  @tag :tmp_dir
  test "from_file! reads Lean source located at the file's start", %{tmp_dir: tmp_dir} do
    path = Path.join(tmp_dir, "tactics.lean")
    File.write!(path, "macro \"done\" : tactic => `(tactic| rfl)\n")

    assert %Lynx.Lean{
             source: "macro \"done\" : tactic => `(tactic| rfl)\n",
             file: ^path,
             span: {1, 1},
             indentation: 0
           } = Lynx.Lean.from_file!(path)
  end
end
