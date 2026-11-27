defmodule Lynx.CmpTermTest do
  use ExUnit.Case, async: false

  @tag :tmp_dir
  test "exact comparison agrees with BEAM on generated literal pairs", %{tmp_dir: tmp_dir} do
    source = Path.join(tmp_dir, "cmp_literal_diff.erl")

    {output, 0} =
      System.cmd("escript", ["test/support/gen_cmp.erl", source], stderr_to_stdout: true)

    assert output =~ "1117 pairs"

    {:ok, :cmp_literal_diff, binary} =
      :compile.file(String.to_charlist(source), [:binary, :debug_info])

    reports =
      Lynx.Laws.verify([binary],
        cache: false,
        options: [maxRecDepth: 10_000, maxHeartbeats: 4_000_000, "exponentiation.threshold": 4096]
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    assert Enum.sum(Enum.map(reports, &length(&1.theorems))) == 1117
  end
end
