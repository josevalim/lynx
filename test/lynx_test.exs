defmodule LynxTest do
  use ExUnit.Case, async: true

  test "verifies laws from a module compiled in memory" do
    {:module, _module, binary, _} =
      defmodule Laws do
        @compile :debug_info
        use Lynx.Laws

        law checked, expects: identity(true)
        law another, expects: true

        defp identity(value), do: value
        def unused, do: make_ref()
      end

    assert [
             %{
               status: :ok,
               diagnostics: [],
               module: "Elixir.LynxTest.Laws",
               source: source,
               file: file,
               time_ms: time,
               cached: cached
             }
           ] =
             Lynx.verify!([binary])

    assert file == __ENV__.file
    assert is_integer(time) and time >= 0
    assert is_boolean(cached)
    assert source =~ "«checked/0»"
    assert source =~ "«another/0»"
    assert source =~ "«identity/1»"
    refute source =~ "«unused/0»"
  end
end
