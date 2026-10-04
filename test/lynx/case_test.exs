defmodule Lynx.CaseTest do
  use ExUnit.Case

  import ExUnit.CaptureIO

  setup_all do
    old_opts = ExUnit.configuration()

    ExUnit.configure(
      autorun: false,
      seed: 0,
      colors: [enabled: false],
      include: [],
      exclude: [],
      only_test_ids: nil,
      max_failures: :infinity
    )

    on_exit(fn -> ExUnit.configure(old_opts) end)
  end

  test "reports translation failures" do
    defmodule TranslationFailure do
      use ExUnit.Case, register: false
      use Lynx.Case

      laws "valid" do
        law valid, expects: true
      end

      laws "unsupported" do
        law unsupported, expects: :erlang.nif_error(:unsupported)
      end
    end

    output =
      capture_io(fn ->
        assert ExUnit.run([TranslationFailure]) ==
                 %{failures: 1, skipped: 0, total: 2, excluded: 0}
      end)

    assert output =~ "laws unsupported"
    assert output =~ "CompileError"
    assert output =~ "cannot locate BEAM for :erlang"
  end

  test "reports failed laws" do
    defmodule LawFailure do
      use ExUnit.Case, register: false
      use Lynx.Case

      laws "valid" do
        law valid, expects: true
      end

      laws "invalid" do
        law invalid, expects: false
      end
    end

    output =
      capture_io(fn ->
        assert ExUnit.run([LawFailure]) == %{failures: 1, skipped: 0, total: 2, excluded: 0}
      end)

    assert output =~ "laws invalid"
    assert output =~ "`rfl` failed"
  end

  describe "errors" do
    test "rejects laws outside a group" do
      assert_raise ArgumentError, "law must be defined inside a laws group", fn ->
        defmodule Ungrouped do
          use ExUnit.Case, register: false
          use Lynx.Case

          law ungrouped, expects: true
        end
      end

      assert_raise ArgumentError, "law must be defined inside a laws group", fn ->
        defmodule AfterGroup do
          use ExUnit.Case, register: false
          use Lynx.Case

          laws "grouped" do
            law grouped, expects: true
          end

          law ungrouped, expects: true
        end
      end
    end

    test "rejects empty groups" do
      assert_raise CompileError, ~r/laws group must contain a law/, fn ->
        defmodule Empty do
          use ExUnit.Case, register: false
          use Lynx.Case

          laws "empty" do
          end
        end
      end
    end

    test "rejects nested groups" do
      assert_raise ArgumentError, "laws groups cannot be nested", fn ->
        defmodule Nested do
          use ExUnit.Case, register: false
          use Lynx.Case

          laws "outer" do
            laws "inner" do
              law nested, expects: true
            end
          end
        end
      end
    end
  end
end
