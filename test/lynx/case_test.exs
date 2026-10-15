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

  test "verifies termination suffixes within their laws group" do
    defmodule TerminationSuffix do
      use ExUnit.Case, register: false
      use Lynx.Case

      def increment(value) when is_integer(value), do: increment(value + 1)
      def increment(_value), do: true

      laws "partial recursion" do
        termination_suffix &__MODULE__.increment/1, ~LEAN"""
        partial_fixpoint monotonicity by
          intro f g h n
          cases n <;> simp
          all_goals first | exact h _ | exact Lean.Order.PartialOrder.rel_refl
        """

        law stops(value),
          requires: is_atom(value),
          expects: increment(value),
          proof: ~LEAN"""
          cases value <;> simp [«stops:requires/1», Erlang.erlang.«is_atom/1»] at requires
          simp [«stops:ensures/1», «increment/1».eq_def]
          """
      end

      laws "without annotation" do
        law valid, expects: true
      end
    end

    capture_io(fn ->
      assert ExUnit.run([TerminationSuffix]) ==
               %{failures: 0, skipped: 0, total: 2, excluded: 0}
    end)
  end

  test "reports multiple failed laws as separate assertions" do
    defmodule LawFailure do
      use ExUnit.Case, register: false
      use Lynx.Case

      laws "valid" do
        law valid, expects: true
      end

      laws "invalid / proof: [errors]" do
        law passing, expects: Function.identity(true)
        law invalid, expects: false
        law sum_bar(a, b), requires: a and b, expects: false
      end

      laws "syntax" do
        law invalid_syntax, expects: true, proof: ~LEAN"exact ("
      end
    end

    error =
      assert_raise ExUnit.MultiError, fn ->
        Lynx.Case.__verify__(
          LawFailure,
          :"laws invalid / proof: [errors]",
          [
            {:passing, 0},
            {:invalid, 0},
            {:sum_bar, 2}
          ],
          %{}
        )
      end

    assert [
             {:error, %ExUnit.AssertionError{message: first}, [_ | _]},
             {:error, %ExUnit.AssertionError{message: second}, [_ | _]}
           ] = error.errors

    assert first =~ "proof for law invalid() failed"
    refute first =~ "proof for law sum_bar(a, b) failed"
    assert second =~ "proof for law sum_bar(a, b) failed"
    refute second =~ "proof for law invalid() failed"
    refute first =~ "The translated .lean files are available at"

    output =
      capture_io(fn ->
        assert ExUnit.run([LawFailure]) == %{failures: 2, skipped: 0, total: 3, excluded: 0}
      end)

    assert output =~ "laws invalid"
    assert output =~ "proof for law invalid() failed\n"
    assert output =~ "proof for law sum_bar(a, b) failed\n"
    assert output =~ "proof for law invalid_syntax() failed\n"

    assert output =~
             ~r/test\/lynx\/case_test\.exs:\d+:\d+: proof for law invalid_syntax\(\) failed/

    refute output =~ "proof for law passing() failed"
    assert output =~ "test/lynx/case_test.exs:"
    refute output =~ Path.expand(__ENV__.file)
    assert output =~ "`rfl` failed"
    assert output =~ "unexpected end of input"

    path = "tmp/Lynx.CaseTest.LawFailure/laws-invalid---proof---errors-"
    assert String.ends_with?(second, "The translated .lean files are available at #{path}")

    assert Enum.sort(File.ls!(path)) == [
             "Elixir.Function.lean",
             "Elixir.Lynx.CaseTest.LawFailure.lean"
           ]

    assert File.read!(Path.join(path, "Elixir.Function.lean")) =~ "identity/1"
    assert File.read!(Path.join(path, "Elixir.Lynx.CaseTest.LawFailure.lean")) =~ "sum_bar/2"
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
