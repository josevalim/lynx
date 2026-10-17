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

  test "cutoffs allow unreachable dependencies but cannot prove a reached call returns" do
    defmodule Cutoffs do
      use ExUnit.Case, register: false
      use Lynx.Case

      def choose(true), do: true
      def choose(value), do: unavailable(value)
      def unavailable(value), do: :erlang.nif_error(value)

      laws "unreached" do
        cutoff &__MODULE__.unavailable/1

        law returns(value),
          requires: value,
          expects: choose(value),
          proof: ~LEAN"""
          have actual : value = .atom "true" := by simpa [«returns:requires/1»] using requires
          subst value
          simp [«returns:ensures/1», «choose/1»]
          """
      end

      laws "reached" do
        cutoff &__MODULE__.unavailable/1

        law cannot_claim_return,
          expects: choose(false),
          proof: ~LEAN"""
          simp [«cannot_claim_return:ensures/0», «choose/1», «unavailable/1»]
          """
      end
    end

    output =
      capture_io(fn ->
        send(self(), {:cutoff_results, ExUnit.run([Cutoffs])})
      end)

    assert_receive {:cutoff_results, results}
    assert results == %{failures: 1, skipped: 0, total: 2, excluded: 0}, output
    assert output =~ "laws reached"
    assert output =~ "proof for law cannot_claim_return() failed"
    refute output =~ "CompileError"
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

  test "preludes are available to suffixes and remain group scoped" do
    defmodule Elaborators do
      use ExUnit.Case, register: false
      use Lynx.Case

      def increment(value) when is_integer(value), do: increment(value + 1)
      def increment(_value), do: true

      laws "custom syntax" do
        prelude ~LEAN"""
        namespace PreludeTest
        theorem truth : True := by trivial
        end PreludeTest
        open Lean Elab Tactic
        elab "test_partial" : tactic => do evalTactic (← `(tactic| (
          intro f g h n
          cases n <;> simp
          all_goals first | exact h _ | exact Lean.Order.PartialOrder.rel_refl)))
        """

        # Parsing this declaration requires the syntax from the previous one.
        prelude ~LEAN"""
        elab "test_partial_again" : tactic => do evalTactic (← `(tactic| test_partial))
        elab "test_finish" : tactic => do evalTactic (← `(tactic| rfl))
        """

        termination_suffix &__MODULE__.increment/1, ~LEAN"""
        partial_fixpoint monotonicity by test_partial_again
        """

        law stops(value),
          requires: is_atom(value),
          expects: increment(value),
          proof: ~LEAN"""
          cases value <;> simp [«stops:requires/1», Erlang.erlang.«is_atom/1»] at requires
          simp [«stops:ensures/1», «increment/1».eq_def]
          """

        law finished, expects: true, proof: ~LEAN"have := PreludeTest.truth; test_finish"
      end

      laws "independent registration" do
        prelude ~LEAN"""
        open Lean Elab Tactic
        elab "test_finish" : tactic => throwError "second prelude loaded"
        """

        law independent,
          expects: true,
          proof: ~LEAN"""
          fail_if_success test_finish
          rfl
          """
      end

      laws "without registration" do
        law unavailable, expects: true, proof: ~LEAN"test_finish"
      end
    end

    output =
      capture_io(fn ->
        assert ExUnit.run([Elaborators]) ==
                 %{failures: 1, skipped: 0, total: 3, excluded: 0}
      end)

    assert output =~ "laws without registration"
    refute output =~ "laws custom syntax ("
    assert output =~ "proof for law unavailable() failed"
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
        LawFailure."laws invalid / proof: [errors]"(%{})
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
             "Elixir.Lynx.CaseTest.LawFailure.laws.lean",
             "Elixir.Lynx.CaseTest.LawFailure.lean"
           ]

    assert File.read!(Path.join(path, "Elixir.Function.lean")) =~ "identity/1"
    assert File.read!(Path.join(path, "Elixir.Lynx.CaseTest.LawFailure.laws.lean")) =~ "sum_bar/2"
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

    test "rejects invalid group options" do
      assert_raise ArgumentError, "unknown laws option :timeout", fn ->
        defmodule UnknownOption do
          use ExUnit.Case, register: false
          use Lynx.Case

          laws "unknown", timeout: 1 do
            law unknown_option, expects: true
          end
        end
      end

      assert_raise ArgumentError, ~r/laws options must be Lean option names/, fn ->
        defmodule InvalidOption do
          use ExUnit.Case, register: false
          use Lynx.Case

          laws "invalid", options: [maxRecDepth: 1.5] do
            law invalid_option, expects: true
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
