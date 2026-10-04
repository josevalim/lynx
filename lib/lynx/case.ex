defmodule Lynx.Case do
  @moduledoc """
  Define callable laws alongside ExUnit tests.

  Add `use Lynx.Case` after `use ExUnit.Case` to import the law DSL and register
  each declared law as an ExUnit test of type `:law`:

      use ExUnit.Case, async: true
      use Lynx.Case

  Each law test translates the law and its callees and verifies its Lean proof.
  Laws also remain callable from regular tests to check concrete inputs.
  Run only law tests with `mix test --only laws`.
  """

  @lean_dir Path.expand("../../Lean", __DIR__)

  defmacro __using__(_opts) do
    quote do
      unless Module.has_attribute?(__MODULE__, :ex_unit_tests) do
        raise ArgumentError, "use ExUnit.Case before use Lynx.Case"
      end

      # Register laws before ExUnit snapshots the module's tests, preserving
      # the order of the other compile callbacks.
      callbacks = Module.get_attribute(__MODULE__, :before_compile)
      Module.delete_attribute(__MODULE__, :before_compile)

      for callback <- Enum.reverse(callbacks) do
        if callback == {ExUnit.Case, :__before_compile__} do
          @before_compile Lynx.Case
        end

        @before_compile callback
      end

      @after_compile Lynx.Case
      @compile :debug_info
      use Lynx.Laws
    end
  end

  @doc false
  defmacro __before_compile__(%{module: module, file: file}) do
    tests =
      for %{name: {name, params}, span: span} <-
            module |> Module.get_attribute(:law) |> Enum.reverse() do
        line = if is_tuple(span), do: elem(span, 0), else: span
        description = "#{name}/#{length(params)}"
        test = ExUnit.Case.register_test(module, file, line, :law, description, [:laws])

        quote do
          def unquote(test)(_context) do
            Lynx.Case.__verify__(__MODULE__, unquote(name), unquote(length(params)))
          end
        end
      end

    quote do
      (unquote_splicing(tests))
    end
  end

  @doc false
  def __after_compile__(env, beam) do
    # ExUnit compiles .exs modules in memory, so there is no BEAM on the code path.
    # Recompiling a module replaces its retained binary.
    :persistent_term.put({__MODULE__, env.module}, beam)
  end

  @doc false
  def __verify__(module, name, arity) do
    reports =
      Lynx.Translation.new()
      |> Lynx.Translation.add(:persistent_term.get({__MODULE__, module}))
      |> Lynx.Translation.translate(module, [{name, arity}])
      |> Lynx.Translation.assemble()
      |> then(&Lynx.Commands.verify!(@lean_dir, &1))

    for report <- reports do
      message =
        Enum.map_join(report.diagnostics, "\n", fn diagnostic ->
          "#{diagnostic.file}:#{Map.get(diagnostic, :line, 1)}: #{diagnostic.message}"
        end)

      ExUnit.Assertions.assert(report.status == :ok, message)
    end

    :ok
  end
end
