defmodule Lynx.Case do
  @moduledoc """
  Define callable laws alongside ExUnit tests.

  Add `use Lynx.Case` after `use ExUnit.Case`, then group laws to verify together:

      use ExUnit.Case, async: true
      use Lynx.Case

      laws "identity" do
        law identity(value), requires: value, expects: value,
          proof: ~LEAN"exact requires"
      end

  Each group registers one ExUnit test of type `:laws`. Its laws and their
  callees are translated together, with theorems verified in source order.
  Laws remain callable from regular tests. Run groups with `mix test --only laws`.
  """

  @lean_dir Path.expand("../../Lean", __DIR__)

  defmacro __using__(_opts) do
    quote do
      Lynx.Case.__register__(__MODULE__)
      import Lynx.Case, only: [law: 2, laws: 2]
    end
  end

  @doc false
  def __register__(module) do
    unless Module.has_attribute?(module, :ex_unit_tests) do
      raise ArgumentError, "you must Lynx.Case after use ExUnit.Case"
    end

    ExUnit.plural_rule("laws", "laws")
    Module.put_attribute(module, :after_compile, __MODULE__)
    Module.put_attribute(module, :compile, :debug_info)
    Lynx.Laws.__register__(module)
  end

  @doc "Defines a callable law and includes it in the current laws group."
  defmacro law(call, opts) do
    {name, definition} = Lynx.Laws.__law__(__CALLER__, call, opts)

    quote do
      Lynx.Case.__law__(__MODULE__, unquote(Macro.escape(name)))
      unquote(definition)
    end
  end

  @doc false
  def __law__(module, name) do
    case Module.get_attribute(module, :lynx_laws) do
      nil ->
        raise ArgumentError, "law must be defined inside a laws group"

      group_laws ->
        Module.put_attribute(module, :lynx_laws, [name | group_laws])
    end
  end

  @doc "Registers a group of laws as one ExUnit test."
  defmacro laws(description, do: block) do
    definition =
      quote unquote: false do
        def unquote(name)(_context) do
          Lynx.Case.__verify__(__MODULE__, unquote(group_laws))
        end
      end

    quote do
      {name, group_laws} =
        Lynx.Case.__laws__(
          __MODULE__,
          unquote(__CALLER__.file),
          unquote(__CALLER__.line),
          unquote(description),
          fn -> unquote(block) end
        )

      unquote(definition)
    end
  end

  @doc false
  def __laws__(module, file, line, description, fun) do
    if Module.get_attribute(module, :lynx_laws) do
      raise ArgumentError, "laws groups cannot be nested"
    end

    Module.put_attribute(module, :lynx_laws, [])

    try do
      fun.()
      group_laws = module |> Module.get_attribute(:lynx_laws) |> Enum.reverse()

      if group_laws == [] do
        raise CompileError, file: file, line: line, description: "laws group must contain a law"
      end

      name = ExUnit.Case.register_test(module, file, line, :laws, description, [:laws])
      {name, group_laws}
    after
      Module.delete_attribute(module, :lynx_laws)
    end
  end

  @doc false
  def __after_compile__(env, beam) do
    # ExUnit compiles .exs modules in memory, so there is no BEAM on the code path.
    # Recompiling a module replaces its retained binary.
    Lynx.Bytecode.put(env.module, beam)
  end

  @doc false
  def __verify__(module, laws) do
    reports =
      Lynx.Translation.new()
      |> Lynx.Translation.add(Lynx.Bytecode.fetch!(module))
      |> Lynx.Translation.verify(module, laws)
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
