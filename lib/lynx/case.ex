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

  Each group registers one ExUnit test of type `:laws`. Run groups with
  `mix test --only laws`.
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

  @doc """
  Defines a callable law and includes it in the current laws group.

  The must be explicitly declared in a `laws/2` block.

  ## Options

    * `:requires` (optional) — the precondition expression. Defaults to `true`.
    * `:expects` (required) — the expression to prove.
    * `:proof` (optional) — a literal `~LEAN` sigil. Defaults to `rfl`.

  ## Executable definition

  Besides defining a law, `law/2` also defines a public function that you can
  invoke passing Elixir values. Elixir will then validate said values against the
  given `:requires`, the given `:expects`, and return true when both predicates
  succeed, otherwise it will raise. This is useful to provide counter examples.
  """
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

  @doc """
  Registers a group of laws as one ExUnit test.

  The test translates the laws and their callees, verifies their proofs,
  and fails if they do not pass.

  Each group has the `:laws` test type and tag. Run only law groups with
  `mix test --only laws`.

  ## Example

      laws "checked" do
        law checked(value),
          requires: value,
          expects: value,
          proof: ~LEAN"exact requires"
      end

  If verifying the laws fail, the error report includes the path to folder with
  all `.lean` files. Use this to debug and guide your proofs.
  """
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
    files =
      Lynx.Translation.new()
      |> Lynx.Translation.add(Lynx.Bytecode.fetch!(module))
      |> Lynx.Translation.verify(module, laws)
      |> Lynx.Translation.assemble()

    signatures =
      for file <- files,
          %{"kind" => "theorem", "name" => name, "params" => params} <- file["contents"],
          into: %{} do
        {{file["module"], "#{name}/#{length(params)}"}, "#{name}(#{Enum.join(params, ", ")})"}
      end

    reports = Lynx.Commands.verify!(@lean_dir, files)

    errors =
      for report <- reports,
          report.status != :ok,
          diagnostic <- report.diagnostics,
          diagnostic.severity == :error do
        location =
          Exception.format_file_line_column(
            Path.relative_to_cwd(diagnostic.file),
            diagnostic[:line],
            diagnostic[:column]
          )

        message =
          case Map.fetch(signatures, {diagnostic.module, diagnostic.declaration}) do
            {:ok, signature} ->
              "#{location} proof for law #{signature} failed\n\n#{diagnostic.message}"

            _ ->
              "#{location} #{diagnostic.message}"
          end

        try do
          ExUnit.Assertions.flunk(message)
        rescue
          error in ExUnit.AssertionError -> {:error, error, __STACKTRACE__}
        end
      end

    if errors != [], do: raise(ExUnit.MultiError, errors: errors)

    :ok
  end
end
