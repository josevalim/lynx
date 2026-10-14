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

  Set `LYNX_PROFILE=1` to print each translated module's reported
  verification time in milliseconds, status, and whether it was cached,
  as well as the elaboration time of any law.

  Set `LYNX_CACHE=0` to disable the verification cache.
  """

  @lean_dir Path.expand("../../Lean", __DIR__)

  defmacro __using__(_opts) do
    quote do
      Lynx.Case.__register__(__MODULE__)
      import Lynx.Case, only: [law: 2, laws: 2, termination_suffix: 2]
      import Lynx.Lean, only: [sigil_LEAN: 2]
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
    * `:proof` (optional) — a `Lynx.Lean` value. Defaults to `rfl`.

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
  Attaches a Lean termination suffix to a translated function for this laws group.

      termination_suffix :calendar.mod/2, ~LEAN"partial_fixpoint"

  The source is a `Lynx.Lean` value. It is parsed as part of the function's
  declaration, after its body. Providing a suffix disables automatic purity
  proofs (`#lynx_pure`) for the function and its callers, regardless of the suffix
  contents. They are conservatively classified as impure; purity may be proved
  separately when needed.
  Raises if the target function is not translated by the group's laws.
  """
  defmacro termination_suffix(target, source) do
    mfa =
      case target do
        {:/, _, [{{:., _, [module, name]}, _, []}, arity]}
        when is_atom(name) and is_integer(arity) and arity >= 0 ->
          module = Macro.expand(module, __CALLER__)

          if not is_atom(module),
            do: raise(ArgumentError, "expected a module in termination_suffix")

          {module, name, arity}

        _ ->
          raise ArgumentError, "termination_suffix expects Module.function/arity"
      end

    quote do
      Lynx.Case.__termination_suffix__(__MODULE__, unquote(Macro.escape(mfa)), unquote(source))
    end
  end

  @doc false
  def __termination_suffix__(module, {target, name, arity} = mfa, %Lynx.Lean{} = source) do
    case Module.get_attribute(module, :lynx_termination_suffixes) do
      nil ->
        raise ArgumentError, "termination_suffix must be defined inside a laws group"

      suffixes ->
        if Map.has_key?(suffixes, mfa),
          do:
            raise(
              ArgumentError,
              "duplicate termination_suffix for #{Exception.format_mfa(target, name, arity)}"
            )

        Module.put_attribute(module, :lynx_termination_suffixes, Map.put(suffixes, mfa, source))
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
          Lynx.Case.__verify__(
            __MODULE__,
            unquote(name),
            unquote(group_laws),
            unquote(Macro.escape(suffixes))
          )
        end
      end

    quote do
      {name, group_laws, suffixes} =
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
    Module.put_attribute(module, :lynx_termination_suffixes, %{})

    try do
      fun.()
      group_laws = module |> Module.get_attribute(:lynx_laws) |> Enum.reverse()

      if group_laws == [] do
        raise CompileError, file: file, line: line, description: "laws group must contain a law"
      end

      name = ExUnit.Case.register_test(module, file, line, :laws, description, [:laws])
      {name, group_laws, Module.get_attribute(module, :lynx_termination_suffixes)}
    after
      Module.delete_attribute(module, :lynx_laws)
      Module.delete_attribute(module, :lynx_termination_suffixes)
    end
  end

  @doc false
  def __after_compile__(env, beam) do
    # ExUnit compiles .exs modules in memory, so there is no BEAM on the code path.
    # Recompiling a module replaces its retained binary.
    Lynx.Bytecode.put(env.module, beam)
  end

  @doc false
  def __verify__(module, name, laws, suffixes) do
    files =
      Lynx.Translation.new(termination_suffixes: suffixes)
      |> Lynx.Translation.add(Lynx.Bytecode.fetch!(module))
      |> Lynx.Translation.verify(module, laws)
      |> Lynx.Translation.assemble(cache: System.get_env("LYNX_CACHE") != "0")

    signatures =
      for file <- files,
          %{"kind" => "theorem", "name" => name, "params" => params} <- file["contents"],
          into: %{} do
        {{file["module"], "#{name}/#{length(params)}"}, "#{name}(#{Enum.join(params, ", ")})"}
      end

    reports = Lynx.Commands.verify!(@lean_dir, files)

    if System.get_env("LYNX_PROFILE") == "1" do
      for report <- reports do
        prefix =
          case report.status do
            :ok -> "Checked"
            :error -> "Failed to check"
            :skipped -> "Skipped"
          end

        cached = if report.cached, do: ", cached", else: ""
        IO.puts("#{prefix} #{report.module} in #{report.time_ms}ms (#{report.status}#{cached})")

        last_index = length(report.theorems) - 1

        for {theorem, index} <- Enum.with_index(report.theorems) do
          branch = if index == last_index, do: "└─", else: "├─"
          IO.puts("#{branch} #{theorem.name} (#{theorem.time_ms}ms)")
        end
      end
    end

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

    if errors != [] do
      path = write_translations!(module, name, reports)

      errors =
        List.update_at(errors, -1, fn {kind, error, stack} ->
          message = error.message <> "\n\nThe translated .lean files are available at #{path}"
          {kind, %{error | message: message}, stack}
        end)

      raise ExUnit.MultiError, errors: errors
    end

    :ok
  end

  # Match ExUnit's tmp_dir path sanitization.
  @escape Enum.map(~c" [~#%&*{}\\:<>?/+|\"]", &<<&1::utf8>>)

  defp write_translations!(module, name, reports) do
    path =
      Path.join([
        "tmp",
        String.replace(inspect(module), @escape, "-"),
        String.replace(to_string(name), @escape, "-")
      ])

    File.rm_rf!(path)
    File.mkdir_p!(path)

    for report <- reports do
      File.write!(Path.join(path, report.module <> ".lean"), report.source)
    end

    path
  end
end
