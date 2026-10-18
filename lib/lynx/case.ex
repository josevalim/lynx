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
  as well as the elaboration time of any law. The translated .lean files are
  also written to `tmp/` for inspection.

  Set `LYNX_CACHE=0` to disable the verification cache.
  """

  @lean_dir Path.expand("../../Lean", __DIR__)

  defmacro __using__(_opts) do
    quote do
      Lynx.Case.__register__(__MODULE__)

      import Lynx.Case,
        only: [law: 2, laws: 2, laws: 3, termination_suffix: 2, cutoff: 1, prelude: 1]

      import Lynx.Lean, only: [sigil_LEAN: 2]
    end
  end

  @doc false
  def __register__(module) do
    unless Module.has_attribute?(module, :ex_unit_tests) do
      raise ArgumentError, "you must Lynx.Case after use ExUnit.Case"
    end

    ExUnit.plural_rule("laws", "laws")

    # Retain bytecode before ExUnit's callback makes async tests runnable.
    callbacks = Module.delete_attribute(module, :after_compile)
    Module.put_attribute(module, :after_compile, __MODULE__)

    for callback <- Enum.reverse(callbacks) do
      Module.put_attribute(module, :after_compile, callback)
    end

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

      termination_suffix &:calendar.mod/2, ~LEAN"partial_fixpoint"

  The source is a `Lynx.Lean` value. It is parsed as part of the function's
  declaration, after its body. Regardless of the suffix contents, the function
  and every function calling it are marked as partial (see the purity model in
  `Lynx`): instead of purity proofs (`#lynx_pure`), they receive partiality proofs
  (`#lynx_partial`), and laws reaching them are still stated directly.
  Raises if the target function is not translated by the group's laws.
  """
  defmacro termination_suffix(target, source) do
    mfa =
      case target do
        {:&, _, [{:/, _, [{{:., _, [module, name]}, _, []}, arity]}]}
        when is_atom(name) and is_integer(arity) and arity >= 0 ->
          module = Macro.expand(module, __CALLER__)

          if not is_atom(module),
            do: raise(ArgumentError, "expected a module in termination_suffix")

          {module, name, arity}

        _ ->
          raise ArgumentError, "termination_suffix expects &Module.function/arity"
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

  @doc ~S'''
  Adds Lean declarations to the prelude for this laws group.

      prelude ~LEAN"""
      open Lean Elab Tactic
      elab "finish" : tactic => do evalTactic (← `(tactic| rfl))
      """

  Blocks contain complete Lean declarations and are elaborated in order in a
  separate public module importing `Lynx`. Every translated module imports the
  prelude before its proofs and termination suffixes are parsed. Definitions,
  lemmas, macros, and elaborators may be declared; namespaces are chosen by the
  source. Meta helper definitions must use Lean's `meta` modifier as usual.

  The prelude cannot refer to translated definitions, which do not exist yet.
  It does not leak into other groups, and its source participates in verification
  cache keys. Proofs retain kernel checking and axiom audits.
  '''
  defmacro prelude(source) do
    quote do
      Lynx.Case.__prelude__(__MODULE__, unquote(source))
    end
  end

  @doc false
  def __prelude__(module, %Lynx.Lean{} = source) do
    case Module.get_attribute(module, :lynx_preludes) do
      nil ->
        raise ArgumentError, "prelude must be defined inside a laws group"

      preludes ->
        Module.put_attribute(module, :lynx_preludes, [source | preludes])
    end
  end

  def __prelude__(_module, _source),
    do: raise(ArgumentError, "prelude expects a Lynx.Lean value")

  @doc """
  Leaves a function untranslated in this laws group.

      cutoff &Float.invalid_precision_message/1

  The function's body becomes `Lynx.Result.exhausted`, not a return value or an
  Erlang exception. A successful-return proof must establish that the cutoff
  is never reached. This supports proofs whose unreachable error paths depend
  on libraries outside the model; it makes no claim about executing those paths.

  The function and every function calling it are marked as partial (see the
  purity model in `Lynx`): they receive partiality proofs (`#lynx_partial`), and
  laws reaching a cutoff are still stated directly.
  """
  defmacro cutoff(target) do
    mfa =
      case target do
        {:&, _, [{:/, _, [{{:., _, [module, name]}, _, []}, arity]}]}
        when is_atom(name) and is_integer(arity) and arity >= 0 ->
          module = Macro.expand(module, __CALLER__)
          if not is_atom(module), do: raise(ArgumentError, "expected a module in cutoff")
          {module, name, arity}

        _ ->
          raise ArgumentError, "cutoff expects &Module.function/arity"
      end

    quote do
      Lynx.Case.__cutoff__(__MODULE__, unquote(Macro.escape(mfa)))
    end
  end

  @doc false
  def __cutoff__(module, mfa) do
    case Module.get_attribute(module, :lynx_cutoffs) do
      nil -> raise ArgumentError, "cutoff must be defined inside a laws group"
      cutoffs -> Module.put_attribute(module, :lynx_cutoffs, MapSet.put(cutoffs, mfa))
    end
  end

  @doc """
  Registers a group of laws as one ExUnit test.

  The test translates the laws and their callees, verifies their proofs,
  and fails if they do not pass.

  Each group has the `:laws` test type and tag. Run only law groups with
  `mix test --only laws`.

  ## Options

    * `:options` (optional) — a keyword list of Lean options, such as
      `[maxHeartbeats: 1_000_000, maxRecDepth: 10_000]`, set at the top of every
      translated module of the group, including its laws. Names are passed to
      Lean as given. Proofs remain kernel-checked.

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
  defmacro laws(description, opts \\ [], do: block) do
    definition =
      quote unquote: false do
        def unquote(name)(_context) do
          Lynx.Case.__verify__(
            __MODULE__,
            unquote(name),
            unquote(group_laws),
            unquote(Macro.escape(suffixes)),
            unquote(Macro.escape(cutoffs)),
            unquote(Macro.escape(preludes)),
            unquote(Macro.escape(options))
          )
        end
      end

    quote do
      {name, group_laws, suffixes, cutoffs, preludes, options} =
        Lynx.Case.__laws__(
          __MODULE__,
          unquote(__CALLER__.file),
          unquote(__CALLER__.line),
          unquote(description),
          unquote(opts),
          fn -> unquote(block) end
        )

      unquote(definition)
    end
  end

  @doc false
  def __laws__(module, file, line, description, opts, fun) do
    if Module.get_attribute(module, :lynx_laws) do
      raise ArgumentError, "laws groups cannot be nested"
    end

    if not Keyword.keyword?(opts) do
      raise ArgumentError, "laws options must be a keyword list, got: #{inspect(opts)}"
    end

    options = Keyword.get(opts, :options, [])

    for key <- Keyword.keys(opts), key != :options do
      raise ArgumentError, "unknown laws option #{inspect(key)}"
    end

    for option <- options do
      case option do
        {name, value}
        when is_atom(name) and (is_integer(value) or is_boolean(value) or is_binary(value)) ->
          :ok

        _ ->
          raise ArgumentError,
                "laws options must be Lean option names with integer, boolean, " <>
                  "or string values, got: #{inspect(option)}"
      end
    end

    Module.put_attribute(module, :lynx_laws, [])
    Module.put_attribute(module, :lynx_termination_suffixes, %{})
    Module.put_attribute(module, :lynx_cutoffs, MapSet.new())
    Module.put_attribute(module, :lynx_preludes, [])

    try do
      fun.()
      group_laws = module |> Module.get_attribute(:lynx_laws) |> Enum.reverse()

      if group_laws == [] do
        raise CompileError, file: file, line: line, description: "laws group must contain a law"
      end

      name = ExUnit.Case.register_test(module, file, line, :laws, description, [:laws])

      {name, group_laws, Module.get_attribute(module, :lynx_termination_suffixes),
       Module.get_attribute(module, :lynx_cutoffs),
       Enum.reverse(Module.get_attribute(module, :lynx_preludes)), options}
    after
      Module.delete_attribute(module, :lynx_laws)
      Module.delete_attribute(module, :lynx_termination_suffixes)
      Module.delete_attribute(module, :lynx_cutoffs)
      Module.delete_attribute(module, :lynx_preludes)
    end
  end

  @doc false
  def __after_compile__(env, beam) do
    # ExUnit compiles .exs modules in memory, so there is no BEAM on the code path.
    # Recompiling a module replaces its retained binary.
    Lynx.Bytecode.put(env.module, beam)
  end

  @doc false
  def __verify__(module, name, laws, suffixes, cutoffs, preludes, options) do
    files =
      Lynx.Translation.new(termination_suffixes: suffixes, cutoffs: cutoffs, preludes: preludes)
      |> Lynx.Translation.add(Lynx.Bytecode.fetch!(module))
      |> Lynx.Translation.verify(module, laws)
      |> Lynx.Translation.assemble(cache: System.get_env("LYNX_CACHE") != "0")

    signatures =
      for file <- files,
          %{"kind" => "theorem", "name" => name, "params" => params} <- file["contents"],
          into: %{} do
        {{file["module"], "#{name}/#{length(params)}"}, "#{name}(#{Enum.join(params, ", ")})"}
      end

    reports = Lynx.Commands.verify!(@lean_dir, files, options)

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

      IO.puts("Translated .lean files written to #{write_translations!(module, name, reports)}")
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
