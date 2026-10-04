defmodule Lynx.Laws do
  @moduledoc ~S'''
  Define executable laws, their Lean proofs, and verify them.

  ## Elixir example

  These examples omit Lean proofs. See the README for complete proofs.

      defmodule Sum do
        use Lynx.Laws

        def sum([]), do: 0
        def sum([x | xs]), do: x + sum(xs)

        law sum_empty,
            expects: sum([]) == 0,
            proof: ~LEAN"""
            PROOF GOES HERE
            """
      end

  Call `Sum.sum_empty/0` to check the law at runtime. Add a `proof: ~LEAN"..."`
  option to verify it with `Lynx.Laws.verify!([Sum])`.

  ## Erlang example

  Each `-law` attribute names an ordinary predicate function:

  ```erlang
  -module(sum).
  -export([sum/1, sum_empty_ensures/0]).

  -law #{name => {sum_empty, []}, ensures => sum_empty_ensures}.
  -proof ~"""
  GOES HERE
  """.

  sum([]) -> 0;
  sum([X | Xs]) -> X + sum(Xs).

  sum_empty_ensures() -> sum([]) == 0.
  ```

  Add a binary `-proof` attribute immediately after the `-law` attribute, then
  call `Lynx.Laws.verify!([:sum])` to verify the law.

  The `-law` map accepts these keys:

    * `name` (required) — `{law_name, argument_names}`, where the argument names
      become Lean theorem parameters.
    * `ensures` (required) — the name of the predicate function to prove.
    * `requires` (optional) — the name of the precondition function. Omit it for
      an unconditional law.

  Both predicate functions receive the law's arguments in order. Their results
  must be `true` for the precondition to hold or the law to succeed. The predicate
  functions remain callable from Erlang; `-law` does not generate a wrapper.
  '''

  @lean_dir Path.expand("../../Lean", __DIR__)

  @typedoc "A verification diagnostic, with source location when available."
  @type diagnostic :: %{
          optional(:line) => pos_integer(),
          optional(:column) => pos_integer(),
          file: String.t(),
          module: String.t(),
          declaration: String.t() | nil,
          severity: :error | :warning | :information,
          message: String.t()
        }

  @typedoc "The verification result for a translated module."
  @type report :: %{
          status: :ok | :error | :skipped,
          file: String.t(),
          module: String.t(),
          source: String.t(),
          time_ms: non_neg_integer(),
          cached: boolean(),
          diagnostics: [diagnostic()]
        }

  @doc """
  Verifies all laws in the given `modules`.

  This is useful for verifying laws in Erlang modules or those using `Lynx.Laws`
  directly. For ExUnit integration, see `Lynx.Case`.

  The laws and proofs for all modules given are verified together within a single
  Lean execution. You must either pass module atoms available on the code path or
  BEAM binaries for modules compiled in memory. Modules must be compiled with debug
  info in all cases.

  Returns one report per translated module, in dependency order, including
  dependencies. Each report contains its Lean source, which is useful
  to understand the translated code, especially when writing proofs.

  A report's `:status` is `:ok` when verification succeeds, `:error` when it fails,
  or `:skipped` when a dependency failed. Lean verification failures are returned
  as reports with `:diagnostics`; they do not raise. Check that every report has
  `status: :ok` to establish successful verification.

  Reports also include the source `:file`, translated `:module` name, `:time_ms`,
  and whether a cached result was used (`:cached`). See `t:report/0` and
  `t:diagnostic/0` for the complete structure.

  Raises on translation failures, including modules without laws or unsupported
  code, and on failures to run Lean or read its response.
  """
  @spec verify!([module() | binary()]) :: [report()]
  def verify!(modules) when is_list(modules) do
    {names, source} = Enum.split_with(modules, &is_atom/1)
    translation = Enum.reduce(source, Lynx.Translation.new(), &Lynx.Translation.add(&2, &1))

    files =
      (names ++ Map.keys(translation.modules))
      |> Enum.reduce(translation, fn module, translation ->
        Lynx.Translation.verify(translation, module)
      end)
      |> Lynx.Translation.assemble()

    Lynx.Commands.verify!(@lean_dir, files)
  end

  defmacro __using__(_opts) do
    quote do
      Lynx.Laws.__register__(__MODULE__)
      import Lynx.Laws, only: [law: 2]
    end
  end

  @doc false
  def __register__(module) do
    Module.register_attribute(module, :law, accumulate: true, persist: true)
  end

  @doc """
  Defines a callable law with an optional precondition and a Lean proof.

  The first argument is a local function declaration, such as `checked(x)` or
  `sum_empty`. Arguments must be distinct named variables: patterns, literals,
  and `_` are not accepted. Those names become the Lean theorem parameters.

  ## Options

    * `:requires` (optional) — an Elixir expression describing the precondition.
      It must evaluate to exactly `true` for the expected expression to be
      evaluated. Defaults to `true`.

    * `:expects` (required) — the Elixir expression to prove. It must evaluate to
      exactly `true` whenever the precondition holds.

    * `:proof` (optional) — a literal `~LEAN` sigil containing the Lean tactic
      proof, without sigil modifiers. Both inline and heredoc sigils are accepted.
      Defaults to `rfl`, which only proves goals that hold by definitional equality.

  ## Example

      law checked(value),
        requires: value,
        expects: value,
        proof: ~LEAN"exact requires"

  ## Executable definition

  Besides defining a law, this macro also defines a public function that you can
  invoke passing Elixir values. Elixir will then validate said values against the
  given `:requires`, the given `:expects`, and return true when both predicates
  succeed, otherwise it will raise. This is useful to provide counter examples.
  """
  defmacro law(call, opts) do
    {_name, definition} = __law__(__CALLER__, call, opts)
    definition
  end

  @doc false
  def __law__(env, call, opts) do
    {name, args} =
      case Macro.decompose_call(call) do
        {name, args} -> {name, args}
        _ -> compile_error!(env, "law must be a local function call")
      end

    params =
      Enum.map(args, fn
        {name, _, context} when is_atom(name) and name != :_ and is_atom(context) -> name
        _ -> compile_error!(env, "law arguments must be named variables")
      end)

    if Enum.uniq(params) != params do
      compile_error!(env, "law arguments must be unique")
    end

    unless Keyword.keyword?(opts) do
      compile_error!(env, "law options must be a keyword list")
    end

    for key <- Keyword.keys(opts), key not in [:requires, :expects, :proof] do
      compile_error!(env, "unknown law option #{inspect(key)}")
    end

    expects =
      case Keyword.fetch(opts, :expects) do
        {:ok, expression} -> expression
        :error -> compile_error!(env, "law requires the :expects option to be given")
      end

    requires_name = :"#{name}:requires"
    ensures_name = :"#{name}:ensures"
    requires = Keyword.get(opts, :requires, true)

    attribute = %{
      name: {name, params},
      ensures: ensures_name,
      span: span(elem(call, 1), env),
      proof: proof(Keyword.fetch(opts, :proof), env)
    }

    attribute =
      if Keyword.has_key?(opts, :requires),
        do: Map.put(attribute, :requires, requires_name),
        else: attribute

    helper_args =
      Enum.map(args, &Macro.update_meta(&1, fn meta -> Keyword.put(meta, :generated, true) end))

    requires_message = "law #{name}/#{length(args)} requires returned "
    expects_message = "law #{name}/#{length(args)} expects returned "

    definition =
      quote generated: true do
        @law unquote(Macro.escape(attribute))

        defp unquote(requires_name)(unquote_splicing(helper_args)), do: unquote(requires)
        defp unquote(ensures_name)(unquote_splicing(helper_args)), do: unquote(expects)

        def unquote(name)(unquote_splicing(args)) do
          case unquote(requires_name)(unquote_splicing(args)) do
            true ->
              case unquote(ensures_name)(unquote_splicing(args)) do
                true -> true
                value -> raise RuntimeError, unquote(expects_message) <> inspect(value)
              end

            value ->
              raise ArgumentError, unquote(requires_message) <> inspect(value)
          end
        end
      end

    {{name, length(args)}, definition}
  end

  defp span(meta, env) do
    line = Keyword.get(meta, :line, env.line)

    case Keyword.fetch(meta, :column) do
      {:ok, column} -> {line, column}
      :error -> line
    end
  end

  defp proof(:error, env), do: %{source: "rfl", indentation: 0, span: env.line}

  defp proof({:ok, {:sigil_LEAN, meta, [{:<<>>, binary_meta, [source]}, []]}}, env)
       when is_binary(source) do
    indentation = Keyword.get(binary_meta, :indentation, 0)
    line = Keyword.get(meta, :line, env.line)

    span =
      if Keyword.get(meta, :delimiter) in ~w(""" ''') do
        {line + 1, indentation + 1}
      else
        case Keyword.fetch(meta, :column) do
          {:ok, column} -> {line, column + 6}
          :error -> line
        end
      end

    %{source: source, indentation: indentation, span: span}
  end

  defp proof(_, env),
    do: compile_error!(env, "proof must be a literal ~LEAN sigil without modifiers")

  defp compile_error!(env, description) do
    raise CompileError, file: env.file, line: env.line, description: description
  end
end
