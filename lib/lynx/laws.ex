defmodule Lynx.Laws do
  @moduledoc """
  Define executable laws and their Lean proofs.

  Add `use Lynx.Laws`, then `law name(arguments), expects: expression, proof: ~LEAN"..."` to declare
  a law. An optional `requires: expression` supplies its precondition. Calling
  the law checks both predicates and returns `true` when they succeed.
  """

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

  @doc "Defines a callable law with an optional precondition and a Lean proof."
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
