defmodule Lynx.Lean do
  @moduledoc """
  Lean source with its original file, span, and indentation.

  Import this module to use `~LEAN`. `Lynx.Laws` and `Lynx.Case` import it
  automatically. The resulting value can be stored in variables or attributes.
  """

  @type t :: %__MODULE__{
          source: String.t(),
          file: String.t(),
          span: pos_integer() | {pos_integer(), pos_integer()},
          indentation: non_neg_integer()
        }
  @enforce_keys [:source, :file, :span, :indentation]
  defstruct [:source, :file, :span, :indentation]

  @doc "Builds Lean source from a literal inline string or heredoc, without modifiers."
  defmacro sigil_LEAN({:<<>>, meta, [source]}, []) when is_binary(source) do
    env = __CALLER__
    indentation = Keyword.get(meta, :indentation, 0)
    line = Keyword.get(meta, :line, env.line)

    span =
      if Keyword.has_key?(meta, :indentation) do
        {line + 1, indentation + 1}
      else
        case Keyword.fetch(meta, :column) do
          {:ok, column} -> {line, column + 6}
          :error -> line
        end
      end

    Macro.escape(%__MODULE__{
      source: source,
      file: env.file,
      span: span,
      indentation: indentation
    })
  end

  defmacro sigil_LEAN(_source, _modifiers) do
    raise CompileError,
      file: __CALLER__.file,
      line: __CALLER__.line,
      description: "~LEAN requires a literal string without modifiers"
  end
end
