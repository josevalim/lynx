defmodule Lynx do
  @moduledoc """
  Translate and verify laws declared in Elixir and Erlang modules.
  """

  @lean_dir Path.expand("../Lean", __DIR__)

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

  All of the functions invoked by the laws and their callees are translated into
  Lean and verified together within a single Lean execution. Modules must be compiled
  with debug information. Pass module atoms available on the code path, or
  BEAM binaries for modules compiled in memory. Source paths come from BEAM metadata.

  This function will raise if any requested module declares no laws or if the
  code being translated has functionality not yet supported by Lynx.

  Returns one report per translated module, in dependency order, including
  dependencies. See the associated typespecs.
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
end
