defmodule Lynx.Translation do
  @moduledoc false

  @doc """
  Translates a Core module's exports and reachable local functions into Lean JSON commands.
  """
  @spec module(tuple()) :: {:ok, [map()]} | {:unsupported_core, binary()}
  def module(core) do
    exports =
      core
      |> :cerl.module_exports()
      |> Enum.map(&:cerl.var_name/1)
      |> Kernel.--([{:module_info, 0}, {:module_info, 1}])

    definitions = :lynx_core_to_leanj.to_definitions(core)

    with {:ok, functions} <- :lynx_core_to_leanj.translate(definitions, exports, %{}) do
      {:ok, assemble(functions)}
    end
  end

  defp assemble(functions) do
    graph = :digraph.new()

    try do
      for {name, %{translation: translation}} <- functions do
        :digraph.add_vertex(graph, name, translation)
      end

      # Edges point from callees to callers, so dependencies are emitted first.
      for {name, %{local_calls: calls}} <- functions, callee <- calls do
        :digraph.add_edge(graph, callee, name)
      end

      components = :digraph_utils.condensation(graph)
      for group <- topsort(components), do: emit_group(group, graph)
    after
      :digraph.delete(graph)
    end
  end

  # Alphabetize each ready batch. OTP's topsort leaves ties in arbitrary order.
  defp topsort(graph) do
    ready =
      for group <- :digraph.vertices(graph), :digraph.in_degree(graph, group) == 0 do
        {Enum.sort(group), group}
      end
      |> Enum.sort()

    case ready do
      [] ->
        []

      _ ->
        groups =
          for {names, group} <- ready do
            :digraph.del_vertex(graph, group)
            names
          end

        groups ++ topsort(graph)
    end
  end

  defp emit_group(names, graph) do
    defs =
      Enum.map(names, fn name ->
        {^name, translation} = :digraph.vertex(graph, name)
        translation
      end)

    [first | _] = defs
    span = first["span"]

    declaration =
      case defs do
        [definition] -> definition
        _ -> %{"kind" => "mutual", "span" => span, "defs" => defs}
      end

    # TODO: Track purity
    %{"kind" => "command", "span" => span, "name" => "lynx_pure", "expr" => declaration}
  end
end
