defmodule Lynx.Translation do
  @moduledoc false

  defstruct modules: %{}

  def new, do: %__MODULE__{}

  @doc "Translates the requested functions and adds them to the module's existing translations."
  def add(%__MODULE__{modules: modules} = translation, core, names) do
    name = core |> :cerl.module_name() |> :cerl.atom_val()
    definitions = :lynx_core_to_leanj.to_definitions(core)
    translated = Map.get(modules, name, %{})

    case :lynx_core_to_leanj.translate(definitions, names, translated) do
      {:ok, functions} ->
        %{translation | modules: Map.put(modules, name, functions)}

      {:unsupported_core, _} = error ->
        error
    end
  end

  @doc "Assembles each module's translated functions into Lean JSON commands."
  def assemble(%__MODULE__{modules: modules}) do
    Map.new(modules, fn {name, functions} -> {name, assemble_module(functions)} end)
  end

  defp assemble_module(functions) do
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

      try do
        for group <- topsort(components), do: emit_group(group, graph)
      after
        :digraph.delete(components)
      end
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
