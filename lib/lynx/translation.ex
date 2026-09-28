defmodule Lynx.Translation do
  @moduledoc false

  defstruct modules: %{}

  def new(cores) do
    modules =
      Map.new(cores, fn {file, core} ->
        name = core |> :cerl.module_name() |> :cerl.atom_val()
        definitions = :lynx_core_to_leanj.to_definitions(core)

        {name, %{definitions: definitions, translations: %{}, file: file}}
      end)

    %__MODULE__{modules: modules}
  end

  @doc "Translates the requested functions using the definitions registered by new/1."
  def add(%__MODULE__{modules: modules} = translation, name, names) do
    module = Map.fetch!(modules, name)

    with {:ok, functions} <-
           :lynx_core_to_leanj.translate(name, module.definitions, names, module.translations) do
      updated = %{module | translations: functions}
      %{translation | modules: Map.put(modules, name, updated)}
    end
  end

  @doc "Translates external callees and assembles modules in dependency order."
  def assemble(%__MODULE__{modules: modules} = translation) do
    calls = for {module, data} <- modules, {name, _} <- data.translations, do: {module, name}

    with %__MODULE__{modules: modules} <- add_external_calls(translation, calls, MapSet.new()) do
      assemble_modules(modules)
    end
  end

  defp add_external_calls(translation, [], _visited), do: translation

  defp add_external_calls(translation, [{module, name} = call | rest], visited) do
    if MapSet.member?(visited, call) do
      add_external_calls(translation, rest, visited)
    else
      with %__MODULE__{} = translation <- add(translation, module, [name]) do
        function = translation.modules[module].translations[name]
        local = Enum.map(function.local_calls, &{module, &1})

        external =
          Enum.map(function.external_calls, fn {mod, fun, arity} -> {mod, {fun, arity}} end)

        add_external_calls(translation, local ++ external ++ rest, MapSet.put(visited, call))
      end
    end
  end

  defp assemble_modules(modules) do
    modules =
      Map.new(modules, fn {name, module} ->
        imports =
          for {_, function} <- module.translations,
              {callee, _, _} <- function.external_calls,
              do: callee

        {name, Map.put(module, :external_modules, imports |> Enum.uniq() |> Enum.sort())}
      end)

    graph = :digraph.new()

    try do
      for {name, _} <- modules, do: :digraph.add_vertex(graph, [name])

      for {name, module} <- modules, dependency <- module.external_modules do
        :digraph.add_edge(graph, [dependency], [name])
      end

      for [name] <- topsort(graph) do
        module = Map.fetch!(modules, name)

        %{
          "module" => Atom.to_string(name),
          "file" => module.file,
          "imports" => Enum.map(module.external_modules, &Atom.to_string/1),
          "contents" => assemble_module(module.translations)
        }
      end
    after
      :digraph.delete(graph)
    end
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

      groups = topsort(components)
      :digraph.delete(components)
      for group <- groups, do: emit_group(group, graph)
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
        if :digraph.no_vertices(graph) != 0 do
          raise ArgumentError, "found cycle during topsort"
        end

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
