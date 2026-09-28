defmodule Lynx.Translation do
  @moduledoc false

  defstruct modules: %{}, external_calls: %{}, builtin_modules: %{}, stack: []

  @external_resource Path.expand("../../Lean/modules.json", __DIR__)
  for {module, functions} <- JSON.decode!(File.read!(@external_resource)),
      {name, %{"pure" => pure}} <- functions do
    [arity | parts] = name |> String.split("/") |> Enum.reverse()
    function = parts |> Enum.reverse() |> Enum.join("/") |> String.to_atom()

    defp lean_bif(
           unquote(String.to_atom(module)),
           unquote(function),
           unquote(String.to_integer(arity))
         ),
         do: {:ok, unquote(pure)}
  end

  defp lean_bif(_, _, _), do: :error

  def new(cores) do
    modules =
      Map.new(cores, fn {file, core} ->
        name = core |> :cerl.module_name() |> :cerl.atom_val()
        {name, module_data(file, core)}
      end)

    %__MODULE__{modules: modules}
  end

  @doc "Translates the requested functions and their local and remote callees."
  def add(%__MODULE__{stack: stack} = translation, name, names) do
    {module, translation} = fetch_module!(translation, name, fn -> [] end)

    for {function, arity} <- names do
      validate_function!(module, name, function, arity, fn -> [file: module.file] end)
    end

    context = {%{translation | stack: [name | stack]}, &remote_call/5}
    %{definitions: definitions, translations: translations, funs: funs} = module

    case :lynx_core_to_leanj.translate(name, definitions, names, translations, funs, context) do
      {:ok, functions, funs, translation} ->
        updated = %{module | translations: propagate_purity(functions), funs: funs}
        %{translation | modules: Map.put(translation.modules, name, updated), stack: stack}

      {:unsupported_core, span_anno, core} ->
        raise CompileError,
              source_location(span_anno, module.file) ++
                [description: "unsupported Core expression:\n#{core}"]
    end
  end

  defp remote_call(
         %__MODULE__{stack: [caller | _]} = translation,
         module,
         function,
         arity,
         span_anno
       ) do
    translation =
      if module == caller do
        translation
      else
        update_in(translation.external_calls[caller], fn
          nil -> MapSet.new([module])
          set -> MapSet.put(set, module)
        end)
      end

    case lean_bif(module, function, arity) do
      {:ok, pure} ->
        translation = put_in(translation.builtin_modules[module], true)

        {if(pure, do: :pure, else: :impure), translation}

      :error when module == caller ->
        :local

      :error ->
        translate_remote(translation, module, function, arity, span_anno)
    end
  end

  defp translate_remote(
         %__MODULE__{stack: [caller | _]} = translation,
         module,
         function,
         arity,
         span_anno
       ) do
    location = fn -> source_location(span_anno, translation.modules[caller].file) end
    {target, translation} = fetch_module!(translation, module, location)
    validate_function!(target, module, function, arity, location)

    if module in translation.stack do
      cycle = Enum.map_join(Enum.reverse([module | translation.stack]), " -> ", &inspect/1)

      raise CompileError,
            location.() ++
              [
                description:
                  "cyclic module call to #{Exception.format_mfa(module, function, arity)} (#{cycle})"
              ]
    end

    translation = add(translation, module, [{function, arity}])
    purity = translation.modules[module].translations[{function, arity}].purity
    {purity, translation}
  end

  defp source_location(annotations, default_file) do
    file =
      case List.keyfind(annotations, :file, 0) do
        {:file, file} when file not in [[], ""] -> :unicode.characters_to_binary(file)
        _ -> default_file
      end

    line =
      Enum.find_value(annotations, fn
        {line, column} when is_integer(line) and line > 0 and is_integer(column) -> line
        line when is_integer(line) and line > 0 -> line
        _ -> nil
      end)

    [file: file, line: line]
  end

  defp fetch_module!(translation, module, location) do
    case translation.modules do
      %{^module => data} ->
        {data, translation}

      %{} ->
        data = load_module!(module, location)
        {data, put_in(translation.modules[module], data)}
    end
  end

  defp load_module!(module, location) do
    beam =
      case :code.which(module) do
        path when is_list(path) ->
          path

        :non_existing ->
          raise CompileError, location.() ++ [description: "unknown module #{inspect(module)}"]

        reason ->
          raise CompileError,
                location.() ++
                  [description: "cannot locate BEAM for #{inspect(module)}: #{inspect(reason)}"]
      end

    case :beam_lib.chunks(beam, [:debug_info, :compile_info]) do
      {:ok, {^module, [debug_info: {:debug_info_v1, backend, data}, compile_info: info]}} ->
        case backend.debug_info(:core_v1, module, data, []) do
          {:ok, core} ->
            file = info |> Keyword.get(:source, beam) |> :unicode.characters_to_binary()
            module_data(file, core)

          {:error, reason} ->
            raise CompileError,
                  location.() ++
                    [
                      description:
                        "cannot convert debug information for #{inspect(module)} to Core: #{inspect(reason)}"
                    ]
        end

      {:error, :beam_lib, _} = error ->
        message = error |> :beam_lib.format_error() |> IO.chardata_to_string()

        raise CompileError,
              location.() ++ [description: "cannot read BEAM for #{inspect(module)}: #{message}"]

      {:ok, _} ->
        raise CompileError,
              location.() ++
                [
                  description:
                    "no supported debug information for #{inspect(module)}; compile with debug_info"
                ]
    end
  end

  defp module_data(file, core) do
    %{
      definitions: :lynx_core_to_leanj.to_definitions(core),
      translations: %{},
      funs: %{},
      file: file
    }
  end

  defp validate_function!(target, module, function, arity, location) do
    if not Map.has_key?(target.definitions, {function, arity}) do
      raise CompileError,
            location.() ++
              [description: "undefined function #{Exception.format_mfa(module, function, arity)}"]
    end
  end

  @doc "Assembles translated modules in dependency order."
  def assemble(%__MODULE__{
        modules: modules,
        external_calls: external_calls,
        builtin_modules: builtin_modules
      }) do
    # Resolve neutral definitions only against the complete translated graph.
    # Keep stored summaries neutral so subsequent add/3 calls can introduce effects.
    neutral_pure? =
      Enum.all?(modules, fn {_, module} ->
        Enum.all?(module.translations, fn {_, definition} -> definition.purity != :impure end)
      end)

    funs =
      for {module_name, module} <- Enum.sort(modules),
          fun <- module.funs |> Map.values() |> Enum.uniq_by(& &1.name) |> Enum.sort_by(& &1.name) do
        definition = Map.fetch!(module.translations, fun.name).translation
        {module_name, fun, definition}
      end

    indices =
      funs
      |> Enum.with_index()
      |> Map.new(fn {{module, _fun, definition}, index} ->
        {{:lynx_core_to_leanj.module_name(module), definition["name"]}, index}
      end)

    table = array(Enum.map(funs, &fun_entry/1))

    external_calls =
      Enum.reduce(modules, external_calls, fn {name, module}, calls ->
        if Enum.any?(module.translations, fn {_, definition} -> definition.dynamic end) do
          dependencies = for {owner, _, _} <- funs, owner != name, do: owner

          Map.update(
            calls,
            name,
            MapSet.new(dependencies),
            &MapSet.union(&1, MapSet.new(dependencies))
          )
        else
          calls
        end
      end)

    graph = :digraph.new()

    try do
      for {name, _} <- modules, do: :digraph.add_vertex(graph, [name])

      for {name, dependencies} <- external_calls,
          dependency <- dependencies,
          Map.has_key?(modules, dependency) do
        :digraph.add_edge(graph, [dependency], [name])
      end

      for [name] <- topsort(graph) do
        module = Map.fetch!(modules, name)
        imports = Map.get(external_calls, name, MapSet.new())
        imports = if builtin_modules[name], do: MapSet.put(imports, name), else: imports

        %{
          "module" => :lynx_core_to_leanj.module_name(name),
          "file" => module.file,
          "imports" =>
            imports
            |> Enum.sort()
            |> Enum.map(&:lynx_core_to_leanj.module_name/1),
          "contents" =>
            module.translations
            |> assemble_module(
              neutral_pure?,
              for({owner, fun, _} <- funs, owner == name, do: fun.name)
            )
            |> resolve_funs(indices, table)
        }
      end
    after
      :digraph.delete(graph)
    end
  end

  # Table adapters keep capture values and invocation arguments separate.
  defp fun_entry({module, fun, definition}) do
    capture_count = length(definition["params"]) - fun.arity
    captures = array_args("_lynx_captures", capture_count)
    args = array_args("_lynx_args", fun.arity)

    body =
      apply_node(
        :lynx_core_to_leanj.module_name(module) <> "." <> definition["name"],
        captures ++ args
      )

    apply_node("Lynx.Term.FunTable.entry", [
      integer(capture_count),
      integer(fun.arity),
      %{
        "kind" => "fun",
        "span" => [],
        "params" => [ident("_lynx_captures"), ident("_lynx_args")],
        "body" => body
      }
    ])
  end

  defp array_args(name, count) do
    for index <- 0..count//1, index < count do
      apply_node("Array.getD", [ident(name), integer(index), ident("Lynx.Term.«nil»")])
    end
  end

  defp integer(value), do: %{"kind" => "integer", "span" => [], "value" => value}

  defp resolve_funs(%{"kind" => "closure"} = closure, indices, table) do
    apply_node("Lynx.Term.«function»", [
      %{
        "kind" => "integer",
        "span" => [],
        "value" => Map.fetch!(indices, {closure["module"], closure["name"]})
      },
      %{"kind" => "integer", "span" => [], "value" => closure["arity"]},
      resolve_funs(closure["captures"], indices, table)
    ])
    |> Map.put("span", closure["span"])
  end

  defp resolve_funs(%{"kind" => "fun_table"}, _indices, table), do: table

  defp resolve_funs(value, indices, table) when is_map(value),
    do: Map.new(value, fn {key, value} -> {key, resolve_funs(value, indices, table)} end)

  defp resolve_funs(values, indices, table) when is_list(values),
    do: Enum.map(values, &resolve_funs(&1, indices, table))

  defp resolve_funs(value, _indices, _table), do: value

  defp ident(name), do: %{"kind" => "ident", "span" => [], "name" => name}
  defp apply_node(name, []), do: ident(name)

  defp apply_node(name, args),
    do: %{"kind" => "apply", "span" => [], "function" => ident(name), "args" => args}

  defp list(values),
    do: Enum.reduce(Enum.reverse(values), ident("List.nil"), &apply_node("List.cons", [&1, &2]))

  defp array(values), do: apply_node("Array.mk", [list(values)])

  defp propagate_purity(functions) do
    {functions, changed?} =
      Enum.reduce(functions, {functions, false}, fn {name, definition}, {functions, changed?} ->
        purity =
          Enum.reduce(definition.local_calls, definition.purity, fn callee, purity ->
            :lynx_core_to_leanj.join_purity(purity, Map.fetch!(functions, callee).purity)
          end)

        if purity != definition.purity do
          {Map.put(functions, name, %{definition | purity: purity}), true}
        else
          {functions, changed?}
        end
      end)

    if changed?, do: propagate_purity(functions), else: functions
  end

  defp assemble_module(functions, neutral_pure?, fun_names) do
    graph = :digraph.new()

    try do
      for {name, %{translation: translation, purity: purity}} <- functions do
        pure = purity == :pure or (purity == :neutral and neutral_pure?)
        :digraph.add_vertex(graph, name, {translation, pure})
      end

      # Edges point from callees to callers, so dependencies are emitted first.
      for {name, definition} <- functions,
          callee <-
            definition.local_calls ++
              definition.references ++
              if(definition.dynamic, do: fun_names, else: []),
          callee != name do
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
          raise CompileError, description: "found cycle during topsort"
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
    {defs, pure} =
      Enum.map_reduce(names, true, fn name, pure ->
        {^name, {translation, definition_pure}} = :digraph.vertex(graph, name)
        {translation, pure and definition_pure}
      end)

    [first | _] = defs
    span = first["span"]

    declaration =
      case defs do
        [definition] -> definition
        _ -> %{"kind" => "mutual", "span" => span, "defs" => defs}
      end

    if pure do
      %{"kind" => "command", "span" => span, "name" => "lynx_pure", "expr" => declaration}
    else
      declaration
    end
  end
end
