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
    %{definitions: definitions, translations: translations} = module

    case :lynx_core_to_leanj.translate(name, definitions, names, translations, context) do
      {:ok, functions, translation} ->
        updated = %{module | translations: propagate_purity(functions)}
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

        {pure, translation}

      :error when module == caller ->
        # A qualified self call such as `?MODULE:missing(X)` compiles in Erlang
        # (it fails with `undef` at runtime), so report it like other undefined
        # remote functions instead of crashing while translating it locally.
        location = fn -> source_location(span_anno, translation.modules[caller].file) end
        validate_function!(translation.modules[caller], module, function, arity, location)
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
    pure = translation.modules[module].translations[{function, arity}].pure
    {pure, translation}
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
    %{definitions: :lynx_core_to_leanj.to_definitions(core), translations: %{}, file: file}
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
          "contents" => assemble_module(module.translations)
        }
      end
    after
      :digraph.delete(graph)
    end
  end

  defp propagate_purity(functions) do
    {functions, changed?} =
      Enum.reduce(functions, {functions, false}, fn {name, definition}, {functions, changed?} ->
        if definition.pure and
             Enum.any?(definition.local_calls, fn callee ->
               not Map.fetch!(functions, callee).pure
             end) do
          {Map.put(functions, name, %{definition | pure: false}), true}
        else
          {functions, changed?}
        end
      end)

    if changed?, do: propagate_purity(functions), else: functions
  end

  defp assemble_module(functions) do
    graph = :digraph.new()

    try do
      for {name, %{translation: translation, pure: pure}} <- functions do
        :digraph.add_vertex(graph, name, {translation, pure})
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
