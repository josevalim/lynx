defmodule Lynx.Translation do
  @moduledoc false

  defstruct modules: %{}, funs: %{}, external_calls: %{}, builtin_modules: %{}, stack: []

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

  def new, do: %__MODULE__{}

  @doc "Adds a BEAM binary or {file, Core Erlang module} as source to avoid disk lookup."
  def add(%__MODULE__{} = translation, {file, core}) when is_binary(file) do
    name = core |> :cerl.module_name() |> :cerl.atom_val()
    put_in(translation.modules[name], module_data(file, core))
  end

  def add(%__MODULE__{} = translation, beam) when is_binary(beam) do
    {name, module} = load_beam!(beam, fn -> [] end)
    put_in(translation.modules[name], module)
  end

  @doc "Translates selected laws (or all laws) and their reachable helpers."
  def verify(%__MODULE__{} = translation, name, laws \\ :all) when is_atom(name) do
    {module, translation} = fetch_module!(translation, name, fn -> [] end)

    laws =
      if laws == :all do
        for {name, {:law, _}} <- module.definitions, do: name
      else
        for law <- laws do
          case module.definitions do
            %{^law => {:law, _}} ->
              law

            _ ->
              raise CompileError,
                file: module.file,
                description: "#{inspect(name)} does not declare law #{inspect(law)}"
          end
        end
      end

    if laws == [] do
      raise CompileError,
        file: module.file,
        description: "module #{inspect(name)} declares no laws"
    end

    translate(translation, name, laws)
  end

  @doc "Translates the requested functions and their local and remote callees."
  def translate(%__MODULE__{stack: stack} = translation, name, names) do
    {module, translation} = fetch_module!(translation, name, fn -> [] end)

    for {function, arity} <- names do
      validate_function!(module, name, function, arity, fn -> [file: module.file] end)
    end

    context = {%{translation | stack: [name | stack]}, &remote_call/6}
    %{definitions: definitions, translations: translations} = module
    %{funs: funs} = translation

    case :lynx_core_to_leanj.translate(name, definitions, names, translations, funs, context) do
      {:ok, functions, funs, translation} ->
        updated = %{module | translations: propagate_purity(functions)}

        %{
          translation
          | modules: Map.put(translation.modules, name, updated),
            funs: funs,
            stack: stack
        }

      {:error, span_anno, reason} ->
        raise CompileError,
              source_location(span_anno, module.file) ++
                [description: String.replace(reason, "\n", "\n    ")]
    end
  end

  defp remote_call(
         %__MODULE__{stack: [caller | _]} = translation,
         module,
         function,
         arity,
         span_anno,
         funs
       ) do
    translation = %{translation | funs: funs}

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

        {pure, translation.funs, translation}

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

    translation = translate(translation, module, [{function, arity}])
    pure = translation.modules[module].translations[{function, arity}].pure
    {pure, translation.funs, translation}
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

    {^module, data} = load_beam!(beam, location, module)
    data
  end

  defp load_beam!(beam, location, expected_module \\ nil) do
    case :beam_lib.chunks(beam, [:debug_info, :compile_info]) do
      {:ok, {module, [debug_info: {:debug_info_v1, backend, data}, compile_info: info]}} ->
        case backend.debug_info(:core_v1, module, data, []) do
          {:ok, core} ->
            default_file = if is_list(beam), do: beam, else: "nofile"
            file = info |> Keyword.get(:source, default_file) |> :unicode.characters_to_binary()

            {module, module_data(file, core)}

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
        context = if expected_module, do: " for #{inspect(expected_module)}", else: ""

        raise CompileError,
              location.() ++ [description: "cannot read BEAM#{context}: #{message}"]

      {:ok, {module, _}} ->
        raise CompileError,
              location.() ++
                [
                  description:
                    "no supported debug information for #{inspect(module)}; compile with debug_info"
                ]
    end
  end

  defp module_data(file, core) do
    case :lynx_core_to_leanj.to_definitions(core) do
      {:error, span_anno, reason} ->
        raise CompileError, source_location(span_anno, file) ++ [description: reason]

      definitions ->
        %{definitions: definitions, translations: %{}, file: file}
    end
  end

  defp validate_function!(target, module, function, arity, location) do
    if not Map.has_key?(target.definitions, {function, arity}) do
      raise CompileError,
            location.() ++
              [description: "undefined function #{Exception.format_mfa(module, function, arity)}"]
    end
  end

  @doc """
  Assembles translated modules in dependency order and assigns file cache keys.

  Pass `cache: false` to omit cache keys and disable persistent verification caching.
  """
  def assemble(
        %__MODULE__{
          modules: modules,
          funs: funs,
          external_calls: external_calls,
          builtin_modules: builtin_modules
        },
        opts \\ []
      ) do
    cache = Keyword.get(opts, :cache, true)
    graph = :digraph.new()

    try do
      for {name, _} <- modules, do: :digraph.add_vertex(graph, [name])

      for {name, dependencies} <- external_calls,
          dependency <- dependencies,
          Map.has_key?(modules, dependency) do
        :digraph.add_edge(graph, [dependency], [name])
      end

      {files, keys} =
        Enum.map_reduce(topsort(graph), %{}, fn [name], keys ->
          module = Map.fetch!(modules, name)
          imports = Map.get(external_calls, name, MapSet.new())
          imports = if builtin_modules[name], do: MapSet.put(imports, name), else: imports

          file = %{
            "module" => :lynx_core_to_leanj.module_name(name),
            "file" => module.file,
            "imports" =>
              imports
              |> Enum.sort()
              |> Enum.map(&:lynx_core_to_leanj.module_name/1),
            "contents" => assemble_module(module.translations)
          }

          cache_file(file, keys, cache)
        end)

      if map_size(funs) == 0 do
        files
      else
        {program, _keys} =
          cache_file(
            %{
              "module" => "Erlang.program",
              "file" => "Erlang/program.lean",
              "imports" => Enum.map(files, & &1["module"]),
              "contents" => [
                %{
                  "kind" => "fun_table",
                  "span" => [],
                  "name" => "fun_table",
                  "entries" => :lynx_core_to_leanj.fun_table(funs, modules)
                }
              ]
            },
            keys,
            cache
          )

        files ++ [program]
      end
    after
      :digraph.delete(graph)
    end
  end

  defp cache_file(file, keys, false), do: {file, keys}

  defp cache_file(file, keys, true) do
    imports = for name <- file["imports"], {:ok, key} <- [Map.fetch(keys, name)], do: {name, key}

    key =
      :crypto.hash(:sha256, :erlang.term_to_binary({file, imports}, [:deterministic]))
      |> Base.encode16(case: :lower)

    {Map.put(file, "cache_key", key), Map.put(keys, file["module"], key)}
  end

  defp propagate_purity(functions) do
    {functions, changed?} =
      Enum.reduce(functions, {functions, false}, fn {name, definition}, {functions, changed?} ->
        pure =
          definition.pure and
            Enum.all?(definition.local_calls, fn callee -> Map.fetch!(functions, callee).pure end)

        if pure != definition.pure do
          {Map.put(functions, name, %{definition | pure: pure}), true}
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
      for {name, definition} <- functions,
          callee <- definition.local_calls,
          callee != name do
        :digraph.add_edge(graph, callee, name)
      end

      # Proof strings can reference preceding theorems without a runtime call.
      laws =
        functions
        |> Enum.filter(fn {_, definition} -> definition.translation["kind"] == "theorem" end)
        |> Enum.sort_by(fn {name, _} -> declaration_location(functions, name) end)
        |> Enum.map(&elem(&1, 0))

      for [earlier, later] <- Enum.chunk_every(laws, 2, 1, :discard) do
        :digraph.add_edge(graph, earlier, later)
      end

      components = :digraph_utils.condensation(graph)

      groups = topsort(components, &declaration_location(functions, &1))
      :digraph.delete(components)
      for group <- groups, do: emit_group(group, graph)
    after
      :digraph.delete(graph)
    end
  end

  defp declaration_location(functions, name) do
    span = functions[name].translation["span"]
    {List.wrap(span), name}
  end

  # Source locations order declarations; module names break ties between modules.
  defp topsort(graph, location \\ &Function.identity/1) do
    ready =
      for group <- :digraph.vertices(graph), :digraph.in_degree(graph, group) == 0 do
        names = Enum.sort_by(group, location)
        {Enum.map(names, location), names, group}
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
          for {_, names, group} <- ready do
            :digraph.del_vertex(graph, group)
            names
          end

        groups ++ topsort(graph, location)
    end
  end

  defp emit_group(names, graph) do
    {defs, pure} =
      Enum.map_reduce(names, true, fn name, pure ->
        {^name, {translation, definition_pure}} = :digraph.vertex(graph, name)

        definition =
          if translation["kind"] == "def",
            do: Map.put(translation, "pure", definition_pure),
            else: translation

        {definition, pure and definition_pure}
      end)

    [first | _] = defs
    span = first["span"]

    case defs do
      [definition] -> definition
      _ -> %{"kind" => "mutual", "span" => span, "defs" => defs, "pure" => pure}
    end
  end
end
