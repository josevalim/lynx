defmodule Lynx.Translation do
  @moduledoc false

  defstruct preludes: [],
            termination_suffixes: %{},
            cutoffs: MapSet.new(),
            modules: %{},
            funs: %{},
            external_calls: %{},
            builtin_modules: %{},
            stack: []

  # Runtime functions without purity proofs use the process environment,
  # except those that make process requests or call function values.
  @runtime_purity %{
    {:erlang, :spawn, 1} => :concurrent,
    {:erlang, :send, 2} => :concurrent,
    {:erlang, :apply, 2} => :dynamic
  }

  @external_resource Path.expand("../../Lean/modules.json", __DIR__)
  for {module, functions} <- JSON.decode!(File.read!(@external_resource)),
      {name, %{"pure" => pure}} <- functions do
    [arity | parts] = name |> String.split("/") |> Enum.reverse()
    function = parts |> Enum.reverse() |> Enum.join("/") |> String.to_atom()
    module = String.to_atom(module)
    arity = String.to_integer(arity)

    purity =
      if pure,
        do: :pure,
        else: Map.get(@runtime_purity, {module, function, arity}, :sequential)

    defp lean_bif(unquote(module), unquote(function), unquote(arity)),
      do: {:ok, unquote(purity)}
  end

  defp lean_bif(_, _, _), do: :error

  def new(opts \\ []) do
    %__MODULE__{
      preludes: Keyword.get(opts, :preludes, []),
      termination_suffixes: Keyword.get(opts, :termination_suffixes, %{}),
      cutoffs: MapSet.new(Keyword.get(opts, :cutoffs, []))
    }
  end

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

    definitions =
      Enum.reduce(translation.cutoffs, module.definitions, fn
        {^name, function, arity}, definitions ->
          validate_function!(module, name, function, arity, fn -> [file: module.file] end)

          Map.update!(definitions, {function, arity}, fn
            {:function, core} -> {:cutoff, core}
          end)

        _, definitions ->
          definitions
      end)

    context = {%{translation | stack: [name | stack]}, &remote_call/6}
    %{translations: translations, literals: literals} = module
    %{funs: funs} = translation

    suffixed =
      for {^name, function, arity} <- Map.keys(translation.termination_suffixes),
          do: {function, arity}

    case :lynx_core_to_leanj.translate(
           name,
           definitions,
           names,
           translations,
           literals,
           funs,
           suffixed,
           context
         ) do
      {:ok, functions, literals, laws, funs, translation} ->
        updated = %{
          module
          | translations: propagate_purity(functions, name, translation.termination_suffixes),
            literals: literals,
            laws: Map.merge(module.laws, laws)
        }

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
      {:ok, purity} ->
        translation = put_in(translation.builtin_modules[module], true)

        {purity, translation.funs, translation}

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

    purity = translation.modules[module].translations[{function, arity}].purity
    {purity, translation.funs, translation}
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
        %{definitions: definitions, translations: %{}, literals: %{}, laws: %{}, file: file}
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
          preludes: preludes,
          termination_suffixes: suffixes,
          funs: funs,
          external_calls: external_calls,
          builtin_modules: builtin_modules
        },
        opts \\ []
      ) do
    cache = Keyword.get(opts, :cache, true)

    modules =
      Enum.reduce(suffixes, modules, fn {{module, function, arity}, %Lynx.Lean{} = suffix},
                                        modules ->
        path = [module, :translations, {function, arity}, :translation]

        if get_in(modules, path ++ ["kind"]) != "def" do
          line =
            case suffix.span do
              {line, _} -> line
              line -> line
            end

          raise CompileError,
            file: suffix.file,
            line: line,
            description:
              "cannot attach termination suffix to #{Exception.format_mfa(module, function, arity)}: function is not translated"
        end

        json = %{
          "source" => suffix.source,
          "file" => suffix.file,
          "span" =>
            case suffix.span do
              {line, column} -> [line, column]
              line -> [line]
            end,
          "indentation" => suffix.indentation
        }

        update_in(modules, path, &Map.put(&1, "termination_suffix", json))
      end)

    modules = resolve_dynamic(modules, funs)
    {support, keys, support_imports} = assemble_preludes(preludes, cache)
    graph = :digraph.new()

    try do
      for {name, _} <- modules, do: :digraph.add_vertex(graph, [name])

      for {name, dependencies} <- external_calls,
          dependency <- dependencies,
          Map.has_key?(modules, dependency) do
        :digraph.add_edge(graph, [dependency], [name])
      end

      names = topsort(graph)

      {files, keys} =
        Enum.map_reduce(names, keys, fn [name], keys ->
          module = Map.fetch!(modules, name)
          imports = Map.get(external_calls, name, MapSet.new())
          imports = if builtin_modules[name], do: MapSet.put(imports, name), else: imports

          file = %{
            "module" => :lynx_core_to_leanj.module_name(name),
            "file" => module.file,
            "imports" =>
              imports
              |> Enum.sort()
              |> Enum.map(&:lynx_core_to_leanj.module_name/1)
              |> then(&(support_imports ++ &1)),
            "contents" => assemble_module(module.translations)
          }

          cache_file(file, keys, cache)
        end)

      {program, keys} =
        if map_size(funs) == 0 do
          {[], keys}
        else
          program = %{
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
          }

          {program, keys} = cache_file(program, keys, cache)
          {[program], keys}
        end

      # Laws follow the program, so their statements may reference its table.
      # Their namespace nests below the module's, so proofs keep resolving
      # unqualified names as before.
      {laws, _keys} =
        Enum.flat_map_reduce(names, keys, fn [name], keys ->
          case Map.fetch!(modules, name) do
            %{laws: laws} when map_size(laws) == 0 ->
              {[], keys}

            module ->
              module_name = :lynx_core_to_leanj.module_name(name)

              file = %{
                "module" => module_name <> ".laws",
                "file" => module.file,
                "imports" => support_imports ++ [module_name | Enum.map(program, & &1["module"])],
                "contents" => assemble_laws(module, program != [])
              }

              {file, keys} = cache_file(file, keys, cache)
              {[file], keys}
          end
        end)

      support ++ files ++ program ++ laws
    after
      :digraph.delete(graph)
    end
  end

  defp assemble_preludes([], _cache), do: {[], %{}, []}

  defp assemble_preludes(preludes, cache) do
    declarations =
      for source <- preludes do
        %Lynx.Lean{} = source

        %{
          "source" => source.source,
          "file" => source.file,
          "span" =>
            case source.span do
              {line, column} -> [line, column]
              line -> [line]
            end,
          "indentation" => source.indentation
        }
      end

    name = "Lynx.Prelude"

    {file, keys} =
      cache_file(
        %{
          "module" => name,
          "file" => hd(declarations)["file"],
          "imports" => [],
          "contents" => [],
          "preludes" => declarations
        },
        %{},
        cache
      )

    {[file], keys, [name]}
  end

  defp cache_file(file, keys, false), do: {file, keys}

  defp cache_file(file, keys, true) do
    imports = for name <- file["imports"], {:ok, key} <- [Map.fetch(keys, name)], do: {name, key}

    key =
      :erlang.term_to_binary({file, imports}, [:deterministic])
      |> cache_hash()
      |> Base.encode16(case: :lower)

    {Map.put(file, "cache_key", key), Map.put(keys, file["module"], key)}
  end

  defp cache_hash(contents) do
    case :erlang.system_info(:wordsize) do
      8 -> :crypto.hash(:blake2b, contents)
      _ -> :crypto.hash(:blake2s, contents)
    end
  rescue
    # Blake may not be available on all OpenSSL distributions.
    _ -> :erlang.md5(contents)
  end

  # A definition is as impure as its callees. Termination suffixes make it
  # partial, since `#lynx_pure` cannot prove that such a definition returns.
  defp propagate_purity(functions, module, suffixes) do
    {functions, changed?} =
      Enum.reduce(functions, {functions, false}, fn {{function, arity} = name, definition},
                                                    {functions, changed?} ->
        own =
          if Map.has_key?(suffixes, {module, function, arity}),
            do: join_purity(definition.purity, :partial),
            else: definition.purity

        purity =
          Enum.reduce(definition.local_calls, own, fn callee, purity ->
            join_purity(purity, Map.fetch!(functions, callee).purity)
          end)

        if purity != definition.purity do
          {Map.put(functions, name, %{definition | purity: purity}), true}
        else
          {functions, changed?}
        end
      end)

    if changed?, do: propagate_purity(functions, module, suffixes), else: functions
  end

  # Calls to function values may reach any entry in the complete program table,
  # so they are concurrent when an entry is, and sequential otherwise.
  defp resolve_dynamic(modules, funs) do
    concurrent? =
      Enum.any?(funs, fn {_, %{module: module, name: name}} ->
        modules[module].translations[name].purity == :concurrent
      end)

    resolved = if concurrent?, do: :concurrent, else: :sequential

    Map.new(modules, fn {name, module} ->
      translations =
        Map.new(module.translations, fn
          {function, %{purity: :dynamic} = definition} ->
            {function, %{definition | purity: resolved}}

          entry ->
            entry
        end)

      {name, %{module | translations: translations}}
    end)
  end

  defp join_purity(left, right), do: :lynx_core_to_leanj.join_purity(left, right)

  defp assemble_module(functions) do
    graph = :digraph.new()

    try do
      for {name, _definition} <- functions do
        :digraph.add_vertex(graph, name)
      end

      # Edges point from callees to callers, so dependencies are emitted first.
      for {name, definition} <- functions,
          callee <- definition.local_calls,
          callee != name do
        :digraph.add_edge(graph, callee, name)
      end

      components = :digraph_utils.condensation(graph)

      groups = topsort(components, &declaration_location(functions, &1))
      :digraph.delete(components)
      for group <- groups, do: emit_group(group, functions)
    after
      :digraph.delete(graph)
    end
  end

  # Proof strings can reference preceding theorems, so laws keep source order.
  # The helpers' purity selects how the runner states and proves each law.
  defp assemble_laws(%{laws: laws, translations: translations}, table?) do
    laws
    |> Enum.sort_by(fn {name, law} -> {List.wrap(law["span"]), name} end)
    |> Enum.map(fn {{_, arity}, law} ->
      law =
        for key <- ["requires", "ensures"], Map.has_key?(law, key), reduce: law do
          law ->
            helper = translations[{String.to_existing_atom(law[key]), arity}]
            Map.put(law, key <> "_purity", Atom.to_string(helper.purity))
        end

      if table?, do: Map.put(law, "table", "Erlang.program.fun_table"), else: law
    end)
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

  defp emit_group(names, functions) do
    {defs, purity} =
      Enum.map_reduce(names, :pure, fn name, purity ->
        %{translation: translation, purity: definition_purity} = Map.fetch!(functions, name)

        definition =
          if translation["kind"] == "def",
            do: Map.put(translation, "purity", Atom.to_string(definition_purity)),
            else: translation

        {definition, join_purity(purity, definition_purity)}
      end)

    [first | _] = defs
    span = first["span"]

    case group_measures(names, defs, functions) do
      [definition] ->
        definition

      defs ->
        %{"kind" => "mutual", "span" => span, "defs" => defs, "purity" => Atom.to_string(purity)}
    end
  end

  # Recursive groups get a lexicographic measure whose coordinates are constants
  # or `sizeOf` of a parameter plus an offset, ordered by the facts each call
  # carries. Lean still checks every descent. Some groups need each function to
  # weigh its parameters differently, such as nested loops that resume their
  # enclosing loop, which Lean's own search cannot find. Lean's search also
  # gives up on large groups, such as state machines over a bitstring.
  #
  # Groups whose calls all pass a value bound inside a constructor pattern are
  # left to Lean, which then recurses structurally, so their definitions keep
  # reducing by evaluation. Remaining bits of a bitstring, and calls passing a
  # parameter unchanged to another function, rule out structural recursion, so
  # emitting a measure there loses nothing.
  @measure_budget 100_000

  defp group_measures(names, defs, functions) do
    if Enum.any?(defs, &Map.has_key?(&1, "termination_suffix")) do
      defs
    else
      index = names |> Enum.with_index() |> Map.new()

      calls =
        for {name, caller} <- Enum.with_index(names),
            {callee, args} <- Map.fetch!(functions, name).size_calls,
            Map.has_key?(index, callee),
            # A self-call decreases only through an argument bound strictly inside
            # its parameter. Lean checks every call of the resulting measures, so
            # self-calls without one, such as those removed by Lean's preprocessing,
            # are not searched.
            caller != index[callee] or
              Enum.any?(args, &match?({_, kind} when kind in [:lt, :bits], &1)),
            do: {caller, index[callee], args}

      sizes = fn offsets ->
        for definition <- defs do
          for param <- 0..(length(definition["params"]) - 1)//1,
              offset <- offsets,
              do: {:size, param, offset}
        end
      end

      structural? =
        Enum.all?(calls, fn {_, _, args} -> Enum.any?(args, &match?({_, :lt}, &1)) end)

      search = fn ->
        with :error <- lexicographic(sizes.([0]), length(defs), calls),
             do: lexicographic(Enum.map(sizes.([0, 1]), &[{:const, 0} | &1]), length(defs), calls)
      end

      with false <- calls == [] or structural?,
           {:ok, coordinates} <- search.() do
        for {definition, index} <- Enum.with_index(defs) do
          measure =
            Enum.map(coordinates, fn coordinate ->
              case Enum.at(coordinate, index) do
                {:const, value} -> %{"const" => value}
                {:size, param, offset} -> %{"param" => param, "offset" => offset}
              end
            end)

          Map.put(definition, "measure", measure)
        end
      else
        _ -> defs
      end
    end
  end

  # Whether a call strictly decreases a coordinate, keeps it equal, or neither.
  # Only equal coordinates move on to the next one, so Lean's default tactic
  # proves each descent.
  defp compare_rank(_args, {:const, a}, {:const, b}),
    do: if(a > b, do: :gt, else: if(a == b, do: :eq, else: :fail))

  defp compare_rank(_args, {:size, _, offset}, {:const, value}),
    do: if(offset > value, do: :gt, else: :fail)

  defp compare_rank(_args, {:const, _}, {:size, _, _}), do: :fail

  defp compare_rank(args, {:size, param, offset}, {:size, callee, callee_offset}) do
    case Enum.at(args, callee) do
      {^param, kind} when kind in [:lt, :bits] and offset >= callee_offset -> :gt
      {^param, :eq} when offset > callee_offset -> :gt
      {^param, :eq} when offset == callee_offset -> :eq
      _ -> :fail
    end
  end

  defp compare_call({caller, callee, args}, coordinate),
    do: compare_rank(args, Enum.at(coordinate, caller), Enum.at(coordinate, callee))

  # Greedily build coordinates until every call strictly decreases.
  defp lexicographic(_candidates, _functions, []), do: {:ok, []}

  defp lexicographic(candidates, functions, calls) do
    # Ordering the functions is a coordinate Lean always considers.
    orders =
      for function <- 0..(functions - 1)//1 do
        for other <- 0..(functions - 1)//1, do: {:const, if(function == other, do: 1, else: 0)}
      end

    options =
      List.wrap(best_coordinate(candidates, calls)) ++
        for order <- orders,
            results = Enum.map(calls, &compare_call(&1, order)),
            :fail not in results,
            do: {order, Enum.count(results, &(&1 == :gt))}

    case Enum.max_by(options, &elem(&1, 1), fn -> nil end) do
      {coordinate, strict} when strict > 0 ->
        remaining = Enum.reject(calls, &(compare_call(&1, coordinate) == :gt))

        with {:ok, coordinates} <- lexicographic(candidates, functions, remaining),
             do: {:ok, [coordinate | coordinates]}

      _ ->
        :error
    end
  end

  # The coordinate deciding the most calls while keeping the others equal,
  # assigning ranks function by function and pruning failed calls early.
  defp best_coordinate(candidates, calls) do
    {best, _budget} = assign_ranks(candidates, [], calls, {nil, @measure_budget})
    best
  end

  defp assign_ranks([], chosen, calls, {best, budget}) do
    strict = Enum.count(calls, &(compare_call(&1, chosen) == :gt))

    if strict > 0 and strict > elem(best || {nil, 0}, 1),
      do: {{chosen, strict}, budget},
      else: {best, budget}
  end

  defp assign_ranks([ranks | rest], chosen, calls, acc) do
    index = length(chosen)

    Enum.reduce_while(ranks, acc, fn rank, {best, budget} ->
      chosen = chosen ++ [rank]

      cond do
        budget == 0 ->
          {:halt, {best, 0}}

        Enum.any?(calls, fn {caller, callee, _} = call ->
          caller <= index and callee <= index and index in [caller, callee] and
              compare_call(call, chosen) == :fail
        end) ->
          {:cont, {best, budget - 1}}

        true ->
          {:cont, assign_ranks(rest, chosen, calls, {best, budget - 1})}
      end
    end)
  end
end
