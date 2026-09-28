-module(lynx_core_to_leanj).

-export([translate/1]).

-include_lib("compiler/src/core_parse.hrl").

-record(state, {name, graph}).

%% Translate the Core tree returned by the debug_info backend's core_v1
%% format into a list of JSON-encodable Lynx commands for one module.
%% Unsupported constructs return their pretty-printed Core as a UTF-8 binary.
-spec translate(cerl:c_module()) -> {ok, [map()]} | {unsupported_core, binary()}.
translate(#c_module{defs = Defs}) ->
    Graph = digraph:new(),
    try
        Functions = [begin
            digraph:add_vertex(Graph, Name),
            Def
        end || {#c_var{name = Name}, _} = Def <- Defs,
               Name =/= {module_info, 0}, Name =/= {module_info, 1}],
        [translate_def(Def, Graph) || Def <- Functions],
        {ok, cluster(Graph)}
    catch
        throw:{unsupported_core, Core} ->
            {unsupported_core, unicode:characters_to_binary(core_pp:format(Core))}
    after
        digraph:delete(Graph)
    end.

translate_def({#c_var{name = Name}, #c_fun{anno = Anno, vars = Vars, body = Body}}, Graph) ->
    {TranslatedBody, _State} = expression(Body, #state{name = Name, graph = Graph}),
    Def = node(~"def", Anno, #{
        ~"name" => function_name(Name),
        ~"params" => [variable(Var) || Var <- Vars],
        ~"body" => TranslatedBody
    }),
    digraph:add_vertex(Graph, Name, Def).

%% Condensation collapses recursive groups into vertices of an acyclic graph.
%% Edges point from callees to callers, so topsort emits dependencies first.
cluster(Graph) ->
    Components = digraph_utils:condensation(Graph),
    try
        [emit_group(Group, Graph) || Group <- topsort(Components)]
    after
        digraph:delete(Components)
    end.

%% Alphabetize each ready batch. OTP's topsort leaves ties in arbitrary order.
%% The condensed graph is acyclic and is no longer needed after this traversal.
topsort(Graph) ->
    Ready = lists:sort([{lists:sort(Group), Group} || Group <- digraph:vertices(Graph),
                                                      digraph:in_degree(Graph, Group) =:= 0]),
    case Ready of
        [] -> [];
        _ ->
            [digraph:del_vertex(Graph, Group) || {_, Group} <- Ready],
            [Names || {Names, _} <- Ready] ++ topsort(Graph)
    end.

emit_group(Names, Graph) ->
    Defs = [Def || Name <- Names, {_, Def} <- [digraph:vertex(Graph, Name)]],
    [First | _] = Defs,
    Span = maps:get(~"span", First),
    Declaration = case Defs of
        [Def] -> Def;
        _ -> #{~"kind" => ~"mutual", ~"span" => Span, ~"defs" => Defs}
    end,
    % TODO: Track purity
    #{~"kind" => ~"command", ~"span" => Span,
      ~"name" => ~"lynx_pure", ~"expr" => Declaration}.

%% Erlang: case X of [] -> 0; Other -> 1 end
%% Lean:
%%   match vX with
%%   | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
%%   | vOther => Lynx.Result.ok (Lynx.Term.integer 1)
expression(#c_case{anno = Anno, arg = Arg, clauses = Clauses}, State0) ->
    {TranslatedArg, State1} = value(Arg, State0),
    {TranslatedClauses, State2} = lists:mapfoldl(fun clause/2, State1, Clauses),
    {node(~"match", Anno, #{
        ~"expression" => TranslatedArg,
        ~"cases" => TranslatedClauses
    }), State2};
%% Erlang: Y = f(X), g(Y)
%% Lean: Lynx.Result.bind (f_1 vX) fun vY => g_1 vY
expression(#c_let{anno = Anno, vars = [Var], arg = Arg, body = Body}, State0) ->
    {TranslatedArg, State1} = expression(Arg, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    Continuation = node(~"fun", Anno, #{
        ~"params" => [variable(Var)], ~"body" => TranslatedBody
    }),
    {apply_node(~"Lynx.Result.bind", [TranslatedArg, Continuation], Anno), State2};
%% Erlang: f(X, Y)
%% Lean: f_2 vX vY
expression(#c_apply{anno = Anno, op = #c_var{name = Name}, args = Args}, State0) ->
    {TranslatedArgs, State1} = lists:mapfoldl(fun value/2, State0, Args),
    case State1#state.name of
        Name -> ok;
        Caller -> digraph:add_edge(State1#state.graph, {Name, Caller}, Name, Caller, [])
    end,
    {apply_node(function_name(Name), TranslatedArgs, Anno), State1};
%% Erlang: X + Y
%% Lean: Lynx.Modules.Erlang.add_2 vX vY
expression(#c_call{anno = Anno, module = #c_literal{val = erlang},
                   name = #c_literal{val = '+'}, args = [Left, Right]}, State0) ->
    {Args, State1} = lists:mapfoldl(fun value/2, State0, [Left, Right]),
    {apply_node(~"Lynx.Modules.Erlang.add_2", Args, Anno), State1};
%% Erlang: f([]) -> ok.
%% Core inserts match_fail for arguments that match no function clause.
%% Lean (the generated fallback body):
%%   Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
expression(#c_primop{anno = Anno, name = #c_literal{val = match_fail},
                     args = [#c_tuple{es = [#c_literal{val = function_clause}, #c_var{}]}]}, State0) ->
    {Reason, State1} = value(#c_literal{anno = Anno, val = function_clause}, State0),
    Exception = apply_node(~"Lynx.Exception.error", [Reason], Anno),
    {apply_node(~"Lynx.Result.error", [Exception], Anno), State1};
%% Erlang: 0
%% Lean: Lynx.Result.ok (Lynx.Term.integer 0)
expression(#c_literal{anno = Anno} = Literal, State0) ->
    {Translated, State1} = value(Literal, State0),
    {apply_node(~"Lynx.Result.ok", [Translated], Anno), State1};
%% Erlang: X
%% Lean: Lynx.Result.ok vX
expression(#c_var{anno = Anno} = Var, State) ->
    {apply_node(~"Lynx.Result.ok", [variable(Var)], Anno), State};
%% Erlang: receive X -> X end
%% Lean: no translation; translate/1 returns {unsupported_core, CoreString}.
expression(Core, _State) ->
    unsupported(Core).

clause(#c_clause{anno = Anno, pats = [Pattern], guard = #c_literal{val = true}, body = Body}, State0) ->
    {Pat, State1} = value(Pattern, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    {#{~"span" => span(Anno), ~"pattern" => Pat, ~"body" => TranslatedBody}, State2};
clause(Core, _State) ->
    unsupported(Core).

%% Core separates values from computations; only computations produce Result.
value(#c_var{} = Var, State) ->
    {variable(Var), State};
value(#c_literal{anno = Anno, val = []}, State) ->
    {ident_node(~"Lynx.Term.nil", Anno), State};
value(#c_literal{anno = Anno, val = N}, State) when is_integer(N) ->
    {apply_node(~"Lynx.Term.integer", [node(~"integer", Anno, #{~"value" => N})], Anno), State};
value(#c_literal{anno = Anno, val = Atom}, State) when is_atom(Atom) ->
    String = node(~"string", Anno, #{~"value" => atom_to_binary(Atom, utf8)}),
    {apply_node(~"Lynx.Term.atom", [String], Anno), State};
value(#c_cons{anno = Anno, hd = Head, tl = Tail}, State0) ->
    {Args, State1} = lists:mapfoldl(fun value/2, State0, [Head, Tail]),
    {apply_node(~"Lynx.Term.cons", Args, Anno), State1};
value(Core, _State) ->
    unsupported(Core).

%% Keep compiler temporaries and source variables in distinct name spaces.
%% Preserve the underscore prefix for source names that start with one.
variable(#c_var{anno = Anno, name = Name}) when is_integer(Name), Name >= 0 ->
    ident_node(<<"_", (integer_to_binary(Name))/binary>>, Anno);
variable(#c_var{anno = Anno, name = Name}) when is_atom(Name) ->
    Binary = atom_to_binary(Name, utf8),
    case Binary of
        <<"_", _/binary>> -> ident_node(<<"_v", Binary/binary>>, Anno);
        _ -> ident_node(<<"v", Binary/binary>>, Anno)
    end;
variable(Core) ->
    unsupported(Core).

function_name({Name, Arity}) when is_atom(Name), is_integer(Arity), Arity >= 0 ->
    <<(atom_to_binary(Name, utf8))/binary, "_", (integer_to_binary(Arity))/binary>>.

ident_node(Name, Anno) ->
    node(~"ident", Anno, #{~"name" => Name}).

apply_node(Name, Args, Anno) ->
    node(~"apply", Anno, #{~"function" => ident_node(Name, []), ~"args" => Args}).

node(Kind, Anno, Fields) ->
    Fields#{~"kind" => Kind, ~"span" => span(Anno)}.

span([{Line, Column} | _]) when is_integer(Line), Line > 0, is_integer(Column), Column > 0 ->
    [Line, Column];
span([Line | _]) when is_integer(Line), Line > 0 ->
    [Line];
span([_ | Rest]) ->
    span(Rest);
span([]) ->
    [].

unsupported(Core) ->
    throw({unsupported_core, Core}).
