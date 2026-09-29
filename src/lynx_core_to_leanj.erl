-module(lynx_core_to_leanj).

-export([module_name/1, to_definitions/1, translate/5]).

-include_lib("compiler/src/core_parse.hrl").

-record(state, {module, name, defs, translated, local_calls = #{}, pure = true, remote}).

-spec module_name(module()) -> binary().
module_name(Module) ->
    case atom_to_binary(Module, utf8) of
        <<"Elixir.", Rest/binary>> ->
            Parts = [module_component(Part) || Part <- binary:split(Rest, ~".", [global])],
            iolist_to_binary(lists:join(~".", [~"Elixir" | Parts]));
        Name -> <<"Erlang.", (module_component(Name))/binary>>
    end.

%% Module names become Lean namespaces. A component that is not a plain
%% identifier, such as the Erlang module 'my-mod', must be quoted as «my-mod».
%% An Erlang module name is one flat component even when it contains dots.
module_component(Name) ->
    case re:run(Name, ~"^[A-Za-z_][A-Za-z0-9_]*$", [unicode]) of
        {match, _} -> Name;
        nomatch -> quote_identifier(Name)
    end.

-spec to_definitions(cerl:c_module()) -> #{{atom(), arity()} => cerl:c_fun()}.
to_definitions(#c_module{defs = Defs}) ->
    maps:from_list([{Name, Fun} || {#c_var{name = Name}, Fun} <- Defs]).

%% Translate the requested functions and their reachable local callees.
%% The supplied map contains functions already translated from this module.
%% The callback returns remote callee purity. Local purity is propagated by Lynx.Translation.
%% Unsupported constructs return their annotations and pretty-printed Core as a UTF-8 binary.
-spec translate(module(), #{{atom(), arity()} => cerl:c_fun()}, [{atom(), arity()}], map(),
                {term(), fun((term(), module(), atom(), arity(), list()) ->
                    {boolean(), term()} | local)}) ->
    {ok, map(), term()} | {unsupported_core, list(), binary()}.
translate(Module, Definitions, Names, Translated, Remote) ->
    try
        State = lists:foldl(fun translate_def/2,
            #state{module = Module, defs = Definitions, translated = Translated, remote = Remote}, Names),
        {Context, _Callback} = State#state.remote,
        {ok, State#state.translated, Context}
    catch
        throw:{unsupported_core, Core} ->
            {unsupported_core, cerl:get_ann(Core),
             unicode:characters_to_binary(core_pp:format(Core))}
    end.

translate_def(Name, #state{translated = Translated} = State0) ->
    case maps:is_key(Name, Translated) of
        true -> State0;
        false ->
            #c_fun{anno = Anno, vars = Vars, body = Body} = definition(Name, State0),
            State1 = State0#state{name = Name, local_calls = #{}, pure = true,
                                  translated = Translated#{Name => pending}},
            {TranslatedBody, State2} = expression(Body, State1),
            Def = node(~"def", Anno, #{
                ~"name" => function_name(Name),
                ~"params" => [variable(Var) || Var <- Vars],
                ~"body" => TranslatedBody
            }),
            Entry = #{translation => Def, local_calls => maps:keys(State2#state.local_calls),
                      pure => State2#state.pure},
            State0#state{translated = (State2#state.translated)#{Name => Entry},
                         remote = State2#state.remote}
    end.

%% Only top-level module functions can be translated. A missing name would
%% otherwise crash with an internal badkey error instead of reporting the call.
definition(Name, #state{defs = Defs}) ->
    case Defs of
        #{Name := Definition} -> Definition;
        #{} -> unsupported(cerl:c_var(Name))
    end.

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
%% Lean: Lynx.Result.bind («f/1» vX) fun vY => «g/1» vY
expression(#c_let{anno = Anno, vars = [Var], arg = Arg, body = Body}, State0) ->
    {TranslatedArg, State1} = expression(Arg, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    Continuation = node(~"fun", Anno, #{
        ~"params" => [variable(Var)], ~"body" => TranslatedBody
    }),
    {apply_node(~"Lynx.Result.«bind»", [TranslatedArg, Continuation], Anno), State2};
%% Erlang: f(X, Y)
%% Lean: «f/2» vX vY
%% Only named module functions ({Name, Arity}) are applied directly. Applying a
%% variable that holds a fun, such as F(X), is reported as unsupported Core by the
%% final clause instead of being treated as a module function.
expression(#c_apply{anno = Anno, op = #c_var{name = {FunName, Arity} = Name}, args = Args}, State0)
        when is_atom(FunName), is_integer(Arity), Arity =:= length(Args) ->
    {TranslatedArgs, State1} = lists:mapfoldl(fun value/2, State0, Args),
    State2 = translate_def(Name, State1),
    Calls = case State2#state.name of
        Name -> State2#state.local_calls;
        _ -> (State2#state.local_calls)#{Name => true}
    end,
    {apply_node(function_name(Name), TranslatedArgs, Anno),
     State2#state{local_calls = Calls}};
%% Erlang: other:f(X)
%% Lean: Erlang.other.«f/1» vX
%% Erlang: ?MODULE:f(X) (non-builtin)
%% Lean: «f/1» vX
expression(#c_call{anno = Anno, module = #c_literal{val = Module},
                   name = #c_literal{val = Name}, args = Args}, State0)
        when is_atom(Module), is_atom(Name) ->
    Arity = length(Args),
    {Context, Callback} = State0#state.remote,
    case Callback(Context, Module, Name, Arity, Anno) of
        local when Module =:= State0#state.module ->
            expression(#c_apply{anno = Anno, op = #c_var{name = {Name, Arity}}, args = Args},
                State0);
        {Pure, NewContext} ->
            {TranslatedArgs, State1} = lists:mapfoldl(fun value/2,
                State0#state{remote = {NewContext, Callback}}, Args),
            Function = <<(module_name(Module))/binary, ".", (function_name({Name, Arity}))/binary>>,
            {apply_node(Function, TranslatedArgs, Anno), State1#state{pure = State1#state.pure andalso Pure}}
    end;
%% Erlang: f([]) -> ok.
%% Core inserts match_fail for arguments that match no function clause.
%% Lean (the generated fallback body):
%%   Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
expression(#c_primop{anno = Anno, name = #c_literal{val = match_fail},
                     args = [#c_tuple{es = [#c_literal{val = function_clause}, #c_var{}]}]}, State0) ->
    {Reason, State1} = value(#c_literal{anno = Anno, val = function_clause}, State0),
    Exception = apply_node(~"Lynx.Exception.«error»", [Reason], Anno),
    {apply_node(~"Lynx.Result.«error»", [Exception], Anno), State1};
%% Erlang: 0
%% Lean: Lynx.Result.ok (Lynx.Term.integer 0)
expression(#c_literal{anno = Anno} = Literal, State0) ->
    {Translated, State1} = value(Literal, State0),
    {apply_node(~"Lynx.Result.«ok»", [Translated], Anno), State1};
%% Erlang: X
%% Lean: Lynx.Result.ok vX
expression(#c_var{anno = Anno} = Var, State) ->
    {apply_node(~"Lynx.Result.«ok»", [variable(Var)], Anno), State};
%% Erlang: receive X -> X end
%% Lean: no translation; translate/5 returns {unsupported_core, SpanAnno, CoreString}.
expression(Core, _State) ->
    unsupported(Core).

clause(#c_clause{anno = Anno, pats = [Pattern], guard = #c_literal{val = true}, body = Body}, State0) ->
    {Pat, State1} = value(Pattern, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    {#{~"span" => span(Anno), ~"pattern" => Pat, ~"body" => TranslatedBody}, State2};
%% core_pp cannot print a clause on its own, so report the offending part:
%% the guard when it is not 'true', otherwise the pattern list.
clause(#c_clause{pats = [_], guard = Guard}, _State) ->
    unsupported(Guard);
clause(#c_clause{anno = Anno, pats = Patterns}, _State) ->
    unsupported(cerl:ann_c_values(Anno, Patterns)).

%% Core separates values from computations; only computations produce Result.
value(#c_var{} = Var, State) ->
    {variable(Var), State};
value(#c_literal{anno = Anno, val = []}, State) ->
    {ident_node(~"Lynx.Term.«nil»", Anno), State};
value(#c_literal{anno = Anno, val = N}, State) when is_integer(N) ->
    {apply_node(~"Lynx.Term.«integer»", [node(~"integer", Anno, #{~"value" => N})], Anno), State};
value(#c_literal{anno = Anno, val = Atom}, State) when is_atom(Atom) ->
    String = node(~"string", Anno, #{~"value" => atom_to_binary(Atom, utf8)}),
    {apply_node(~"Lynx.Term.«atom»", [String], Anno), State};
%% The compiler folds constant lists such as [1, a] into a single literal.
%% Translate them element by element, exactly like the equivalent c_cons nodes.
value(#c_literal{anno = Anno, val = [Head | Tail]}, State0) ->
    {Args, State1} = lists:mapfoldl(fun value/2, State0,
        [#c_literal{anno = Anno, val = Head}, #c_literal{anno = Anno, val = Tail}]),
    {apply_node(~"Lynx.Term.«cons»", Args, Anno), State1};
value(#c_cons{anno = Anno, hd = Head, tl = Tail}, State0) ->
    {Args, State1} = lists:mapfoldl(fun value/2, State0, [Head, Tail]),
    {apply_node(~"Lynx.Term.«cons»", Args, Anno), State1};
value(Core, _State) ->
    unsupported(Core).

%% Keep compiler temporaries and source variables in distinct name spaces.
%% Preserve the underscore prefix for source names that start with one.
variable(#c_var{anno = Anno, name = Name}) when is_integer(Name), Name >= 0 ->
    ident_node(quote_identifier(<<"_", (integer_to_binary(Name))/binary>>), Anno);
variable(#c_var{anno = Anno, name = Name}) when is_atom(Name) ->
    Binary = atom_to_binary(Name, utf8),
    case Binary of
        <<"_", _/binary>> -> ident_node(quote_identifier(<<"_v", Binary/binary>>), Anno);
        _ -> ident_node(quote_identifier(<<"v", Binary/binary>>), Anno)
    end;
variable(Core) ->
    unsupported(Core).

function_name({Name, Arity}) when is_atom(Name), is_integer(Arity), Arity >= 0 ->
    quote_identifier(<<(atom_to_binary(Name, utf8))/binary, "/", (integer_to_binary(Arity))/binary>>).

quote_identifier(Name) ->
    <<$«/utf8, Name/binary, $»/utf8>>.

ident_node(Name, Anno) ->
    node(~"ident", Anno, #{~"name" => Name}).

%% A call without arguments, such as zero() or self(), is just a reference to the
%% zero-parameter Lean definition. The runner rejects applications without arguments.
apply_node(Name, [], Anno) ->
    ident_node(Name, Anno);
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
