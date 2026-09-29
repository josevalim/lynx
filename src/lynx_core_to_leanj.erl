-module(lynx_core_to_leanj).

-export([module_name/1, to_definitions/1, translate/6, fun_table/2]).

-include_lib("compiler/src/core_parse.hrl").

%% Anonymous functions use integer keys; named functions use {Module, {Name, Arity}}.
%% Every entry carries a global integer ID for ordering and dispatch.
-record(state, {module, name, defs, translated, funs = #{},
                local_calls = #{}, pure = true, remote}).

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
    %% Without dollar_endonly, $ also matches before a trailing newline, which
    %% Lean would ignore as whitespace instead of preserving it in the name.
    case re:run(Name, ~"^[A-Za-z_][A-Za-z0-9_]*$", [unicode, dollar_endonly]) of
        {match, _} -> Name;
        nomatch ->
            %% Lean has no escape for a closing identifier quote. Reject it so
            %% source text cannot close the name and append qualifiers or comments.
            case binary:match(Name, ~"»") of
                nomatch -> quote_identifier(Name);
                _ -> erlang:error({unsupported_lean_module_name, Name})
            end
    end.

-spec to_definitions(cerl:c_module()) -> #{{atom(), arity()} => cerl:c_fun()}.
to_definitions(#c_module{defs = Defs}) ->
    maps:from_list([{Name, Fun} || {#c_var{name = Name}, Fun} <- Defs]).

-spec fun_table(map(), map()) -> map().
fun_table(Funs, Modules) ->
    Entries = [begin
        #{Module := #{translations := #{Name := #{translation := Definition}}}} = Modules,
        {Id, Module, Fun, Definition}
    end || _ := #{id := Id, module := Module, name := Name} = Fun <- Funs],
    array_node([fun_entry(Entry) || Entry <- lists:sort(Entries)], []).

fun_entry({_Id, Module, #{arity := Arity}, #{~"params" := Params, ~"name" := Name}}) ->
    Captures = [ident_node(<<"cap", (integer_to_binary(I))/binary>>, [])
                || I <- lists:seq(1, length(Params) - Arity)],
    Args = [ident_node(<<"arg", (integer_to_binary(I))/binary>>, [])
            || I <- lists:seq(1, Arity)],
    Body = apply_node(<<(module_name(Module))/binary, ".", Name/binary>>, Captures ++ Args, []),
    Inputs = [ident_node(~"captures", []), ident_node(~"args", [])],
    node(~"fun", [], #{
        ~"params" => Inputs,
        ~"body" => node(~"match", [], #{
            ~"expressions" => Inputs,
            ~"cases" => [
                #{~"patterns" => [array_node(Captures, []), array_node(Args, [])],
                  ~"body" => Body, ~"span" => []},
                #{~"patterns" => [node(~"wildcard", [], #{}), node(~"wildcard", [], #{})],
                  ~"body" => error_node(badarg, []), ~"span" => []}
            ]
        })
    }).

%% Translate the requested functions and their reachable local callees.
%% The supplied maps contain this module's definitions and the program-wide function registry.
%% The callback returns remote callee purity. Local purity is propagated by Lynx.Translation.
%% Unsupported constructs return their annotations and pretty-printed Core as a UTF-8 binary.
-spec translate(module(), #{{atom(), arity()} => cerl:c_fun()}, [{atom(), arity()}], map(), map(),
                {term(), fun((term(), module(), atom(), arity(), list(), map()) ->
                    {boolean(), map(), term()} | local)}) ->
    {ok, map(), map(), term()} | {unsupported_core, list(), binary()}.
translate(Module, Definitions, Names, Translated, Funs, Remote) ->
    try
        State = #state{
          module = Module,
          defs = Definitions,
          translated = Translated,
          funs = Funs,
          remote = Remote
        },

        #state{
          translated = NewTranslated,
          funs = NewFuns,
          remote = {NewContext, _Callback}
        } = lists:foldl(fun translate_def/2, State, Names),

        {ok, NewTranslated, NewFuns, NewContext}
    catch
        throw:{unsupported_core, Core} ->
            {unsupported_core, cerl:get_ann(Core),
             unicode:characters_to_binary(core_pp:format(Core))}
    end.

translate_def(Name, #state{translated = Translated} = State) ->
    case maps:is_key(Name, Translated) of
        true -> State;
        false -> translate_def(Name, definition(Name, State), State)
    end.

translate_def(Name, #c_fun{anno = Anno, vars = Vars, body = Body}, State0) ->
    State1 = State0#state{name = Name, local_calls = #{}, pure = true,
                          translated = (State0#state.translated)#{Name => pending}},
    {TranslatedBody, State2} = expression(Body, State1),
    Def = node(~"def", Anno, #{
        ~"name" => function_name(Name),
        ~"params" => [variable(Var) || Var <- Vars],
        ~"body" => TranslatedBody
    }),
    Entry = #{translation => Def, local_calls => maps:keys(State2#state.local_calls),
              pure => State2#state.pure},
    State0#state{translated = (State2#state.translated)#{Name => Entry},
                 funs = State2#state.funs, remote = State2#state.remote}.

%% Named calls must refer to module definitions. A missing name would otherwise
%% crash with an internal badkey error instead of reporting the unsupported call.
%% Generated anonymous helpers pass their definition directly to translate_def/3.
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
    Values = case Arg of #c_values{es = Es} -> Es; _ -> [Arg] end,
    {TranslatedArgs, State1} = lists:mapfoldl(fun value/2, State0, Values),
    {TranslatedClauses, State2} = lists:mapfoldl(fun clause/2, State1, Clauses),
    {node(~"match", Anno, #{
        ~"expressions" => match_values(TranslatedArgs, Anno),
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
    {apply_node(~"Lynx.Result.bind", [TranslatedArg, Continuation], Anno), State2};
%% Erlang: f(X, Y)
%% Lean: «f/2» vX vY
%% Named module functions are applied directly only when their arity matches.
%% Function values use the dynamic application clause below instead.
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
%% A malformed named call must not fall through to dynamic application.
expression(#c_apply{op = #c_var{name = Name}} = Core, _State) when is_tuple(Name) ->
    unsupported(Core);
%% Erlang: F(X, Y)
%% Lean: Lynx.Term.apply vF #[vX, vY]
expression(#c_apply{anno = Anno, op = Op, args = Args}, State0) ->
    {Function, State1} = value(Op, State0),
    {TranslatedArgs, State2} = lists:mapfoldl(fun value/2, State1, Args),
    {apply_node(~"Lynx.Term.apply", [Function, array_node(TranslatedArgs, Anno)], Anno),
     State2#state{pure = false}};
%% Erlang: other:f(X)
%% Lean: Erlang.other.«f/1» vX
%% Erlang: ?MODULE:f(X) (non-builtin)
%% Lean: «f/1» vX
expression(#c_call{anno = Anno, module = #c_literal{val = Module},
                   name = #c_literal{val = Name}, args = Args}, State0)
        when is_atom(Module), is_atom(Name) ->
    Arity = length(Args),
    {Context, Callback} = State0#state.remote,
    case Callback(Context, Module, Name, Arity, Anno, State0#state.funs) of
        local when Module =:= State0#state.module ->
            expression(#c_apply{anno = Anno, op = #c_var{name = {Name, Arity}}, args = Args},
                State0);
        {Pure, NewFuns, NewContext} ->
            {TranslatedArgs, State1} = lists:mapfoldl(fun value/2,
                State0#state{funs = NewFuns, remote = {NewContext, Callback}}, Args),
            Function = <<(module_name(Module))/binary, ".", (function_name({Name, Arity}))/binary>>,
            {apply_node(Function, TranslatedArgs, Anno), State1#state{pure = State1#state.pure andalso Pure}}
    end;
%% Erlang: f([]) -> ok.
%% Core inserts match_fail for arguments that match no function clause.
%% Lean (the generated fallback body):
%%   Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
expression(#c_primop{anno = Anno, name = #c_literal{val = match_fail},
                     args = [#c_literal{val = {function_clause}}]}, State) ->
    {error_node(function_clause, Anno), State};
expression(#c_primop{anno = Anno, name = #c_literal{val = match_fail},
                     args = [#c_tuple{es = [#c_literal{val = function_clause} | _]}]}, State) ->
    {error_node(function_clause, Anno), State};
%% Everything else (literals, cons, etc)
%% Lean: Lynx.Result.ok (Lynx.Term.integer 0)
expression(Value, State0) ->
    {Translated, State1} = value(Value, State0),
    {apply_node(~"Lynx.Result.ok", [Translated], cerl:get_ann(Value)), State1}.

clause(#c_clause{anno = Anno, pats = Patterns, guard = #c_literal{val = true}, body = Body}, State0) ->
    {Pats, State1} = lists:mapfoldl(fun value/2, State0, Patterns),
    {TranslatedBody, State2} = expression(Body, State1),
    {#{~"span" => span(Anno), ~"patterns" => match_values(Pats, Anno), ~"body" => TranslatedBody}, State2};
%% core_pp cannot print a clause on its own. Multiple patterns are supported;
%% a nontrivial guard is still unsupported, so report the guard itself.
clause(#c_clause{guard = Guard}, _State) ->
    unsupported(Guard).

%% Core separates values from computations; only computations produce Result.
value(#c_fun{vars = Vars} = Fun, State0) ->
    Captures = [#c_var{name = V} || V <- cerl_trees:free_variables(Fun),
                                   not is_tuple(V)],
    Id = map_size(State0#state.funs),
    Name = {list_to_atom("$lynx_fun_" ++ integer_to_list(Id)), length(Captures) + length(Vars)},
    Entry = #{id => Id, module => State0#state.module,
              name => Name, arity => length(Vars), captures => Captures},
    State1 = State0#state{funs = (State0#state.funs)#{Id => Entry}},
    State2 = translate_def(Name, Fun#c_fun{vars = Captures ++ Vars}, State1),
    function_node(Entry, cerl:get_ann(Fun), State2);
value(#c_var{anno = Anno, name = {_, Arity} = Name}, State0) ->
    Key = {State0#state.module, Name},
    case maps:find(Key, State0#state.funs) of
        {ok, Entry} -> function_node(Entry, Anno, State0);
        error ->
            Entry = #{id => map_size(State0#state.funs), module => State0#state.module,
                      name => Name, arity => Arity, captures => []},
            State1 = State0#state{funs = (State0#state.funs)#{Key => Entry}},
            State2 = translate_def(Name, State1),
            function_node(Entry, Anno, State2)
    end;
value(#c_var{} = Var, State) ->
    {variable(Var), State};
value(#c_literal{anno = Anno, val = []}, State) ->
    {ident_node(~"Lynx.Term.nil", Anno), State};
%% The compiler folds constant lists into a single literal. Decompose it just
%% like c_cons nodes, including a non-list tail for improper lists.
value(#c_literal{anno = Anno, val = [Head | Tail]}, State0) ->
    {TranslatedHead, State1} = value(#c_literal{anno = Anno, val = Head}, State0),
    {TranslatedTail, State2} = value(#c_literal{anno = Anno, val = Tail}, State1),
    {apply_node(~"Lynx.Term.cons", [TranslatedHead, TranslatedTail], Anno), State2};
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

%% The table contains code; every function value carries its own capture values.
function_node(#{id := Id, arity := Arity, captures := Captures}, Anno, State0) ->
    {Values, State1} = lists:mapfoldl(fun value/2, State0, Captures),
    {apply_node(~"Lynx.Term.function", [node(~"integer", [], #{~"value" => Id}),
                                      node(~"integer", [], #{~"value" => Arity}),
                                      array_node(Values, Anno)], Anno), State1}.

match_values([], Anno) -> [ident_node(~"Unit.unit", Anno)];
match_values(Values, _Anno) -> Values.

array_node(Values, Anno) ->
    node(~"array", Anno, #{~"elements" => Values}).

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

error_node(Reason, Anno) ->
    String = node(~"string", Anno, #{~"value" => atom_to_binary(Reason, utf8)}),
    Atom = apply_node(~"Lynx.Term.atom", [String], Anno),
    Exception = apply_node(~"Lynx.Exception.error", [Atom], Anno),
    apply_node(~"Lynx.Result.error", [Exception], Anno).

%% A zero-argument call is a reference to its Lean definition; the runner
%% rejects applications without arguments.
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
