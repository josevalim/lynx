-module(lynx_core_to_leanj).

-export([module_name/1, to_definitions/1, translate/6, join_purity/2]).

-include_lib("compiler/src/core_parse.hrl").

-record(state, {module, name, defs, translated, funs = #{},
                local_calls = #{}, references = #{}, dynamic = false, purity = pure, remote}).

-spec module_name(module()) -> binary().
module_name(Module) ->
    case atom_to_binary(Module, utf8) of
        <<"Elixir.", _/binary>> = Name -> Name;
        Name -> <<"Erlang.", Name/binary>>
    end.

-spec to_definitions(cerl:c_module()) -> #{{atom(), arity()} => cerl:c_fun()}.
to_definitions(#c_module{defs = Defs}) ->
    maps:from_list([{Name, Fun} || {#c_var{name = Name}, Fun} <- Defs]).

%% Translate the requested functions and their reachable local callees.
%% The supplied maps contain translated definitions and closure metadata for this module.
%% The callback returns remote callee purity. Local purity is propagated by Lynx.Translation.
%% Unsupported constructs return their annotations and pretty-printed Core as a UTF-8 binary.
-spec translate(module(), #{{atom(), arity()} => cerl:c_fun()}, [{atom(), arity()}], map(), map(),
                {term(), fun((term(), module(), atom(), arity(), list()) ->
                    {pure | impure | neutral, term()} | local)}) ->
    {ok, map(), map(), term()} | {unsupported_core, list(), binary()}.
translate(Module, Definitions, Names, Translated, Funs, Remote) ->
    try
        State = lists:foldl(fun translate_def/2,
            #state{module = Module, defs = Definitions, translated = Translated, funs = Funs, remote = Remote}, Names),
        {Context, _Callback} = State#state.remote,
        {ok, State#state.translated, State#state.funs, Context}
    catch
        throw:{unsupported_core, Core} ->
            {unsupported_core, cerl:get_ann(Core),
             unicode:characters_to_binary(core_pp:format(Core))}
    end.

translate_def(Name, #state{translated = Translated} = State0) ->
    case maps:is_key(Name, Translated) of
        true -> State0;
        false ->
            #c_fun{anno = Anno, vars = Vars, body = Body} = maps:get(Name, State0#state.defs),
            State1 = State0#state{name = Name, local_calls = #{}, references = #{}, dynamic = false, purity = pure,
                                  translated = Translated#{Name => pending}},
            {TranslatedBody, State2} = expression(Body, State1),
            Def = node(~"def", Anno, #{
                ~"name" => function_name(Name),
                ~"params" => [variable(Var) || Var <- Vars],
                ~"body" => TranslatedBody
            }),
            Entry = #{translation => Def, local_calls => maps:keys(State2#state.local_calls),
                      references => maps:keys(State2#state.references),
                      dynamic => State2#state.dynamic, purity => State2#state.purity},
            State0#state{translated = (State2#state.translated)#{Name => Entry},
                         defs = State2#state.defs, funs = State2#state.funs,
                         remote = State2#state.remote}
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
expression(#c_apply{anno = Anno, op = #c_var{name = {_, _} = Name}, args = Args}, State0) ->
    {TranslatedArgs, State1} = lists:mapfoldl(fun value/2, State0, Args),
    State2 = translate_def(Name, State1),
    Calls = case State2#state.name of
        Name -> State2#state.local_calls;
        _ -> (State2#state.local_calls)#{Name => true}
    end,
    {apply_node(function_name(Name), TranslatedArgs, Anno),
     State2#state{local_calls = Calls}};
%% Erlang: F(X, Y)
%% Lean: Erlang.erlang.«apply/2» vF (Lynx.Term.cons vX (Lynx.Term.cons vY Lynx.Term.nil))
expression(#c_apply{anno = Anno, op = Op, args = Args}, State0) ->
    ArgList = lists:foldr(fun(Arg, Tail) ->
        #c_cons{anno = Anno, hd = Arg, tl = Tail}
    end, #c_literal{anno = Anno, val = []}, Args),
    expression(#c_call{anno = Anno, module = #c_literal{val = erlang},
        name = #c_literal{val = apply}, args = [Op, ArgList]}, State0);
%% apply/2 dispatches through the program's function table and has neutral purity.
expression(#c_call{anno = Anno, module = #c_literal{val = erlang},
                   name = #c_literal{val = apply}, args = Args}, State0)
        when length(Args) =:= 2 ->
    {Context, Callback} = State0#state.remote,
    {_Purity, NewContext} = Callback(Context, erlang, apply, 2, Anno),
    {TranslatedArgs, State1} = lists:mapfoldl(fun value/2,
        State0#state{remote = {NewContext, Callback}}, Args),
    {apply_node(~"Erlang.erlang.«apply/2»", TranslatedArgs, Anno),
     State1#state{dynamic = true, purity = join_purity(State1#state.purity, neutral)}};
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
        {Purity, NewContext} ->
            {TranslatedArgs, State1} = lists:mapfoldl(fun value/2,
                State0#state{remote = {NewContext, Callback}}, Args),
            Function = <<(module_name(Module))/binary, ".", (function_name({Name, Arity}))/binary>>,
            {apply_node(Function, TranslatedArgs, Anno), State1#state{purity = join_purity(State1#state.purity, Purity)}}
    end;
%% Erlang: f([]) -> ok.
%% Core inserts match_fail for arguments that match no function clause.
%% Lean (the generated fallback body):
%%   Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
expression(#c_primop{anno = Anno, name = #c_literal{val = match_fail},
                     args = [#c_literal{val = {function_clause}}]} = Core, State0) ->
    expression(Core#c_primop{args = [#c_tuple{es = [#c_literal{anno = Anno, val = function_clause}]}]},
               State0);
expression(#c_primop{anno = Anno, name = #c_literal{val = match_fail},
                     args = [#c_tuple{es = [#c_literal{val = function_clause} | _]}]}, State0) ->
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
expression(#c_var{anno = Anno} = Var, State0) ->
    {Translated, State1} = value(Var, State0),
    {apply_node(~"Lynx.Result.«ok»", [Translated], Anno), State1};
expression(#c_fun{anno = Anno} = Fun, State0) ->
    {Translated, State1} = value(Fun, State0),
    {apply_node(~"Lynx.Result.«ok»", [Translated], Anno), State1};
expression(#c_cons{anno = Anno} = Cons, State0) ->
    {Translated, State1} = value(Cons, State0),
    {apply_node(~"Lynx.Result.«ok»", [Translated], Anno), State1};
%% Erlang: receive X -> X end
%% Lean: no translation; translate/6 returns {unsupported_core, SpanAnno, CoreString}.
expression(Core, _State) ->
    unsupported(Core).

clause(#c_clause{anno = Anno, pats = Patterns, guard = #c_literal{val = true}, body = Body}, State0) ->
    {Pats, State1} = lists:mapfoldl(fun value/2, State0, Patterns),
    Pat = values_node(Pats, Anno),
    {TranslatedBody, State2} = expression(Body, State1),
    {#{~"span" => span(Anno), ~"pattern" => Pat, ~"body" => TranslatedBody}, State2};
clause(Core, _State) ->
    unsupported(Core).

%% Core separates values from computations; only computations produce Result.
value(#c_values{anno = Anno, es = Values}, State0) ->
    {Translated, State1} = lists:mapfoldl(fun value/2, State0, Values),
    {values_node(Translated, Anno), State1};
value(#c_fun{vars = Vars} = Fun, State0) ->
    Key = {anonymous, State0#state.name, Fun},
    case maps:find(Key, State0#state.funs) of
        {ok, Entry} -> closure(Entry, cerl:get_ann(Fun), State0);
        error ->
            Captures = [#c_var{name = V} || V <- cerl_trees:free_variables(Fun),
                                           not is_tuple(V)],
            Name = {{anonymous, map_size(State0#state.funs)}, length(Captures) + length(Vars)},
            Entry = #{name => Name, arity => length(Vars), captures => Captures},
            State1 = State0#state{
                funs = (State0#state.funs)#{Key => Entry},
                defs = (State0#state.defs)#{Name => Fun#c_fun{vars = Captures ++ Vars}}},
            State2 = translate_def(Name, State1),
            closure(Entry, cerl:get_ann(Fun), State2)
    end;
value(#c_var{anno = Anno, name = {_, _} = Name}, State0) ->
    Entry = #{name => Name, arity => element(2, Name), captures => []},
    State1 = translate_def(Name, State0),
    closure(Entry, Anno, State1#state{funs = (State1#state.funs)#{{named, Name} => Entry}});
value(#c_var{} = Var, State) ->
    {variable(Var), State};
value(#c_literal{anno = Anno, val = []}, State) ->
    {ident_node(~"Lynx.Term.«nil»", Anno), State};
value(#c_literal{anno = Anno, val = [Head | Tail]}, State0) ->
    value(#c_cons{anno = Anno, hd = #c_literal{anno = Anno, val = Head},
                  tl = #c_literal{anno = Anno, val = Tail}}, State0);
value(#c_literal{anno = Anno, val = N}, State) when is_integer(N) ->
    {apply_node(~"Lynx.Term.«integer»", [node(~"integer", Anno, #{~"value" => N})], Anno), State};
value(#c_literal{anno = Anno, val = Atom}, State) when is_atom(Atom) ->
    String = node(~"string", Anno, #{~"value" => atom_to_binary(Atom, utf8)}),
    {apply_node(~"Lynx.Term.«atom»", [String], Anno), State};
value(#c_cons{anno = Anno, hd = Head, tl = Tail}, State0) ->
    {Args, State1} = lists:mapfoldl(fun value/2, State0, [Head, Tail]),
    {apply_node(~"Lynx.Term.«cons»", Args, Anno), State1};
value(Core, _State) ->
    unsupported(Core).

%% The table contains code; every function value carries its own capture values.
closure(#{name := Name, arity := Arity, captures := Captures}, Anno, State0) ->
    {Values, State1} = lists:mapfoldl(fun value/2, State0, Captures),
    {node(~"closure", Anno, #{~"module" => module_name(State1#state.module),
                             ~"name" => function_name(Name), ~"arity" => Arity,
                             ~"captures" => array_node(Values, Anno)}),
     State1#state{references = (State1#state.references)#{Name => true}}}.

values_node([], Anno) -> ident_node(~"Unit.unit", Anno);
values_node([Value], _Anno) -> Value;
values_node([Value | Rest], Anno) ->
    apply_node(~"Prod.mk", [Value, values_node(Rest, Anno)], Anno).

array_node(Values, Anno) ->
    apply_node(~"Array.mk", [list_node(Values, Anno)], Anno).

list_node(Values, Anno) ->
    lists:foldr(fun(Value, Tail) -> apply_node(~"List.cons", [Value, Tail], Anno) end,
                ident_node(~"List.nil", Anno), Values).

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

function_name({{anonymous, Index}, _Arity}) ->
    quote_identifier(<<"$lynx_fun_", (integer_to_binary(Index))/binary>>);
function_name({Name, Arity}) when is_atom(Name), is_integer(Arity), Arity >= 0 ->
    quote_identifier(<<(atom_to_binary(Name, utf8))/binary, "/", (integer_to_binary(Arity))/binary>>).

quote_identifier(Name) ->
    <<$«/utf8, Name/binary, $»/utf8>>.

ident_node(Name, Anno) ->
    node(~"ident", Anno, #{~"name" => Name}).

apply_node(Name, [], Anno) -> ident_node(Name, Anno);
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

-spec join_purity(pure | impure | neutral, pure | impure | neutral) -> pure | impure | neutral.
join_purity(impure, _) -> impure;
join_purity(_, impure) -> impure;
join_purity(neutral, _) -> neutral;
join_purity(_, neutral) -> neutral;
join_purity(pure, pure) -> pure.

unsupported(Core) ->
    throw({unsupported_core, Core}).
