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
        <<"Elixir.", _/binary>> = Name -> Name;
        Name -> <<"Erlang.", Name/binary>>
    end.

-spec to_definitions(cerl:c_module()) -> #{{atom(), arity()} => cerl:c_fun()}.
to_definitions(#c_module{defs = Defs}) ->
    maps:from_list([{Name, Fun} || {#c_var{name = Name}, Fun} <- Defs]).

-spec fun_table(map(), map()) -> [map()].
fun_table(Funs, Modules) ->
    Entries = [begin
        #{Module := #{translations := #{Name := #{translation := Definition, pure := Pure}}}} = Modules,
        {Id, Module, Fun, Definition, Pure}
    end || _ := #{id := Id, module := Module, name := Name} = Fun <- Funs],
    [fun_entry(Entry) || Entry <- lists:sort(Entries)].

fun_entry({_Id, Module, #{arity := Arity}, #{~"params" := Params, ~"name" := Name}, Pure}) ->
    Captures = [var_node(<<"cap", (integer_to_binary(I))/binary>>, [])
                || I <- lists:seq(1, length(Params) - Arity)],
    Args = [var_node(<<"arg", (integer_to_binary(I))/binary>>, [])
            || I <- lists:seq(1, Arity)],
    Body = remote_call_node(module_name(Module), Name, Captures ++ Args, []),
    #{~"body" => Body, ~"captures" => Captures, ~"args" => Args,
      ~"pure" => Pure, ~"span" => []}.

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
        false -> translate_def(Name, maps:get(Name, State#state.defs), State)
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
        ~"expressions" => TranslatedArgs,
        ~"cases" => TranslatedClauses
    }), State2};
%% Erlang: Y = f(X), g(Y)
%% Lean: Lynx.Result.bind («f/1» vX) fun vY => «g/1» vY
expression(#c_let{anno = Anno, vars = [Var], arg = Arg, body = Body}, State0) ->
    {TranslatedArg, State1} = expression(Arg, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    {node(~"bind", Anno, #{~"var" => variable(Var),
        ~"computation" => TranslatedArg, ~"body" => TranslatedBody}), State2};
%% Erlang: f(X), g(X)
%% Lean: do let _ ← «f/1» vX; «g/1» vX
expression(#c_seq{anno = Anno, arg = Arg, body = Body}, State0) ->
    {TranslatedArg, State1} = expression(Arg, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    {node(~"bind", Anno, #{~"var" => node(~"wildcard", Anno, #{}),
        ~"computation" => TranslatedArg, ~"body" => TranslatedBody}), State2};
%% Erlang: f(X, Y)
%% Lean: «f/2» vX vY
expression(#c_apply{anno = Anno, op = #c_var{name = {_, _} = Name}, args = Args}, State0) ->
    {TranslatedArgs, State1} = lists:mapfoldl(fun value/2, State0, Args),
    State2 = translate_def(Name, State1),
    Calls = case State2#state.name of
        Name -> State2#state.local_calls;
        _ -> (State2#state.local_calls)#{Name => true}
    end,
    {local_call_node(function_name(Name), TranslatedArgs, Anno),
     State2#state{local_calls = Calls}};
%% Erlang: F(X, Y)
%% Lean: Lynx.Term.apply vF #[vX, vY]
expression(#c_apply{anno = Anno, op = Op, args = Args}, State0) ->
    {Function, State1} = value(Op, State0),
    {TranslatedArgs, State2} = lists:mapfoldl(fun value/2, State1, Args),
    {node(~"fun_call", Anno, #{~"function" => Function, ~"args" => TranslatedArgs}),
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
            {remote_call_node(module_name(Module), atom_to_binary(Name, utf8), TranslatedArgs, Anno), State1#state{pure = State1#state.pure andalso Pure}}
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
    {node(~"return", cerl:get_ann(Value), #{~"value" => Translated}), State1}.

clause(#c_clause{anno = Anno, pats = Patterns, guard = #c_literal{val = true}, body = Body}, State0) ->
    {Pats, State1} = lists:mapfoldl(fun value/2, State0, Patterns),
    {TranslatedBody, State2} = expression(Body, State1),
    {#{~"span" => span(Anno), ~"patterns" => Pats, ~"body" => TranslatedBody}, State2};
clause(Core, _State) ->
    unsupported(Core).

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
    {node(~"nil", Anno, #{}), State};
value(#c_literal{anno = Anno, val = [Head | Tail]}, State0) ->
    {TranslatedHead, State1} = value(#c_literal{anno = Anno, val = Head}, State0),
    {TranslatedTail, State2} = value(#c_literal{anno = Anno, val = Tail}, State1),
    {node(~"cons", Anno, #{~"head" => TranslatedHead, ~"tail" => TranslatedTail}), State2};
value(#c_literal{anno = Anno, val = N}, State) when is_integer(N) ->
    {node(~"integer", Anno, #{~"value" => N}), State};
value(#c_literal{anno = Anno, val = Atom}, State) when is_atom(Atom) ->
    {node(~"atom", Anno, #{~"value" => atom_to_binary(Atom, utf8)}), State};
value(#c_cons{anno = Anno, hd = Head, tl = Tail}, State0) ->
    {TranslatedHead, State1} = value(Head, State0),
    {TranslatedTail, State2} = value(Tail, State1),
    {node(~"cons", Anno, #{~"head" => TranslatedHead, ~"tail" => TranslatedTail}), State2};
value(Core, _State) ->
    unsupported(Core).

%% The table contains code; every function value carries its own capture values.
function_node(#{id := Id, arity := Arity, captures := Captures}, Anno, State0) ->
    {Values, State1} = lists:mapfoldl(fun value/2, State0, Captures),
    {node(~"function", Anno, #{~"id" => Id, ~"arity" => Arity, ~"captures" => Values}), State1}.

%% Preserve Core names. Lean owns identifier escaping and separates integer
%% compiler temporaries from atom-named source variables.
variable(#c_var{anno = Anno, name = Name}) when is_integer(Name), Name >= 0 ->
    var_node(Name, Anno);
variable(#c_var{anno = Anno, name = Name}) when is_atom(Name) ->
    var_node(atom_to_binary(Name, utf8), Anno);
variable(Core) ->
    unsupported(Core).

function_name({Name, Arity}) when is_atom(Name), is_integer(Arity), Arity >= 0 ->
    atom_to_binary(Name, utf8).

var_node(Name, Anno) ->
    node(~"var", Anno, #{~"name" => Name}).

error_node(Reason, Anno) ->
    node(~"raise", Anno, #{~"class" => ~"error",
        ~"reason" => node(~"atom", Anno, #{~"value" => atom_to_binary(Reason, utf8)})}).

local_call_node(Name, Args, Anno) ->
    node(~"local_call", Anno, #{~"name" => Name, ~"args" => Args}).

remote_call_node(Module, Name, Args, Anno) ->
    node(~"remote_call", Anno, #{~"module" => Module, ~"name" => Name, ~"args" => Args}).

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
