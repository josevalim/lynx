-module(lynx_core_to_leanj).

-export([module_name/1, to_definitions/1, translate/6, fun_table/2]).

-include_lib("compiler/src/core_parse.hrl").

%% Anonymous functions use integer keys; named functions use {Module, {Name, Arity}}.
%% Every entry carries a global integer ID for ordering and dispatch.
-record(state, {module, name, defs, translated, funs = #{},
                local_calls = #{}, pure = true, remote, next_var = 0}).

-spec module_name(module()) -> binary().
module_name(Module) ->
    case atom_to_binary(Module, utf8) of
        <<"Elixir.", _/binary>> = Name -> Name;
        Name -> <<"Erlang.", Name/binary>>
    end.

-spec to_definitions(cerl:c_module()) ->
    #{{atom(), arity()} => {function, cerl:c_fun()} | {law, map()}} |
    {error, list(), binary()}.
to_definitions(#c_module{defs = Defs, attrs = Attrs}) ->
    try
        definitions(Defs ++ Attrs, #{})
    catch
        throw:{error, Core, Reason} -> {error, cerl:get_ann(Core), Reason}
    end.

definitions([{#c_var{name = Name}, #c_fun{} = Fun} | Rest], Definitions) ->
    definitions(Rest, Definitions#{Name => {function, Fun}});
definitions([{#c_literal{val = law}, #c_literal{val = [#{proof := _}]} = LawNode} | Rest], Definitions) ->
    {Name, Law} = law(LawNode, embedded_proof(LawNode)),
    definitions(Rest, Definitions#{Name => {law, Law}});
definitions([{#c_literal{val = law}, LawNode},
             {#c_literal{val = proof}, ProofNode} | Rest], Definitions) ->
    {Name, Law} = law(LawNode, attribute_proof(ProofNode)),
    definitions(Rest, Definitions#{Name => {law, Law}});
definitions([{#c_literal{val = law}, Core} | _], _) ->
    core_error(Core, ~"proof must immediately follow law");
definitions([{#c_literal{val = proof}, Core} | _], _) ->
    core_error(Core, ~"proof without preceding law");
definitions([_ | Rest], Definitions) -> definitions(Rest, Definitions);
definitions([], Definitions) -> Definitions.

law(#c_literal{val = [#{name := {Name, Params}, ensures := Ensures} = Law]} = Core, Proof)
        when is_atom(Name), is_list(Params), is_atom(Ensures) ->
    case lists:all(fun erlang:is_atom/1, Params) of
        true -> ok;
        false -> core_error(Core, ~"law parameters must be atoms")
    end,
    case length(lists:usort(Params)) =:= length(Params) of
        true -> ok;
        false -> core_error(Core, ~"law parameters must be unique")
    end,
    Arity = length(Params),
    case maps:find(requires, Law) of
        error -> ok;
        {ok, Requires} when is_atom(Requires) -> ok;
        _ -> core_error(Core, ~"law requires must be a function name")
    end,
    Anno = case maps:find(span, Law) of
        error -> cerl:get_ann(Core);
        {ok, Span} ->
            case span([Span]) of
                [] -> core_error(Core, ~"law span must be a line or {line, column}");
                _ -> [Span | cerl:get_ann(Core)]
            end
    end,
    {{Name, Arity}, Law#{anno => Anno, proof => Proof}};
law(Core, _) -> core_error(Core, ~"law must contain name {atom, parameters} and ensures function name").

embedded_proof(#c_literal{val = [#{proof := #{source := Proof, indentation := Indentation, span := Span}}]} = Core)
        when is_binary(Proof), is_integer(Indentation), Indentation >= 0 ->
    case span([Span]) of
        [] -> core_error(Core, ~"embedded proof span must be a line or {line, column}");
        ProofSpan -> #{~"source" => Proof, ~"indentation" => Indentation, ~"span" => ProofSpan}
    end;
embedded_proof(Core) ->
    core_error(Core, ~"embedded proof requires a binary, nonnegative indentation and span").

attribute_proof(#c_literal{val = [Proof]} = Core) when is_binary(Proof) ->
    %% Erlang multiline strings begin on the line after the proof attribute.
    ProofSpan = case span(cerl:get_ann(Core)) of
        [Line | _] -> [Line + 1];
        [] -> []
    end,
    #{~"source" => Proof, ~"indentation" => 0, ~"span" => ProofSpan};
attribute_proof(Core) -> core_error(Core, ~"proof must be a binary").

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
-spec translate(module(), #{{atom(), arity()} => {function, cerl:c_fun()} | {law, map()}}, [{atom(), arity()}], map(), map(),
                {term(), fun((term(), module(), atom(), arity(), list(), map()) ->
                    {boolean(), map(), term()} | local)}) ->
    {ok, map(), map(), term()} | {error, list(), binary()}.
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
        throw:{error, Core, Reason} -> {error, cerl:get_ann(Core), Reason}
    end.

translate_def(Name, #state{translated = Translated} = State) ->
    case maps:is_key(Name, Translated) of
        true -> State;
        false -> translate_def(Name, maps:get(Name, State#state.defs), State)
    end.

translate_def(Name, {function, #c_fun{anno = Anno, vars = Vars, body = Body}}, State) ->
    try translate_definition(Name, Anno, Vars, {function, Body}, State)
    catch
        throw:{error, Core, Reason} ->
            %% Compiler-generated primops may have no source position.
            %% Fall back to the innermost function containing the expression.
            case span(cerl:get_ann(Core)) of
                [] -> core_error(cerl:set_ann(Core, cerl:get_ann(Core) ++ Anno), Reason);
                _ -> core_error(Core, Reason)
            end
    end;
translate_def(Name, {law, #{name := {_, Params}, anno := Anno, ensures := Ensures, proof := Proof} = Law}, State) ->
    translate_definition(Name, Anno, Params, {law, maps:find(requires, Law), Ensures, Proof}, State).

translate_definition(Name, Anno, Vars, Definition, State0) ->
    State1 = State0#state{name = Name, local_calls = #{}, pure = true, next_var = 0,
                          translated = (State0#state.translated)#{Name => pending}},
    {Def, State2} = case Definition of
        {function, Body} ->
            {TranslatedBody, Next} = expression(Body, State1),
            {node(~"def", Anno, #{
                ~"name" => function_name(Name),
                ~"params" => [variable(Var) || Var <- Vars],
                ~"body" => TranslatedBody
            }), Next};
        {law, Requires, Ensures, Proof} ->
            {_, Arity} = Name,
            {Requirement, Next1} = case Requires of
                error -> {#{}, State1};
                {ok, Helper} ->
                    Next = translate_law_helper(Helper, Arity, State1),
                    {#{~"requires" => atom_to_binary(Helper, utf8)}, Next}
            end,
            Next2 = translate_law_helper(Ensures, Arity, Next1),
            {node(~"theorem", Anno, Requirement#{
                ~"name" => function_name(Name), ~"params" => [atom_to_binary(Param, utf8) || Param <- Vars],
                ~"ensures" => atom_to_binary(Ensures, utf8), ~"proof" => Proof
            }), Next2}
    end,
    Entry = #{translation => Def, local_calls => maps:keys(State2#state.local_calls),
              pure => State2#state.pure},
    State0#state{translated = (State2#state.translated)#{Name => Entry},
                 funs = State2#state.funs, remote = State2#state.remote}.

translate_law_helper(Name, Arity, State) ->
    Callee = {Name, Arity},
    Next = translate_def(Callee, State),
    Next#state{local_calls = (Next#state.local_calls)#{Callee => true}}.

%% OTP lowers receive to a local scan/wait loop. Recover the operation before
%% translating ordinary expressions; loop identity is checked structurally,
%% never inferred from the compiler's generated function spelling.
expression(#c_letrec{anno = Anno, defs = [{#c_var{name = Loop},
             #c_fun{vars = [], body = LoopBody}}],
             body = #c_apply{op = #c_var{name = Loop}, args = []}} = Core, State0) ->
    {Message, Clauses, Timeout, Action} = receive_parts(LoopBody, Loop, Core),
    {TranslatedMessage, State1} = case Message of
        none ->
            {var_node(#{~"generated" => State0#state.next_var}, Anno),
             State0#state{next_var = State0#state.next_var + 1}};
        _ -> {variable(Message), State0}
    end,
    {TranslatedTimeout, State2} = value(Timeout, State1),
    {TranslatedClauses, State3} = lists:mapfoldl(fun receive_clause/2, State2, Clauses),
    {TranslatedAction, State4} = case Timeout of
        #c_literal{val = infinity} ->
            {node(~"return", Anno, #{~"values" => [node(~"atom", Anno, #{~"value" => ~"true"})]}), State3};
        _ -> expression(Action, State3)
    end,
    {node(~"receive", Anno, #{~"message" => TranslatedMessage,
        ~"cases" => TranslatedClauses, ~"timeout" => TranslatedTimeout,
        ~"after" => TranslatedAction}), State4#state{pure = false}};
%% Core try catches only the protected expression, not its success continuation.
expression(#c_try{anno = Anno, arg = Arg, vars = Vars, body = Body,
                  evars = EVars, handler = Handler}, State0) ->
    {TranslatedArg, State1} = expression(Arg, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    {TranslatedHandler, State3} = expression(Handler, State2),
    {node(~"try", Anno, #{~"computation" => TranslatedArg,
        ~"vars" => [variable(V) || V <- Vars], ~"body" => TranslatedBody,
        ~"exception_vars" => [variable(V) || V <- EVars],
        ~"handler" => TranslatedHandler}), State3};
%% Multiple Core return values are internal Lean products, not Erlang tuples.
expression(#c_values{anno = Anno, es = Values}, State0) ->
    {Translated, State1} = lists:mapfoldl(fun value/2, State0, Values),
    {node(~"return", Anno, #{~"values" => Translated}), State1};
%% Erlang: case X of [] -> 0; Other -> 1 end
%% Lean:
%%   match vX with
%%   | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
%%   | vOther => Lynx.Result.ok (Lynx.Term.integer 1)
expression(#c_case{anno = Anno, arg = Arg, clauses = Clauses}, State0) ->
    {Translated, Next} = expression(Arg, State0),
    {Args, Bind, State1} = case Translated of
        #{~"kind" := ~"return", ~"values" := Values} ->
            {Values, none, Next};
        _ ->
            [#c_clause{pats = Patterns} | _] = Clauses,
            {Vars, BoundState} = lists:mapfoldl(fun(_, Acc) ->
                Var = var_node(#{~"generated" => Acc#state.next_var}, Anno),
                {Var, Acc#state{next_var = Acc#state.next_var + 1}}
            end, Next, lists:seq(1, length(Patterns))),
            {Vars, {Vars, Translated}, BoundState}
    end,
    {TranslatedClauses, State2} = lists:mapfoldl(fun clause/2, State1, Clauses),
    Match = node(~"match", Anno, #{~"expressions" => Args, ~"cases" => TranslatedClauses}),
    case Bind of
        none -> {Match, State2};
        {Binders, Computation} ->
            {node(~"bind", Anno, #{~"vars" => Binders,
                ~"computation" => Computation, ~"body" => Match}), State2}
    end;
%% Erlang: Y = f(X), g(Y)
%% Lean: Lynx.Result.bind («f/1» vX) fun vY => «g/1» vY
expression(#c_let{anno = Anno, vars = Vars, arg = Arg, body = Body}, State0) ->
    {TranslatedArg, State1} = expression(Arg, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    {node(~"bind", Anno, #{~"vars" => [variable(V) || V <- Vars],
        ~"computation" => TranslatedArg, ~"body" => TranslatedBody}), State2};
%% Erlang: f(X), g(X)
%% Lean: do let _ ← «f/1» vX; «g/1» vX
expression(#c_seq{anno = Anno, arg = Arg, body = Body}, State0) ->
    {TranslatedArg, State1} = expression(Arg, State0),
    {TranslatedBody, State2} = expression(Body, State1),
    {node(~"bind", Anno, #{~"vars" => [node(~"wildcard", Anno, #{})],
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
%% Erlang: error(Reason)
%% Lean: Lynx.Result.error (Lynx.Exception.error reason)
expression(#c_call{anno = Anno, module = #c_literal{val = erlang},
                   name = #c_literal{val = Class}, args = [Reason]}, State0)
        when Class =:= error; Class =:= throw; Class =:= exit ->
    {TranslatedReason, State1} = value(Reason, State0),
    {node(~"raise", Anno, #{~"class" => atom_to_binary(Class, utf8), ~"reason" => TranslatedReason}), State1};
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
expression(#c_primop{anno = Anno, name = #c_literal{val = Op}, args = Args}, State) ->
    prim_op(Op, Anno, Args, State);
%% Everything else (literals, cons, etc)
%% Lean: Lynx.Result.ok (Lynx.Term.integer 0)
expression(Value, State0) ->
    {Translated, State1} = value(Value, State0),
    {node(~"return", cerl:get_ann(Value), #{~"values" => [Translated]}), State1}.

%% Erlang: f([]) -> ok.
%% Core inserts match_fail for arguments that match no function clause.
%% Lean (the generated fallback body):
%%   Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
prim_op(match_fail, Anno, [#c_literal{val = {function_clause}}], State) ->
    {error_node(function_clause, Anno), State};
prim_op(match_fail, Anno, [#c_tuple{es = [#c_literal{val = function_clause} | _]}], State) ->
    {error_node(function_clause, Anno), State};
%% The runtime retains class and reason, but does not record stack frames.
prim_op(build_stacktrace, Anno, [Trace], State0) ->
    {Translated, State1} = value(Trace, State0),
    {node(~"stacktrace", Anno, #{~"exception" => Translated}), State1};
prim_op(raise, Anno, [Trace, Reason], State0) ->
    {TranslatedTrace, State1} = value(Trace, State0),
    {TranslatedReason, State2} = value(Reason, State1),
    {node(~"reraise", Anno, #{~"exception" => TranslatedTrace,
        ~"reason" => TranslatedReason}), State2};
prim_op(raw_raise, Anno, [Class, Reason, Trace], State0) ->
    {TranslatedClass, State1} = value(Class, State0),
    {TranslatedReason, State2} = value(Reason, State1),
    {TranslatedTrace, State3} = value(Trace, State2),
    {node(~"raise_dynamic", Anno, #{~"class" => TranslatedClass,
        ~"reason" => TranslatedReason, ~"exception" => TranslatedTrace}), State3};
prim_op(match_fail, Anno, [Reason], State0) ->
    {Translated, State1} = value(Reason, State0),
    {node(~"raise", Anno, #{~"class" => ~"error", ~"reason" => Translated}), State1};
prim_op(Op, Anno, Args, _State) ->
    unsupported(#c_primop{anno = Anno, name = #c_literal{val = Op}, args = Args}).

clause(#c_clause{anno = Anno, pats = Patterns, guard = #c_literal{val = true}, body = Body}, State0) ->
    {Pats, State1} = lists:mapfoldl(fun value/2, State0, Patterns),
    {TranslatedBody, State2} = expression(Body, State1),
    {#{~"span" => span(Anno), ~"patterns" => Pats, ~"body" => TranslatedBody}, State2};
clause(#c_clause{anno = Anno, pats = Patterns, guard = Guard, body = Body}, State0) ->
    {Pats, State1} = lists:mapfoldl(fun value/2, State0, Patterns),
    {TranslatedGuard, State2} = expression(Guard, State1),
    {TranslatedBody, State3} = expression(Body, State2),
    {#{~"span" => span(Anno), ~"patterns" => Pats, ~"guard" => TranslatedGuard,
       ~"body" => TranslatedBody}, State3};
clause(Core, _State) ->
    unsupported(Core).

receive_parts(#c_let{vars = [#c_var{name = Available}, Message],
        arg = #c_primop{name = #c_literal{val = recv_peek_message}, args = []},
        body = #c_case{arg = #c_var{name = Available}, clauses = Branches}}, Loop, Core) ->
    {Scan, Wait} = receive_booleans(Branches, Core),
    {Timeout, Action} = receive_wait(Wait, Loop, Core),
    {Message, receive_clauses(Scan, Message, Loop, Core), Timeout, Action};
receive_parts(Wait, Loop, Core) ->
    {Timeout, Action} = receive_wait(Wait, Loop, Core),
    {none, [], Timeout, Action}.

receive_booleans([
        #c_clause{pats = [#c_literal{val = true}], guard = #c_literal{val = true}, body = Yes},
        #c_clause{pats = [#c_literal{val = false}], guard = #c_literal{val = true}, body = No}], _) ->
    {Yes, No};
receive_booleans(_, Core) -> unsupported(Core).

receive_wait(#c_let{vars = [#c_var{name = Expired}],
        arg = #c_primop{name = #c_literal{val = recv_wait_timeout}, args = [Timeout]},
        body = #c_case{arg = #c_var{name = Expired}, clauses = Branches}}, Loop, Core) ->
    case receive_booleans(Branches, Core) of
        {Action, #c_apply{op = #c_var{name = Loop}, args = []}} -> {Timeout, Action};
        _ -> unsupported(Core)
    end;
receive_wait(_, _, Core) -> unsupported(Core).

receive_clauses(#c_case{arg = #c_var{name = Message}, clauses = Clauses},
                #c_var{name = Message}, Loop, Core) ->
    receive_scan_clauses(Clauses, Loop, Core);
receive_clauses(#c_seq{arg = #c_primop{name = #c_literal{val = remove_message}, args = []},
                       body = Body}, Message, _, _) ->
    [#c_clause{pats = [Message], guard = #c_literal{val = true}, body = Body}];
receive_clauses(_, _, _, Core) -> unsupported(Core).

receive_scan_clauses([#c_clause{pats = [#c_var{}], guard = #c_literal{val = true},
        body = #c_seq{arg = #c_primop{name = #c_literal{val = recv_next}, args = []},
        body = #c_apply{op = #c_var{name = Loop}, args = []}}}], Loop, _) -> [];
receive_scan_clauses([#c_clause{body = #c_seq{
        arg = #c_primop{name = #c_literal{val = remove_message}, args = []}, body = Body}} = Clause | Rest],
        Loop, Core) ->
    [Clause#c_clause{body = Body} | receive_scan_clauses(Rest, Loop, Core)];
receive_scan_clauses([], _, _) -> [];
receive_scan_clauses(_, _, Core) -> unsupported(Core).

receive_clause(#c_clause{anno = Anno, pats = [Pattern], guard = Guard, body = Body}, State0) ->
    {Pat, State1} = value(Pattern, State0),
    {TranslatedGuard, State2} = expression(Guard, State1),
    {TranslatedBody, State3} = expression(Body, State2),
    Bound = ordsets:intersection(cerl_trees:variables(Pattern), cerl_trees:free_variables(Body)),
    Vars = [variable(#c_var{name = Name}) || Name <- Bound],
    {#{~"span" => span(Anno), ~"pattern" => Pat, ~"vars" => Vars,
       ~"guard" => TranslatedGuard, ~"body" => TranslatedBody}, State3}.

%% Core separates values from computations; only computations produce Result.
value(#c_fun{vars = Vars} = Fun, State0) ->
    Captures = [#c_var{name = V} || V <- cerl_trees:free_variables(Fun),
                                   not is_tuple(V)],
    Id = map_size(State0#state.funs),
    Name = {list_to_atom("$lynx_fun_" ++ integer_to_list(Id)), length(Captures) + length(Vars)},
    Entry = #{id => Id, module => State0#state.module,
              name => Name, arity => length(Vars), captures => Captures},
    State1 = State0#state{funs = (State0#state.funs)#{Id => Entry}},
    State2 = translate_def(Name, {function, Fun#c_fun{vars = Captures ++ Vars}}, State1),
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
value(#c_alias{anno = Anno, var = Var, pat = Pattern}, State0) ->
    {Translated, State1} = value(Pattern, State0),
    {node(~"alias", Anno, #{~"var" => variable(Var), ~"pattern" => Translated}), State1};
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
value(#c_literal{anno = Anno, val = Tuple}, State) when is_tuple(Tuple) ->
    value(#c_tuple{anno = Anno, es = [#c_literal{anno = Anno, val = V} || V <- tuple_to_list(Tuple)]}, State);
value(#c_tuple{anno = Anno, es = Elements}, State0) ->
    {Translated, State1} = lists:mapfoldl(fun value/2, State0, Elements),
    {node(~"tuple", Anno, #{~"elements" => Translated}), State1};
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
    core_error(Core, <<"unsupported Core expression:\n\n",
                       (unicode:characters_to_binary(core_pp:format(Core)))/binary>>).

core_error(Core, Reason) ->
    throw({error, Core, Reason}).
