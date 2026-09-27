-module(lynx_core_to_leanj).

-export([translate/1]).

-include_lib("compiler/src/core_parse.hrl").

%% Translate the Core tree returned by the debug_info backend's core_v1
%% format into a list of JSON-encodable Lynx commands for one module.
%% Unsupported constructs return their pretty-printed Core as a UTF-8 binary.
-spec translate(cerl:c_module()) -> {ok, [map()]} | {unsupported_core, binary()}.
translate(#c_module{defs = Defs}) ->
    try lists:flatmap(fun translate_def/1, Defs) of
        Commands -> {ok, Commands}
    catch
        throw:{unsupported_core, Core} ->
            {unsupported_core, unicode:characters_to_binary(core_pp:format(Core))}
    end.

translate_def({#c_var{name = {module_info, Arity}}, _})
        when Arity =:= 0; Arity =:= 1 ->
    [];
translate_def({#c_var{name = Name}, #c_fun{anno = Anno, vars = Vars, body = Body}}) ->
    Def = node(~"def", Anno, #{
        ~"name" => function_name(Name),
        ~"params" => [variable(Var) || Var <- Vars],
        ~"body" => expression(Body)
    }),
    % TODO: Track purity
    [node(~"command", Anno, #{~"name" => ~"lynx_pure", ~"expr" => Def})].

%% Erlang: case X of [] -> 0; Other -> 1 end
%% Lean:
%%   match v_X with
%%   | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
%%   | v_Other => Lynx.Result.ok (Lynx.Term.integer 1)
expression(#c_case{anno = Anno, arg = Arg, clauses = Clauses}) ->
    node(~"match", Anno, #{
        ~"expression" => value(Arg),
        ~"cases" => [clause(Clause) || Clause <- Clauses]
    });
%% Erlang: Y = f(X), g(Y)
%% Lean: Lynx.Result.bind (f_1 v_X) fun v_Y => g_1 v_Y
expression(#c_let{anno = Anno, vars = [Var], arg = Arg, body = Body}) ->
    Continuation = node(~"fun", Anno, #{
        ~"params" => [variable(Var)], ~"body" => expression(Body)
    }),
    apply_node(~"Lynx.Result.bind", [expression(Arg), Continuation], Anno);
%% Erlang: f(X, Y)
%% Lean: f_2 v_X v_Y
expression(#c_apply{anno = Anno, op = #c_var{name = Name}, args = Args}) ->
    apply_node(function_name(Name), [value(Arg) || Arg <- Args], Anno);
%% Erlang: X + Y
%% Lean: Lynx.Modules.Erlang.add_2 v_X v_Y
expression(#c_call{anno = Anno, module = #c_literal{val = erlang},
                   name = #c_literal{val = '+'}, args = [Left, Right]}) ->
    apply_node(~"Lynx.Modules.Erlang.add_2", [value(Left), value(Right)], Anno);
%% Erlang: f([]) -> ok.
%% Core inserts match_fail for arguments that match no function clause.
%% Lean (the generated fallback body):
%%   Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
expression(#c_primop{anno = Anno, name = #c_literal{val = match_fail},
                     args = [#c_tuple{es = [#c_literal{val = function_clause}, #c_var{}]}]}) ->
    Reason = value(#c_literal{anno = Anno, val = function_clause}),
    Exception = apply_node(~"Lynx.Exception.error", [Reason], Anno),
    apply_node(~"Lynx.Result.error", [Exception], Anno);
%% Erlang: 0
%% Lean: Lynx.Result.ok (Lynx.Term.integer 0)
expression(#c_literal{anno = Anno} = Literal) ->
    apply_node(~"Lynx.Result.ok", [value(Literal)], Anno);
%% Erlang: X
%% Lean: Lynx.Result.ok v_X
expression(#c_var{anno = Anno} = Var) ->
    apply_node(~"Lynx.Result.ok", [variable(Var)], Anno);
%% Erlang: receive X -> X end
%% Lean: no translation; translate/1 returns {unsupported_core, CoreString}.
expression(Core) ->
    unsupported(Core).

clause(#c_clause{anno = Anno, pats = [Pattern], guard = #c_literal{val = true}, body = Body}) ->
    Pat = case {lists:member(compiler_generated, Anno), Pattern, Body} of
        {true, #c_var{}, #c_primop{name = #c_literal{val = match_fail}}} ->
            node(~"wildcard", [], #{});
        _ -> value(Pattern)
    end,
    #{~"span" => span(Anno), ~"pattern" => Pat, ~"body" => expression(Body)};
clause(Core) ->
    unsupported(Core).

%% Core separates values from computations; only computations produce Result.
value(#c_var{} = Var) ->
    variable(Var);
value(#c_literal{anno = Anno, val = []}) ->
    ident_node(~"Lynx.Term.nil", Anno);
value(#c_literal{anno = Anno, val = N}) when is_integer(N) ->
    apply_node(~"Lynx.Term.integer", [node(~"integer", Anno, #{~"value" => N})], Anno);
value(#c_literal{anno = Anno, val = Atom}) when is_atom(Atom) ->
    String = node(~"string", Anno, #{~"value" => atom_to_binary(Atom, utf8)}),
    apply_node(~"Lynx.Term.atom", [String], Anno);
value(#c_cons{anno = Anno, hd = Head, tl = Tail}) ->
    apply_node(~"Lynx.Term.cons", [value(Head), value(Tail)], Anno);
value(Core) ->
    unsupported(Core).

%% Keep compiler temporaries and source variables in distinct name spaces.
%% Prefixing also avoids Lean keywords without losing the original spelling.
variable(#c_var{anno = Anno, name = Name}) when is_integer(Name), Name >= 0 ->
    ident_node(<<"v", (integer_to_binary(Name))/binary>>, Anno);
variable(#c_var{anno = Anno, name = Name}) when is_atom(Name) ->
    ident_node(<<"v_", (atom_to_binary(Name, utf8))/binary>>, Anno);
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
