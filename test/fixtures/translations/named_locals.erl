-module(named_locals).
-export([comprehension_filtered/1, comprehension_nested/2, named/2, self_reference/0]).

comprehension_filtered(List) -> [{K, V} || {K, V} <- List, is_atom(K)].
comprehension_nested(Tag, Lists) -> [[{Tag, X} || X <- List] || List <- Lists].

%% Named recursion follows the same translation path as generator loops.
named(Tag, List) ->
    F = fun Loop([]) -> [];
            Loop([X | Xs]) -> [{Tag, X} | Loop(Xs)]
        end,
    F(List).

self_reference() ->
    F = fun Self() -> Self end,
    F =:= F().
