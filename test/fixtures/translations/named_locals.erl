-module(named_locals).
-export([comprehension_filtered/1, comprehension_nested/2, comprehension_lists/2,
         comprehension_lists3/3, comprehension_mixed3/3, comprehension_zip/2,
         map_generator/1, map_generator_strict/1, map_comprehension/1, map_to_map/1,
         comprehension_list_map/2, comprehension_map_list/2, comprehension_filtered_maps/2,
         named/2, self_reference/0]).

comprehension_filtered(List) -> [{K, V} || {K, V} <- List, is_atom(K)].
comprehension_nested(Tag, Lists) -> [[{Tag, X} || X <- List] || List <- Lists].
%% Each generator nests a loop that returns to the enclosing one when exhausted.
comprehension_lists(A, B) -> [{X, Y} || X <- A, Y <- B].
%% Deeper nesting needs a measure where each loop weighs its parameters differently.
comprehension_lists3(A, B, C) -> [{X, Y, Z} || X <- A, Y <- B, Z <- C].
comprehension_mixed3(A, Map, B) -> [{X, K, Y} || X <- A, K := V <- Map, V > X, Y <- B].
comprehension_zip(A, B) -> [{X, Y} || X <- A && Y <- B].

map_generator(Map) -> [{K, V} || K := V <- Map].
map_generator_strict(Map) -> [K || K := ok <:- Map].
map_comprehension(List) -> #{K => V || {K, V} <- List}.
map_to_map(Map) -> #{V => K || K := V <- Map}.
comprehension_list_map(List, Map) -> [{X, K} || X <- List, K := _ <- Map].
comprehension_map_list(Map, List) -> #{{K, X} => V || K := V <- Map, X <- List}.
comprehension_filtered_maps(List, Map) -> [V || X <- List, is_integer(X), K := V <- Map, K =:= X].

%% Named recursion follows the same translation path as generator loops.
named(Tag, List) ->
    F = fun Loop([]) -> [];
            Loop([X | Xs]) -> [{Tag, X} | Loop(Xs)]
        end,
    F(List).

self_reference() ->
    F = fun Self() -> Self end,
    F =:= F().
