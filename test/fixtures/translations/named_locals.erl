-module(named_locals).
-export([comprehension_filtered/1, comprehension_nested/2, comprehension_lists/2,
         comprehension_lists3/3, comprehension_mixed3/3, comprehension_zip/2,
         map_generator/1, map_generator_strict/1, map_comprehension/1, map_to_map/1,
         comprehension_list_map/2, comprehension_map_list/2, comprehension_filtered_maps/2,
         binary_generator/1, bits_generator/1, binary_generator_strict/1, utf8_generator/1,
         sized_generator/2, zero_generator/1, binary_comprehension/1, binary_to_binary/1,
         binary_nested/2, binary_zip/2, binary_list/2, named/2, self_reference/0]).

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

%% Bitstring generators recurse on the bits left after each match.
binary_generator(Bin) -> [X || <<X>> <= Bin].
bits_generator(Bits) -> [{X, Y} || <<X:3, Y:2>> <= Bits, X > Y].
binary_generator_strict(Bin) -> [X || <<X:16>> <:= Bin].
utf8_generator(Bin) -> [C || <<C/utf8>> <= Bin].
%% Widths that may be zero raise badarg, rather than repeating forever.
sized_generator(Size, Bin) -> [X || <<X:Size/binary>> <= Bin].
zero_generator(Bin) -> [X || <<X:0>> <= Bin].
binary_comprehension(List) -> << <<X:4>> || X <- List >>.
binary_to_binary(Bin) -> << <<Y:8, X:8>> || <<X:8, Y:8>> <= Bin >>.
binary_nested(A, B) -> [{X, Y} || <<X>> <= A, <<Y:4>> <= B].
binary_zip(A, B) -> [{X, Y} || <<X>> <= A && <<Y:4>> <= B].
binary_list(Bin, List) -> [{X, Y} || <<X>> <= Bin, Y <- List].

%% Named recursion follows the same translation path as generator loops.
named(Tag, List) ->
    F = fun Loop([]) -> [];
            Loop([X | Xs]) -> [{Tag, X} | Loop(Xs)]
        end,
    F(List).

self_reference() ->
    F = fun Self() -> Self end,
    F =:= F().
