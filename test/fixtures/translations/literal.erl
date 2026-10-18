-module(literal).
-export([integers/0, floats/0, bitstrings/0, atoms/0, empty_list/0, tuples/0, computed_tuples/1, maps/0, computed_maps/2, table/0, table_lookup/1]).

-define(TABLE, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
                16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}).

integers() -> [-1, 0, 1, 9223372036854775808].
atoms() -> [foo, 'bar baz'].
empty_list() -> [].
tuples() -> [{}, {ok}, {ok, 1}, {nested, {1, [foo]}}].
computed_tuples(X) -> {ok, X, {X, [X]}}.
maps() -> [#{}, #{a => 1, 1 => #{b => 2}}].
computed_maps(Key, Value) -> #{a => 1, Key => #{Key => 1, Key => Value}}.

floats() -> [-1.5, 0.0, -0.0, 1.0, 0.1, 1.0e-300, 5.0e-324, 1.7976931348623157e308,
             {nested, [1.5]}, #{1.0 => 0.1, 1 => integer}].

bitstrings() -> [<<0, 255>>, <<5:3>>, <<1:1, 0:7, 511:9>>].

%% Large literal tuples are shared by the functions using them.
table() -> ?TABLE.
table_lookup(I) -> {element(I, ?TABLE), element(I + 1, ?TABLE)}.
