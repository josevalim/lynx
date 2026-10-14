-module(literal).
-export([integers/0, floats/0, atoms/0, empty_list/0, tuples/0, computed_tuples/1, maps/0, computed_maps/2]).

integers() -> [-1, 0, 1, 9223372036854775808].
atoms() -> [foo, 'bar baz'].
empty_list() -> [].
tuples() -> [{}, {ok}, {ok, 1}, {nested, {1, [foo]}}].
computed_tuples(X) -> {ok, X, {X, [X]}}.
maps() -> [#{}, #{a => 1, 1 => #{b => 2}}].
computed_maps(Key, Value) -> #{a => 1, Key => #{Key => 1, Key => Value}}.

floats() -> [-1.5, 0.0, -0.0, 1.0, 0.1, 1.0e-300, 5.0e-324, 1.7976931348623157e308,
             {nested, [1.5]}, #{1.0 => 0.1, 1 => integer}].
