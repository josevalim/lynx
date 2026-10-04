-module(literal).
-export([integers/0, atoms/0, empty_list/0, tuples/0, computed_tuples/1]).

integers() -> [-1, 0, 1, 9223372036854775808].
atoms() -> [foo, 'bar baz'].
empty_list() -> [].
tuples() -> [{}, {ok}, {ok, 1}, {nested, {1, [foo]}}].
computed_tuples(X) -> {ok, X, {X, [X]}}.
