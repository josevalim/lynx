-module(literal).
-export([integers/0, atoms/0, empty_list/0]).

integers() -> [-1, 0, 1, 9223372036854775808].
atoms() -> [foo, 'bar baz'].
empty_list() -> [].
