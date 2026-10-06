-module(patterns).
-export([grouped/1]).

grouped(a) -> first;
grouped(b) -> second;
grouped([c | X]) when is_integer(X) -> guarded;
grouped([c | _]) -> rejected;
grouped(_) -> other.
