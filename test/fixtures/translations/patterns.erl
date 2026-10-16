-module(patterns).
-export([grouped/1, map_grouped/1, map_nested/1, map_duplicate/3,
         map_computed/2, map_fallthrough/2, floats/1]).

grouped(a) -> first;
grouped(b) -> second;
grouped([c | X]) when is_integer(X) -> guarded;
grouped([c | _]) -> rejected;
grouped(_) -> other.

map_grouped(#{a := 0, b := B}) when is_integer(B) -> first;
map_grouped(#{a := 1, b := B}) when is_integer(B) -> second;
map_grouped(#{a := A}) -> {second, A};
map_grouped(#{a := 2, b := B}) when is_integer(B) -> fourth;
map_grouped(#{}) -> map;
map_grouped(_) -> other.

map_nested({tag, [#{a := #{b := Value} = Inner} = Outer]}) when is_integer(Value) ->
    {Value, Inner, Outer};
map_nested(_) -> other.

map_duplicate(K1, K2, Map) ->
    case Map of #{K1 := X, K2 := {ok, Y}} -> {X, Y}; _ -> missing end.

map_computed(Key, Map) ->
    case Map of #{(Key + 1) := Value} -> Value; _ -> missing end.

floats(1) -> integer;
floats(1.0) -> float;
floats(0.0) -> positive_zero;
floats(-0.0) -> negative_zero;
floats(-1.5) -> negative;
floats({0.1, [5.0e-324]}) -> nested;
floats(#{1.0 := 1.5}) -> map;
floats(_) -> other.

%% A guard falling through to grouped map clauses needs a typed continuation.
map_fallthrough(_, #{b := B}) when B /= 1 -> b;
map_fallthrough(Value, #{a := A}) when A < 0 -> Value;
map_fallthrough(_, #{a := A}) -> A.
