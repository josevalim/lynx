-module(guard_patterns).
-compile({no_auto_import, [float/1]}).
-export([integer/1, float/1, atom/1, tuple/1, map/1, bitstring/1, binary/1,
         pid/1, function/1, reference/1,
         conjunction/1, nested/1, conflict/1, repeated/1, negated/1,
         disjunction/2, outer/2]).

integer(X) when is_integer(X) -> X; integer(_) -> no.
float(X) when is_float(X) -> X; float(_) -> no.
atom(X) when is_atom(X) -> X; atom(_) -> no.
tuple(X) when is_tuple(X) -> X; tuple(_) -> no.
map(X) when is_map(X) -> X; map(_) -> no.
bitstring(X) when is_bitstring(X) -> X; bitstring(_) -> no.
binary(X) when is_binary(X) -> X; binary(_) -> no.
pid(X) when is_pid(X) -> X; pid(_) -> no.
reference(X) when is_reference(X) -> X; reference(_) -> no.
function(X) when is_function(X) -> X; function(_) -> no.

conjunction({X, Y}) when is_integer(X), is_map(Y) -> {X, Y};
conjunction(_) -> no.
nested({tag, [#{a := X}]}) when is_binary(X) -> X; nested(_) -> no.
conflict({X}) when is_integer(X), is_float(X) -> X; conflict(_) -> no.
repeated({X, X}) when is_integer(X) -> X; repeated(_) -> no.
negated(X) when not is_integer(X) -> X; negated(_) -> no.
disjunction({X}, Y) when is_integer(X), (is_integer(Y) orelse is_map(Y)) -> X;
disjunction(_, _) -> no.
outer(X, Y) -> case Y of {Z} when is_integer(X) -> Z; _ -> no end.
