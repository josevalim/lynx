-module(literals).
-export([sign/1, zero/0, call_zero/1, one_two/1]).

sign(-1) -> minus_one;
sign(X) -> X + -5.

zero() -> 0.

call_zero(_) -> zero().

one_two([1, -2]) -> yes;
one_two(_) -> [no, -1].
