-module(mutual).
-export([odd/1, even/1, first/1, second/1, third/1, identity/1]).

odd([]) -> false;
odd([_ | Xs]) -> even(Xs).

even([]) -> true;
even([_ | Xs]) -> odd(Xs).

first([]) -> 0;
first([_ | Xs]) -> second(Xs).

second([]) -> 1;
second([_ | Xs]) -> third(Xs).

third([]) -> 2;
third([_ | Xs]) -> first(Xs).

identity(X) -> X.
