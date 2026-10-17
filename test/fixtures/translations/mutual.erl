-module(mutual).
-export([odd/1, even/1, first/1, second/1, triples/3, identity/1]).

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

%% Each function resumes the enclosing traversal once its own list is
%% exhausted, so every function weighs its parameters differently.
triples(Xs, Ys, Zs) -> outer(Xs, Ys, Zs).

outer([X | Xs], Ys, Zs) -> middle(Ys, Xs, Ys, Zs, X);
outer([], _, _) -> [].

middle([Y | Rest], Xs, Ys, Zs, X) -> inner(Zs, Rest, Xs, Ys, Zs, {X, Y});
middle([], Xs, Ys, Zs, _) -> outer(Xs, Ys, Zs).

inner([Z | Rest], Pending, Xs, Ys, Zs, Pair) ->
    [{Pair, Z} | inner(Rest, Pending, Xs, Ys, Zs, Pair)];
inner([], Pending, Xs, Ys, Zs, {X, _}) -> middle(Pending, Xs, Ys, Zs, X).

identity(X) -> X.
