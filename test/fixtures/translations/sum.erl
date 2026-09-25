-module(sum).
-export([sum/1]).
sum([]) -> 0;
sum([X | Xs]) -> X + sum(Xs).
