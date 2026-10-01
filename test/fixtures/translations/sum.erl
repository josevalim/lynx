-module(sum).
-export([sum/1, sum_empty_ensures/0, sum_singleton_requires/1, sum_singleton_ensures/1]).

-law #{name => {sum_empty, 0}, ensures => sum_empty_ensures}.
-proof ~"""
simp [«sum_empty_ensures/0», «sum/1», Erlang.lists.«sum/1», Erlang.lists.«sum/2», Erlang.erlang.«==/2»]
""".

-law #{name => {sum_singleton, 1}, requires => sum_singleton_requires, ensures => sum_singleton_ensures}.
-proof ~"""
cases _0 <;> simp [«sum_singleton_requires/1», «sum_singleton_ensures/1», Erlang.erlang.«is_integer/1», «sum/1», Erlang.lists.«sum/1», Erlang.lists.«sum/2», Erlang.erlang.«==/2»] at requires ⊢
""".

-law #{name => {sum_empty_again, 0}, ensures => sum_empty_ensures}.
-proof ~"""
exact «sum_empty/0»
""".

sum(List) -> lists:sum(List).
sum_empty_ensures() -> sum([]) == 0.
sum_singleton_requires(X) -> is_integer(X).
sum_singleton_ensures(X) -> sum([X]) == X.
