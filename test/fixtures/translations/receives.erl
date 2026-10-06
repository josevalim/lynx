-module(receives).
-export([plain/0, selective/1, guarded/1, self_guard/0, poll/0,
         timed/1, sleep/1, computed/1, nested/0, bindings/0,
         repeated/0, alias/0, lists/0, alternatives/0, sequence/0]).

plain() -> receive X -> X end.
selective(Tag) -> receive {Tag, X} -> X; stop -> done end.
guarded(Tag) ->
    receive
        {Tag, X} when byte_size(X) == 1 -> {first, X};
        {Tag, X} when is_integer(X), X > 0 -> {second, X};
        {Tag, X} -> {fallback, X};
        stop -> done
    end.
self_guard() -> receive {Pid, X} when Pid =:= self() -> X end.
poll() -> receive {ok, X} -> X after 0 -> timeout end.
timed(T) -> receive {ok, X} -> X after T -> timeout end.
sleep(T) -> receive after T -> done end.
computed(T) -> receive X -> X after T + 1 -> timeout end.
nested() -> receive {ok, X} -> receive X -> yes after 0 -> no end; stop -> no end.
bindings() -> receive {pair, X, Y} -> {X, Y}; stop -> done end.
repeated() -> receive {X, X} -> X after 0 -> timeout end.
alias() -> receive Pair = {pair, X, Y} -> {Pair, X, Y} end.
lists() -> receive [X, Y | Rest] -> {X, Y, Rest} after 0 -> timeout end.
alternatives() -> receive X when not is_integer(X); X > 0 -> X after 0 -> timeout end.
sequence() -> receive after 0 -> ok end, receive after 0 -> done end.
