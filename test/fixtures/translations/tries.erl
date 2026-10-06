-module(tries).
-export([caught/1, scope/1, handler_scope/1, selective_catch/1,
         guarded_catch/1, reraised/1, after_effect/1, after_raises/1,
         success_clause/1, nested/1, dynamic/1, effectful/0]).

caught(X) -> try X + 1 of Y -> {ok, Y} catch C:R:S -> {C, R, S} end.
scope(X) -> try X + 1 of Y -> error({body, Y}) catch _:_ -> caught end.
handler_scope(X) -> try X + 1 catch _:_ -> throw(handler) end.
selective_catch(X) -> try X + 1 catch throw:R -> {throw, R} end.
guarded_catch(X) -> try error(X) catch error:R when is_integer(R), R > 0 -> positive; _:_ -> other end.
reraised(X) -> try X + 1 catch error:R:S -> erlang:raise(error, R, S) end.
after_effect(X) -> try X + 1 after put(key, done) end.
after_raises(X) -> try X + 1 after exit(cleanup) end.
success_clause(X) -> try X + 1 of 2 -> yes catch _:_ -> caught end.
nested(X) -> try scope(X) catch C:R -> {C, R} end.
dynamic(F) -> try F() of X -> {ok, X} catch C:R -> {C, R} end.
effectful() -> try put(key, protected), throw(failure) catch C:R -> {C, R, get(key)} end.
