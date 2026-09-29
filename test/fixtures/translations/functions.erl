-module(functions).
-export([run/1, make/1, explicit/2, inc/1]).

run(X) ->
    F = make(X),
    G = make(X + 10),
    A = F(1),
    B = explicit(G, [2]),
    H = fun inc/1,
    H(A + B).

make(X) -> fun(Y) -> X + Y end.
explicit(F, Args) -> apply(F, Args).
inc(X) -> X + 1.
