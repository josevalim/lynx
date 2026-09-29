-module(functions).
-export([run/1, make/1, explicit/2, inc/1, zero/0]).

run(X) ->
    F = make(X),
    G = make(X + 10),
    A = F(1),
    B = explicit(G, [2]),
    Z = zero(),
    Zero = fun zero/0,
    C = Zero(),
    H = fun inc/1,
    H(A + B + Z + C).

make(X) -> fun(Y) -> X + Y end.
explicit(F, Args) -> apply(F, Args).
inc(X) -> X + 1.
zero() -> 0.
