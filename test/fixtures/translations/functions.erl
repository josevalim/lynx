-module(functions).
-export([captured_closures/1, zero_arity_calls/0, apply_calls/1, sequence_calls/1,
         make/1, explicit/2, inc/1, zero/0, remember/1, make_store/1]).

%% Two closures share code but retain different captured values.
captured_closures(X) ->
    F = make(X),
    G = make(X + 10),
    A = F(1),
    B = G(2),
    A + B.

%% Direct and function-value calls with no arguments.
zero_arity_calls() ->
    Z = zero(),
    Zero = fun zero/0,
    C = Zero(),
    Z + C.

%% Explicit apply, named function values, and an effectful captured closure.
apply_calls(X) ->
    F = make(X),
    A = explicit(F, [2]),
    H = fun inc/1,
    Remember = fun remember/1,
    Store = make_store(X),
    Store(Remember(H(A))).

%% Core c_seq: execute the effect and discard its result before returning X.
sequence_calls(X) ->
    remember(X),
    X.

make(X) -> fun(Y) -> X + Y end.
explicit(F, Args) -> apply(F, Args).
inc(X) -> X + 1.
zero() -> 0.
remember(X) -> put(last, X).
make_store(X) -> fun(Y) -> put(X, Y) end.
