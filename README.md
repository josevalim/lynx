<div align="center">
  <img height="240" alt="Lynx logo" src="logo.png" />
</div>

# LYNX

An experimental Erlang/Elixir-to-Lean translation and verification project.

## Proposal

You define a set of laws in Erlang/Elixir and prove them in Lean:

```elixir
defmodule SumProofs do
  use Lynx.Laws

  import :lists, only: [sum: 1]

  law sum_empty, expects: sum([]) == 0

  law sum_append(l, r),
    requires: is_integer_list(l) and is_integer_list(r),
    expects: sum(l) + sum(r) == sum(l ++ r),
    proof: ~LEAN"""
    PROOF GOES HERE
    """

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
```

In Erlang, each `-law` attribute names ordinary predicate functions. A separate
binary `-proof` attribute must immediately follow its law:

```erlang
-module(sum_proofs).
-export([sum/1, sum_empty_ensures/0,
         sum_singleton_requires/1, sum_singleton_ensures/1]).

-law #{name => {sum_empty, []}, ensures => sum_empty_ensures}.
-proof ~"""
simp [«sum_empty_ensures/0», «sum/1», Erlang.lists.«sum/1»,
  Erlang.lists.«sum/2», Erlang.erlang.«==/2»]
""".

-law #{name => {sum_singleton, [x]},
       requires => sum_singleton_requires,
       ensures => sum_singleton_ensures}.
-proof ~"""
cases x <;>
  simp [«sum_singleton_requires/1», «sum_singleton_ensures/1»,
    Erlang.erlang.«is_integer/1», «sum/1», Erlang.lists.«sum/1»,
    Erlang.lists.«sum/2», Erlang.erlang.«==/2»] at requires ⊢
""".

sum(List) -> lists:sum(List).
sum_empty_ensures() -> sum([]) == 0.
sum_singleton_requires(X) -> is_integer(X).
sum_singleton_ensures(X) -> sum([X]) == X.
```

The argument names in `name` become Lean theorem parameters; the arity is inferred
from their number. The predicate helpers receive those arguments in order and remain
callable from Erlang. `ensures` is required, while `requires` may be omitted for an
unconditional law. The law name does not need a matching Erlang function.

Automatic translation from Erlang/Elixir to Lean is work in progress,
see the [fixtures folder](test/fixtures/translations/) for examples.

## Implementation

This project models Erlang terms with an inductive type (see [`Lynx.Term`](Lean/Lynx/Term.lean))
and implements Erlang NIFs in Lean (see [Lean/Erlang](Lean/Erlang)).
Only some terms and NIFs are implemented in the current proof of concept.

Modules are translated following a clear rule:

* Erlang modules become `Erlang.module_name` in Lean
* Elixir modules become `Elixir.ModuleName` in Lean
* Function names are have the shape `«fun/arity»`

The Elixir/Erlang code has been fully verified by humans as well as the
modeling of the Erlang runtime in Lean. Note the operational semantics of
translating Erlang/Elixir to Lean has not been verified and the translation
mechanism may have bugs.

## Contributing

The project requires Elixir 1.18 or newer in the 1.x series and Lean 4.33.1,
which includes Lake. With those installed, fetch dependencies and build Lean with:

```console
mix setup
```

Run tests with:

```console
mix test          # Elixir tests
mix test.lean     # Lean tests only
mix test.all      # Elixir + Lean
```

Before committing:

```console
mix precommit
```

The Lean source code can be found in the `Lean` directory,
you can run `lake` commands from that directory whenever working
with Lean directly.

Benchmarks comparing the translated examples with native ones
can be run with:

```console
sh Lean/Benchmarks/run.sh 5
```
