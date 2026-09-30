<div align="center">
  <img height="240" alt="Lynx logo" src="logo.png" />
</div>

# LYNX

An experimental Erlang/Elixir-to-Lean translation and verification project.

## Proposal

You define a set of laws in Erlang/Elixir and prove them in Lean:

```elixir
defmodule SumProofs do
  use Lynx

  import :lists, only: [sum: 1]

  # by rfl
  law sum_empty, expects: sum([]) == 0

  law sum_append(l, r),
          requires: is_integer_list(l) and is_integer_list(r),
          expects: sum(l) + sum(r) == sum(l ++ r) do
    ~LEAN"""
    PROOF GOES HERE
    """
  end

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
```

Automatic translation from Erlang/Elixir to Lean is work in progress.
For now, you can find manual translations within the
[LynxTest/Integration](Lean/LynxTest/Integration) directory. Also check the
[Benchmarks](Lean/Benchmarks) folder to compare those examples with native
implementations.

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
