# Lynx

An experimental Erlang/Elixir-to-Lean translation and verification project.

## Proposal

Contracts and properties would be written as ordinary Elixir expressions
immediately before a function definition:

```elixir
expects is_proper_list(list, &is_number/1)
ensures (result -> is_number(result))
property sum(l) + sum(r) == sum(l ++ r)
def sum(list)
```

- `expects` restricts the inputs for which Lynx verifies the function.
- `ensures` states a guarantee about a successful return. The name to the left
  of `->` is a local binding for the returned value, not a reserved name.
- `property` states an additional expression that Lynx must prove. It can call
  the function directly and does not have an implicit result binding.

Proofs are done over dynamic Erlang terms. For programs that need
additional proofs, a proposed `~LEAN"..."` sigil would embed Lean source
within each module. The sigil is not implemented yet.

Automatic translation from Erlang/Elixir to Lean is work in progress.
For now, you can find manual translations within the
[LynxTest/Integration](Lean/LynxTest/Integration) directory. Also check the
[Benchmarks](Lean/Benchmarks) folder to compare those examples with native
implementations.

## Implementation

This project models Erlang terms with an inductive type (see [`Lynx.Term`](Lean/Lynx/Term.lean))
and implements Erlang NIFs in Lean (see [Lynx/Modules](Lean/Lynx/Modules)).
Only some terms and NIFs are implemented in the current proof of concept.

Expectations, assurances, and properties are then shaped into a contract,
which is verified by [`Lynx.Tactic`](Lean/Lynx/Tactic.lean).

Everything in this project has been human verified, except for the tactic and
theorems, which are written with coding agents. In particular, `Lynx.Tactic`
constructs proof terms that Lean's kernel independently checks. Proofs must not
introduce untrusted axioms or sorry. Read that module source and documentation
for more information.

Note the operational semantics of translating Erlang/Elixir to Lean has not
been verified and the translation mechanism may have bugs.

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
