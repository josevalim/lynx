# Lynx

An experimental Elixir-to-Lean translation and verification project.

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

Proofs are done over dynamic Erlang terms. For programs that need additional proofs,
there is a `~LEAN"..."` sigil to embed LEAN source within each module.

At the moment, automatic translation from Erlang/Elixir to Lean has not yet
been implemented. In the future, it should likely be done from Core Erlang
AST. For now, you can find manual translations within the
[LynxTest/Integration](LynxTest/Integration) directory. Also check the
[Benchmarks](Benchmarks) folder to compare those examples with native
implementations.

## Implementation

This project models Erlang terms with an inductive type (see [`Lynx.Term`](Lynx/Term.lean))
and implements Erlang NIFs in Lean (see [Lynx/Modules](Lynx/Modules)).
Only some terms and NIFs are implemented in this proof of concept.

Expectations, assurances, and properties are then shaped into a contract,
which is verified by [`Lynx.Tactic`](Lynx/Tactic.lean).

Everything in this project has been human verified, except for `Lynx.Tactic`.
`Lynx.Tactic` constructs proof terms that Lean’s kernel independently checks.
Its proof-search implementation therefore need not itself be trusted for logical
correctness, provided proofs introduce no untrusted axioms or sorry.
Read that module source and documentation for more information.

## Running tests

Build with:

```console
lake build
```

Elaborate and kernel-check the integration-test examples with:

```console
lake test
```

[LynxTest/Integration](LynxTest/Integration) contains end-to-end translated examples.

Run benchmarks comparing the translated examples with native ones:

```console
sh Benchmarks/run.sh 5
```
