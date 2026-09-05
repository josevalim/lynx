# Lynx

An experimental Elixir-to-Lean translation and verification project.

## Example

Contracts and properties are written as ordinary Elixir expressions immediately
before a function definition:

```elixir
expects is_list(list) and Enum.all?(list, &is_number/1)
ensures (result -> is_number(result))
property sum(l) + sum(r) == sum(l ++ r)
def sum(list)
```

- `expects` restricts the inputs for which Lynx verifies the function.
- `ensures` states a guarantee about a successful return. The name to the left
  of `->` is a local binding for the returned value, not a reserved name.
- `property` states an additional expression that Lynx must prove. It can call
  the function directly and does not have an implicit result binding.

All three clauses contain single expressions; they do not introduce `do` blocks.

## Implementation

This project models Erlang terms with an inductive type and implements Erlang
NIFs in Lean. Expectations, assurances, and properties are then shaped into a
contract, which is verified by Lynx.Tactic.

Lynx.Tactic constructs proof terms that Lean’s kernel independently checks.
Its proof-search implementation therefore need not itself be trusted for logical
correctness, provided proofs introduce no untrusted axioms or sorry.

Everything in this project has been human verified, except for Lynx.Tactic.
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

`LynxTest/Integration` contains end-to-end translated examples. Focused tactic
tests live under `LynxTest/Tactic` and cover contracts, source-labelled VCs,
distinct recursion shapes, representative failures, and coverage diagnostics.
