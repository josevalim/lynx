# Lynx

An experimental Elixir-to-Lean translation and verification project.

## Elixir syntax

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

Build the public library with:

```console
lake build
```

Elaborate and kernel-check the integration-test examples with:

```console
lake test
```
