# Lynx

An experimental Elixir-to-Lean translation and verification project.

The initial example has two layers:

- `Lynx.Examples.LeanSum` defines a typed integer-list sum and proves that it
  distributes over list append.
- `Lynx.Examples.TermSum` implements the same function over dynamically typed
  Elixir terms, including cons-cell lists and raised `error`/`throw`/`exit`
  exceptions, and proves that it agrees with the typed version for valid inputs.
- `Lynx.Contract` defines when translated, guard-like preconditions and
  postconditions are satisfied: only an ordinary return of the atom `true`
  counts as acceptance.

Build and run it with:

```console
lake build
lake exe lynx
```
