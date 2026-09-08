Start with the README.md to understand the general project scope.

The Erlang Term definition and its general properties are defined
in Lynx/Term.lean and within the Lynx/Term/ directory.

The implementation of Erlang NIFs goes to Lynx/Modules/.
Functions follow their Erlang name with the arity followed
by underscore, such as `is_integer_1`. There is an additional
set of custom "NIFs" in the Extensions.lean file.

Integration tests go in LynxTest/Integration and they all
have the same shape: they have a version of the Elixir module
at the top and their manual translation in LEAN, including the
implementation, ensures, and expects. Preferrably verifications
are then done with the `lynx_verify` tactic instead of custom
theorems.

Whenever a new integration example is added, you must also add
a Benchmarks/Native equivalent example, using the same data types
but without the Term wrapping, so we can compare them. Add the
relevant #bench annotations to both native and integration.
Read Benchmarks/README.md for context around benchmarks.

Do not change the README.md unless asked to do so.