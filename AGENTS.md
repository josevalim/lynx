Start with the README.md to understand the general project scope.

The implementation of Erlang NIFs go in Lynx.Modules.
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

Do not change the README.md unless asked to do so.