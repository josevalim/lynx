# Verification benchmarks

Run from the repository root:

```console
sh Benchmarks/run.sh 5
```

See [RESULTS.md](RESULTS.md) for the latest captured output and median timings.

Each file runs in a separate Lean process. `LYNX_BENCH` measures theorem
elaboration, including tactic execution, after imports have loaded, in
milliseconds. These are proof times, not executable runtime measurements.

## Suites

- **Sum:** Integer-list result contract and append property, compared with native `List Int`.
- **Reverse:** Proper-list return contract, involution, and append reversal, compared with native lists.
- **Sets:** Map-backed union contract, commutativity, and empty identity, compared with native `Std.ExtTreeMap`.

## Implementation reuse and measurement boundaries

Sum, Reverse, and Sets each keep their Elixir source comments, translated definitions,
supporting lemmas, and final proofs in one `LynxTest/Integration` module.
`#bench` marks only final contracts and properties, not supporting lemmas.
The benchmark runner compiles these source files directly on every run,
so cached integration modules do not skip proof elaboration. The same declarations
also run during integration-test builds.

Native benchmarks contain their own implementations. All use the timing command
in `LynxTest/Bench.lean`.

Run several times and compare medians. Theorems within a file elaborate in order
and may use earlier lemmas. Supporting lemmas are elaborated on each run, but
their elaboration and module imports are outside the measured sections.
`LynxTest/ProofAudit.lean` audits representative integration, library, and tactic
proofs for unexpected axioms as part of `lake test`, separately from benchmarks.
