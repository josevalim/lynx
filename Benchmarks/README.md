# Verification benchmarks

Run from the repository root:

```console
sh Benchmarks/run.sh 5
```

See [RESULTS.md](RESULTS.md) for the latest captured output and median timings.

Each file runs in a separate Lean process. `LYNX_BENCH` measures theorem
elaboration, including tactic execution, after imports have loaded, in
milliseconds. These are proof times, not executable runtime measurements.

## Guarantees

`Sum` compares automatic `lynx_verify` proofs with native `List Int`.
The Lynx version proves its integer-list contract and the append property;
native proves the append property.

`Reverse` proves successful proper-list return and involution over Term.
Both final Term proofs use `lynx_verify`, supported by handwritten `@[simp]`
accumulator lemmas. Unmatched function clauses raise `function_clause`.
The native implementation proves exact reversal and involution using a
handwritten accumulator lemma and Lean's existing list theorems.

Native lists statically exclude malformed outer lists; the native functions
have no exception result. Coverage remains part of the Lynx specifications,
rather than a standalone benchmark.

## Implementation reuse and measurement boundaries

Sum and Reverse each keep their Elixir source comments, translated definitions,
supporting lemmas, and final proofs in one `LynxTest/Integration` module.
`#bench` marks only final contracts and properties, not supporting lemmas.
The benchmark runner compiles these source files directly on every run,
so cached integration modules do not skip
proof elaboration. The same declarations also run during integration-test builds.

Native benchmarks contain their own implementations. All use the timing command
in `LynxTest/Bench.lean`.

Run several times and compare medians. Theorems within a file elaborate in order
and may use earlier lemmas. Supporting lemmas are elaborated on each run, but
their elaboration and module imports are outside the measured sections.
`LynxTest/ProofAudit.lean` audits representative integration, library, and tactic
proofs for unexpected axioms as part of `lake test`, separately from benchmarks.
