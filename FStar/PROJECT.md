# Foxy

Foxy is the F* counterpart of Daxie in `Dafny/`: Erlang terms, comparisons,
`add_2`, integer-list sum, anonymous functions, immutable process effects, and
association-list maps. It reproduces the Term/native sum and set-union
verification benchmarks. Translation is manual, as in the other experiments.

## Run

```console
sh FStar/Tests/run.sh
sh FStar/Benchmarks/run.sh 5
sh FStar/verify.sh
```

The tested installation is F* **2026.03.24**, commit
`70671ffb81fa30aba09b9d6e2af275dfbccaa8f8`, OCaml **5.4.1**, and Z3 **4.16.0**
on arm64 macOS. `tools.sh` uses the installed `fstar.exe` and `ocamlfind`.
`FSTAR`, `OCAMLFIND`, and `Z3` can override these executables.

F* defaults to Z3 4.13.3, which was absent on this machine. The runner first
looks for `z3-4.13.3`, then the existing Dafny Z3 4.16.0, then `z3` on PATH.
It passes the selected solver's actual version explicitly and records it in
benchmark logs. No toolchain installation or shell configuration is performed.
The existing OCaml `fstar.lib` package provides the extraction runtime.

The test runner deletes `.build/`, verifies every project module, extracts
OCaml, compiles it, and runs the tests. All model and test logic is written in
F*. Generated OCaml, compiler artifacts, and verified-module caches live in
ignored `.build/`; benchmark logs live in ignored `.benchmarks/`. No Python,
handwritten OCaml adapter, package installation, or home-directory changes are
needed.

## Design decisions against Daxie and Lean

| Decision | Foxy / F* evaluation |
| --- | --- |
| Term representation | An inductive `term` with unbounded `int`, finite binary64 data, atoms, functions, PIDs, tuples, maps, nil, and cons. Lists and pairs are standard F* types. |
| Floats | The installed `FStar.Float` is only an abstract placeholder. Foxy implements finite binary64 in F*, rather than claiming host floats have verified IEEE semantics. Details below. |
| Numeric and exact equality | Explicit comparators retain `1 == 1.0`, distinguish `1 =:= 1.0`, and distinguish signed zeros under exact comparison, matching Daxie/Lean. F* structural equality is not used as Erlang equality. |
| Maps | `list (term & term)`, with first-binding precedence and exact key comparison. Native F* maps require an `eqtype` key, but structural Term equality would distinguish reordered nested maps. It does not implement our key semantics. |
| Anonymous functions | `Function id arity captures`. Embedding `list term -> Tot term` inside `term` fails strict positivity, just as the analogous Lean/Dafny representations fail. Function bodies therefore live in a dispatcher. |
| Function comparison | Order by ID, then exact captured terms. The program table owns the arity for an ID. F* logical function equality is not decidable runtime equality; comparing native functions is rejected. |
| Cross-module calls | One whole-program ID/arity table and dispatcher. Only the runner receives this `program`; generated bodies receive captures and arguments. Static calls can remain ordinary F* calls. |
| Effects and processes | Pure request data plus callbacks, interpreted by an immutable runner. Bodies do not explicitly thread runtime, PID, or mailboxes through every call. |
| Sequencing | `bind` simplifies `Ok`/`Error`, otherwise emits `Then`. The runner maintains frames, avoiding recursive rewriting of callbacks and preserving a simple totality argument. |
| Contracts | F* `Lemma (requires ...) (ensures ...)`, refinement types, and `Pure` pre/post types. Recursive proofs use ordinary F* recursion and SMT. There is no custom verification tactic. |
| Native benchmarks | Native sum uses `list int`; native sets use `FStar.FiniteMap.Base.map int (list int)`. The latter has finite domains and domain-sensitive extensional equality. |
| Executable checks | All tests execute after OCaml extraction, including native map operations and signed-zero Term map keys. Only the two intentionally rejected language probes are expected to fail checking. |

### Floats

The installed [FStar.Float interface](https://github.com/FStarLang/FStar/blob/70671ffb81fa30aba09b9d6e2af275dfbccaa8f8/ulib/FStar.Float.fsti)
exposes an abstract float type with no arithmetic API or IEEE proof model.
Using its OCaml backing alone would require an external implementation boundary
and specifications not justified by that interface.

`Foxy.Float.t` instead stores the sign, exponent field (0–2046), and 52-bit
fraction, constrained by refinements. It retains signed zero and subnormals;
NaN/infinity bit patterns cannot produce a float term. Constructors accept raw
binary64 bits or integers, so no decimal parser or host float conversion is
needed.

Every finite binary64 value is an integer multiple of `2^-1074`. Comparison
uses these exact integer units, including mixed comparisons with arbitrary
integers. Addition forms the exact integer sum and rounds once to binary64,
with ties to even. Mixed addition first rounds the integer operand to binary64,
then adds, matching Daxie's two-stage conversion. Non-finite conversion or
addition returns `badarith`. Cancellation yields positive zero; adding two
negative zeros preserves negative zero.

The implementation is total and its representation constraints are checked.
A lemma proves bits-to-fields round trips for every representable value.
Executable tests cover subnormals, normal/subnormal transitions, both signed
zeros, rounding ties, huge integer comparisons, and the overflow threshold.
**A full theorem equating the rounding algorithm with an independent IEEE-754
specification has not been proved.** This model is designed for verification,
not native floating-point execution speed.

### Maps and comparisons

Lookup takes the first exactly matching key. `put_3` prepends a binding;
`merge_2` prepends the right operand's entries. Shadowed bindings remain in
storage but do not affect equality, effective size, or set membership.

Map comparison first checks effective bindings. Unequal maps are compared by
size, all keys, then values using a sorted, deduplicated view. Keys always
compare exactly; values use numeric or exact comparison as requested. Nested
maps and closures work as keys. Term order is:

```text
number < atom < function < pid < tuple < map < nil < cons
```

Mutual recursion through map lookup and comparison terminates using a term
height measure and a small helper-stage ordering. Termination is checked by
F*; there is no fuel cutoff in comparison. General comparator transitivity and
map-normalization laws remain outside the proved properties.

The native set benchmark uses `FStar.FiniteMap.Base` rather than `FStar.Map`.
The installed `FStar.Map.equal` also compares backing function values outside
the declared domain; that is not the intended finite-map equality. The finite
map library's `equal` compares domains and values within them.

### Anonymous functions and processes

`Foxy.Process` implements `apply_2`, `spawn_1`, `send_2`, and `self_0` as
requests. `Foxy.Runner` checks IDs and arities, dispatches bodies, allocates
fresh PIDs, maintains FIFO mailboxes and continuation frames, and records
process results. Errors propagate through `bind`; low-level Apply callbacks
can handle them. A child error does not terminate its parent.

The root PID is 1, and spawned zero-arity closures receive increasing PIDs.
Send returns its message; sending to an absent or finished PID succeeds without
delivery. Scheduling choices are a list of PIDs consumed at spawn/send
boundaries. Missing choices preserve runnable order. Without a choice, the
current process continues until it finishes. Each interpreter step consumes
fuel; `Exhausted` is distinct from `Completed`, which requires every process
to finish. There is no receive, registered-name routing, linking, or OS-thread
execution in this subset.

`Tests/Foxy.Tests.Program.fst` shows a captured adder, calls between generated
bodies representing different modules, recursive dynamic apply, and a worker
that sends its PID to its parent. The dispatcher demonstrates the whole-program
interface; this project does not yet generate it from source modules.

### Purity in F*

F* has no Dafny-style function/method split. Effects belong to function types:
`Tot` is pure and terminating; `Pure` adds explicit pre/postconditions;
`Lemma` is a proof erased during extraction. `ML` permits general effects and
is used only by the executable test harness. Foxy's modeled Erlang effects
are ordinary total data-producing functions; they do not perform host I/O.

Callbacks such as `reply -> Tot result` are permitted because `result` occurs
positively. Putting the full callable body in `term` introduces a negative
occurrence of `term` in its argument type. The negative tests in
`Tests/Rejected/` check that strict positivity and executable function equality
are still rejected by the selected toolchain.

## Verification and benchmarks

The sum proofs establish the integer result contract and append law. A separate
inductive proof relates Term sum to native sum for every encoded integer list.
The set proofs establish preservation of the effective-empty-list invariant,
commutativity, and empty-map identity; they use logical expectations, as in
Daxie. Empty-set witnesses demonstrate these preconditions are satisfiable.
The runtime proofs cover a captured adder for arbitrary integers, delivery
length, and the head process's mailbox update.

There are no project `admit`, `assume`, lax-checking, or positivity bypasses.
As usual, verification trusts F*, its standard-library specifications, and Z3.
The project does not prove a full correspondence with Erlang's operational
semantics or a general runtime invariant for arbitrary manually forged states.

Benchmarks measure **verification**, not execution. The runner first verifies
all sources, then uses one discarded warm-up and five measured runs by default,
alternating suite order. Each suite runs in a fresh F* process with `--force`;
only already-verified supporting imports are cached. It records F*'s
`process_one_decl` time for the nine named final proofs, excluding imports and
supporting declarations, plus raw SMT query statistics.

Term sum's result contract and append property each perform their induction
inside the measured declaration, as in Lean and Daxie. The only imported sum
lemma proves integer-list preservation and successful append; it proves no
sum-value law. There is no imported exact-sum theorem. Native sum likewise
performs its induction inside the measured append lemma. Set lookup and
extensional-equality helpers remain excluded, matching Daxie's proof boundary.

F* declaration times include elaboration and proof checking and have millisecond
resolution. They are not the same metric as Daxie's SMT-batch times. See
[Benchmarks/RESULTS.md](Benchmarks/RESULTS.md) for measured results and scope.
