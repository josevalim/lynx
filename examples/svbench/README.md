# SV-COMP benchmarks

Programs from the [SV-COMP](https://sv-comp.sosy-lab.org) benchmark set
([sv-benchmarks](https://github.com/sosy-lab/sv-benchmarks), commit `2e1723f`),
translated to Elixir and proved with Lynx. They exercise recursion, termination
arguments, and nonlinear arithmetic.

Each SV-COMP task pairs a program with properties and their expected verdicts.
These examples cover the tasks below whose `unreach-call` (C) or `assert`
(Java) verdict is `true` and which do not depend on integer overflow
(`no-overflow` is `true` or not checked). Every `assert` must hold, so each law
states that the asserted condition holds.

Run a single file with:

    LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/svbench/recursive/ackermann.exs

## Translation

The programs are rewritten in idiomatic Elixir rather than transliterated. Each
file's header lists the tasks it covers, with their original input domains.

  * Nondeterministic inputs become law parameters. Erlang integers are
    unbounded, so the laws drop the bounds that only prevent overflow and hold
    over the most general domain that still implies each task's assertion.
    They keep restrictions where the program would otherwise diverge or fail.

  * A law only holds for computations that return, so every law also proves
    termination on its domain, which `unreach-call` does not require.

  * Loops become tail-recursive functions. Assertions inside loops raise
    `:reach_error` when they fail, and final assertions are the law's `expects:`.

  * Global state, such as a move counter, is returned instead of stored.

Java tasks in `java/jayhorn-recursive` are mostly ports of the C programs. They
share a file, and a law when they assert the same property.

## Coverage

57 of the 59 tasks in scope are proved.

### `c/recursive` and `java/jayhorn-recursive`

| Task | File | Law |
|---|---|---|
| `c/recursive/Ackermann01-2`, `java/SatAckermann01` | `recursive/ackermann.exs` | `ackermann01_2` |
| `c/recursive/Ackermann03`, `java/SatAckermann02` | `recursive/ackermann.exs` | `ackermann03` |
| `c/recursive/Ackermann04`, `java/SatAckermann03` | `recursive/ackermann.exs` | `ackermann04` |
| `c/recursive/Addition01-2`, `java/Addition`, `java/SatAddition01` | `recursive/addition.exs` | `addition01_2` |
| `c/recursive/Addition03-1` | `recursive/addition.exs` | `addition03_1` |
| `c/recursive/EvenOdd01-1`, `java/SatEvenOdd01` | `recursive/even_odd.exs` | `evenodd01_1` |
| `c/recursive/Fibonacci01-1`, `java/SatFibonacci01` | `recursive/fibonacci.exs` | `fibonacci01_1` |
| `c/recursive/Fibonacci02`, `java/SatFibonacci02` | `recursive/fibonacci.exs` | `fibonacci02` |
| `c/recursive/Fibonacci03`, `java/SatFibonacci03` | `recursive/fibonacci.exs` | `fibonacci03` |
| `c/recursive/gcd01-1`, `java/SatGcd` | `recursive/gcd.exs` | `gcd01_1` |
| `c/recursive/gcd02` | `recursive/gcd.exs` | `gcd02` |
| `c/recursive/recHanoi01`, `java/SatHanoi01` | `recursive/hanoi.exs` | `rec_hanoi01` |
| `c/recursive/recHanoi02-2` | `recursive/hanoi.exs` | `rec_hanoi02_2` |
| `c/recursive/recHanoi03-2` | `recursive/hanoi.exs` | `rec_hanoi03_2` |
| `c/recursive/McCarthy91-2` | `recursive/mccarthy91.exs` | `mccarthy91_2` |
| `java/SatMccarthy91` | `recursive/mccarthy91.exs` | `sat_mccarthy91` |
| `c/recursive/MultCommutative-2`, `java/SatMultCommutative01` | `recursive/mult_commutative.exs` | `mult_commutative_2` |

Not covered: `c/recursive/Primes` and `java/SatPrimes01`. Their `multiple_of`
diverges unless its second argument divides the first, so `is_prime(n)` never
returns for `n > 2`, and the expected verdict holds only because execution
never reaches the assertion. A law, which requires the computation to return,
would only cover `n <= 2`.

### `c/nla-digbench`

Each task has its own file under `nla/`, with a law named after the task: for
example, `c/nla-digbench/cohencu-ll` is proved by law `cohencu_ll` in
`nla/cohencu_ll.exs`. All 27 tasks are covered:

`bresenham-ll`, `cohencu-ll`, `cohendiv-ll`, `dijkstra-u`, `divbin2`,
`egcd-ll`, `egcd2-ll`, `egcd3-ll`, `fermat1-ll`, `fermat2-ll`, `geo1-ll`,
`geo2-ll`, `geo3-ll`, `hard-ll`, `hard2`, `knuth`, `lcm1`, `lcm2`, `mannadiv`,
`prod4br-ll`, `prodbin-ll`, `ps2-ll`, `ps3-ll`, `ps4-ll`, `ps5-ll`, `ps6-ll`,
and `sqrt1-ll`.

Unbounded integers differ from C in two tasks, as described in their headers:
`knuth` models `unsigned` arithmetic and `sqrt` with integers, and `divbin2`
terminates for every input, while the C program diverges once its input
exceeds `2^31` and the doubling wraps around.
