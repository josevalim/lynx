<div align="center">
  <img height="240" alt="Lynx logo" src="logo.png" />
</div>

# LYNX

Write proofs about Erlang/Elixir programs using Lean.

This project implements a model of the Erlang runtime in Lean
and automatically translates your Erlang/Elixir code to Lean.

Automatic translation from Erlang/Elixir to Lean is work in progress.
The operational semantics have not yet been formally validated.

## Example

Use Lynx with ExUnit to run proofs alongside ordinary tests. Save this example
as `test/laws/sum_test.exs`. It defines a recursive sum and proves that the empty
list sums to zero and that, for integer lists, summing each list and adding the
results equals summing their concatenation:

```elixir
defmodule SumProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def sum([]), do: 0
  def sum([x | xs]), do: x + sum(xs)

  laws "sum" do
    law sum_empty,
      expects: sum([]) == 0,
      proof: ~LEAN"""
      simp [«sum_empty:ensures/0», «sum/1», Erlang.erlang.«==/2»]
      """

    law sum_append(l, r),
      requires: is_integer_list(l) and is_integer_list(r),
      expects: sum(l) + sum(r) == sum(l ++ r),
      proof: ~LEAN"""
      have cons_valid (head tail : Lynx.Term)
          (valid : «is_integer_list/1» (.cons head tail) = .ok Lynx.Term.true) :
          ∃ value, head = .integer value ∧ «is_integer_list/1» tail = .ok Lynx.Term.true := by
        cases head <;> simp_all [«is_integer_list/1», Erlang.erlang.«is_integer/1»]

      have sum_result (input : Lynx.Term)
          (valid : «is_integer_list/1» input = .ok Lynx.Term.true) :
          ∃ value : Int, «sum/1» input = .ok (.integer value) := by
        induction input using «sum/1».induct with
        | case1 => exact ⟨0, rfl⟩
        | case2 head tail ih =>
          obtain ⟨value, rfl, tailValid⟩ := cons_valid head tail valid
          obtain ⟨subtotal, returned⟩ := ih tailValid
          exact ⟨value + subtotal, by simp [«sum/1», returned]⟩
        | case3 input notNil notCons => simp_all [«is_integer_list/1»]

      have validity : «is_integer_list/1» l = .ok Lynx.Term.true ∧
          «is_integer_list/1» r = .ok Lynx.Term.true := by
        simp only [«sum_append:requires/2»] at requires
        cases left : «is_integer_list/1» l <;> simp [left] at requires
        case ok value =>
          split at requires <;> simp_all [Lynx.Term.true]

      obtain ⟨leftValid, rightValid⟩ := validity
      obtain ⟨rightSum, rightReturned⟩ := sum_result r rightValid

      have append_ok (input : Lynx.Term)
          (valid : «is_integer_list/1» input = .ok Lynx.Term.true) :
          ∃ leftSum joined,
            «sum/1» input = .ok (.integer leftSum) ∧
            Erlang.erlang.«++/2» input r = .ok joined ∧
            «sum/1» joined = .ok (.integer (leftSum + rightSum)) := by
        induction input using «sum/1».induct with
        | case1 => exact ⟨0, r, rfl, rfl, by simpa using rightReturned⟩
        | case2 head tail ih =>
          obtain ⟨value, rfl, tailValid⟩ := cons_valid head tail valid
          obtain ⟨subtotal, joined, returned, appended, combined⟩ := ih tailValid
          refine ⟨value + subtotal, .cons (.integer value) joined, ?_, ?_, ?_⟩
          · simp [«sum/1», returned]
          · simp [Erlang.erlang.«++/2», appended]
          · simp [«sum/1», combined, Int.add_assoc]
        | case3 input notNil notCons => simp_all [«is_integer_list/1»]

      obtain ⟨leftSum, joined, leftReturned, appended, combined⟩ := append_ok l leftValid
      simp [«sum_append:ensures/2», leftReturned, rightReturned, appended, combined,
        Erlang.erlang.«==/2»]
      """
  end

  test "laws are callable with concrete inputs" do
    assert sum_empty()
    assert sum_append([1, 2], [3, 4])
  end

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
```

`requires:` states the input assumptions; `expects:` must evaluate to `true`
under those assumptions. Each `laws` block registers one ExUnit test and verifies
all its laws together. The `~LEAN` sigils contain the proofs checked by Lean.
Laws also remain callable from ordinary tests, as shown above.

Run the example or all law groups with:

```console
mix test test/laws/sum_test.exs
mix test --only laws
```

## Erlang integration

Lynx can also verify laws written in Erlang.

Each `-law` attribute names ordinary predicate functions. A separate
binary `-proof` attribute must immediately follow its law:

```erlang
-module(sum_proofs).
-export([sum/1, sum_empty_ensures/0,
         sum_append_requires/2, sum_append_ensures/2]).

-law #{name => {sum_empty, []}, ensures => sum_empty_ensures}.
-proof ~"""
(SAME PROOF AS ABOVE)
""".

-law #{name => {sum_append, [l, r]},
       requires => sum_append_requires,
       ensures => sum_append_ensures}.
-proof ~"""
(SAME PROOF AS ABOVE)
""".

sum([]) -> 0;
sum([X | Xs]) -> X + sum(Xs).

sum_empty_ensures() -> sum([]) == 0.
sum_append_requires(L, R) -> is_integer_list(L) andalso is_integer_list(R).
sum_append_ensures(L, R) -> sum(L) + sum(R) == sum(L ++ R).

is_integer_list([H | T]) -> is_integer(H) andalso is_integer_list(T);
is_integer_list([]) -> true;
is_integer_list(_) -> false.
```

The proof placeholders refer to the proofs above, with the generated Elixir
predicate names replaced by their Erlang equivalents.

The argument names in `name` become Lean theorem parameters. The predicate
helpers receive those arguments in order and remain callable from Erlang.
`ensures` is required, while `requires` may be omitted for an unconditional
law. The law name does not need a matching Erlang function.

## Installation

Install Elixir 1.18+ and Elan, Lean's toolchain manager, with `lake` available on
`PATH`. The project's `Lean/lean-toolchain` selects Lean 4.33.1.

Add Lynx to your application's `mix.exs` dependencies:

```elixir
defp deps do
  [
    {:lynx, git: "https://github.com/josevalim/lynx.git", only: :test}
  ]
end
```

Fetch and compile the dependency:

```console
mix deps.get
MIX_ENV=test mix deps.compile lynx
```

Ensure `test/test_helper.exs` calls `ExUnit.start()`, then add the example above.

## Contributing

The project requires Elixir 1.18+ and Lean 4.33.1+, which includes Lake.
With those installed, fetch dependencies and compile the project with:

```console
mix deps.get
mix compile
```

Run tests with:

```console
mix test          # Elixir tests
mix test.lean     # Lean tests only
mix test.all      # Elixir + Lean
```

Before committing:

```console
mix precommit
```

The Lean source code can be found in the `Lean` directory,
you can run `lake` commands from that directory whenever working
with Lean directly.

Benchmarks comparing the translated examples with native ones
can be run with:

```console
sh Lean/Benchmarks/run.sh 5
```
