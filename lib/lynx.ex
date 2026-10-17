defmodule Lynx do
  @moduledoc """
  Lynx allows you to write proofs about Erlang/Elixir programs using Lean.

  This is done by writing laws, in Erlang/Elixir, with a Lean proof
  that guarantees your Erlang/Elixir code obey those laws. This is done
  by implementing a model of the Erlang runtime in Lean and automatically
  translating your Erlang/Elixir code to Lean.

  ## Usage

  There are two ways of using this project:

    * via `Lynx.Case` - the recommended usage for most Elixir projects,
      as it leverages ExUnit's runner and conveniences. See `Lynx.Case`
      for more information

    * via `Lynx.Laws` and module attributes - the recommended API for Erlang
      users and those who want to control when the laws are verified.
      See `Lynx.Laws` to get started

  ## Writing proofs

  When you write a law, Lynx will translate all functions and all of its dependencies
  to Lean. Modules are translated following a clear rule:

  * Erlang modules become `Erlang.module_name` in Lean
  * Elixir modules become `Elixir.ModuleName` in Lean
  * Function names are have the shape `«fun/arity»`

  Each argument is an Erlang term which is modelled as `Lynx.Term`. Each function
  returns a `Lynx.Result`, which returns `ok`, `error` (in case of exceptions),
  and other possible statuses code.

  For example, `:lists.sum/1` will become `Erlang.lists.«sum/1»` in Lean with the
  following signature:

      def «sum/1» (_0 : Lynx.Term) : Lynx.Result

  Each law becomes a Lean theorem whose parameters are the law's arguments, whose
  hypothesis states that `requires:` returns `true`, and whose goal states that
  `expects:` returns `true`. Your proof is elaborated against that theorem as is.

  The Lean source code is present in the "Lean" folder of the Lynx project. Besides
  the basic definition of Erlang terms, it also contains the implementation of Erlang
  NIFs within `Lynx/Modules/Erlang`. It may be necessary to navigate the source code
  in order to best understand the constructs when writing proofs.

  Furthermore, when running proofs with ExUnit, the error reports include the path to
  folder with all `.lean` files. Use this to debug and guide your proofs.

  ### Purity model

  To choose how each side of a law is stated, Lynx tracks the purity of every
  translated function. A function has the purity of the most impure code it
  reaches, through its own body and every function it calls:

    * `pure` — returns a value or raises an exception without consulting the
      runtime. Exceptions are part of the result, so code that raises is pure.

    * `partial` — pure, except that it may not return. Functions with a
      `termination_suffix` or a `cutoff`, and their callers, are partial.

    * `sequential` — runs in a single process, but uses the process dictionary,
      references, `self()`, or invokes anonymous functions, which are resolved
      against the program's function table.

    * `concurrent` — may spawn processes, send messages, or receive them.
      Invoking anonymous functions is concurrent when any function in the
      program's table is.

  Each law then uses the strongest construction its purity allows:

    * Pure and partial expectations, and pure preconditions, are stated directly:

          theorem «law/1» (x : Lynx.Term)
              (requires : «law:requires/1» x = .ok Lynx.Term.true) :
              «law:ensures/1» x = .ok Lynx.Term.true

    * Sequential code, and partial preconditions, are stated through `Lynx.run`,
      which executes the code from a fresh runtime against the function table:

          Lynx.run («law:ensures/1» x) table 100 = .ok Lynx.Term.true

    * Concurrent code is stated through `Lynx.schedule`, which also takes the
      scheduler's choices. The precondition must hold under some schedule, and
      the expectation under all of them:

          (requires : ∃ schedule, Lynx.schedule («law:requires/1» x) schedule table 100 = .ok Lynx.Term.true)
          (schedule : List Lynx.ScheduleChoice) :
          Lynx.schedule («law:ensures/1» x) schedule table 100 = .ok Lynx.Term.true

  Both `Lynx.run` and `Lynx.schedule` start from a fresh runtime: a single
  process, with an empty process dictionary, and an empty mailbox. The
  precondition and the expectation each start from this runtime separately,
  so nothing stored or sent by one is visible to the other. Laws over sequential
  and concurrent code therefore describe a freshly started process. For example,
  `Process.get(:key) == nil` is provable, even though it does not hold in a
  process that has stored `:key`.

  A direct statement is the strongest: code that returns `true` directly also does
  so when run, under every schedule. Partial preconditions are run because Lean
  cannot confirm that they make no runtime requests. Proofs citing other laws
  receive the statements of those laws.

  ### Guidelines

  A few tools and proof patterns help when working with existing library code:

    * State the input domain with `requires:` and the intended general property
      with `expects:`. Focus on properties ranging over variables instead of
      passing specific values whenever possible. A terminating example does
      not establish totality over all inputs.

    * Use `cutoff &Module.function/arity` inside a `laws` group for dependencies
      that the property's inputs must never reach, such as unsupported error
      formatting. Lynx replaces the function before traversing its body or
      dependencies. It returns an exhausted computation, so a proof of a
      successful result must establish that the cutoff is never reached.
      A cutoff does not assume a return value or an exception. Keep reachable
      behavior translated and prove the actual implementation. The cutoff
      function, and every function calling it, is marked as partial.

    * Use `termination_suffix &Module.function/arity, ~LEAN"..."` inside a group
      when Lean cannot infer termination of a translated recursive function.
      Supply a well-founded `termination_by` argument when appropriate, or use
      `partial_fixpoint` with a monotonicity proof when totality depends on the
      law's input domain. In the latter case, use the generated `.eq_def`
      equation and induction on a decreasing measure to establish that calls
      in the domain return. The suffix alone does not prove totality. The
      function, and every function calling it, is marked as partial.

    * Inspect the generated Lean before writing the proof. BEAM compilation
      can inline helpers or replace arithmetic with bit operations. Prove
      equations for the translated operations first, then reason about those
      equations mathematically. Keep the implementation separate from its
      specification instead of proving a rewritten substitute.

    * Reduce type checks and impossible branches early. Preserve shared
      continuations and introduce names for intermediate arithmetic values
      before simplifying; expanding every bind and nested expression can make
      a small property expensive to prove. For complex nonrecursive functions,
      `unfold` followed by selective simplification can avoid expensive
      generation of simplification equations.

    * Use `max_heartbeats: 1_000_000` on an individual law when a proof needs a
      larger Lean elaboration budget. It does not weaken kernel checking.
      First look for repeated expansion or unnecessary case splits. Measure
      verification with `LYNX_PROFILE=1 LYNX_CACHE=0` so cached results do not
      hide slow proofs.

  ## Limitations

  Lynx implements most Erlang/Elixir language constructs, although several
  built-in functions (BIFs) may be missing. The focus is on verifying sequential
  programs rather than concurrent or distributed ones.

  Proofs describe Lynx's model of the Erlang runtime. The following restrictions
  matter when interpreting their results:

    * Bitstring float segments support only 64 bits. Float-16 and float-32
      construction currently raises `badarg` in the model, and matching those
      sizes is rejected during translation. Float segment sizes must be known
      at translation time.

    * `native` endianness in bitstring construction and matching is resolved to
      `little` or `big` during translation, according to the platform running
      Lynx. The generated Lean code retains that choice when used elsewhere.

    * `node()` (`:erlang.node/0`) always returns `:nonode@nohost`. Distributed
      nodes are not modeled. Sending messages supports local PIDs only;
      registered names and remote destinations are not modeled.

    * Receive timeouts do not measure wall-clock time. Positive timeouts expire
      according to the modeled scheduler's choices, or when no process can run.

    * Exception stack traces are not recorded and are represented by `[]`.

    * Laws cannot quantify over arbitrary functions. A function parameter ranges
      over every function term, with no behavior of its own; calling one resolves
      only against the functions the program defines. Restrict function
      parameters in `requires:` to explicitly listed functions, for example
      `fun in [fn x -> x end, fn x -> {x} end]`.

  Missing constructs or BIFs produce translation errors. Feel free to
  [open an issue](https://github.com/josevalim/lynx/issues) for missing functionality.
  """
end
