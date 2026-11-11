defmodule Lynx do
  @moduledoc """
  Write proofs about Erlang/Elixir programs using Lean.

  You write laws in Erlang/Elixir, which are automatically translated to
  Lean alongside your Erlang/Elixir code, and you write proofs in Lean.
  The laws and proofs are assembled together and verified by Lean's kernel.

  This technique is also known as _shallow embedding_, since it translates
  Erlang/Elixir to Lean and then use the features and properties of Lean
  for proofs. If there are no bugs during translation (or in Lean's kernel),
  then the proofs are correct.

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

  Finally, because the Lynx translates your Erlang/Elixir program to Lean,
  it relies on whole program analysis. As seen below, it does support both
  sequential and concurrent features of the Erlang runtime, but it cannot
  prove anything that involves external systems, running either over the network
  (sockets) or I/O (ports).

  ### Purity model

  To choose how each side of a law is stated, Lynx tracks the purity of every
  translated function. A function has the purity of the most impure code it
  reaches, through its own body and every function it calls:

    * `pure` — returns a value or raises an exception without consulting the
      runtime. Exceptions are part of the result, so code that raises is pure.
      Pure functions return `Except Lynx.Exception Lynx.Term`, and other code
      embeds their calls with `Lynx.Result.ofExcept`. Pure code may also not
      return, such as a `cutoff` or a diverging `partial_fixpoint`: it then
      raises `Lynx.Exception.exhausted`, which is not an Erlang exception.
      Handlers never catch it, so a law proving a value or an Erlang exception
      also proves that the computation returns.

    * `apply` — pure, except that it invokes anonymous functions, when every
      function in the program's table is pure or `apply`. Calls by name, such as
      `apply(mod, fun, args)` or `mod.fun(x)`, and `:erlang.fun_info_mfa/1` are
      at this level too. It also returns `Except`, and receives a
      `Lynx.Dispatcher`, which calls anonymous functions through the program's
      function table.

    * `sequential` — runs in a single process, but uses the process dictionary,
      references, or `self()`. Invoking anonymous functions is sequential when
      any function in the program's table is.

    * `concurrent` — may spawn processes, send messages, or receive them, or
      act on other processes through links, monitors, and exit signals, such
      as `Process.monitor/1`, `Process.exit/2`, or `Process.alive?/1`.
      Invoking anonymous functions is concurrent when any function in the
      program's table is.

  Code at the `apply` level and above receives the dispatcher as its first
  parameter. Laws pass it through `Lynx.apply helper table depth`, where `table`
  is the program's function table, `Erlang.program.fun_table`, and the
  dispatcher resolves it up to the given call depth. Such code must return
  `true` from some depth on, so a law holds however deep its calls go, and the
  proof chooses the bound, which may depend on the inputs. Each law then uses
  the strongest construction its purity allows:

    * Pure code is stated directly, as an `Except` value:

          theorem «law/1» (x : Lynx.Term)
              (requires : «law:requires/1» x = .ok Lynx.Term.true) :
              «law:ensures/1» x = .ok Lynx.Term.true

    * Code at the `apply` level is also stated directly, as an `Except` value:

          ∃ bound : Nat, ∀ depth : Nat, bound ≤ depth →
            Lynx.apply «law:ensures/1» table depth x = .ok Lynx.Term.true

    * Sequential code is stated through `Lynx.sequential`, which executes the
      code from a fresh runtime:

          ∃ bound : Nat, ∀ depth : Nat, bound ≤ depth →
            Lynx.sequential (Lynx.apply «law:ensures/1» table depth x) = .ok Lynx.Term.true

    * Concurrent code is stated through `Lynx.concurrent`, which also takes the
      scheduler's choices. The precondition must hold under some schedule, and
      the expectation under all of them:

          (requires : ∃ schedule, ∃ bound : Nat, ∀ depth : Nat, bound ≤ depth →
            Lynx.concurrent (Lynx.apply «law:requires/1» table depth x) schedule =
              .ok Lynx.Term.true)
          (schedule : List Lynx.ScheduleChoice) :
          ∃ bound : Nat, ∀ depth : Nat, bound ≤ depth →
            Lynx.concurrent (Lynx.apply «law:ensures/1» table depth x) schedule =
              .ok Lynx.Term.true

  A precondition at these levels is assumed in the same form, with its own
  bound. Start such a proof with `refine ⟨bound, fun depth deep => ?_⟩`. When
  the code makes no dynamic calls, or only calls pure functions, any depth
  works and the bound is `0`.

  Both `Lynx.sequential` and `Lynx.concurrent` start from a fresh runtime: a single
  process, with an empty process dictionary, and an empty mailbox. The
  precondition and the expectation each start from this runtime separately,
  so nothing stored or sent by one is visible to the other. Laws over sequential
  and concurrent code therefore describe a freshly started process. For example,
  `Process.get(:key) == nil` is provable, even though it does not hold in a
  process that has stored `:key`.

  Proofs must not introduce untrusted axioms or `sorry`.

  ### Proofs and versions

  Proofs are tied to the implementation they verify. Lynx translates the compiled
  code of your functions and all of their dependencies, including functions from
  Elixir and Erlang's standard library. The translated code is also shaped by the
  compiler, which may inline helpers, reorder clauses, or rewrite expressions.

  Therefore, updating Elixir, Erlang/OTP, or any of your dependencies may change
  the generated Lean code, even when the behavior is the same. Laws that held
  before may require further proofs afterwards.

  ### Guidelines

  A few tools and proof patterns help when working with existing library code:

    * State the input domain with `requires:` and the intended general property
      with `expects:`. Focus on properties ranging over variables instead of
      passing specific values whenever possible. A terminating example does
      not establish totality over all inputs.

    * Use `cutoff &Module.function/arity` inside a `laws` group for dependencies
      that the property's inputs must never reach, such as unsupported error
      formatting. Lynx replaces the function before traversing its body or
      dependencies. It raises `Lynx.Exception.exhausted`, which no handler
      catches, so a proof of a successful result must establish that the
      cutoff is never reached. A cutoff does not assume a return value or an
      Erlang exception. Keep reachable behavior translated and prove the actual
      implementation.

    * Use `termination_suffix &Module.function/arity, ~LEAN"..."` inside a group
      when Lean cannot infer termination of a translated recursive function.
      Supply a well-founded `termination_by` argument when appropriate, or use
      `partial_fixpoint` when totality depends on the law's input domain. Lean
      proves its monotonicity for translated code. Inputs on which the function
      diverges raise `Lynx.Exception.exhausted`. Use the generated `.eq_def`
      equation and induction on a decreasing measure to establish that calls
      in the domain return. To prove a property of every value the function
      returns, use its `fixpoint_induct` principle with
      `Lynx.Except.admissible_returnsN` instead (see `Lynx.Case.termination_suffix/2`).
      The suffix alone does not prove totality, and does not change the
      function's purity.

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

    * Use `options: [maxHeartbeats: 1_000_000]` on a laws group when a proof
      needs a larger Lean elaboration budget. It does not weaken kernel checking.
      First look for repeated expansion or unnecessary case splits. Measure
      verification with `LYNX_DEBUG=lean LYNX_CACHE=0` so cached results do not
      hide slow proofs, and see "Profiling proofs" to find where time goes.

  ### Limitations

  Lynx implements most Erlang/Elixir language constructs, although several
  built-in functions (BIFs) may be missing. The focus is on verifying sequential
  programs rather than concurrent or distributed ones.

  Proofs describe Lynx's model of the Erlang runtime. The following restrictions
  matter when interpreting their results:

    * Bitstring generators whose segment widths may all be zero, such as
      `for <<x::size(n) <- bits>>` with `n = 0`, raise `badarg` instead of
      repeating forever as Erlang does.

    * `native` endianness in bitstring construction and matching is resolved to
      `little` or `big` during translation, according to the platform running
      Lynx. The generated Lean code retains that choice when used elsewhere.

    * `node()` (`:erlang.node/0`) always returns `:nonode@nohost`. Distributed
      nodes are not modeled. Sending messages supports local PIDs and aliases;
      registered names and remote destinations are not modeled.

    * Receive timeouts do not measure wall-clock time. Positive timeouts expire
      according to the modeled scheduler's choices, or when no process can run.

    * Exception stack traces are not recorded and are represented by `[]`.

    * Map iteration order is unspecified, as in Erlang. Map generators and
      other enumerations visit each key once, but proofs cannot rely on any
      particular order.

    * Erlang's `sets` are only modeled as version 2 sets, which are maps from
      their elements to `[]`. `sets:new/0,1` and `sets:from_list/1,2` always
      create version 2 sets, ignoring any version given in their options.
      `union/2`, `intersection/2`, `subtract/2`, `is_subset/2`, and
      `is_element/2` operate on those maps directly, and do not return for
      version 1 sets or maps holding other values.

    * Function references and calls that name their module and function at
      compile time, such as `&Foo.bar/1`, `fun foo:bar/1`, and `Foo.bar(x)`,
      are translated directly. Dynamic references and calls, such as
      `&mod.bar/1`, `mod.bar(x)`, and `apply(mod, fun, args)`, only reach the
      functions the program captures by name and those declared with
      `Lynx.Case.dynamic/1`. Spawning a named function, as in
      `spawn_link(Foo, :bar, [x])`, is supported when the module and function
      are literals and the arguments a literal list.

    * Laws cannot quantify over arbitrary functions, only over the functions
      the program defines. See "Anonymous functions" below.

  Missing constructs or BIFs produce translation errors. Feel free to
  [open an issue](https://github.com/josevalim/lynx/issues) for missing functionality.

  ### Anonymous functions

  Lynx collects every anonymous function and function reference in the
  translated program, including those in dependencies, into a single table,
  `Erlang.program.fun_table`, sorted by name. A function value is a
  `Lynx.Term.function` holding the module, name, and arity the compiler gave its
  function, such as `"-make/1-fun-0-"` for an anonymous function, and its
  captured values. Invoking it calls the table entry of that name with the
  captured values followed by the arguments. Names outside the table raise
  `badfun`, and calls with the wrong number of arguments raise `badarity`, as per
  Erlang semantics.

  Anonymous functions are translated to definitions named after the compiler's
  name and the number of captures and arguments, such as `«-make/1-fun-0-/2»`,
  and captures of other modules' functions to wrappers such as
  `«lists:reverse/1»`. Each table entry has equations named after its function,
  such as `Erlang.program.«example:-make/1-fun-0-/1».pure` and `.call`, which
  state what calling it returns.

  This has several consequences for laws:

    * A function parameter ranges over every function term, not over every
      function. Calling one resolves only against the functions the program
      defines, paired with arbitrary captured values, including values the
      function's own code could never capture. A law proven for every function
      parameter therefore holds for the program's functions, and not necessarily
      for functions defined elsewhere. To reason about particular functions,
      restrict the parameter in `requires:`, for example
      `fun in [fn x -> x end, fn x -> {x} end]`.

    * The table depends on the whole program. Adding an anonymous function
      anywhere, including in a dependency or after updating Elixir or
      Erlang/OTP, changes it. Prefer proofs that hold for any table entry over
      proofs that enumerate the table, which are slower and break when it changes.

    * Invoking a function value has the purity of the most impure function in
      the table. A single function that uses the process dictionary makes every
      invocation sequential.

    * `requires:` is an Erlang expression, so it cannot assume a property of a
      function for every input. Check the property against the data the law
      uses instead, such as `Enum.all?(list, &is_boolean(fun.(&1)))`.

    * Invocations are bounded by the call depth. Pure functions consume no
      depth, and neither do calls in sequence, such as `Enum.map/2` invoking
      `fun` once per element. A function that itself invokes function values
      consumes one level for the invocations it makes. Exceeding the depth
      raises `Lynx.Exception.exhausted`, so the bound a proof chooses must
      cover the deepest nesting of invocations, which may grow with the input.

  ### Proving concurrent laws

  A concurrent law must hold under every schedule. `Lynx.Concurrent` describes
  every interleaving of a program's processes: a `Lynx.Concurrent.Step`
  advances one process, and a `Lynx.Concurrent.Run` records consecutive steps.
  Every schedule is such a run (`Lynx.concurrent_reaches`), so a law is proven
  in one of three ways:

    * Programs without races are proven from a single run, since all runs end
      alike. Two steps race when both deliver to the same process, when one
      delivers to a process whose receive the other times out, or when one
      delivers to the process the other spawns. Links, monitors, exit signals,
      and other requests to the scheduler count as races whenever another
      process can step. `Lynx.Result.Talks` rules races out when each process
      only sends to itself, its ancestors, or its own children, each receiver
      has a single sender, no receive has a timeout, and no process links,
      monitors, or makes requests; `Lynx.Concurrent.Config.RaceFree.of_talks`
      turns it into race freedom. `Lynx.concurrent_eq_advance` then evaluates
      the outcome of every schedule with `Lynx.Concurrent.Config.advance`,
      which takes the first available step, and `Config.advance_add` splits the
      run into phases that proofs can take by induction. See
      `examples/concurrency/server.exs`, which proves a law for every list.

    * Programs whose processes take the same steps for every input are proven
      by evaluating every run, as described below. See
      `examples/concurrency/workers.exs`, where two workers race.

    * Other programs are proven with an invariant preserved by every step,
      through `Lynx.concurrent_of_invariant`.

  PIDs are paths from the process that runs the law, which is `[]`: a process's
  n-th child extends its PID with `n`, so `[1]` is its first child. References
  extend the allocating process's PID with its own count. Allocation therefore
  does not depend on the schedule, while both remain opaque to the program.

  `Lynx.Concurrent.check` explores the runs of a program, up to a depth
  bounding the steps along each run, and `Lynx.concurrent_of_check` turns its
  result into the law. For example, for a law over an integer `x` that is only
  carried by messages and arithmetic:

      obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
        cases x <;> simp_all [«law:requires/1», Erlang.erlang.«is_integer/1»]
      refine ⟨1, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      have checked := Lynx.concurrent_of_check
        (Lynx.apply «law:ensures/1» Erlang.program.fun_table (depth + 1) (.integer n))
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 300
        (by cbv; simp [Rat.lt_irrefl]) schedule
      split at checked
      · assumption
      · contradiction

  The predicate accepts the outcomes the law allows, and `cbv` evaluates the
  check. Writing the depth as `depth + 1` lets evaluation take the level the
  spawned function consumes, whatever the remaining depth. The final comparison of `n * 2` with itself depends on `n`, which
  `simp` decides (`==` compares numbers as rationals, hence `Rat.lt_irrefl`).
  A few things to keep in mind:

    * Reduce the input to the shape the program needs, as `obtain` does above,
      so evaluation can select the program's branches. Evaluation covers every
      `n` at once only when no branch the processes take depends on its value.

    * A depth that is too small makes the check `false` rather than failing
      the evaluation, so the proof does not close. Increase it until every run
      ends within it.

    * Evaluation stops at comparisons it cannot decide, such as `n * 2 == n * 2`
      for a symbolic `n`, and does not explore the runs after them. Decide them
      with `simp` and resume, repeating until every run is evaluated:
      `cbv; repeat (simp only [Int.lt_irrefl, ite_false, ite_true]; cbv)`
      (`===` and `in` compare integers exactly, hence `Int.lt_irrefl`).

    * Receive timeouts with a positive duration may expire at any step, so a
      law about `Task.await/2` with a timeout must allow both outcomes. When a
      process is about to read its environment, such as its PID or process
      dictionary, the check follows only that read first: every other order
      reaches the same outcomes, as `Lynx.Concurrent.check_sound` proves.

  When a check of a closed program fails, such as a law without parameters,
  `lynx_counterexample` explains why. Run it before evaluating the check, as in
  `(by lynx_counterexample; cbv)`: it runs the program in Lean's interpreter,
  which is much faster than the kernel, and fails with a schedule the check
  rejects, one step per line, or with one that takes more steps than the
  depth. Otherwise it leaves the goal for `cbv`. It proves nothing itself.
  Traces show the first process as `<0>` and its first child as `<0.1>`, and
  references as their allocating process followed by a count, as in `#Ref<0.1>`.

  See `examples/elixir/task.exs` for laws about `Task.async/1`,
  `Task.await/2`, and `Task.ignore/1`, which link and monitor, so they are
  proven this way.

  ## Taking it to the next level

  ### Profiling proofs

  `LYNX_DEBUG=lean` reports how long each translated module and law takes to
  verify. To see where the time goes inside a proof, use
  [leanprof](https://github.com/unbalancedparentheses/leanprof). First, run your
  laws with `LYNX_DEBUG=olean`, which writes each group's translated sources,
  together with their compiled modules, to `tmp/<test module>/<group>/`:

      LYNX_DEBUG=olean mix test test/json_test.exs --only laws

  Then profile the laws module from that directory. Its imports are loaded from
  the compiled modules, so only the given file is elaborated:

      cd tmp/JsonProofsTest/laws-json-round-trip
      LEAN_PATH=$PWD:$LYNX/Lean/.lake/build/lib/lean ELAN_TOOLCHAIN=$(cat $LYNX/lean-toolchain) \\
        leanprof elab --heartbeats Elixir/JsonProofsTest/laws.lean

  where `$LYNX` is the absolute path to Lynx, such as your project's `deps/lynx`. Any
  other module in the directory, such as `Erlang/json.lean`, can be profiled
  the same way to measure the elaboration of translated code.

  `--heartbeats` counts work instead of time, so results are the same on every
  run and can be compared before and after changing a proof. The report lists
  the costliest declarations and tactics by source range, work repeated across
  goals, and the definitions and simp lemmas behind the work. Locations refer
  to the translated sources, where proofs appear verbatim as written in your laws.

  ### Independent kernel checks

  Lean's kernel checks every proof as Lynx verifies it. Lean also bundles
  independent checkers, which can check the same declarations again from an
  export of the elaborated proofs. Set `LYNX_EXPORT` to a directory when running
  laws defined with `Lynx.Case`:

      LYNX_EXPORT=tmp/export mix test --only laws

  Each laws group writes `tmp/export/<test module>/<group>.ndjson`.

  An export contains the translated modules and every declaration they depend
  on. Exporting bypasses the verification cache, and an export is written only
  when every module verifies. Check an export with Lean's kernel and every
  bundled checker:

      lake --dir deps/lynx/Lean check --paranoid --from-export tmp/export/MyTest/my-group.ndjson

  The command also rejects axioms other than `propext`, `Quot.sound`, and
  `Classical.choice`. It runs the checkers in a `bwrap` sandbox, available on
  Linux. Pass `--inadvisably-no-sandbox` to run them without one elsewhere.

  Some checkers bound the reduction they perform. When `con-leche` or `con-ron`
  report `fuel exhausted`, the proof relies on more computation than they allow,
  which is not a rejection. Replacing `simp` or `decide` with explicit rewrites
  where heavy computation happens usually avoids it.

  If you are using Erlang or `Lynx.Laws` directly, pass the file to write with
  the `:export` option:

      Lynx.Laws.verify([Sum], export: "tmp/export/sum.ndjson")

  """
end
