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

  The Lean source code is present in the "Lean" folder of the Lynx project. Besides
  the basic definition of Erlang terms, it also contains the implementation of Erlang
  NIFs within `Lynx/Modules/Erlang`. It may be necessary to navigate the source code
  in order to best understand the constructs when writing proofs.

  Furthermore, when running proofs with ExUnit, the error reports include the path to
  folder with all `.lean` files. Use this to debug and guide your proofs.

  ## Limitations

  Lynx models a subset of Erlang/Elixir and the Erlang runtime. Proofs describe
  this model, the following restrictions matter when interpreting their results:

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

  Lynx does not yet translate all language constructs nor implements all BIFs.
  Those will lead to errors when attempting to translate them.
  """
end
