# Semantic translation nodes

The Core translator emits Erlang values and computations. `Lean/Lynx/Runner.lean`
assembles their Lean syntax; JSON uses semantic nodes instead of Lean constructor
calls or quoted function names. Module qualification remains on the producer side.
The request version remains `1.0`.

Every node carries `kind` and `span`. A span is `[]`, `[line]`, or `[line, column]`,
using one-based Unicode character positions. An empty span inherits its enclosing
location. Match cases and table entries carry spans too.

## Values and patterns

| Kind | Additional fields | Meaning |
| --- | --- | --- |
| `var` | `name` | Original Core variable name: a nonnegative integer temporary or a string source name. |
| `integer` | `value` | Erlang integer, including negative and arbitrary-precision values. |
| `atom` | `value` | Atom spelling as a UTF-8 string. |
| `nil` | — | Empty Erlang list. |
| `cons` | `head`, `tail` | List cell; both fields are value nodes. Improper tails are preserved. |
| `function` | `id`, `arity`, `captures` | Closure with a program-wide ID, source arity, and captured value nodes. |
| `wildcard` | — | Anonymous pattern, accepted only in patterns. |

The decoder constructs `Term` values. Integer variable names become `_N`; string
names become `vName`, or `_vName` when the original name starts with `_`. This
keeps compiler temporaries distinct from source variables. Lean performs identifier
escaping, including names containing punctuation or reserved words.

## Computations

| Kind | Additional fields | Meaning |
| --- | --- | --- |
| `local_call` | `name`, `args` | Direct call in the current module; arguments are value nodes. |
| `remote_call` | `module`, `name`, `args` | Direct call to a qualified module and raw function name. |
| `fun_call` | `function`, `args` | Apply a function value using `Term.apply` and a native argument array. |
| `bind` | `var`, `computation`, `body` | Bind a computation's successful result to a `var` node, then execute the body. |
| `return` | `value` | Successful computation returning a value node. |
| `raise` | `class`, `reason` | Exception; class is `error`, `throw`, or `exit`, and reason is a value node. |
| `match` | `expressions`, `cases` | Match value nodes against cases with `patterns`, `body`, and `span`. |

Each match case has one pattern per expression. Zero expressions and zero patterns
are valid: the decoder supplies Lean's unit match for a zero-argument Core case.
Computation nodes are rejected in patterns.

Calls acquire their `/arity` suffix from the number of arguments, including zero.
The producer qualifies module names as `Erlang.foo` or `Elixir.Foo`.
The decoder uses those names directly.
Explicit `erlang:apply/2` remains a remote call; dynamic application is a distinct
node. Only the decoder chooses `Result.bind`, `Result.ok`, and exception constructors.

## Declarations

| Kind | Additional fields | Meaning |
| --- | --- | --- |
| `def` | `name`, `params`, `body`, `pure` | Function with a raw name, `var` parameters, and a computation body. Arity comes from the parameter count. |
| `mutual` | `defs`, `pure` | Nonempty group of mutually recursive definitions. |
| `fun_table` | `name`, `entries` | Program function table and its generated application equations. |

Every definition and mutual group has a Boolean `pure` field. `true` causes the
decoder to invoke `#lynx_pure`; it is a claim checked by Lean, not a trusted fact.
Definitions inside a mutual group agree with its flag, and the decoder generates
one joint purity proof for the group. `false` emits ordinary definitions.

Table entries have `body`, `captures`, `args`, `pure`, and `span`. Captures and
arguments are arrays of `var` binders. The body calls the implementation with the
captures preceding the arguments. Pure adapters require checked purity proofs;
the flag is not trusted. Application lemmas are generated for both pure and
effectful entries, preserving the caller's depth in continuations.

Input files have `file`, `module`, `imports`, and `contents`. Module and import
names are already qualified by the producer; files arrive in dependency order.
The generated table uses module `Erlang.program`. The runner emits those supplied
namespaces and imports.

## Regenerating fixtures

From the project root:

```sh
mix run test/fixtures/translations/regenerate.exs json
mix run test/fixtures/translations/regenerate.exs lean
```

`json` compiles each Erlang fixture with debug information and translates its
exports and reachable callees. `lean` builds the runtime and renders the checked-in JSON fixtures through
the Lean runner, writing ordinary `.lean` and generated `.program.lean` snapshots.
