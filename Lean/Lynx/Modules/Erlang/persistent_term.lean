module

public import Lynx.Term

/-! Persistent terms, which every process shares. Modeled after
`erl_bif_persistent.c` in OTP 30: lookups read the table without waiting,
while updates take turns holding the update permission. A process whose update
changes the table is suspended until the change is visible to every process,
which happens in a step of its own (`Lynx.Concurrent.State.commit`), even if
the process exits first. Keys and values compare exactly, as OTP's `EQ` does.

`get/0` and `info/0` are not modeled: the order of `get/0` follows OTP's
internal hash table, and `info/0` reports memory. -/

public section

namespace Erlang.persistent_term

open Lynx

/-- The value stored under `key`, raising `badarg` when there is none. -/
@[expose] def «get/1» (_ : Dispatcher) (key : Term) : Result :=
  .request (.persistentGet key) fun reply =>
    match reply with
    | .cons value _ => .ok value
    | _ => .error (.error (.atom "badarg"))

/-- The value stored under `key`, or `default` when there is none. -/
@[expose] def «get/2» (_ : Dispatcher) (key default : Term) : Result :=
  .request (.persistentGet key) fun reply =>
    match reply with
    | .cons value _ => .ok value
    | _ => .ok default

/-- Store `value` under `key`, returning `ok` once every process sees it. -/
@[expose] def «put/2» (_ : Dispatcher) (key value : Term) : Result :=
  .request (.persistentPut key value false) .ok

/-- Store `value` under `key` unless another value is stored there, which
raises `badarg`. -/
@[expose] def «put_new/2» (_ : Dispatcher) (key value : Term) : Result :=
  .request (.persistentPut key value true) fun reply =>
    match reply with
    | .atom "badarg" => .error (.error (.atom "badarg"))
    | reply => .ok reply

/-- Erase `key`, returning whether it was stored, once every process sees it erased. -/
@[expose] def «erase/1» (_ : Dispatcher) (key : Term) : Result :=
  .request (.persistentErase key) .ok

end Erlang.persistent_term
