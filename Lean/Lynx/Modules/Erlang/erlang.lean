module

public import Lynx.Modules.Erlang.erlang.Guards
public import Lynx.Modules.Erlang.erlang.Process
public import Lynx.Modules.Erlang.erlang.Exceptions
public import Lynx.Modules.Erlang.erlang.Conversions
public import Lynx.Modules.Erlang.erlang.Hashing

public section

namespace Erlang.erlang

open Lynx

/-- Dynamically apply a function to an Erlang list of arguments. Internal
application uses an array and does not retain the source list encoding. It
returns `Except` when the program's function values do. -/
@[expose] def «apply/2» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m] [Dispatch m]
    (dispatcher : Dispatcher) (function arguments : Term) : m Term :=
  match Lynx.Term.properList? arguments with
  | none => throw (.error (.atom "badarg"))
  | some decoded => Dispatch.dispatch dispatcher function decoded.toArray

/-- Apply `Module:Name` to an Erlang list of arguments. Calls by name reach
the function values the program creates, such as `&Module.name/arity`, and the
targets a law declares with `dynamic`. Lean cannot load other code, so calls to
other functions do not return. -/
@[expose] def «apply/3» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m] [Dispatch m]
    (dispatcher : Dispatcher) (module name arguments : Term) : m Term :=
  match module, name, Lynx.Term.properList? arguments with
  | .atom _, .atom _, some decoded =>
    match dispatcher.resolve module name decoded.length with
    | some function => Dispatch.dispatch dispatcher function decoded.toArray
    | none => throw .exhausted
  | _, _, _ => throw (.error (.atom "badarg"))

/-- The function `fun Module:Name/Arity`. Like `apply/3`, it reaches the function
values the program creates, and does not return for others. -/
@[expose] def «make_fun/3» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m]
    (dispatcher : Dispatcher) (module name arity : Term) : m Term :=
  match module, name, arity with
  | .atom _, .atom _, .integer (.ofNat arity) =>
    match dispatcher.resolve module name arity with
    | some function => pure function
    | none => throw .exhausted
  | _, _, _ => throw (.error (.atom "badarg"))

/-- The `{Module, Name, Arity}` the compiler gave a function value, which the value
carries. -/
@[expose] def «fun_info_mfa/1» (function : Term) : Except Exception Term :=
  match function with
  | .function module name arity _ =>
    .ok (.tuple #[.atom module, .atom name, .integer arity])
  | _ => .error (.error (.atom "badarg"))

end Erlang.erlang
