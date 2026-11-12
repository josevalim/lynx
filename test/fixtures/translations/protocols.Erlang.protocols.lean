module

public import Lynx
import Lynx.Runner.Elab
public import Elixir.Lynx.Support.Describe
public import Elixir.Lynx.Support.Size
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.protocols

section

set_option «match».ignoreUnusedAlts true

def «size/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Elixir.Lynx.Support.Size.«size/1» _0

def «describe/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Elixir.Lynx.Support.Describe.«describe/2» _0 _1

def «size_list_requires/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let _1 ← Erlang.erlang.«length/1» _0
  Erlang.erlang.«>=/2» _1 (Lynx.Term.integer 0)

def «size_undefined_requires/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Erlang.erlang.«is_float/1» _0

def «describe_fallback_requires/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Erlang.erlang.«is_integer/1» _0

def «size_list_ensures/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let _2 ← «size/1» _0
  let _1 ← Erlang.erlang.«length/1» _0
  Erlang.erlang.«=:=/2» _2 _1

def «size_struct_ensures/0» : Except Lynx.Exception Lynx.Term := do
  let _0 ←
    «size/1»
        (Lynx.Term.map
          [(Lynx.Term.atom "__struct__", Lynx.Term.atom "Elixir.Lynx.Support.Point"),
            (Lynx.Term.atom "y", Lynx.Term.integer 2), (Lynx.Term.atom "x", Lynx.Term.integer 1)])
  Erlang.erlang.«=:=/2» _0 (Lynx.Term.integer 2)

def «size_undefined_ensures/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Except.tryWith («size/1» _0) (fun _1 => pure (Lynx.Term.atom "false"))
    (fun _3 =>
      have _5 := Lynx.Exception.classTerm _3
      have _4 := Lynx.Exception.reason _3
      (fun {lynxValue : Type}
            (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
            (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          match _5, _4, _3 with
          | Lynx.Term.atom "error", lynxMap75, _9 =>
            match
              (Lynx.Term.getMapKeys [Lynx.Term.atom "__struct__", Lynx.Term.atom "value"]
                lynxMap75) with
            | [Lynx.Term.atom "Elixir.Protocol.UndefinedError", _8] =>
              Lynx.Except.guard (Erlang.erlang.«=:=/2» _8 _0)
                (fun _ => pure (Lynx.Term.atom "true")) lynxMatchNext
            | _ => lynxMatchNext ()
          | _5, _4, _3 => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _5, _4, _3 with
          | _11, _12, _13 => Except.error (Lynx.Exception.withReason _13 _12)))

def «describe_fallback_ensures/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let _1 ← «describe/2» _0 (Lynx.Term.atom "prefix")
  Erlang.erlang.«=:=/2» _1 (Lynx.Term.tuple #[Lynx.Term.atom "prefix", Lynx.Term.atom "any"])

end

end Erlang.protocols
