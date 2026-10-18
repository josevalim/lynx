module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.guard_patterns

section

set_option «match».ignoreUnusedAlts true

def «integer/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.integer _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «float/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.float _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «atom/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.atom _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «tuple/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.tuple _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «map/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.map _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «bitstring/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.bitstring _ _ _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «binary/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.bitstring _ 0 _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «pid/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.pid _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «reference/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.reference _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «function/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vX@(Lynx.Term.function _ _ _) => pure vX
  | _2 => pure (Lynx.Term.atom "no")

def «conjunction/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | «v@r0»@(Lynx.Term.tuple ⟨[vX@(Lynx.Term.integer _), vY@(Lynx.Term.map _)]⟩) => pure «v@r0»
  | _4 => pure (Lynx.Term.atom "no")

def «nested/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0 with
      | Lynx.Term.tuple ⟨[Lynx.Term.atom "tag", Lynx.Term.cons lynxMap169 Lynx.Term.nil]⟩ =>
        match (Lynx.Term.getMapKeys [Lynx.Term.atom "a"] lynxMap169) with
        | [vX@(Lynx.Term.bitstring _ 0 _)] => pure vX
        | _ => lynxMatchNext ()
      | _0 => lynxMatchNext ())
    (fun (_ : Unit) =>
      match _0 with
      | _2 => pure (Lynx.Term.atom "no"))

def «conflict/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0 with
      | Lynx.Term.tuple ⟨[vX@(Lynx.Term.integer _)]⟩ =>
        Lynx.Except.guard
          (do
            let _2 ← Erlang.erlang.«is_float/1» vX
            Erlang.erlang.«and/2» (Lynx.Term.atom "true") _2)
          (fun _ => pure vX) lynxMatchNext
      | _0 => lynxMatchNext ())
    (fun (_ : Unit) =>
      match _0 with
      | _4 => pure (Lynx.Term.atom "no"))

def «repeated/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0 with
      | Lynx.Term.tuple ⟨[vX@(Lynx.Term.integer _), _2]⟩ =>
        Lynx.Except.guard
          (do
            let _3 ← Erlang.erlang.«=:=/2» _2 vX
            Erlang.erlang.«and/2» _3 (Lynx.Term.atom "true"))
          (fun _ => pure vX) lynxMatchNext
      | _0 => lynxMatchNext ())
    (fun (_ : Unit) =>
      match _0 with
      | _5 => pure (Lynx.Term.atom "no"))

def «negated/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0 with
      | vX =>
        Lynx.Except.guard
          (do
            let _1 ← Erlang.erlang.«is_integer/1» _0
            Erlang.erlang.«not/1» _1)
          (fun _ => pure vX) lynxMatchNext)
    (fun (_ : Unit) =>
      match _0 with
      | _3 => pure (Lynx.Term.atom "no"))

def «disjunction/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0, _1 with
      | Lynx.Term.tuple ⟨[vX@(Lynx.Term.integer _)]⟩, vY =>
        Lynx.Except.guard
          (Lynx.Except.tryWith
            (do
              let _5 ←
                Lynx.Except.orElse (Erlang.erlang.«is_integer/1» vY) (Erlang.erlang.«is_map/1» vY)
              let _6 ← Erlang.erlang.«=:=/2» _5 (Lynx.Term.atom "true")
              Erlang.erlang.«and/2» (Lynx.Term.atom "true") _6)
            (fun vTry => pure vTry)
            (fun lynxException =>
              let vT := Lynx.Exception.classTerm lynxException
              let vR := Lynx.Exception.reason lynxException
              pure (Lynx.Term.atom "false")))
          (fun _ => pure vX) lynxMatchNext
      | _0, _1 => lynxMatchNext ())
    (fun (_ : Unit) =>
      match _0, _1 with
      | _9, _10 => pure (Lynx.Term.atom "no"))

def «chain/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0 with
      | vX =>
        Lynx.Except.guard
          (Except.ok
            (Lynx.Term.isMember _0 [Lynx.Term.integer 1, Lynx.Term.integer 2, Lynx.Term.integer 3]))
          (fun _ => pure (Lynx.Term.atom "yes")) lynxMatchNext)
    (fun (_ : Unit) =>
      match _0 with
      | _7 => pure (Lynx.Term.atom "no"))

def «names/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0 with
      | vX =>
        Lynx.Except.guard
          (Except.ok
            (Lynx.Term.isMember _0
              [Lynx.Term.atom "ok", Lynx.Term.atom "error",
                Lynx.Term.bitstring ⟨#[120]⟩ 0 (by decide)]))
          (fun _ => pure (Lynx.Term.atom "yes")) lynxMatchNext)
    (fun (_ : Unit) =>
      match _0 with
      | _7 => pure (Lynx.Term.atom "no"))

def «numbers/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _0 with
      | vX =>
        Lynx.Except.guard
          (Lynx.Except.orElse (Erlang.erlang.«==/2» _0 (Lynx.Term.integer 1))
            (Erlang.erlang.«==/2» _0 (Lynx.Term.integer 2)))
          (fun _ => pure (Lynx.Term.atom "yes")) lynxMatchNext)
    (fun (_ : Unit) =>
      match _0 with
      | _5 => pure (Lynx.Term.atom "no"))

def «short_circuit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let _8 ←
    Lynx.Except.orElse (Erlang.erlang.«=:=/2» _0 (Lynx.Term.integer 0)) do
        let _6 ← Erlang.erlang.«length/1» _1
        Erlang.erlang.«>/2» _6 (Lynx.Term.integer 0)
  let _4 ← Lynx.Except.andAlso (Erlang.erlang.«is_list/1» _0) (pure _1)
  pure (Lynx.Term.tuple #[_8, _4])

def «outer/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  (fun {lynxValue : Type}
        (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
        (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
      lynxBody lynxNext)
    (fun lynxMatchNext =>
      match _1 with
      | Lynx.Term.tuple ⟨[vZ]⟩ =>
        Lynx.Except.guard (Erlang.erlang.«is_integer/1» _0) (fun _ => pure vZ) lynxMatchNext
      | _1 => lynxMatchNext ())
    (fun (_ : Unit) =>
      match _1 with
      | _5 => pure (Lynx.Term.atom "no"))

end

end Erlang.guard_patterns
