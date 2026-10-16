module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.guard_patterns

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  def «integer/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.integer _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «float/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.float _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «atom/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.atom _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «tuple/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.tuple _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «map/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.map _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «bitstring/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.bitstring _ _ _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «binary/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.bitstring _ 0 _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «pid/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.pid _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «reference/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.reference _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «function/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | vX@(Lynx.Term.function _ _ _) => pure vX
    | _2 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «conjunction/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | «v@r0»@(Lynx.Term.tuple ⟨[vX@(Lynx.Term.integer _), vY@(Lynx.Term.map _)]⟩) => pure «v@r0»
    | _4 => pure (Lynx.Term.atom "no")

#lynx_pure
  def «nested/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | Lynx.Term.tuple ⟨[Lynx.Term.atom "tag", Lynx.Term.cons lynxMap169 Lynx.Term.nil]⟩ =>
          match (Lynx.Term.getMapKeys [Lynx.Term.atom "a"] lynxMap169) with
          | [vX@(Lynx.Term.bitstring _ 0 _)] => pure vX
          | _ => lynxMatchNext ()
        | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "no"))

#lynx_pure
  def «conflict/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | Lynx.Term.tuple ⟨[vX@(Lynx.Term.integer _)]⟩ =>
          Lynx.Result.tryWith
            (do
              let _2 ← Erlang.erlang.«is_float/1» vX
              Erlang.erlang.«and/2» (Lynx.Term.atom "true") _2)
            (fun lynxGuardValue =>
              match lynxGuardValue with
              | Lynx.Term.atom "true" => pure vX
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ())
        | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _4 => pure (Lynx.Term.atom "no"))

#lynx_pure
  def «repeated/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | Lynx.Term.tuple ⟨[vX@(Lynx.Term.integer _), _2]⟩ =>
          Lynx.Result.tryWith
            (do
              let _3 ← Erlang.erlang.«=:=/2» _2 vX
              Erlang.erlang.«and/2» _3 (Lynx.Term.atom "true"))
            (fun lynxGuardValue =>
              match lynxGuardValue with
              | Lynx.Term.atom "true" => pure vX
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ())
        | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _5 => pure (Lynx.Term.atom "no"))

#lynx_pure
  def «negated/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | vX =>
          Lynx.Result.tryWith
            (do
              let _1 ← Erlang.erlang.«is_integer/1» _0
              Erlang.erlang.«not/1» _1)
            (fun lynxGuardValue =>
              match lynxGuardValue with
              | Lynx.Term.atom "true" => pure vX
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _3 => pure (Lynx.Term.atom "no"))

#lynx_pure
  def «disjunction/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0, _1 with
        | Lynx.Term.tuple ⟨[vX]⟩, vY =>
          Lynx.Result.tryWith
            (Lynx.Result.tryWith
              (do
                let _2 ← Erlang.erlang.«is_integer/1» vX
                let _5 ←
                  do
                    let lynxGenerated0 ← Erlang.erlang.«is_integer/1» vY
                    match lynxGenerated0 with
                      | Lynx.Term.atom "true" => pure (Lynx.Term.atom "true")
                      | Lynx.Term.atom "false" => Erlang.erlang.«is_map/1» vY
                      | _3 =>
                        Lynx.Result.error
                          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "badarg", _3]))
                let _6 ← Erlang.erlang.«=:=/2» _5 (Lynx.Term.atom "true")
                Erlang.erlang.«and/2» _2 _6)
              (fun vTry => pure vTry)
              (fun lynxException =>
                let vT := Lynx.Exception.classTerm lynxException
                let vR := Lynx.Exception.reason lynxException
                pure (Lynx.Term.atom "false")))
            (fun lynxGuardValue =>
              match lynxGuardValue with
              | Lynx.Term.atom "true" => pure vX
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ())
        | _, _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0, _1 with
        | _9, _10 => pure (Lynx.Term.atom "no"))

#lynx_pure
  def «outer/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _1 with
        | Lynx.Term.tuple ⟨[vZ]⟩ =>
          Lynx.Result.tryWith (Erlang.erlang.«is_integer/1» _0)
            (fun lynxGuardValue =>
              match lynxGuardValue with
              | Lynx.Term.atom "true" => pure vZ
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ())
        | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "no"))

end

end Erlang.guard_patterns
