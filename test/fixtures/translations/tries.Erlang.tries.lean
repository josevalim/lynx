module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.tries

#lynx_pure
  def «caught/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1))
      (fun _1 => pure (Lynx.Term.tuple #[Lynx.Term.atom "ok", _1]))
      (fun _3 =>
        let _5 := Lynx.Exception.classTerm _3
        let _4 := Lynx.Exception.reason _3
        do
        let vS ← Lynx.Result.ok (Lynx.Exception.stacktrace _3)
        pure (Lynx.Term.tuple #[_5, _4, vS]))

#lynx_pure
  def «scope/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1))
      (fun _1 =>
        Lynx.Result.error (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "body", _1])))
      (fun _3 =>
        let _5 := Lynx.Exception.classTerm _3
        let _4 := Lynx.Exception.reason _3
        pure (Lynx.Term.atom "caught"))

#lynx_pure
  def «handler_scope/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)) (fun _1 => pure _1)
      (fun _2 =>
        let _4 := Lynx.Exception.classTerm _2
        let _3 := Lynx.Exception.reason _2
        Lynx.Result.error (Lynx.Exception.throw (Lynx.Term.atom "handler")))

#lynx_pure
  def «selective_catch/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)) (fun _1 => pure _1)
      (fun _2 =>
        let _4 := Lynx.Exception.classTerm _2
        let _3 := Lynx.Exception.reason _2
        match _4, _3, _2 with
        | Lynx.Term.atom "throw", vR, _6 => pure (Lynx.Term.tuple #[Lynx.Term.atom "throw", vR])
        | _7, _8, _9 => Lynx.Result.error (Lynx.Exception.withReason _9 _8))

#lynx_pure
  def «guarded_catch/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Lynx.Result.error (Lynx.Exception.error _0)) (fun _1 => pure _1)
      (fun _2 =>
        let _4 := Lynx.Exception.classTerm _2
        let _3 := Lynx.Exception.reason _2
        (fun lynxMatchNext =>
            match _4, _3, _2 with
            | Lynx.Term.atom "error", vR, _8 =>
              Lynx.Result.tryWith
                (do
                  let _5 ← Erlang.erlang.«is_integer/1» vR
                  let _6 ← Erlang.erlang.«>/2» vR (Lynx.Term.integer 0)
                  Erlang.erlang.«and/2» _5 _6)
                (fun lynxGuardValue =>
                  match lynxGuardValue with
                  | Lynx.Term.atom "true" => pure (Lynx.Term.atom "positive")
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ())
            | _, _, _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            match _4, _3, _2 with
            | _9, _10, _11 => pure (Lynx.Term.atom "other")))

#lynx_pure
  def «reraised/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)) (fun _1 => pure _1)
      (fun _2 =>
        let _4 := Lynx.Exception.classTerm _2
        let _3 := Lynx.Exception.reason _2
        match _4, _3, _2 with
        | Lynx.Term.atom "error", vR, _6 => Lynx.Result.error (Lynx.Exception.error vR)
        | _7, _8, _9 => Lynx.Result.error (Lynx.Exception.withReason _9 _8))

def «after_effect/1» (_0 : Lynx.Term) : Lynx.Result :=
  Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1))
    (fun _2 => do
      let _ ← Erlang.erlang.«put/2» (Lynx.Term.atom "key") (Lynx.Term.atom "done")
      pure _2)
    (fun _3 =>
      let _5 := Lynx.Exception.classTerm _3
      let _4 := Lynx.Exception.reason _3
      do
      let _ ← Erlang.erlang.«put/2» (Lynx.Term.atom "key") (Lynx.Term.atom "done")
      Lynx.Result.error (Lynx.Exception.withReason _3 _4))

#lynx_pure
  def «after_raises/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1))
      (fun _2 => Lynx.Result.error (Lynx.Exception.exit (Lynx.Term.atom "cleanup")))
      (fun _3 =>
        let _5 := Lynx.Exception.classTerm _3
        let _4 := Lynx.Exception.reason _3
        Lynx.Result.error (Lynx.Exception.exit (Lynx.Term.atom "cleanup")))

#lynx_pure
  def «success_clause/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1))
      (fun _1 =>
        match _1 with
        | Lynx.Term.integer 2 => pure (Lynx.Term.atom "yes")
        | _2 =>
          Lynx.Result.error
            (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "try_clause", _2])))
      (fun _3 =>
        let _5 := Lynx.Exception.classTerm _3
        let _4 := Lynx.Exception.reason _3
        pure (Lynx.Term.atom "caught"))

def «dynamic/1» (_0 : Lynx.Term) : Lynx.Result :=
  Lynx.Result.tryWith (Lynx.Term.apply _0 #[])
    (fun _1 => pure (Lynx.Term.tuple #[Lynx.Term.atom "ok", _1]))
    (fun _3 =>
      let _5 := Lynx.Exception.classTerm _3
      let _4 := Lynx.Exception.reason _3
      pure (Lynx.Term.tuple #[_5, _4]))

def «effectful/0» : Lynx.Result :=
  Lynx.Result.tryWith
    (do
      let _ ← Erlang.erlang.«put/2» (Lynx.Term.atom "key") (Lynx.Term.atom "protected")
      Lynx.Result.error (Lynx.Exception.throw (Lynx.Term.atom "failure")))
    (fun _0 => pure _0)
    (fun _1 =>
      let _3 := Lynx.Exception.classTerm _1
      let _2 := Lynx.Exception.reason _1
      do
      let _4 ← Erlang.erlang.«get/1» (Lynx.Term.atom "key")
      pure (Lynx.Term.tuple #[_3, _2, _4]))

#lynx_pure
  def «nested/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.tryWith («scope/1» _0) (fun _1 => pure _1)
      (fun _2 =>
        let _4 := Lynx.Exception.classTerm _2
        let _3 := Lynx.Exception.reason _2
        pure (Lynx.Term.tuple #[_4, _3]))

end Erlang.tries
