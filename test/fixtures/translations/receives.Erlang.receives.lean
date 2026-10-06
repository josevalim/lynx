module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.receives

def «plain/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.atom "infinity")
    (fun (_lynxReceiveEnv : Lynx.Environment) (_0 : Lynx.Term) =>
      (match _0 with
        | _0 => Option.some _0 :
        Option Lynx.Term))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | _0 => pure _0
      | Option.none => pure (Lynx.Term.atom "true"))

def «selective/1» (_0 : Lynx.Term) : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.atom "infinity")
    (fun (_lynxReceiveEnv : Lynx.Environment) (_3 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) =>
          (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option (Sum Lynx.Term Unit))
            match _3 with
            | Lynx.Term.atom "stop" => Option.some (Sum.inr ())
            | _ => lynxReceiveNext () :
            Option (Sum Lynx.Term Unit))
        match _3 with
        | Lynx.Term.tuple #[_2, vX] =>
          match
            (Lynx.Result.toExceptRead (Erlang.erlang.«=:=/2» _2 _0) _lynxReceiveEnv
              (by simp (config := { maxDischargeDepth := 64 }))) with
          | Except.ok (Lynx.Term.atom "true") => Option.some (Sum.inl vX)
          | _ => lynxReceiveNext ()
        | _ => lynxReceiveNext () :
        Option (Sum Lynx.Term Unit)))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | Sum.inl vX => pure vX
        | Sum.inr () => pure (Lynx.Term.atom "done")
      | Option.none => pure (Lynx.Term.atom "true"))

def «guarded/1» (_0 : Lynx.Term) : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.atom "infinity")
    (fun (_lynxReceiveEnv : Lynx.Environment) (_12 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) =>
          (let lynxReceiveNext := fun (_ : Unit) =>
              (let lynxReceiveNext := fun (_ : Unit) =>
                  (let lynxReceiveNext := fun (_ : Unit) =>
                      (Option.none : Option (Sum Lynx.Term (Sum Lynx.Term (Sum Lynx.Term Unit))))
                    match _12 with
                    | Lynx.Term.atom "stop" => Option.some (Sum.inr (Sum.inr (Sum.inr ())))
                    | _ => lynxReceiveNext () :
                    Option (Sum Lynx.Term (Sum Lynx.Term (Sum Lynx.Term Unit))))
                match _12 with
                | Lynx.Term.tuple #[_11, vX] =>
                  match
                    (Lynx.Result.toExceptRead (Erlang.erlang.«=:=/2» _11 _0) _lynxReceiveEnv
                      (by simp (config := { maxDischargeDepth := 64 }))) with
                  | Except.ok (Lynx.Term.atom "true") =>
                    Option.some (Sum.inr (Sum.inr (Sum.inl vX)))
                  | _ => lynxReceiveNext ()
                | _ => lynxReceiveNext () :
                Option (Sum Lynx.Term (Sum Lynx.Term (Sum Lynx.Term Unit))))
            match _12 with
            | Lynx.Term.tuple #[_8, vX] =>
              match
                (Lynx.Result.toExceptRead
                  (do
                    let _9 ← Erlang.erlang.«=:=/2» _8 _0
                    let _10 ←
                      do
                        let _2 ← Erlang.erlang.«is_integer/1» vX
                        let _3 ← Erlang.erlang.«>/2» vX (Lynx.Term.integer 0)
                        Erlang.erlang.«and/2» _2 _3
                    Erlang.erlang.«and/2» _9 _10)
                  _lynxReceiveEnv (by simp (config := { maxDischargeDepth := 64 }))) with
              | Except.ok (Lynx.Term.atom "true") => Option.some (Sum.inr (Sum.inl vX))
              | _ => lynxReceiveNext ()
            | _ => lynxReceiveNext () :
            Option (Sum Lynx.Term (Sum Lynx.Term (Sum Lynx.Term Unit))))
        match _12 with
        | Lynx.Term.tuple #[_5, vX] =>
          match
            (Lynx.Result.toExceptRead
              (do
                let _6 ← Erlang.erlang.«=:=/2» _5 _0
                let _7 ←
                  Lynx.Result.tryWith
                      (do
                        let _1 ← Erlang.erlang.«byte_size/1» vX
                        Erlang.erlang.«==/2» _1 (Lynx.Term.integer 1))
                      (fun vTry => pure vTry)
                      (fun lynxException =>
                        let vT := Lynx.Exception.classTerm lynxException
                        let vR := Lynx.Exception.reason lynxException
                        pure (Lynx.Term.atom "false"))
                Erlang.erlang.«and/2» _6 _7)
              _lynxReceiveEnv (by simp (config := { maxDischargeDepth := 64 }))) with
          | Except.ok (Lynx.Term.atom "true") => Option.some (Sum.inl vX)
          | _ => lynxReceiveNext ()
        | _ => lynxReceiveNext () :
        Option (Sum Lynx.Term (Sum Lynx.Term (Sum Lynx.Term Unit)))))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | Sum.inl vX => pure (Lynx.Term.tuple #[Lynx.Term.atom "first", vX])
        | Sum.inr (Sum.inl vX) => pure (Lynx.Term.tuple #[Lynx.Term.atom "second", vX])
        | Sum.inr (Sum.inr (Sum.inl vX)) => pure (Lynx.Term.tuple #[Lynx.Term.atom "fallback", vX])
        | Sum.inr (Sum.inr (Sum.inr ())) => pure (Lynx.Term.atom "done")
      | Option.none => pure (Lynx.Term.atom "true"))

def «self_guard/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.atom "infinity")
    (fun (_lynxReceiveEnv : Lynx.Environment) (_1 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option Lynx.Term)
        match _1 with
        | Lynx.Term.tuple #[vPid, vX] =>
          match
            (Lynx.Result.toExceptRead
              (Lynx.Result.tryWith
                (do
                  let _0 ← Erlang.erlang.«self/0»
                  Erlang.erlang.«=:=/2» vPid _0)
                (fun vTry => pure vTry)
                (fun lynxException =>
                  let vT := Lynx.Exception.classTerm lynxException
                  let vR := Lynx.Exception.reason lynxException
                  pure (Lynx.Term.atom "false")))
              _lynxReceiveEnv (by simp (config := { maxDischargeDepth := 64 }))) with
          | Except.ok (Lynx.Term.atom "true") => Option.some vX
          | _ => lynxReceiveNext ()
        | _ => lynxReceiveNext () :
        Option Lynx.Term))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | vX => pure vX
      | Option.none => pure (Lynx.Term.atom "true"))

def «poll/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.integer 0)
    (fun (_lynxReceiveEnv : Lynx.Environment) (_0 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option Lynx.Term)
        match _0 with
        | Lynx.Term.tuple #[Lynx.Term.atom "ok", vX] => Option.some vX
        | _ => lynxReceiveNext () :
        Option Lynx.Term))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | vX => pure vX
      | Option.none => pure (Lynx.Term.atom "timeout"))

def «timed/1» (_0 : Lynx.Term) : Lynx.Result :=
  Lynx.Result.receiveWith _0
    (fun (_lynxReceiveEnv : Lynx.Environment) (_2 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option Lynx.Term)
        match _2 with
        | Lynx.Term.tuple #[Lynx.Term.atom "ok", vX] => Option.some vX
        | _ => lynxReceiveNext () :
        Option Lynx.Term))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | vX => pure vX
      | Option.none => pure (Lynx.Term.atom "timeout"))

def «sleep/1» (_0 : Lynx.Term) : Lynx.Result :=
  Lynx.Result.receiveWith _0
    (fun (_ : Lynx.Environment) (_ : Lynx.Term) => (Option.none : Option Empty))
    (fun
      | Option.some lynxReceived => nomatch lynxReceived
      | Option.none => pure (Lynx.Term.atom "done"))

def «computed/1» (_0 : Lynx.Term) : Lynx.Result := do
  let _2 ← Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)
  Lynx.Result.receiveWith _2
      (fun (_lynxReceiveEnv : Lynx.Environment) (_3 : Lynx.Term) =>
        (match _3 with
          | _3 => Option.some _3 :
          Option Lynx.Term))
      (fun
        | Option.some lynxReceived =>
          match lynxReceived with
          | _3 => pure _3
        | Option.none => pure (Lynx.Term.atom "timeout"))

def «nested/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.atom "infinity")
    (fun (_lynxReceiveEnv : Lynx.Environment) (_4 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) =>
          (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option (Sum Lynx.Term Unit))
            match _4 with
            | Lynx.Term.atom "stop" => Option.some (Sum.inr ())
            | _ => lynxReceiveNext () :
            Option (Sum Lynx.Term Unit))
        match _4 with
        | Lynx.Term.tuple #[Lynx.Term.atom "ok", vX] => Option.some (Sum.inl vX)
        | _ => lynxReceiveNext () :
        Option (Sum Lynx.Term Unit)))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | Sum.inl vX =>
          Lynx.Result.receiveWith (Lynx.Term.integer 0)
            (fun (_lynxReceiveEnv : Lynx.Environment) (_1 : Lynx.Term) =>
              (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option Unit)
                match _1 with
                | _0 =>
                  match
                    (Lynx.Result.toExceptRead (Erlang.erlang.«=:=/2» _1 vX) _lynxReceiveEnv
                      (by simp (config := { maxDischargeDepth := 64 }))) with
                  | Except.ok (Lynx.Term.atom "true") => Option.some ()
                  | _ => lynxReceiveNext () :
                Option Unit))
            (fun
              | Option.some lynxReceived =>
                match lynxReceived with
                | () => pure (Lynx.Term.atom "yes")
              | Option.none => pure (Lynx.Term.atom "no"))
        | Sum.inr () => pure (Lynx.Term.atom "no")
      | Option.none => pure (Lynx.Term.atom "true"))

def «bindings/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.atom "infinity")
    (fun (_lynxReceiveEnv : Lynx.Environment) (_0 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) =>
          (let lynxReceiveNext := fun (_ : Unit) =>
              (Option.none : Option (Sum (Lynx.Term × Lynx.Term) Unit))
            match _0 with
            | Lynx.Term.atom "stop" => Option.some (Sum.inr ())
            | _ => lynxReceiveNext () :
            Option (Sum (Lynx.Term × Lynx.Term) Unit))
        match _0 with
        | Lynx.Term.tuple #[Lynx.Term.atom "pair", vX, vY] => Option.some (Sum.inl (vX, vY))
        | _ => lynxReceiveNext () :
        Option (Sum (Lynx.Term × Lynx.Term) Unit)))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | Sum.inl (vX, vY) => pure (Lynx.Term.tuple #[vX, vY])
        | Sum.inr () => pure (Lynx.Term.atom "done")
      | Option.none => pure (Lynx.Term.atom "true"))

def «repeated/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.integer 0)
    (fun (_lynxReceiveEnv : Lynx.Environment) (_1 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option Lynx.Term)
        match _1 with
        | Lynx.Term.tuple #[vX, _0] =>
          match
            (Lynx.Result.toExceptRead (Erlang.erlang.«=:=/2» _0 vX) _lynxReceiveEnv
              (by simp (config := { maxDischargeDepth := 64 }))) with
          | Except.ok (Lynx.Term.atom "true") => Option.some vX
          | _ => lynxReceiveNext ()
        | _ => lynxReceiveNext () :
        Option Lynx.Term))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | vX => pure vX
      | Option.none => pure (Lynx.Term.atom "timeout"))

def «alias/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.atom "infinity")
    (fun (_lynxReceiveEnv : Lynx.Environment) (_0 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) =>
          (Option.none : Option (Lynx.Term × Lynx.Term × Lynx.Term))
        match _0 with
        | vPair@(Lynx.Term.tuple #[Lynx.Term.atom "pair", vX, vY]) => Option.some (vPair, (vX, vY))
        | _ => lynxReceiveNext () :
        Option (Lynx.Term × Lynx.Term × Lynx.Term)))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | (vPair, (vX, vY)) => pure (Lynx.Term.tuple #[vPair, vX, vY])
      | Option.none => pure (Lynx.Term.atom "true"))

def «lists/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.integer 0)
    (fun (_lynxReceiveEnv : Lynx.Environment) (_0 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) =>
          (Option.none : Option (Lynx.Term × Lynx.Term × Lynx.Term))
        match _0 with
        | Lynx.Term.cons vX (Lynx.Term.cons vY vRest) => Option.some (vRest, (vX, vY))
        | _ => lynxReceiveNext () :
        Option (Lynx.Term × Lynx.Term × Lynx.Term)))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | (vRest, (vX, vY)) => pure (Lynx.Term.tuple #[vX, vY, vRest])
      | Option.none => pure (Lynx.Term.atom "timeout"))

def «alternatives/0» : Lynx.Result :=
  Lynx.Result.receiveWith (Lynx.Term.integer 0)
    (fun (_lynxReceiveEnv : Lynx.Environment) (_3 : Lynx.Term) =>
      (let lynxReceiveNext := fun (_ : Unit) => (Option.none : Option Lynx.Term)
        match _3 with
        | vX =>
          match
            (Lynx.Result.toExceptRead
              (do
                let _1 ←
                  do
                    let _0 ← Erlang.erlang.«is_integer/1» _3
                    Erlang.erlang.«not/1» _0
                let _2 ← Erlang.erlang.«>/2» _3 (Lynx.Term.integer 0)
                Erlang.erlang.«or/2» _1 _2)
              _lynxReceiveEnv (by simp (config := { maxDischargeDepth := 64 }))) with
          | Except.ok (Lynx.Term.atom "true") => Option.some vX
          | _ => lynxReceiveNext () :
        Option Lynx.Term))
    (fun
      | Option.some lynxReceived =>
        match lynxReceived with
        | vX => pure vX
      | Option.none => pure (Lynx.Term.atom "timeout"))

def «sequence/0» : Lynx.Result := do
  let _ ←
    Lynx.Result.receiveWith (Lynx.Term.integer 0)
        (fun (_ : Lynx.Environment) (_ : Lynx.Term) => (Option.none : Option Empty))
        (fun
          | Option.some lynxReceived => nomatch lynxReceived
          | Option.none => pure (Lynx.Term.atom "ok"))
  Lynx.Result.receiveWith (Lynx.Term.integer 0)
      (fun (_ : Lynx.Environment) (_ : Lynx.Term) => (Option.none : Option Empty))
      (fun
        | Option.some lynxReceived => nomatch lynxReceived
        | Option.none => pure (Lynx.Term.atom "done"))

end Erlang.receives
