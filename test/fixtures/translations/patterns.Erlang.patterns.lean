module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.patterns

#lynx_pure
  def «grouped/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.atom "a" => pure (Lynx.Term.atom "first")
    | Lynx.Term.atom "b" => pure (Lynx.Term.atom "second")
    | _ =>
      (fun lynxMatchNext =>
          match _0 with
          | Lynx.Term.cons (Lynx.Term.atom "c") vX =>
            Lynx.Result.tryWith (Erlang.erlang.«is_integer/1» vX)
              (fun lynxGuardValue =>
                match lynxGuardValue with
                | Lynx.Term.atom "true" => pure (Lynx.Term.atom "guarded")
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ())
          | _ => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _0 with
          | Lynx.Term.cons (Lynx.Term.atom "c") _2 => pure (Lynx.Term.atom "rejected")
          | _3 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «map_grouped/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxLabel_map_group_34 =>
        (fun lynxMatchNext =>
            match _0 with
            | lynxMap76 =>
              match (Lynx.Term.getMapKeys [Lynx.Term.atom "a", Lynx.Term.atom "b"] lynxMap76) with
              | [lynxMapGroup34_0, lynxMapGroup34_1] =>
                (fun lynxMatchNext =>
                    match lynxMapGroup34_0, lynxMapGroup34_1 with
                    | Lynx.Term.integer 0, vB =>
                      Lynx.Result.tryWith (Erlang.erlang.«is_integer/1» vB)
                        (fun lynxGuardValue =>
                          match lynxGuardValue with
                          | Lynx.Term.atom "true" => pure (Lynx.Term.atom "first")
                          | _ => lynxMatchNext ())
                        (fun _ => lynxMatchNext ())
                    | _, _ => lynxMatchNext ())
                  (fun (_ : Unit) =>
                    (fun lynxMatchNext =>
                        match lynxMapGroup34_0, lynxMapGroup34_1 with
                        | Lynx.Term.integer 1, vB =>
                          Lynx.Result.tryWith (Erlang.erlang.«is_integer/1» vB)
                            (fun lynxGuardValue =>
                              match lynxGuardValue with
                              | Lynx.Term.atom "true" => pure (Lynx.Term.atom "second")
                              | _ => lynxMatchNext ())
                            (fun _ => lynxMatchNext ())
                        | _, _ => lynxMatchNext ())
                      (fun (_ : Unit) =>
                        match lynxMapGroup34_0, lynxMapGroup34_1 with
                        | _, _ => lynxLabel_map_group_34 ()))
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            match _0 with
            | _ => lynxLabel_map_group_34 ()))
      (fun (_ : Unit) =>
        (fun lynxMatchNext =>
            match _0 with
            | lynxMap39 =>
              match (Lynx.Term.getMapKeys [Lynx.Term.atom "a"] lynxMap39) with
              | [vA] => pure (Lynx.Term.tuple #[Lynx.Term.atom "second", vA])
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            (fun lynxMatchNext =>
                match _0 with
                | lynxMap48 =>
                  match
                    (Lynx.Term.getMapKeys [Lynx.Term.atom "a", Lynx.Term.atom "b"] lynxMap48) with
                  | [Lynx.Term.integer 2, vB] =>
                    Lynx.Result.tryWith (Erlang.erlang.«is_integer/1» vB)
                      (fun lynxGuardValue =>
                        match lynxGuardValue with
                        | Lynx.Term.atom "true" => pure (Lynx.Term.atom "fourth")
                        | _ => lynxMatchNext ())
                      (fun _ => lynxMatchNext ())
                  | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _0 with
                | Lynx.Term.map _ => pure (Lynx.Term.atom "map")
                | _2 => pure (Lynx.Term.atom "other"))))

#lynx_pure
  def «map_nested/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        |
        Lynx.Term.tuple
            ⟨[Lynx.Term.atom "tag", Lynx.Term.cons (vOuter@lynxMap122) Lynx.Term.nil]⟩ =>
          match (Lynx.Term.getMapKeys [Lynx.Term.atom "a"] lynxMap122) with
          | [vInner@lynxMap142] =>
            match (Lynx.Term.getMapKeys [Lynx.Term.atom "b"] lynxMap142) with
            | [vValue] =>
              Lynx.Result.tryWith (Erlang.erlang.«is_integer/1» vValue)
                (fun lynxGuardValue =>
                  match lynxGuardValue with
                  | Lynx.Term.atom "true" => pure (Lynx.Term.tuple #[vValue, vInner, vOuter])
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ())
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ()
        | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «map_duplicate/3» (_0 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _2 with
        | lynxMap155 =>
          match (Lynx.Term.getMapKeys [_0, _1] lynxMap155) with
          | [vX, Lynx.Term.tuple ⟨[Lynx.Term.atom "ok", vY]⟩] => pure (Lynx.Term.tuple #[vX, vY])
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _2 with
        | _7 => pure (Lynx.Term.atom "missing"))

#lynx_pure
  def «map_computed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun «lynxLabel_label^0» =>
        match _1 with
        | _6@(Lynx.Term.map _) => do
          let (_11, _7) ←
            Lynx.Result.tryWith (Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1))
                (fun _7 => pure (Lynx.Term.atom "true", _7))
                (fun _8 =>
                  let _10 := Lynx.Exception.classTerm _8
                  let _9 := Lynx.Exception.reason _8
                  pure (Lynx.Term.atom "false", Lynx.Term.atom "false"))
          (fun lynxMatchNext =>
                match _11, _6 with
                | Lynx.Term.atom "true", lynxMap209 =>
                  match (Lynx.Term.getMapKeys [_7] lynxMap209) with
                  | [vValue] => pure vValue
                  | _ => lynxMatchNext ()
                | _, _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _11, _6 with
                | _15, _16 => «lynxLabel_label^0» ())
        | _13 => «lynxLabel_label^0» ())
      (fun (_ : Unit) => pure (Lynx.Term.atom "missing"))

end Erlang.patterns
