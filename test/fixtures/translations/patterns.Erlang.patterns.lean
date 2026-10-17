module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.patterns

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  def «grouped/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.atom "a" => pure (Lynx.Term.atom "first")
    | Lynx.Term.atom "b" => pure (Lynx.Term.atom "second")
    | Lynx.Term.cons (Lynx.Term.atom "c") vX@(Lynx.Term.integer _) =>
      pure (Lynx.Term.atom "guarded")
    | Lynx.Term.cons (Lynx.Term.atom "c") _2 => pure (Lynx.Term.atom "rejected")
    | _3 => pure (Lynx.Term.atom "other")

#lynx_pure
  def «map_grouped/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxLabel_map_group_33 =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match _0 with
            | lynxMap73 =>
              match (Lynx.Term.getMapKeys [Lynx.Term.atom "a", Lynx.Term.atom "b"] lynxMap73) with
              | [lynxMapGroup33_0, lynxMapGroup33_1] =>
                match lynxMapGroup33_0, lynxMapGroup33_1 with
                | Lynx.Term.integer 0, vB@(Lynx.Term.integer _) => pure (Lynx.Term.atom "first")
                | Lynx.Term.integer 1, vB@(Lynx.Term.integer _) => pure (Lynx.Term.atom "second")
                | _, _ => lynxLabel_map_group_33 ()
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            match _0 with
            | _ => lynxLabel_map_group_33 ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match _0 with
            | lynxMap38 =>
              match (Lynx.Term.getMapKeys [Lynx.Term.atom "a"] lynxMap38) with
              | [vA] => pure (Lynx.Term.tuple #[Lynx.Term.atom "second", vA])
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match _0 with
                | lynxMap48 =>
                  match
                    (Lynx.Term.getMapKeys [Lynx.Term.atom "a", Lynx.Term.atom "b"] lynxMap48) with
                  | [Lynx.Term.integer 2, vB@(Lynx.Term.integer _)] =>
                    pure (Lynx.Term.atom "fourth")
                  | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _0 with
                | Lynx.Term.map _ => pure (Lynx.Term.atom "map")
                | _2 => pure (Lynx.Term.atom "other"))))

#lynx_pure
  def «map_nested/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        |
        Lynx.Term.tuple
            ⟨[Lynx.Term.atom "tag", Lynx.Term.cons (vOuter@lynxMap116) Lynx.Term.nil]⟩ =>
          match (Lynx.Term.getMapKeys [Lynx.Term.atom "a"] lynxMap116) with
          | [vInner@lynxMap122] =>
            match (Lynx.Term.getMapKeys [Lynx.Term.atom "b"] lynxMap122) with
            | [vValue@(Lynx.Term.integer _)] => pure (Lynx.Term.tuple #[vValue, vInner, vOuter])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ()
        | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «map_duplicate/3» (_0 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _2 with
        | lynxMap147 =>
          match (Lynx.Term.getMapKeys [_0, _1] lynxMap147) with
          | [vX, Lynx.Term.tuple ⟨[Lynx.Term.atom "ok", vY]⟩] => pure (Lynx.Term.tuple #[vX, vY])
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _2 with
        | _7 => pure (Lynx.Term.atom "missing"))

#lynx_pure
  def «map_computed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
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
          (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match _11, _6 with
                | Lynx.Term.atom "true", lynxMap200 =>
                  match (Lynx.Term.getMapKeys [_7] lynxMap200) with
                  | [vValue] => pure vValue
                  | _ => lynxMatchNext ()
                | _, _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _11, _6 with
                | _15, _16 => «lynxLabel_label^0» ())
        | _13 => «lynxLabel_label^0» ())
      (fun (_ : Unit) => pure (Lynx.Term.atom "missing"))

#lynx_pure
  def «floats/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.integer 1 => pure (Lynx.Term.atom "integer")
    | Lynx.Term.float ⟨Bool.false, 1023, 0⟩ => pure (Lynx.Term.atom "float")
    | Lynx.Term.float ⟨Bool.false, 0, 0⟩ => pure (Lynx.Term.atom "positive_zero")
    | Lynx.Term.float ⟨Bool.true, 0, 0⟩ => pure (Lynx.Term.atom "negative_zero")
    | Lynx.Term.float ⟨Bool.true, 1023, 2251799813685248⟩ => pure (Lynx.Term.atom "negative")
    |
    Lynx.Term.tuple
        ⟨[Lynx.Term.float ⟨Bool.false, 1019, 2702159776422298⟩,
            Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 0, 1⟩) Lynx.Term.nil]⟩ =>
      pure (Lynx.Term.atom "nested")
    | _ =>
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          match _0 with
          | lynxMap248 =>
            match (Lynx.Term.getMapKeys [Lynx.Term.float ⟨Bool.false, 1023, 0⟩] lynxMap248) with
            | [Lynx.Term.float ⟨Bool.false, 1023, 2251799813685248⟩] => pure (Lynx.Term.atom "map")
            | _ => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _0 with
          | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «map_fallthrough/2» (vValue : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxLabel_map_group_263 =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match _1 with
            | lynxMap274 =>
              match (Lynx.Term.getMapKeys [Lynx.Term.atom "b"] lynxMap274) with
              | [vB] =>
                Lynx.Result.guard (Erlang.erlang.«/=/2» vB (Lynx.Term.integer 1))
                  (fun _ => pure (Lynx.Term.atom "b")) lynxMatchNext
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match _1 with
                | lynxMap282 =>
                  match (Lynx.Term.getMapKeys [Lynx.Term.atom "a"] lynxMap282) with
                  | [lynxMapGroup263_0] =>
                    (fun {lynxValue : Type}
                          (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                          (lynxNext : Unit → Lynx.Result lynxValue) =>
                        lynxBody lynxNext)
                      (fun lynxMatchNext =>
                        match lynxMapGroup263_0 with
                        | vA =>
                          Lynx.Result.guard (Erlang.erlang.«</2» vA (Lynx.Term.integer 0))
                            (fun _ => pure vValue) lynxMatchNext)
                      (fun (_ : Unit) =>
                        match lynxMapGroup263_0 with
                        | vA => pure vA
                        | _ => lynxLabel_map_group_263 ())
                  | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _1 with
                | _ => lynxLabel_map_group_263 ())))
      (fun (_ : Unit) =>
        match _1 with
        | _2 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause")))

end

end Erlang.patterns
