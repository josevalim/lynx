module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.bitstring_matching

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  def «empty_or_byte/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
          (fun vX lynxBits0 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits0 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits0) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match (Lynx.Term.Bitstring.matchEnd _0) with
            | Bool.true✝ => pure (Lynx.Term.atom "empty")
            | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            match _0 with
            | _2 => pure (Lynx.Term.atom "other")))

#lynx_pure
  def «empty/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.bitstring ⟨⟨[]⟩⟩ 0 _ => pure (Lynx.Term.atom "empty")
    | _2 => pure (Lynx.Term.atom "other")

#lynx_pure
  def «literal/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.bitstring ⟨⟨[1, 2, 160]⟩⟩ ⟨3, _⟩ _ => pure (Lynx.Term.atom "matched")
    | _2 => pure (Lynx.Term.atom "other")

#lynx_pure
  def «partial_literal/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.bitstring ⟨⟨[160]⟩⟩ ⟨3, _⟩ _ => pure (Lynx.Term.atom "matched")
    | _2 => pure (Lynx.Term.atom "other")

#lynx_pure
  def «binary_literal/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.bitstring ⟨⟨[97, 98, 99]⟩⟩ 0 _ => pure (Lynx.Term.atom "matched")
    | _2 => pure (Lynx.Term.atom "other")

#lynx_pure
  def «string_literal/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.bitstring ⟨⟨[97, 98, 99]⟩⟩ 0 _ => pure (Lynx.Term.atom "matched")
    | _2 => pure (Lynx.Term.atom "other")

#lynx_pure
  def «signed_literal/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.bitstring ⟨⟨[255, 35, 1, 0]⟩⟩ 0 _ => pure (Lynx.Term.atom "matched")
    | _2 => pure (Lynx.Term.atom "other")

#lynx_pure
  def «integers/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
          (fun vA lynxBits1 =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger lynxBits1 (Lynx.Term.integer 12) 1 Bool.true
                Bool.false)
              (fun vB lynxBits2 =>
                Lynx.Term.Bitstring.extract
                  (Lynx.Term.Bitstring.matchInteger lynxBits2 (Lynx.Term.integer 12) 1 Bool.true
                    Bool.true)
                  (fun vC lynxBits3 =>
                    match (Lynx.Term.Bitstring.matchEnd lynxBits3) with
                    | Bool.true✝ => pure (Lynx.Term.tuple #[vA, vB, vC])
                    | _ => lynxMatchNext ())
                  (fun _ => lynxMatchNext ()))
              (fun _ => lynxMatchNext ()))
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «integer_sized/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun «lynxLabel_label^0» =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
              (fun vSize lynxBits4 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits4 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits4) with
                  | _3 =>
                    (fun {lynxValue : Type}
                          (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                          (lynxNext : Unit → Lynx.Result lynxValue) =>
                        lynxBody lynxNext)
                      (fun lynxMatchNext =>
                        Lynx.Term.Bitstring.extract
                          (Lynx.Term.Bitstring.matchInteger _3 vSize 1 Bool.true Bool.true)
                          (fun vX lynxBits5 =>
                            match
                              (Lynx.Term.Bitstring.matchTail lynxBits5 (Lynx.Term.atom "all")
                                1) with
                            | Bool.true✝ =>
                              match (lynxBits5) with
                              | vTail => pure (Lynx.Term.tuple #[vSize, vX, vTail])
                            | _ => lynxMatchNext ())
                          (fun _ => lynxMatchNext ()))
                      (fun (_ : Unit) =>
                        match _3 with
                        | _4 => «lynxLabel_label^0» ())
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun (_ : Unit) =>
            match _0 with
            | _5 => «lynxLabel_label^0» ()))
      (fun (_ : Unit) => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «integer_external_size/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchInteger _1 _0 3 Bool.false Bool.false)
          (fun vX lynxBits6 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits6 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits6) with
              | vTail => pure (Lynx.Term.tuple #[vX, vTail])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «float64/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchFloat _0 64 Bool.false)
          (fun vX lynxBits7 =>
            Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchFloat lynxBits7 64 Bool.true)
              (fun vY lynxBits8 =>
                match (Lynx.Term.Bitstring.matchEnd lynxBits8) with
                | Bool.true✝ => pure (Lynx.Term.tuple #[vX, vY])
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun vTag lynxBits9 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits9 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits9) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun vTag lynxBits10 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits10 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits10) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_literal_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun lynxExtracted lynxBits11 =>
            match lynxExtracted with
            | Lynx.Term.integer 1 =>
              match (Lynx.Term.Bitstring.matchTail lynxBits11 (Lynx.Term.atom "all") 8) with
              | Bool.true✝ =>
                match (lynxBits11) with
                | vTail => pure vTail
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_literal_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun lynxExtracted lynxBits12 =>
            match lynxExtracted with
            | Lynx.Term.integer 1 =>
              match (Lynx.Term.Bitstring.matchTail lynxBits12 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits12) with
                | vTail => pure vTail
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_fixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _1 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun vTag lynxBits13 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits13 _0 8) with
            | Bool.true✝ =>
              match (lynxBits13) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_fixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _1 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun vTag lynxBits14 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits14 _0 1) with
            | Bool.true✝ =>
              match (lynxBits14) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_prefix/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchBinary _1 _0 8)
          (fun vPrefix lynxBits15 =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger lynxBits15 (Lynx.Term.integer 3) 1 Bool.false
                Bool.false)
              (fun vTag lynxBits16 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits16 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits16) with
                  | vTail => pure (Lynx.Term.tuple #[vPrefix, vTag, vTail])
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «nested/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | Lynx.Term.tuple ⟨[Lynx.Term.atom "tag", Lynx.Term.cons lynxMap392 Lynx.Term.nil]⟩ =>
          match (Lynx.Term.getMapKeys [Lynx.Term.atom "bits"] lynxMap392) with
          | [lynxBits17] =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger lynxBits17 (Lynx.Term.integer 8) 1 Bool.false
                Bool.false)
              (fun vX lynxBits18 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits18 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits18) with
                  | vRest => pure (Lynx.Term.tuple #[vX, vRest])
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ())
          | _ => lynxMatchNext ()
        | _0 => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «guarded/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
          (fun vX lynxBits19 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits19 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits19) with
              | vRest =>
                Lynx.Result.guard (Erlang.erlang.«>/2» vX (Lynx.Term.integer 10))
                  (fun _ => pure (Lynx.Term.tuple #[Lynx.Term.atom "large", vX, vRest]))
                  lynxMatchNext
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
              (fun vX lynxBits20 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits20 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits20) with
                  | vRest => pure (Lynx.Term.tuple #[Lynx.Term.atom "small", vX, vRest])
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun (_ : Unit) =>
            match _0 with
            | _2 => pure (Lynx.Term.atom "other")))

#lynx_pure
  def «alias/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | vWhole@lynxBits21 =>
          Lynx.Term.Bitstring.extract
            (Lynx.Term.Bitstring.matchInteger lynxBits21 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false)
            (fun vX lynxBits22 =>
              match (Lynx.Term.Bitstring.matchTail lynxBits22 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits22) with
                | vRest => pure (Lynx.Term.tuple #[vX, vRest, vWhole])
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «pinned/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _1 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
          (fun _5 lynxBits23 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits23 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits23) with
              | vRest =>
                Lynx.Result.guard (Erlang.erlang.«=:=/2» _5 _0)
                  (fun _ => pure (Lynx.Term.tuple #[_0, vRest])) lynxMatchNext
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _1 with
        | _6 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf8/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf8 _0)
          (fun vX lynxBits24 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits24 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits24) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf8_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf8 _0)
          (fun vX lynxBits25 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits25 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits25) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf16/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf16 _0 Bool.false)
          (fun vX lynxBits26 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits26 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits26) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf16_big/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf16 _0 Bool.false)
          (fun vX lynxBits27 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits27 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits27) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf16_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf16 _0 Bool.true)
          (fun vX lynxBits28 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits28 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits28) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf32/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf32 _0 Bool.false)
          (fun vX lynxBits29 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits29 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits29) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf32_big/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf32 _0 Bool.false)
          (fun vX lynxBits30 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits30 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits30) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf32_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf32 _0 Bool.true)
          (fun vX lynxBits31 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits31 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits31) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf_mixed/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _0 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun vTag lynxBits32 =>
            Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf8 lynxBits32)
              (fun vX lynxBits33 =>
                Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf16 lynxBits33 Bool.true)
                  (fun vY lynxBits34 =>
                    Lynx.Term.Bitstring.extract
                      (Lynx.Term.Bitstring.matchUtf32 lynxBits34 Bool.false)
                      (fun vZ lynxBits35 =>
                        match
                          (Lynx.Term.Bitstring.matchTail lynxBits35 (Lynx.Term.atom "all") 1) with
                        | Bool.true✝ =>
                          match (lynxBits35) with
                          | vRest => pure (Lynx.Term.tuple #[vTag, vX, vY, vZ, vRest])
                        | _ => lynxMatchNext ())
                      (fun _ => lynxMatchNext ()))
                  (fun _ => lynxMatchNext ()))
              (fun _ => lynxMatchNext ()))
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf_literal/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf8 _0)
          (fun lynxExtracted lynxBits36 =>
            match lynxExtracted with
            | Lynx.Term.integer 8364 =>
              Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf16 lynxBits36 Bool.true)
                (fun lynxExtracted lynxBits37 =>
                  match lynxExtracted with
                  | Lynx.Term.integer 128512 =>
                    Lynx.Term.Bitstring.extract
                      (Lynx.Term.Bitstring.matchUtf32 lynxBits37 Bool.false)
                      (fun lynxExtracted lynxBits38 =>
                        match lynxExtracted with
                        | Lynx.Term.integer 1114111 =>
                          match (Lynx.Term.Bitstring.matchEnd lynxBits38) with
                          | Bool.true✝ => pure (Lynx.Term.atom "matched")
                          | _ => lynxMatchNext ()
                        | _ => lynxMatchNext ())
                      (fun _ => lynxMatchNext ())
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ())
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf_pinned/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf8 _1)
          (fun _5 lynxBits39 =>
            Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf16 lynxBits39 Bool.false)
              (fun _6 lynxBits40 =>
                Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf32 lynxBits40 Bool.true)
                  (fun _7 lynxBits41 =>
                    match (Lynx.Term.Bitstring.matchEnd lynxBits41) with
                    | Bool.true✝ =>
                      Lynx.Result.guard
                        (do
                          let _10 ← Erlang.erlang.«=:=/2» _5 _0
                          let _8 ← Erlang.erlang.«=:=/2» _6 _0
                          let _9 ← Erlang.erlang.«=:=/2» _7 _0
                          let _11 ← Erlang.erlang.«and/2» _8 _9
                          Erlang.erlang.«and/2» _10 _11)
                        (fun _ => pure (Lynx.Term.atom "matched")) lynxMatchNext
                    | _ => lynxMatchNext ())
                  (fun _ => lynxMatchNext ()))
              (fun _ => lynxMatchNext ()))
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        match _1 with
        | _12 => pure (Lynx.Term.atom "other"))

end

end Erlang.bitstring_matching
