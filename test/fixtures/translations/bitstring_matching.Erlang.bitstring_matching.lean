module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.bitstring_matching

section

set_option «match».ignoreUnusedAlts true

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
        match _0 with
        | lynxBits0 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits0 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vA, lynxBits1) =>
            match
              (Lynx.Term.Bitstring.matchInteger lynxBits1 (Lynx.Term.integer 12) 1 Bool.true
                Bool.false) with
            | Option.some✝ (vB, lynxBits2) =>
              match
                (Lynx.Term.Bitstring.matchInteger lynxBits2 (Lynx.Term.integer 12) 1 Bool.true
                  Bool.true) with
              | Option.some✝ (vC, lynxBits3) =>
                match (Lynx.Term.Bitstring.matchEnd lynxBits3) with
                | Bool.true✝ => pure (Lynx.Term.tuple #[vA, vB, vC])
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
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
            match _0 with
            | lynxBits4 =>
              match
                (Lynx.Term.Bitstring.matchInteger lynxBits4 (Lynx.Term.integer 8) 1 Bool.false
                  Bool.false) with
              | Option.some✝ (vSize, lynxBits5) =>
                match (Lynx.Term.Bitstring.matchTail lynxBits5 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits5) with
                  | _3 =>
                    (fun {lynxValue : Type}
                          (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                          (lynxNext : Unit → Lynx.Result lynxValue) =>
                        lynxBody lynxNext)
                      (fun lynxMatchNext =>
                        match _3 with
                        | lynxBits6 =>
                          match
                            (Lynx.Term.Bitstring.matchInteger lynxBits6 vSize 1 Bool.true
                              Bool.true) with
                          | Option.some✝ (vX, lynxBits7) =>
                            match
                              (Lynx.Term.Bitstring.matchTail lynxBits7 (Lynx.Term.atom "all")
                                1) with
                            | Bool.true✝ =>
                              match (lynxBits7) with
                              | vTail => pure (Lynx.Term.tuple #[vSize, vX, vTail])
                            | _ => lynxMatchNext ()
                          | _ => lynxMatchNext ())
                      (fun (_ : Unit) =>
                        match _3 with
                        | _4 => «lynxLabel_label^0» ())
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ())
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
        match _1 with
        | lynxBits8 =>
          match (Lynx.Term.Bitstring.matchInteger lynxBits8 _0 3 Bool.false Bool.false) with
          | Option.some✝ (vX, lynxBits9) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits9 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits9) with
              | vTail => pure (Lynx.Term.tuple #[vX, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «float64/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits10 =>
          match (Lynx.Term.Bitstring.matchFloat lynxBits10 64 Bool.false) with
          | Option.some✝ (vX, lynxBits11) =>
            match (Lynx.Term.Bitstring.matchFloat lynxBits11 64 Bool.true) with
            | Option.some✝ (vY, lynxBits12) =>
              match (Lynx.Term.Bitstring.matchEnd lynxBits12) with
              | Bool.true✝ => pure (Lynx.Term.tuple #[vX, vY])
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits13 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits13 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits14) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits14 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits14) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits15 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits15 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits16) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits16 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits16) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_literal_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits17 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits17 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (Lynx.Term.integer 1, lynxBits18) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits18 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits18) with
              | vTail => pure vTail
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_literal_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits19 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits19 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (Lynx.Term.integer 1, lynxBits20) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits20 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits20) with
              | vTail => pure vTail
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_fixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _1 with
        | lynxBits21 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits21 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits22) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits22 _0 8) with
            | Bool.true✝ =>
              match (lynxBits22) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_fixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _1 with
        | lynxBits23 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits23 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits24) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits24 _0 1) with
            | Bool.true✝ =>
              match (lynxBits24) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_prefix/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _1 with
        | lynxBits25 =>
          match (Lynx.Term.Bitstring.matchBinary lynxBits25 _0 8) with
          | Option.some✝ (vPrefix, lynxBits26) =>
            match
              (Lynx.Term.Bitstring.matchInteger lynxBits26 (Lynx.Term.integer 3) 1 Bool.false
                Bool.false) with
            | Option.some✝ (vTag, lynxBits27) =>
              match (Lynx.Term.Bitstring.matchTail lynxBits27 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits27) with
                | vTail => pure (Lynx.Term.tuple #[vPrefix, vTag, vTail])
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
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
        | Lynx.Term.tuple ⟨[Lynx.Term.atom "tag", Lynx.Term.cons lynxMap363 Lynx.Term.nil]⟩ =>
          match (Lynx.Term.getMapKeys [Lynx.Term.atom "bits"] lynxMap363) with
          | [lynxBits28] =>
            match
              (Lynx.Term.Bitstring.matchInteger lynxBits28 (Lynx.Term.integer 8) 1 Bool.false
                Bool.false) with
            | Option.some✝ (vX, lynxBits29) =>
              match (Lynx.Term.Bitstring.matchTail lynxBits29 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits29) with
                | vRest => pure (Lynx.Term.tuple #[vX, vRest])
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ()
        | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «guarded/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits30 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits30 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vX, lynxBits31) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits31 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits31) with
              | vRest =>
                Lynx.Result.guard (Erlang.erlang.«>/2» vX (Lynx.Term.integer 10))
                  (fun _ => pure (Lynx.Term.tuple #[Lynx.Term.atom "large", vX, vRest]))
                  lynxMatchNext
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match _0 with
            | lynxBits32 =>
              match
                (Lynx.Term.Bitstring.matchInteger lynxBits32 (Lynx.Term.integer 8) 1 Bool.false
                  Bool.false) with
              | Option.some✝ (vX, lynxBits33) =>
                match (Lynx.Term.Bitstring.matchTail lynxBits33 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits33) with
                  | vRest => pure (Lynx.Term.tuple #[Lynx.Term.atom "small", vX, vRest])
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ())
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
        | vWhole@lynxBits34 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits34 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vX, lynxBits35) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits35 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits35) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest, vWhole])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «pinned/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _1 with
        | lynxBits36 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits36 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (_5, lynxBits37) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits37 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits37) with
              | vRest =>
                Lynx.Result.guard (Erlang.erlang.«=:=/2» _5 _0)
                  (fun _ => pure (Lynx.Term.tuple #[_0, vRest])) lynxMatchNext
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _6 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf8/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits38 =>
          match (Lynx.Term.Bitstring.matchUtf8 lynxBits38) with
          | Option.some✝ (vX, lynxBits39) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits39 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits39) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf8_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits40 =>
          match (Lynx.Term.Bitstring.matchUtf8 lynxBits40) with
          | Option.some✝ (vX, lynxBits41) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits41 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits41) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf16/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits42 =>
          match (Lynx.Term.Bitstring.matchUtf16 lynxBits42 Bool.false) with
          | Option.some✝ (vX, lynxBits43) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits43 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits43) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf16_big/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits44 =>
          match (Lynx.Term.Bitstring.matchUtf16 lynxBits44 Bool.false) with
          | Option.some✝ (vX, lynxBits45) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits45 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits45) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf16_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits46 =>
          match (Lynx.Term.Bitstring.matchUtf16 lynxBits46 Bool.true) with
          | Option.some✝ (vX, lynxBits47) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits47 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits47) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf32/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits48 =>
          match (Lynx.Term.Bitstring.matchUtf32 lynxBits48 Bool.false) with
          | Option.some✝ (vX, lynxBits49) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits49 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits49) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf32_big/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits50 =>
          match (Lynx.Term.Bitstring.matchUtf32 lynxBits50 Bool.false) with
          | Option.some✝ (vX, lynxBits51) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits51 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits51) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf32_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits52 =>
          match (Lynx.Term.Bitstring.matchUtf32 lynxBits52 Bool.true) with
          | Option.some✝ (vX, lynxBits53) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits53 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits53) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf_mixed/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits54 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits54 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits55) =>
            match (Lynx.Term.Bitstring.matchUtf8 lynxBits55) with
            | Option.some✝ (vX, lynxBits56) =>
              match (Lynx.Term.Bitstring.matchUtf16 lynxBits56 Bool.true) with
              | Option.some✝ (vY, lynxBits57) =>
                match (Lynx.Term.Bitstring.matchUtf32 lynxBits57 Bool.false) with
                | Option.some✝ (vZ, lynxBits58) =>
                  match (Lynx.Term.Bitstring.matchTail lynxBits58 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (lynxBits58) with
                    | vRest => pure (Lynx.Term.tuple #[vTag, vX, vY, vZ, vRest])
                  | _ => lynxMatchNext ()
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf_literal/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _0 with
        | lynxBits59 =>
          match (Lynx.Term.Bitstring.matchUtf8 lynxBits59) with
          | Option.some✝ (Lynx.Term.integer 8364, lynxBits60) =>
            match (Lynx.Term.Bitstring.matchUtf16 lynxBits60 Bool.true) with
            | Option.some✝ (Lynx.Term.integer 128512, lynxBits61) =>
              match (Lynx.Term.Bitstring.matchUtf32 lynxBits61 Bool.false) with
              | Option.some✝ (Lynx.Term.integer 1114111, lynxBits62) =>
                match (Lynx.Term.Bitstring.matchEnd lynxBits62) with
                | Bool.true✝ => pure (Lynx.Term.atom "matched")
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «utf_pinned/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _1 with
        | lynxBits63 =>
          match (Lynx.Term.Bitstring.matchUtf8 lynxBits63) with
          | Option.some✝ (_5, lynxBits64) =>
            match (Lynx.Term.Bitstring.matchUtf16 lynxBits64 Bool.false) with
            | Option.some✝ (_6, lynxBits65) =>
              match (Lynx.Term.Bitstring.matchUtf32 lynxBits65 Bool.true) with
              | Option.some✝ (_7, lynxBits66) =>
                match (Lynx.Term.Bitstring.matchEnd lynxBits66) with
                | Bool.true✝ =>
                  Lynx.Result.guard
                    (do
                      let _10 ← Erlang.erlang.«=:=/2» _5 _0
                      let _8 ← Erlang.erlang.«=:=/2» _6 _0
                      let _9 ← Erlang.erlang.«=:=/2» _7 _0
                      let _11 ← Erlang.erlang.«and/2» _8 _9
                      Erlang.erlang.«and/2» _10 _11)
                    (fun _ => pure (Lynx.Term.atom "matched")) lynxMatchNext
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _12 => pure (Lynx.Term.atom "other"))

end

end Erlang.bitstring_matching
