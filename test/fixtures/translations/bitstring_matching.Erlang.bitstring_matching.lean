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
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits0 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits0 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (Lynx.Term.integer 1, lynxBits1) =>
            match
              (Lynx.Term.Bitstring.matchInteger lynxBits1 (Lynx.Term.integer 8) 1 Bool.false
                Bool.false) with
            | Option.some✝ (Lynx.Term.integer 2, lynxBits2) =>
              match
                (Lynx.Term.Bitstring.matchInteger lynxBits2 (Lynx.Term.integer 3) 1 Bool.false
                  Bool.false) with
              | Option.some✝ (Lynx.Term.integer 5, lynxBits3) =>
                match (Lynx.Term.Bitstring.matchEnd lynxBits3) with
                | Bool.true✝ => pure (Lynx.Term.atom "matched")
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

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
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits4 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits4 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vA, lynxBits5) =>
            match
              (Lynx.Term.Bitstring.matchInteger lynxBits5 (Lynx.Term.integer 12) 1 Bool.true
                Bool.false) with
            | Option.some✝ (vB, lynxBits6) =>
              match
                (Lynx.Term.Bitstring.matchInteger lynxBits6 (Lynx.Term.integer 12) 1 Bool.true
                  Bool.true) with
              | Option.some✝ (vC, lynxBits7) =>
                match (Lynx.Term.Bitstring.matchEnd lynxBits7) with
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
    (fun «lynxLabel_label^0» =>
        (fun lynxMatchNext =>
            match _0 with
            | lynxBits8 =>
              match
                (Lynx.Term.Bitstring.matchInteger lynxBits8 (Lynx.Term.integer 8) 1 Bool.false
                  Bool.false) with
              | Option.some✝ (vSize, lynxBits9) =>
                match (Lynx.Term.Bitstring.matchTail lynxBits9 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits9) with
                  | _3 =>
                    (fun lynxMatchNext =>
                        match _3 with
                        | lynxBits10 =>
                          match
                            (Lynx.Term.Bitstring.matchInteger lynxBits10 vSize 1 Bool.true
                              Bool.true) with
                          | Option.some✝ (vX, lynxBits11) =>
                            match
                              (Lynx.Term.Bitstring.matchTail lynxBits11 (Lynx.Term.atom "all")
                                1) with
                            | Bool.true✝ =>
                              match (lynxBits11) with
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
    (fun lynxMatchNext =>
        match _1 with
        | lynxBits12 =>
          match (Lynx.Term.Bitstring.matchInteger lynxBits12 _0 3 Bool.false Bool.false) with
          | Option.some✝ (vX, lynxBits13) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits13 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits13) with
              | vTail => pure (Lynx.Term.tuple #[vX, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «float64/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits14 =>
          match (Lynx.Term.Bitstring.matchFloat lynxBits14 64 Bool.false) with
          | Option.some✝ (vX, lynxBits15) =>
            match (Lynx.Term.Bitstring.matchFloat lynxBits15 64 Bool.true) with
            | Option.some✝ (vY, lynxBits16) =>
              match (Lynx.Term.Bitstring.matchEnd lynxBits16) with
              | Bool.true✝ => pure (Lynx.Term.tuple #[vX, vY])
              | _ => lynxMatchNext ()
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits17 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits17 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits18) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits18 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits18) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits19 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits19 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits20) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits20 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits20) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_literal_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits21 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits21 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (Lynx.Term.integer 1, lynxBits22) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits22 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits22) with
              | vTail => pure vTail
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_literal_tail/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits23 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits23 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (Lynx.Term.integer 1, lynxBits24) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits24 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits24) with
              | vTail => pure vTail
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «binary_fixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _1 with
        | lynxBits25 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits25 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits26) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits26 _0 8) with
            | Bool.true✝ =>
              match (lynxBits26) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «bitstring_fixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _1 with
        | lynxBits27 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits27 (Lynx.Term.integer 3) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vTag, lynxBits28) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits28 _0 1) with
            | Bool.true✝ =>
              match (lynxBits28) with
              | vTail => pure (Lynx.Term.tuple #[vTag, vTail])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _5 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «nested/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        | Lynx.Term.tuple ⟨[Lynx.Term.atom "tag", Lynx.Term.cons lynxMap382 Lynx.Term.nil]⟩ =>
          match (Lynx.Term.getMapKeys [Lynx.Term.atom "bits"] lynxMap382) with
          | [lynxBits29] =>
            match
              (Lynx.Term.Bitstring.matchInteger lynxBits29 (Lynx.Term.integer 8) 1 Bool.false
                Bool.false) with
            | Option.some✝ (vX, lynxBits30) =>
              match (Lynx.Term.Bitstring.matchTail lynxBits30 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits30) with
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
    (fun lynxMatchNext =>
        match _0 with
        | lynxBits31 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits31 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vX, lynxBits32) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits32 (Lynx.Term.atom "all") 8) with
            | Bool.true✝ =>
              match (lynxBits32) with
              | vRest =>
                Lynx.Result.tryWith (Erlang.erlang.«>/2» vX (Lynx.Term.integer 10))
                  (fun lynxGuardValue =>
                    match lynxGuardValue with
                    | Lynx.Term.atom "true" =>
                      pure (Lynx.Term.tuple #[Lynx.Term.atom "large", vX, vRest])
                    | _ => lynxMatchNext ())
                  (fun _ => lynxMatchNext ())
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        (fun lynxMatchNext =>
            match _0 with
            | lynxBits33 =>
              match
                (Lynx.Term.Bitstring.matchInteger lynxBits33 (Lynx.Term.integer 8) 1 Bool.false
                  Bool.false) with
              | Option.some✝ (vX, lynxBits34) =>
                match (Lynx.Term.Bitstring.matchTail lynxBits34 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits34) with
                  | vRest => pure (Lynx.Term.tuple #[Lynx.Term.atom "small", vX, vRest])
                | _ => lynxMatchNext ()
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            match _0 with
            | _2 => pure (Lynx.Term.atom "other")))

#lynx_pure
  def «alias/1» (_0 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _0 with
        | vWhole@lynxBits35 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits35 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (vX, lynxBits36) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits36 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits36) with
              | vRest => pure (Lynx.Term.tuple #[vX, vRest, vWhole])
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _0 with
        | _2 => pure (Lynx.Term.atom "other"))

#lynx_pure
  def «pinned/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    (fun lynxMatchNext =>
        match _1 with
        | lynxBits37 =>
          match
            (Lynx.Term.Bitstring.matchInteger lynxBits37 (Lynx.Term.integer 8) 1 Bool.false
              Bool.false) with
          | Option.some✝ (_5, lynxBits38) =>
            match (Lynx.Term.Bitstring.matchTail lynxBits38 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits38) with
              | vRest =>
                Lynx.Result.tryWith (Erlang.erlang.«=:=/2» _5 _0)
                  (fun lynxGuardValue =>
                    match lynxGuardValue with
                    | Lynx.Term.atom "true" => pure (Lynx.Term.tuple #[_0, vRest])
                    | _ => lynxMatchNext ())
                  (fun _ => lynxMatchNext ())
            | _ => lynxMatchNext ()
          | _ => lynxMatchNext ())
      (fun (_ : Unit) =>
        match _1 with
        | _6 => pure (Lynx.Term.atom "other"))

end

end Erlang.bitstring_matching
