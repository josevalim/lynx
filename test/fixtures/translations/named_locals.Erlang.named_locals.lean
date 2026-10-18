module

public import Lynx
public import Lynx.Modules.Erlang.erlang
public import Lynx.Modules.Erlang.erts_internal
public import Lynx.Modules.Erlang.maps

@[expose] public section

namespace Erlang.named_locals

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  def «lynx_local_19/1» (_3 : Lynx.Term) : Lynx.Result :=
    match _3 with
    | Lynx.Term.cons («v@r0»@(Lynx.Term.tuple ⟨[vK@(Lynx.Term.atom _), vV]⟩)) _2 => do
      let _5 ← «lynx_local_19/1» _2
      pure (Lynx.Term.cons «v@r0» _5)
    | Lynx.Term.cons _1 _2 => «lynx_local_19/1» _2
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _4 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _4]))

#lynx_pure
  def «lynx_local_42/2» (_8 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result :=
    match _8 with
    | Lynx.Term.cons vX _7 => do
      let _10 ← «lynx_local_42/2» _7 _0
      pure (Lynx.Term.cons (Lynx.Term.tuple #[_0, vX]) _10)
    | Lynx.Term.cons _6 _7 => «lynx_local_42/2» _7 _0
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _9 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _9]))

#lynx_pure
  mutual
    def «lynx_local_27/2» (_6 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      match _6 with
      | Lynx.Term.cons vX _3 => «lynx_local_28/4» _1 _1 _3 vX
      | Lynx.Term.cons _2 _3 => «lynx_local_27/2» _3 _1
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _7 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))
    termination_by (sizeOf✝ _6, (0, sizeOf✝ _6))
    def «lynx_local_28/4» (_8 : Lynx.Term) (_1 : Lynx.Term) (_3 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      match _8 with
      | Lynx.Term.cons vY _5 => do
        let _10 ← «lynx_local_28/4» _5 _1 _3 vX
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _10)
      | Lynx.Term.cons _4 _5 => «lynx_local_28/4» _5 _1 _3 vX
      | Lynx.Term.nil => «lynx_local_27/2» _3 _1
      | _9 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _9]))
    termination_by (sizeOf✝ _3, (1, sizeOf✝ _8))
  end

#lynx_pure
  mutual
    def «lynx_local_30/3» (_9 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
      match _9 with
      | Lynx.Term.cons vX _4 => «lynx_local_31/5» _1 _1 _2 _4 vX
      | Lynx.Term.cons _3 _4 => «lynx_local_30/3» _4 _1 _2
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    termination_by (sizeOf✝ _9, (0, 0))
    def «lynx_local_31/5» (_11 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (vX : Lynx.Term) : Lynx.Result :=
      match _11 with
      | Lynx.Term.cons vY _6 => «lynx_local_32/7» _2 _1 _2 _4 _6 vX vY
      | Lynx.Term.cons _5 _6 => «lynx_local_31/5» _6 _1 _2 _4 vX
      | Lynx.Term.nil => «lynx_local_30/3» _4 _1 _2
      | _12 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12]))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _11, 0))
    def «lynx_local_32/7» (_13 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (_6 : Lynx.Term) (vX : Lynx.Term) (vY : Lynx.Term) : Lynx.Result :=
      match _13 with
      | Lynx.Term.cons vZ _8 => do
        let _15 ← «lynx_local_32/7» _8 _1 _2 _4 _6 vX vY
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY, vZ]) _15)
      | Lynx.Term.cons _7 _8 => «lynx_local_32/7» _8 _1 _2 _4 _6 vX vY
      | Lynx.Term.nil => «lynx_local_31/5» _6 _1 _2 _4 vX
      | _14 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _14]))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _6, 1 + sizeOf✝ _13))
  end

#lynx_pure
  mutual
    def «lynx_local_37/3» (_12 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
      match _12 with
      | Lynx.Term.cons vX _4 => do
        let _6 ←
          do
            let lynxGenerated0 ← Erlang.erts_internal.«mc_iterator/1» _1
            match lynxGenerated0 with
              | Lynx.Term.nil =>
                Lynx.Result.error
                  (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _1]))
              | _7 => pure _7
        «lynx_local_38/5» _6 _1 _2 _4 vX
      | Lynx.Term.cons _3 _4 => «lynx_local_37/3» _4 _1 _2
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _13 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _13]))
    termination_by (sizeOf✝ _12, (0, 0))
    def «lynx_local_38/5» (_14 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (vX : Lynx.Term) : Lynx.Result :=
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          match _14 with
          | Lynx.Term.tuple ⟨[vK, vV, _7]⟩ =>
            Lynx.Result.guard (Erlang.erlang.«>/2» vV vX)
              (fun _ => «lynx_local_39/7» _2 _1 _2 _4 _7 vK vX) lynxMatchNext
          | _14 => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _14 with
          | Lynx.Term.tuple ⟨[_9, _8, _7]⟩ => «lynx_local_38/5» _7 _1 _2 _4 vX
          | Lynx.Term.atom "none" => «lynx_local_37/3» _4 _1 _2
          | «v@r0»@(Lynx.Term.cons _9 _8) => do
            let _7 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
            «lynx_local_38/5» _7 _1 _2 _4 vX
          | _15 =>
            Lynx.Result.error
              (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _15])))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _14, 0))
    def «lynx_local_39/7» (_16 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (_7 : Lynx.Term) (vK : Lynx.Term) (vX : Lynx.Term) : Lynx.Result :=
      match _16 with
      | Lynx.Term.cons vY _11 => do
        let _18 ← «lynx_local_39/7» _11 _1 _2 _4 _7 vK vX
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vK, vY]) _18)
      | Lynx.Term.cons _10 _11 => «lynx_local_39/7» _11 _1 _2 _4 _7 vK vX
      | Lynx.Term.nil => «lynx_local_38/5» _7 _1 _2 _4 vX
      | _17 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _17]))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _7, 1 + sizeOf✝ _16))
  end

#lynx_pure
  def «lynx_local_44/2» (_7 : Lynx.Term) (_6 : Lynx.Term) : Lynx.Result :=
    match _7, _6 with
    | Lynx.Term.cons vX _3, Lynx.Term.cons vY _5 => do
      let _10 ← «lynx_local_44/2» _3 _5
      pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _10)
    | Lynx.Term.cons _2 _3, Lynx.Term.cons _4 _5 => «lynx_local_44/2» _3 _5
    | Lynx.Term.nil, Lynx.Term.nil => pure Lynx.Term.nil
    | _9, _8 =>
      Lynx.Result.error
        (Lynx.Exception.error
          (Lynx.Term.tuple #[Lynx.Term.atom "bad_generators", Lynx.Term.tuple #[_9, _8]]))

#lynx_pure
  def «lynx_local_48/1» (_6 : Lynx.Term) : Lynx.Result :=
    match _6 with
    | Lynx.Term.tuple ⟨[vK, vV, _3]⟩ => do
      let _8 ← «lynx_local_48/1» _3
      pure (Lynx.Term.cons (Lynx.Term.tuple #[vK, vV]) _8)
    | Lynx.Term.tuple ⟨[_5, _4, _3]⟩ => «lynx_local_48/1» _3
    | Lynx.Term.atom "none" => pure Lynx.Term.nil
    | «v@r0»@(Lynx.Term.cons _5 _4) => do
      let _3 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
      «lynx_local_48/1» _3
    | _7 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))

#lynx_pure
  def «lynx_local_50/1» (_6 : Lynx.Term) : Lynx.Result :=
    match _6 with
    | Lynx.Term.tuple ⟨[vK, Lynx.Term.atom "ok", _3]⟩ => do
      let _8 ← «lynx_local_50/1» _3
      pure (Lynx.Term.cons vK _8)
    | Lynx.Term.tuple ⟨[_5, _4, _3]⟩ =>
      Lynx.Result.error
        (Lynx.Exception.error
          (Lynx.Term.tuple #[Lynx.Term.atom "badmatch", Lynx.Term.tuple #[_5, _4]]))
    | Lynx.Term.atom "none" => pure Lynx.Term.nil
    | «v@r0»@(Lynx.Term.cons _5 _4) => do
      let _3 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
      «lynx_local_50/1» _3
    | _7 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))

#lynx_pure
  def «lynx_local_46/1» (_3 : Lynx.Term) : Lynx.Result :=
    match _3 with
    | Lynx.Term.cons («v@r0»@(Lynx.Term.tuple ⟨[vK, vV]⟩)) _2 => do
      let _5 ← «lynx_local_46/1» _2
      pure (Lynx.Term.cons «v@r0» _5)
    | Lynx.Term.cons _1 _2 => «lynx_local_46/1» _2
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _4 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _4]))

#lynx_pure
  def «lynx_local_52/1» (_6 : Lynx.Term) : Lynx.Result :=
    match _6 with
    | Lynx.Term.tuple ⟨[vK, vV, _3]⟩ => do
      let _8 ← «lynx_local_52/1» _3
      pure (Lynx.Term.cons (Lynx.Term.tuple #[vV, vK]) _8)
    | Lynx.Term.tuple ⟨[_5, _4, _3]⟩ => «lynx_local_52/1» _3
    | Lynx.Term.atom "none" => pure Lynx.Term.nil
    | «v@r0»@(Lynx.Term.cons _5 _4) => do
      let _3 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
      «lynx_local_52/1» _3
    | _7 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))

#lynx_pure
  mutual
    def «lynx_local_24/2» (_9 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      match _9 with
      | Lynx.Term.cons vX _3 => do
        let _5 ←
          do
            let lynxGenerated0 ← Erlang.erts_internal.«mc_iterator/1» _1
            match lynxGenerated0 with
              | Lynx.Term.nil =>
                Lynx.Result.error
                  (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _1]))
              | _6 => pure _6
        «lynx_local_25/4» _5 _1 _3 vX
      | Lynx.Term.cons _2 _3 => «lynx_local_24/2» _3 _1
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    termination_by (sizeOf✝ _9, (0, sizeOf✝ _9))
    def «lynx_local_25/4» (_11 : Lynx.Term) (_1 : Lynx.Term) (_3 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      match _11 with
      | Lynx.Term.tuple ⟨[vK, _16, _6]⟩ => do
        let _13 ← «lynx_local_25/4» _6 _1 _3 vX
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vK]) _13)
      | Lynx.Term.tuple ⟨[_8, _7, _6]⟩ => «lynx_local_25/4» _6 _1 _3 vX
      | Lynx.Term.atom "none" => «lynx_local_24/2» _3 _1
      | «v@r0»@(Lynx.Term.cons _8 _7) => do
        let _6 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
        «lynx_local_25/4» _6 _1 _3 vX
      | _12 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12]))
    termination_by (sizeOf✝ _3, (1, sizeOf✝ _11))
  end

#lynx_pure
  mutual
    def «lynx_local_34/2» (_9 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      match _9 with
      | Lynx.Term.tuple ⟨[vK, vV, _4]⟩ => «lynx_local_35/5» _1 _1 _4 vK vV
      | Lynx.Term.tuple ⟨[_6, _5, _4]⟩ => «lynx_local_34/2» _4 _1
      | Lynx.Term.atom "none" => pure Lynx.Term.nil
      | «v@r0»@(Lynx.Term.cons _6 _5) => do
        let _4 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
        «lynx_local_34/2» _4 _1
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    termination_by (sizeOf✝ _9, (0, sizeOf✝ _9))
    def «lynx_local_35/5» (_11 : Lynx.Term) (_1 : Lynx.Term) (_4 : Lynx.Term) (vK : Lynx.Term)
        (vV : Lynx.Term) : Lynx.Result :=
      match _11 with
      | Lynx.Term.cons vX _8 => do
        let _13 ← «lynx_local_35/5» _8 _1 _4 vK vV
        pure (Lynx.Term.cons (Lynx.Term.tuple #[Lynx.Term.tuple #[vK, vX], vV]) _13)
      | Lynx.Term.cons _7 _8 => «lynx_local_35/5» _8 _1 _4 vK vV
      | Lynx.Term.nil => «lynx_local_34/2» _4 _1
      | _12 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12]))
    termination_by (sizeOf✝ _4, (1, sizeOf✝ _11))
  end

#lynx_pure
  mutual
    def «lynx_local_21/2» (_9 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      match _9 with
      | Lynx.Term.cons (vX@(Lynx.Term.integer _)) _3 => do
        let _5 ←
          do
            let lynxGenerated0 ← Erlang.erts_internal.«mc_iterator/1» _1
            match lynxGenerated0 with
              | Lynx.Term.nil =>
                Lynx.Result.error
                  (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _1]))
              | _6 => pure _6
        «lynx_local_22/4» _5 _1 _3 vX
      | Lynx.Term.cons _2 _3 => «lynx_local_21/2» _3 _1
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    termination_by (sizeOf✝ _9, (0, sizeOf✝ _9))
    def «lynx_local_22/4» (_11 : Lynx.Term) (_1 : Lynx.Term) (_3 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          match _11 with
          | Lynx.Term.tuple ⟨[vK, vV, _6]⟩ =>
            Lynx.Result.guard (Erlang.erlang.«=:=/2» vK vX)
              (fun _ => do
                let _13 ← «lynx_local_22/4» _6 _1 _3 vX
                pure (Lynx.Term.cons vV _13))
              lynxMatchNext
          | _11 => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _11 with
          | Lynx.Term.tuple ⟨[_8, _7, _6]⟩ => «lynx_local_22/4» _6 _1 _3 vX
          | Lynx.Term.atom "none" => «lynx_local_21/2» _3 _1
          | «v@r0»@(Lynx.Term.cons _8 _7) => do
            let _6 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
            «lynx_local_22/4» _6 _1 _3 vX
          | _12 =>
            Lynx.Result.error
              (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12])))
    termination_by (sizeOf✝ _3, (1, sizeOf✝ _11))
  end

#lynx_pure
  def «lynx_local_3/1» (_2 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _2 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
          (fun vX lynxBits0 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits0 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits0) with
              | _1 => do
                let _4 ← «lynx_local_3/1» _1
                pure (Lynx.Term.cons vX _4)
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger _2 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
              (fun vX lynxBits1 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits1 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits1) with
                  | _1 => «lynx_local_3/1» _1
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match (Lynx.Term.Bitstring.matchTail _2 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (_2) with
                  | _1 => pure Lynx.Term.nil
                | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _2 with
                | _3 =>
                  Lynx.Result.error
                    (Lynx.Exception.error
                      (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _3])))))
  termination_by sizeOf✝ _2

#lynx_pure
  def «lynx_local_17/1» (_2 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _2 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
          (fun vX lynxBits2 =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger lynxBits2 (Lynx.Term.integer 2) 1 Bool.false
                Bool.false)
              (fun vY lynxBits3 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits3 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits3) with
                  | _1 =>
                    Lynx.Result.guard (Erlang.erlang.«>/2» vX vY)
                      (fun _ => do
                        let _4 ← «lynx_local_17/1» _1
                        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _4))
                      lynxMatchNext
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger _2 (Lynx.Term.integer 3) 1 Bool.false Bool.false)
              (fun vX lynxBits4 =>
                Lynx.Term.Bitstring.extract
                  (Lynx.Term.Bitstring.matchInteger lynxBits4 (Lynx.Term.integer 2) 1 Bool.false
                    Bool.false)
                  (fun vY lynxBits5 =>
                    match (Lynx.Term.Bitstring.matchTail lynxBits5 (Lynx.Term.atom "all") 1) with
                    | Bool.true✝ =>
                      match (lynxBits5) with
                      | _1 => «lynx_local_17/1» _1
                    | _ => lynxMatchNext ())
                  (fun _ => lynxMatchNext ()))
              (fun _ => lynxMatchNext ()))
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match (Lynx.Term.Bitstring.matchTail _2 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (_2) with
                  | _1 => pure Lynx.Term.nil
                | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _2 with
                | _3 =>
                  Lynx.Result.error
                    (Lynx.Exception.error
                      (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _3])))))
  termination_by sizeOf✝ _2

#lynx_pure
  def «lynx_local_5/1» (_2 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _2 (Lynx.Term.integer 16) 1 Bool.false Bool.false)
          (fun vX lynxBits6 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits6 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits6) with
              | _1 => do
                let _4 ← «lynx_local_5/1» _1
                pure (Lynx.Term.cons vX _4)
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match (Lynx.Term.Bitstring.matchEnd _2) with
            | Bool.true✝ => pure Lynx.Term.nil
            | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match (Lynx.Term.Bitstring.matchTail _2 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (_2) with
                  | _1 =>
                    Lynx.Result.error
                      (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "badmatch", _1]))
                | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _2 with
                | _3 =>
                  Lynx.Result.error
                    (Lynx.Exception.error
                      (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _3])))))
  termination_by sizeOf✝ _2

#lynx_pure
  def «lynx_local_62/1» (_2 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf8 _2)
          (fun vC lynxBits7 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits7 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits7) with
              | _1 => do
                let _4 ← «lynx_local_62/1» _1
                pure (Lynx.Term.cons vC _4)
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchUtf8 _2)
              (fun vC lynxBits8 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits8 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits8) with
                  | _1 => «lynx_local_62/1» _1
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match (Lynx.Term.Bitstring.matchTail _2 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (_2) with
                  | _1 => pure Lynx.Term.nil
                | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _2 with
                | _3 =>
                  Lynx.Result.error
                    (Lynx.Exception.error
                      (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _3])))))
  termination_by sizeOf✝ _2

#lynx_pure
  def «lynx_local_60/2» (_3 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result :=
    if lynxNonzero : Lynx.Term.Bitstring.zeroWidth _0 = Bool.true✝ then
      Lynx.Result.error✝ (Lynx.Exception.error✝ (Lynx.Term.atom✝ "badarg"))
    else
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchBinary _3 _0 8)
            (fun vX lynxBits9 =>
              match (Lynx.Term.Bitstring.matchTail lynxBits9 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits9) with
                | _2 => do
                  let _5 ← «lynx_local_60/2» _2 _0
                  pure (Lynx.Term.cons vX _5)
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ()))
        (fun (_ : Unit) =>
          (fun {lynxValue : Type}
                (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                (lynxNext : Unit → Lynx.Result lynxValue) =>
              lynxBody lynxNext)
            (fun lynxMatchNext =>
              Lynx.Term.Bitstring.extract (Lynx.Term.Bitstring.matchBinary _3 _0 8)
                (fun vX lynxBits10 =>
                  match (Lynx.Term.Bitstring.matchTail lynxBits10 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (lynxBits10) with
                    | _2 => «lynx_local_60/2» _2 _0
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ()))
            (fun (_ : Unit) =>
              (fun {lynxValue : Type}
                    (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                    (lynxNext : Unit → Lynx.Result lynxValue) =>
                  lynxBody lynxNext)
                (fun lynxMatchNext =>
                  match (Lynx.Term.Bitstring.matchTail _3 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (_3) with
                    | _2 => pure Lynx.Term.nil
                  | _ => lynxMatchNext ())
                (fun (_ : Unit) =>
                  match _3 with
                  | _4 =>
                    Lynx.Result.error
                      (Lynx.Exception.error
                        (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _4])))))
  termination_by sizeOf✝ _3

#lynx_pure
  def «lynx_local_64/1» (_2 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))

#lynx_pure
  def «lynx_local_1/2» (_5 : Lynx.Term) (_4 : Lynx.Term) : Lynx.Result :=
    match _5, _4 with
    | Lynx.Term.cons vX _3, _8 => do
      let _10 ←
        Lynx.Result.bind (Lynx.Term.Bitstring.binarySegment _4 (Lynx.Term.atom "all") 1)
            (fun lynxBinarySegment✝ =>
              Lynx.Result.bind
                (Lynx.Term.Bitstring.integerSegment vX (Lynx.Term.integer 4) 1 Bool.false)
                (fun lynxBinaryTail✝ =>
                  Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))
      «lynx_local_1/2» _3 _10
    | Lynx.Term.cons _2 _3, _8 => «lynx_local_1/2» _3 _4
    | Lynx.Term.nil, _8 => pure _4
    | _7, _6 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))

#lynx_pure
  def «lynx_local_13/2» (_4 : Lynx.Term) (_3 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        match _3 with
        | _7 =>
          Lynx.Term.Bitstring.extract
            (Lynx.Term.Bitstring.matchInteger _4 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
            (fun vX lynxBits11 =>
              Lynx.Term.Bitstring.extract
                (Lynx.Term.Bitstring.matchInteger lynxBits11 (Lynx.Term.integer 8) 1 Bool.false
                  Bool.false)
                (fun vY lynxBits12 =>
                  match (Lynx.Term.Bitstring.matchTail lynxBits12 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (lynxBits12) with
                    | _2 => do
                      let _9 ←
                        Lynx.Result.bind
                            (Lynx.Term.Bitstring.binarySegment _3 (Lynx.Term.atom "all") 1)
                            (fun lynxBinarySegment✝ =>
                              Lynx.Result.bind
                                (Lynx.Result.bind
                                  (Lynx.Term.Bitstring.integerSegment vY (Lynx.Term.integer 8) 1
                                    Bool.false)
                                  (fun lynxBinarySegment✝ =>
                                    Lynx.Result.bind
                                      (Lynx.Term.Bitstring.integerSegment vX (Lynx.Term.integer 8) 1
                                        Bool.false)
                                      (fun lynxBinaryTail✝ =>
                                        Lynx.Term.Bitstring.append lynxBinarySegment✝
                                          lynxBinaryTail✝)))
                                (fun lynxBinaryTail✝ =>
                                  Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))
                      «lynx_local_13/2» _2 _9
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ()))
            (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match _3 with
            | _7 =>
              Lynx.Term.Bitstring.extract
                (Lynx.Term.Bitstring.matchInteger _4 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
                (fun vX lynxBits13 =>
                  Lynx.Term.Bitstring.extract
                    (Lynx.Term.Bitstring.matchInteger lynxBits13 (Lynx.Term.integer 8) 1 Bool.false
                      Bool.false)
                    (fun vY lynxBits14 =>
                      match (Lynx.Term.Bitstring.matchTail lynxBits14 (Lynx.Term.atom "all") 1) with
                      | Bool.true✝ =>
                        match (lynxBits14) with
                        | _2 => «lynx_local_13/2» _2 _3
                      | _ => lynxMatchNext ())
                    (fun _ => lynxMatchNext ()))
                (fun _ => lynxMatchNext ()))
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match _3 with
                | _7 =>
                  match (Lynx.Term.Bitstring.matchTail _4 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (_4) with
                    | _2 => pure _3
                  | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _4, _3 with
                | _6, _5 =>
                  Lynx.Result.error
                    (Lynx.Exception.error
                      (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _6])))))
  termination_by sizeOf✝ _4

#lynx_pure
  mutual
    def «lynx_local_10/2» (_4 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          Lynx.Term.Bitstring.extract
            (Lynx.Term.Bitstring.matchInteger _4 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
            (fun vX lynxBits15 =>
              match (Lynx.Term.Bitstring.matchTail lynxBits15 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits15) with
                | _2 => «lynx_local_11/4» _1 _1 _2 vX
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ()))
        (fun (_ : Unit) =>
          (fun {lynxValue : Type}
                (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                (lynxNext : Unit → Lynx.Result lynxValue) =>
              lynxBody lynxNext)
            (fun lynxMatchNext =>
              Lynx.Term.Bitstring.extract
                (Lynx.Term.Bitstring.matchInteger _4 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
                (fun vX lynxBits16 =>
                  match (Lynx.Term.Bitstring.matchTail lynxBits16 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (lynxBits16) with
                    | _2 => «lynx_local_10/2» _2 _1
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ()))
            (fun (_ : Unit) =>
              (fun {lynxValue : Type}
                    (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                    (lynxNext : Unit → Lynx.Result lynxValue) =>
                  lynxBody lynxNext)
                (fun lynxMatchNext =>
                  match (Lynx.Term.Bitstring.matchTail _4 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (_4) with
                    | _2 => pure Lynx.Term.nil
                  | _ => lynxMatchNext ())
                (fun (_ : Unit) =>
                  match _4 with
                  | _5 =>
                    Lynx.Result.error
                      (Lynx.Exception.error
                        (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _5])))))
    termination_by (sizeOf✝ _4, (0, sizeOf✝ _4))
    def «lynx_local_11/4» (_6 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          Lynx.Term.Bitstring.extract
            (Lynx.Term.Bitstring.matchInteger _6 (Lynx.Term.integer 4) 1 Bool.false Bool.false)
            (fun vY lynxBits17 =>
              match (Lynx.Term.Bitstring.matchTail lynxBits17 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits17) with
                | _3 => do
                  let _8 ← «lynx_local_11/4» _3 _1 _2 vX
                  pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _8)
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ()))
        (fun (_ : Unit) =>
          (fun {lynxValue : Type}
                (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                (lynxNext : Unit → Lynx.Result lynxValue) =>
              lynxBody lynxNext)
            (fun lynxMatchNext =>
              Lynx.Term.Bitstring.extract
                (Lynx.Term.Bitstring.matchInteger _6 (Lynx.Term.integer 4) 1 Bool.false Bool.false)
                (fun vY lynxBits18 =>
                  match (Lynx.Term.Bitstring.matchTail lynxBits18 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (lynxBits18) with
                    | _3 => «lynx_local_11/4» _3 _1 _2 vX
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ()))
            (fun (_ : Unit) =>
              (fun {lynxValue : Type}
                    (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                    (lynxNext : Unit → Lynx.Result lynxValue) =>
                  lynxBody lynxNext)
                (fun lynxMatchNext =>
                  match (Lynx.Term.Bitstring.matchTail _6 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (_6) with
                    | _3 => «lynx_local_10/2» _2 _1
                  | _ => lynxMatchNext ())
                (fun (_ : Unit) =>
                  match _6 with
                  | _7 =>
                    Lynx.Result.error
                      (Lynx.Exception.error
                        (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7])))))
    termination_by (sizeOf✝ _2, (1, sizeOf✝ _6))
  end

#lynx_pure
  def «lynx_local_15/2» (_5 : Lynx.Term) (_4 : Lynx.Term) : Lynx.Result :=
    (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
          (lynxNext : Unit → Lynx.Result lynxValue) =>
        lynxBody lynxNext)
      (fun lynxMatchNext =>
        Lynx.Term.Bitstring.extract
          (Lynx.Term.Bitstring.matchInteger _5 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
          (fun vX lynxBits19 =>
            match (Lynx.Term.Bitstring.matchTail lynxBits19 (Lynx.Term.atom "all") 1) with
            | Bool.true✝ =>
              match (lynxBits19) with
              | _2 =>
                Lynx.Term.Bitstring.extract
                  (Lynx.Term.Bitstring.matchInteger _4 (Lynx.Term.integer 4) 1 Bool.false
                    Bool.false)
                  (fun vY lynxBits20 =>
                    match (Lynx.Term.Bitstring.matchTail lynxBits20 (Lynx.Term.atom "all") 1) with
                    | Bool.true✝ =>
                      match (lynxBits20) with
                      | _3 => do
                        let _8 ← «lynx_local_15/2» _2 _3
                        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _8)
                    | _ => lynxMatchNext ())
                  (fun _ => lynxMatchNext ())
            | _ => lynxMatchNext ())
          (fun _ => lynxMatchNext ()))
      (fun (_ : Unit) =>
        (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
              (lynxNext : Unit → Lynx.Result lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            Lynx.Term.Bitstring.extract
              (Lynx.Term.Bitstring.matchInteger _5 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
              (fun vX lynxBits21 =>
                match (Lynx.Term.Bitstring.matchTail lynxBits21 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (lynxBits21) with
                  | _2 =>
                    Lynx.Term.Bitstring.extract
                      (Lynx.Term.Bitstring.matchInteger _4 (Lynx.Term.integer 4) 1 Bool.false
                        Bool.false)
                      (fun vY lynxBits22 =>
                        match
                          (Lynx.Term.Bitstring.matchTail lynxBits22 (Lynx.Term.atom "all") 1) with
                        | Bool.true✝ =>
                          match (lynxBits22) with
                          | _3 => «lynx_local_15/2» _2 _3
                        | _ => lynxMatchNext ())
                      (fun _ => lynxMatchNext ())
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ()))
          (fun (_ : Unit) =>
            (fun {lynxValue : Type}
                  (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                  (lynxNext : Unit → Lynx.Result lynxValue) =>
                lynxBody lynxNext)
              (fun lynxMatchNext =>
                match (Lynx.Term.Bitstring.matchTail _5 (Lynx.Term.atom "all") 1) with
                | Bool.true✝ =>
                  match (_5) with
                  | _2 =>
                    match (Lynx.Term.Bitstring.matchTail _4 (Lynx.Term.atom "all") 1) with
                    | Bool.true✝ =>
                      match (_4) with
                      | _3 => pure Lynx.Term.nil
                    | _ => lynxMatchNext ()
                | _ => lynxMatchNext ())
              (fun (_ : Unit) =>
                match _5, _4 with
                | _7, _6 =>
                  Lynx.Result.error
                    (Lynx.Exception.error
                      (Lynx.Term.tuple
                        #[Lynx.Term.atom "bad_generators", Lynx.Term.tuple #[_7, _6]])))))
  termination_by sizeOf✝ _5

#lynx_pure
  mutual
    def «lynx_local_7/2» (_5 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          Lynx.Term.Bitstring.extract
            (Lynx.Term.Bitstring.matchInteger _5 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
            (fun vX lynxBits23 =>
              match (Lynx.Term.Bitstring.matchTail lynxBits23 (Lynx.Term.atom "all") 1) with
              | Bool.true✝ =>
                match (lynxBits23) with
                | _2 => «lynx_local_8/4» _1 _1 _2 vX
              | _ => lynxMatchNext ())
            (fun _ => lynxMatchNext ()))
        (fun (_ : Unit) =>
          (fun {lynxValue : Type}
                (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                (lynxNext : Unit → Lynx.Result lynxValue) =>
              lynxBody lynxNext)
            (fun lynxMatchNext =>
              Lynx.Term.Bitstring.extract
                (Lynx.Term.Bitstring.matchInteger _5 (Lynx.Term.integer 8) 1 Bool.false Bool.false)
                (fun vX lynxBits24 =>
                  match (Lynx.Term.Bitstring.matchTail lynxBits24 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (lynxBits24) with
                    | _2 => «lynx_local_7/2» _2 _1
                  | _ => lynxMatchNext ())
                (fun _ => lynxMatchNext ()))
            (fun (_ : Unit) =>
              (fun {lynxValue : Type}
                    (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
                    (lynxNext : Unit → Lynx.Result lynxValue) =>
                  lynxBody lynxNext)
                (fun lynxMatchNext =>
                  match (Lynx.Term.Bitstring.matchTail _5 (Lynx.Term.atom "all") 1) with
                  | Bool.true✝ =>
                    match (_5) with
                    | _2 => pure Lynx.Term.nil
                  | _ => lynxMatchNext ())
                (fun (_ : Unit) =>
                  match _5 with
                  | _6 =>
                    Lynx.Result.error
                      (Lynx.Exception.error
                        (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _6])))))
    termination_by (sizeOf✝ _5, (0, sizeOf✝ _5))
    def «lynx_local_8/4» (_7 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      match _7 with
      | Lynx.Term.cons vY _4 => do
        let _9 ← «lynx_local_8/4» _4 _1 _2 vX
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _9)
      | Lynx.Term.cons _3 _4 => «lynx_local_8/4» _4 _1 _2 vX
      | Lynx.Term.nil => «lynx_local_7/2» _2 _1
      | _8 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _8]))
    termination_by (sizeOf✝ _2, (1, sizeOf✝ _7))
  end

def «named/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result := do
  let vF ← pure (Lynx.Term.function 0 1 #[_0])
  Lynx.Term.apply vF #[_1]

def «lynx_local_54/2» (_3 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result := do
  let vLoop ← pure (Lynx.Term.function 0 1 #[_0])
  match _3 with
    | Lynx.Term.nil => pure Lynx.Term.nil
    | Lynx.Term.cons vX vXs => do
      let _2 ← Lynx.Term.apply vLoop #[vXs]
      pure (Lynx.Term.cons (Lynx.Term.tuple #[_0, vX]) _2)
    | _4 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))

def «self_reference/0» : Lynx.Result := do
  let vF ← pure (Lynx.Term.function 1 0 #[])
  let _1 ← Lynx.Term.apply vF #[]
  Erlang.erlang.«=:=/2» vF _1

#lynx_pure
  def «lynx_local_57/0» : Lynx.Result :=
    pure (Lynx.Term.function 1 0 #[])

def «$lynx_fun_0/2» (_0 : Lynx.Term) (lynxGenerated0 : Lynx.Term) : Lynx.Result :=
  «lynx_local_54/2» lynxGenerated0 _0

#lynx_pure
  def «$lynx_fun_1/0» : Lynx.Result :=
    «lynx_local_57/0»

#lynx_pure
  def «comprehension_filtered/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_19/1» _0

#lynx_pure
  def «lynx_local_41/2» (_4 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result :=
    match _4 with
    | Lynx.Term.cons vList _3 => do
      let _11 ← «lynx_local_42/2» vList _0
      let _12 ← «lynx_local_41/2» _3 _0
      pure (Lynx.Term.cons _11 _12)
    | Lynx.Term.cons _2 _3 => «lynx_local_41/2» _3 _0
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _5 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _5]))

#lynx_pure
  def «comprehension_lists/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_27/2» _0 _1

#lynx_pure
  def «comprehension_lists3/3» (_0 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
    «lynx_local_30/3» _0 _1 _2

#lynx_pure
  def «comprehension_mixed3/3» (_0 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
    «lynx_local_37/3» _0 _1 _2

#lynx_pure
  def «comprehension_zip/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_44/2» _0 _1

#lynx_pure
  def «map_generator/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _2 ←
      do
        let lynxGenerated0 ← Erlang.erts_internal.«mc_iterator/1» _0
        match lynxGenerated0 with
          | Lynx.Term.nil =>
            Lynx.Result.error
              (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _0]))
          | _3 => pure _3
    «lynx_local_48/1» _2

#lynx_pure
  def «map_generator_strict/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _2 ←
      do
        let lynxGenerated0 ← Erlang.erts_internal.«mc_iterator/1» _0
        match lynxGenerated0 with
          | Lynx.Term.nil =>
            Lynx.Result.error
              (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _0]))
          | _3 => pure _3
    «lynx_local_50/1» _2

#lynx_pure
  def «map_comprehension/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _6 ← «lynx_local_46/1» _0
    Erlang.maps.«from_list/1» _6

#lynx_pure
  def «map_to_map/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _9 ←
      do
        let _2 ←
          do
            let lynxGenerated0 ← Erlang.erts_internal.«mc_iterator/1» _0
            match lynxGenerated0 with
              | Lynx.Term.nil =>
                Lynx.Result.error
                  (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _0]))
              | _3 => pure _3
        «lynx_local_52/1» _2
    Erlang.maps.«from_list/1» _9

#lynx_pure
  def «comprehension_list_map/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_24/2» _0 _1

#lynx_pure
  def «comprehension_map_list/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result := do
    let _14 ←
      do
        let _3 ←
          do
            let lynxGenerated0 ← Erlang.erts_internal.«mc_iterator/1» _0
            match lynxGenerated0 with
              | Lynx.Term.nil =>
                Lynx.Result.error
                  (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _0]))
              | _4 => pure _4
        «lynx_local_34/2» _3 _1
    Erlang.maps.«from_list/1» _14

#lynx_pure
  def «comprehension_filtered_maps/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_21/2» _0 _1

#lynx_pure
  def «binary_generator/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_3/1» _0

#lynx_pure
  def «bits_generator/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_17/1» _0

#lynx_pure
  def «binary_generator_strict/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_5/1» _0

#lynx_pure
  def «utf8_generator/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_62/1» _0

#lynx_pure
  def «sized_generator/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_60/2» _1 _0

#lynx_pure
  def «zero_generator/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_64/1» _0

#lynx_pure
  def «binary_comprehension/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _1 ← pure (Lynx.Term.bitstring ⟨#[]⟩ 0 (by decide))
    «lynx_local_1/2» _0 _1

#lynx_pure
  def «binary_to_binary/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _1 ← pure (Lynx.Term.bitstring ⟨#[]⟩ 0 (by decide))
    «lynx_local_13/2» _0 _1

#lynx_pure
  def «binary_nested/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_10/2» _0 _1

#lynx_pure
  def «binary_zip/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_15/2» _0 _1

#lynx_pure
  def «binary_list/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_7/2» _0 _1

#lynx_pure
  def «comprehension_nested/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_41/2» _1 _0

end

end Erlang.named_locals
