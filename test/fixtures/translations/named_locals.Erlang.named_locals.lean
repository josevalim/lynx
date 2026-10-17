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
  def «lynx_local_1/1» (_3 : Lynx.Term) : Lynx.Result :=
    match _3 with
    | Lynx.Term.cons («v@r0»@(Lynx.Term.tuple ⟨[vK@(Lynx.Term.atom _), vV]⟩)) _2 => do
      let _5 ← «lynx_local_1/1» _2
      pure (Lynx.Term.cons «v@r0» _5)
    | Lynx.Term.cons _1 _2 => «lynx_local_1/1» _2
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _4 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _4]))

#lynx_pure
  def «lynx_local_24/2» (_8 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result :=
    match _8 with
    | Lynx.Term.cons vX _7 => do
      let _10 ← «lynx_local_24/2» _7 _0
      pure (Lynx.Term.cons (Lynx.Term.tuple #[_0, vX]) _10)
    | Lynx.Term.cons _6 _7 => «lynx_local_24/2» _7 _0
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _9 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _9]))

#lynx_pure
  mutual
    def «lynx_local_9/2» (_6 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      match _6 with
      | Lynx.Term.cons vX _3 => «lynx_local_10/4» _1 _1 _3 vX
      | Lynx.Term.cons _2 _3 => «lynx_local_9/2» _3 _1
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _7 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))
    def «lynx_local_10/4» (_8 : Lynx.Term) (_1 : Lynx.Term) (_3 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      match _8 with
      | Lynx.Term.cons vY _5 => do
        let _10 ← «lynx_local_10/4» _5 _1 _3 vX
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _10)
      | Lynx.Term.cons _4 _5 => «lynx_local_10/4» _5 _1 _3 vX
      | Lynx.Term.nil => «lynx_local_9/2» _3 _1
      | _9 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _9]))
  end

#lynx_pure
  mutual
    def «lynx_local_12/3» (_9 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
      match _9 with
      | Lynx.Term.cons vX _4 => «lynx_local_13/5» _1 _1 _2 _4 vX
      | Lynx.Term.cons _3 _4 => «lynx_local_12/3» _4 _1 _2
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    termination_by (sizeOf✝ _9, (0, 0))
    def «lynx_local_13/5» (_11 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (vX : Lynx.Term) : Lynx.Result :=
      match _11 with
      | Lynx.Term.cons vY _6 => «lynx_local_14/7» _2 _1 _2 _4 _6 vX vY
      | Lynx.Term.cons _5 _6 => «lynx_local_13/5» _6 _1 _2 _4 vX
      | Lynx.Term.nil => «lynx_local_12/3» _4 _1 _2
      | _12 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12]))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _11, 0))
    def «lynx_local_14/7» (_13 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (_6 : Lynx.Term) (vX : Lynx.Term) (vY : Lynx.Term) : Lynx.Result :=
      match _13 with
      | Lynx.Term.cons vZ _8 => do
        let _15 ← «lynx_local_14/7» _8 _1 _2 _4 _6 vX vY
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY, vZ]) _15)
      | Lynx.Term.cons _7 _8 => «lynx_local_14/7» _8 _1 _2 _4 _6 vX vY
      | Lynx.Term.nil => «lynx_local_13/5» _6 _1 _2 _4 vX
      | _14 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _14]))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _6, 1 + sizeOf✝ _13))
  end

#lynx_pure
  mutual
    def «lynx_local_19/3» (_12 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
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
        «lynx_local_20/5» _6 _1 _2 _4 vX
      | Lynx.Term.cons _3 _4 => «lynx_local_19/3» _4 _1 _2
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _13 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _13]))
    termination_by (sizeOf✝ _12, (0, 0))
    def «lynx_local_20/5» (_14 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (vX : Lynx.Term) : Lynx.Result :=
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          match _14 with
          | Lynx.Term.tuple ⟨[vK, vV, _7]⟩ =>
            Lynx.Result.guard (Erlang.erlang.«>/2» vV vX)
              (fun _ => «lynx_local_21/7» _2 _1 _2 _4 _7 vK vX) lynxMatchNext
          | _ => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _14 with
          | Lynx.Term.tuple ⟨[_9, _8, _7]⟩ => «lynx_local_20/5» _7 _1 _2 _4 vX
          | Lynx.Term.atom "none" => «lynx_local_19/3» _4 _1 _2
          | «v@r0»@(Lynx.Term.cons _9 _8) => do
            let _7 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
            «lynx_local_20/5» _7 _1 _2 _4 vX
          | _15 =>
            Lynx.Result.error
              (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _15])))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _14, 0))
    def «lynx_local_21/7» (_16 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) (_4 : Lynx.Term)
        (_7 : Lynx.Term) (vK : Lynx.Term) (vX : Lynx.Term) : Lynx.Result :=
      match _16 with
      | Lynx.Term.cons vY _11 => do
        let _18 ← «lynx_local_21/7» _11 _1 _2 _4 _7 vK vX
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vK, vY]) _18)
      | Lynx.Term.cons _10 _11 => «lynx_local_21/7» _11 _1 _2 _4 _7 vK vX
      | Lynx.Term.nil => «lynx_local_20/5» _7 _1 _2 _4 vX
      | _17 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _17]))
    termination_by (sizeOf✝ _4, (1 + sizeOf✝ _7, 1 + sizeOf✝ _16))
  end

#lynx_pure
  def «lynx_local_26/2» (_7 : Lynx.Term) (_6 : Lynx.Term) : Lynx.Result :=
    match _7, _6 with
    | Lynx.Term.cons vX _3, Lynx.Term.cons vY _5 => do
      let _10 ← «lynx_local_26/2» _3 _5
      pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vY]) _10)
    | Lynx.Term.cons _2 _3, Lynx.Term.cons _4 _5 => «lynx_local_26/2» _3 _5
    | Lynx.Term.nil, Lynx.Term.nil => pure Lynx.Term.nil
    | _9, _8 =>
      Lynx.Result.error
        (Lynx.Exception.error
          (Lynx.Term.tuple #[Lynx.Term.atom "bad_generators", Lynx.Term.tuple #[_9, _8]]))

#lynx_pure
  def «lynx_local_30/1» (_6 : Lynx.Term) : Lynx.Result :=
    match _6 with
    | Lynx.Term.tuple ⟨[vK, vV, _3]⟩ => do
      let _8 ← «lynx_local_30/1» _3
      pure (Lynx.Term.cons (Lynx.Term.tuple #[vK, vV]) _8)
    | Lynx.Term.tuple ⟨[_5, _4, _3]⟩ => «lynx_local_30/1» _3
    | Lynx.Term.atom "none" => pure Lynx.Term.nil
    | «v@r0»@(Lynx.Term.cons _5 _4) => do
      let _3 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
      «lynx_local_30/1» _3
    | _7 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))

#lynx_pure
  def «lynx_local_32/1» (_6 : Lynx.Term) : Lynx.Result :=
    match _6 with
    | Lynx.Term.tuple ⟨[vK, Lynx.Term.atom "ok", _3]⟩ => do
      let _8 ← «lynx_local_32/1» _3
      pure (Lynx.Term.cons vK _8)
    | Lynx.Term.tuple ⟨[_5, _4, _3]⟩ =>
      Lynx.Result.error
        (Lynx.Exception.error
          (Lynx.Term.tuple #[Lynx.Term.atom "badmatch", Lynx.Term.tuple #[_5, _4]]))
    | Lynx.Term.atom "none" => pure Lynx.Term.nil
    | «v@r0»@(Lynx.Term.cons _5 _4) => do
      let _3 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
      «lynx_local_32/1» _3
    | _7 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))

#lynx_pure
  def «lynx_local_28/1» (_3 : Lynx.Term) : Lynx.Result :=
    match _3 with
    | Lynx.Term.cons («v@r0»@(Lynx.Term.tuple ⟨[vK, vV]⟩)) _2 => do
      let _5 ← «lynx_local_28/1» _2
      pure (Lynx.Term.cons «v@r0» _5)
    | Lynx.Term.cons _1 _2 => «lynx_local_28/1» _2
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _4 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _4]))

#lynx_pure
  def «lynx_local_34/1» (_6 : Lynx.Term) : Lynx.Result :=
    match _6 with
    | Lynx.Term.tuple ⟨[vK, vV, _3]⟩ => do
      let _8 ← «lynx_local_34/1» _3
      pure (Lynx.Term.cons (Lynx.Term.tuple #[vV, vK]) _8)
    | Lynx.Term.tuple ⟨[_5, _4, _3]⟩ => «lynx_local_34/1» _3
    | Lynx.Term.atom "none" => pure Lynx.Term.nil
    | «v@r0»@(Lynx.Term.cons _5 _4) => do
      let _3 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
      «lynx_local_34/1» _3
    | _7 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _7]))

#lynx_pure
  mutual
    def «lynx_local_6/2» (_9 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
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
        «lynx_local_7/4» _5 _1 _3 vX
      | Lynx.Term.cons _2 _3 => «lynx_local_6/2» _3 _1
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    def «lynx_local_7/4» (_11 : Lynx.Term) (_1 : Lynx.Term) (_3 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      match _11 with
      | Lynx.Term.tuple ⟨[vK, _16, _6]⟩ => do
        let _13 ← «lynx_local_7/4» _6 _1 _3 vX
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vX, vK]) _13)
      | Lynx.Term.tuple ⟨[_8, _7, _6]⟩ => «lynx_local_7/4» _6 _1 _3 vX
      | Lynx.Term.atom "none" => «lynx_local_6/2» _3 _1
      | «v@r0»@(Lynx.Term.cons _8 _7) => do
        let _6 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
        «lynx_local_7/4» _6 _1 _3 vX
      | _12 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12]))
  end

#lynx_pure
  mutual
    def «lynx_local_16/2» (_9 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
      match _9 with
      | Lynx.Term.tuple ⟨[vK, vV, _4]⟩ => «lynx_local_17/5» _1 _1 _4 vK vV
      | Lynx.Term.tuple ⟨[_6, _5, _4]⟩ => «lynx_local_16/2» _4 _1
      | Lynx.Term.atom "none" => pure Lynx.Term.nil
      | «v@r0»@(Lynx.Term.cons _6 _5) => do
        let _4 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
        «lynx_local_16/2» _4 _1
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    def «lynx_local_17/5» (_11 : Lynx.Term) (_1 : Lynx.Term) (_4 : Lynx.Term) (vK : Lynx.Term)
        (vV : Lynx.Term) : Lynx.Result :=
      match _11 with
      | Lynx.Term.cons vX _8 => do
        let _13 ← «lynx_local_17/5» _8 _1 _4 vK vV
        pure (Lynx.Term.cons (Lynx.Term.tuple #[Lynx.Term.tuple #[vK, vX], vV]) _13)
      | Lynx.Term.cons _7 _8 => «lynx_local_17/5» _8 _1 _4 vK vV
      | Lynx.Term.nil => «lynx_local_16/2» _4 _1
      | _12 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12]))
  end

#lynx_pure
  mutual
    def «lynx_local_3/2» (_9 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
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
        «lynx_local_4/4» _5 _1 _3 vX
      | Lynx.Term.cons _2 _3 => «lynx_local_3/2» _3 _1
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _10 =>
        Lynx.Result.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _10]))
    def «lynx_local_4/4» (_11 : Lynx.Term) (_1 : Lynx.Term) (_3 : Lynx.Term) (vX : Lynx.Term) :
        Lynx.Result :=
      (fun {lynxValue : Type} (lynxBody : (Unit → Lynx.Result lynxValue) → Lynx.Result lynxValue)
            (lynxNext : Unit → Lynx.Result lynxValue) =>
          lynxBody lynxNext)
        (fun lynxMatchNext =>
          match _11 with
          | Lynx.Term.tuple ⟨[vK, vV, _6]⟩ =>
            Lynx.Result.guard (Erlang.erlang.«=:=/2» vK vX)
              (fun _ => do
                let _13 ← «lynx_local_4/4» _6 _1 _3 vX
                pure (Lynx.Term.cons vV _13))
              lynxMatchNext
          | _ => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _11 with
          | Lynx.Term.tuple ⟨[_8, _7, _6]⟩ => «lynx_local_4/4» _6 _1 _3 vX
          | Lynx.Term.atom "none" => «lynx_local_3/2» _3 _1
          | «v@r0»@(Lynx.Term.cons _8 _7) => do
            let _6 ← Erlang.erts_internal.«mc_refill/1» «v@r0»
            «lynx_local_4/4» _6 _1 _3 vX
          | _12 =>
            Lynx.Result.error
              (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _12])))
  end

def «named/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result := do
  let vF ← pure (Lynx.Term.function 0 1 #[_0])
  Lynx.Term.apply vF #[_1]

def «lynx_local_36/2» (_3 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result := do
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
  def «lynx_local_39/0» : Lynx.Result :=
    pure (Lynx.Term.function 1 0 #[])

def «$lynx_fun_0/2» (_0 : Lynx.Term) (lynxGenerated0 : Lynx.Term) : Lynx.Result :=
  «lynx_local_36/2» lynxGenerated0 _0

#lynx_pure
  def «$lynx_fun_1/0» : Lynx.Result :=
    «lynx_local_39/0»

#lynx_pure
  def «comprehension_filtered/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_1/1» _0

#lynx_pure
  def «lynx_local_23/2» (_4 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result :=
    match _4 with
    | Lynx.Term.cons vList _3 => do
      let _11 ← «lynx_local_24/2» vList _0
      let _12 ← «lynx_local_23/2» _3 _0
      pure (Lynx.Term.cons _11 _12)
    | Lynx.Term.cons _2 _3 => «lynx_local_23/2» _3 _0
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _5 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _5]))

#lynx_pure
  def «comprehension_lists/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_9/2» _0 _1

#lynx_pure
  def «comprehension_lists3/3» (_0 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
    «lynx_local_12/3» _0 _1 _2

#lynx_pure
  def «comprehension_mixed3/3» (_0 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
    «lynx_local_19/3» _0 _1 _2

#lynx_pure
  def «comprehension_zip/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_26/2» _0 _1

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
    «lynx_local_30/1» _2

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
    «lynx_local_32/1» _2

#lynx_pure
  def «map_comprehension/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _6 ← «lynx_local_28/1» _0
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
        «lynx_local_34/1» _2
    Erlang.maps.«from_list/1» _9

#lynx_pure
  def «comprehension_list_map/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_6/2» _0 _1

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
        «lynx_local_16/2» _3 _1
    Erlang.maps.«from_list/1» _14

#lynx_pure
  def «comprehension_filtered_maps/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_3/2» _0 _1

#lynx_pure
  def «comprehension_nested/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_23/2» _1 _0

end

end Erlang.named_locals
