module

public import Lynx
public import Lynx.Modules.Erlang.erlang

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
  def «lynx_local_4/2» (_8 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result :=
    match _8 with
    | Lynx.Term.cons vX _7 => do
      let _10 ← «lynx_local_4/2» _7 _0
      pure (Lynx.Term.cons (Lynx.Term.tuple #[_0, vX]) _10)
    | Lynx.Term.cons _6 _7 => «lynx_local_4/2» _7 _0
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _9 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _9]))

def «named/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result := do
  let vF ← pure (Lynx.Term.function 0 1 #[_0])
  Lynx.Term.apply vF #[_1]

def «lynx_local_6/2» (_3 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result := do
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
  def «lynx_local_9/0» : Lynx.Result :=
    pure (Lynx.Term.function 1 0 #[])

def «$lynx_fun_0/2» (_0 : Lynx.Term) (lynxGenerated0 : Lynx.Term) : Lynx.Result :=
  «lynx_local_6/2» lynxGenerated0 _0

#lynx_pure
  def «$lynx_fun_1/0» : Lynx.Result :=
    «lynx_local_9/0»

#lynx_pure
  def «comprehension_filtered/1» (_0 : Lynx.Term) : Lynx.Result :=
    «lynx_local_1/1» _0

#lynx_pure
  def «lynx_local_3/2» (_4 : Lynx.Term) (_0 : Lynx.Term) : Lynx.Result :=
    match _4 with
    | Lynx.Term.cons vList _3 => do
      let _11 ← «lynx_local_4/2» vList _0
      let _12 ← «lynx_local_3/2» _3 _0
      pure (Lynx.Term.cons _11 _12)
    | Lynx.Term.cons _2 _3 => «lynx_local_3/2» _3 _0
    | Lynx.Term.nil => pure Lynx.Term.nil
    | _5 =>
      Lynx.Result.error
        (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "bad_generator", _5]))

#lynx_pure
  def «comprehension_nested/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    «lynx_local_3/2» _1 _0

end

end Erlang.named_locals
