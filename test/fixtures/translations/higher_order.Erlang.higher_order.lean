module

public import Lynx
public import Lynx.Modules.Erlang.erlang
public import Lynx.Modules.Erlang.lists

@[expose] public section

namespace Erlang.higher_order

section

set_option «match».ignoreUnusedAlts true

def «map/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
  match _0, _1 with
  | Lynx.Term.nil, _v_F => pure Lynx.Term.nil
  | Lynx.Term.cons vHead vTail, vF => do
    let _3 ← Lynx.Term.apply vF #[vHead]
    let _2 ← «map/2» vTail vF
    pure (Lynx.Term.cons _3 _2)
  | _5, _4 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))

#lynx_pure
  def «proper_list/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.nil => pure (Lynx.Term.atom "true")
    | Lynx.Term.cons _2 vTail => «proper_list/1» vTail
    | _3 => pure (Lynx.Term.atom "false")

#lynx_pure
  def «$lynx_fun_0/1» (_6 : Lynx.Term) : Lynx.Result :=
    pure _6

#lynx_pure
  def «$lynx_fun_1/1» (_3 : Lynx.Term) : Lynx.Result :=
    pure (Lynx.Term.tuple #[_3])

#lynx_pure
  def «map_returns_list_requires/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result := do
    let lynxGenerated0 ← «proper_list/1» _0
    match lynxGenerated0 with
      | Lynx.Term.atom "true" => do
        let _8 ← pure (Lynx.Term.function 0 1 #[])
        let _5 ← pure (Lynx.Term.function 1 1 #[])
        Erlang.lists.«member/2» _1 (Lynx.Term.cons _8 (Lynx.Term.cons _5 Lynx.Term.nil))
      | Lynx.Term.atom "false" => pure (Lynx.Term.atom "false")
      | _2 =>
        Lynx.Result.error (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "badarg", _2]))

def «map_returns_list_ensures/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result := do
  let _2 ← «map/2» _0 _1
  Erlang.erlang.«is_list/1» _2

end

end Erlang.higher_order
