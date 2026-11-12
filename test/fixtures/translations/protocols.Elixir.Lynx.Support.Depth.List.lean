module

public import Lynx
import Lynx.Runner.Elab
public import Elixir.Lynx.Support.Depth.Integer
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Elixir.Lynx.Support.Depth.List

section

set_option «match».ignoreUnusedAlts true

def «Lynx.Support.Depth.impl_for/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | Lynx.Term.nil => pure (Lynx.Term.atom "Elixir.Lynx.Support.Depth.List")
  | Lynx.Term.cons _v_Head _v_Tail => pure (Lynx.Term.atom "Elixir.Lynx.Support.Depth.List")
  | vOther@(Lynx.Term.integer _) => pure (Lynx.Term.atom "Elixir.Lynx.Support.Depth.Integer")
  | vOther => pure (Lynx.Term.atom "nil")

def «Lynx.Support.Depth.impl_for!/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let lynxGenerated0 ← «Lynx.Support.Depth.impl_for/1» _0
  (match lynxGenerated0 with
    | Lynx.Term.atom "nil" =>
      Except.error
        (Lynx.Exception.error
          (Lynx.Term.map
            [(Lynx.Term.atom "description", Lynx.Term.bitstring ⟨#[]⟩ 0 (by decide)),
              (Lynx.Term.atom "value", _0),
              (Lynx.Term.atom "protocol", Lynx.Term.atom "Elixir.Lynx.Support.Depth"),
              (Lynx.Term.atom "__exception__", Lynx.Term.atom "true"),
              (Lynx.Term.atom "__struct__", Lynx.Term.atom "Elixir.Protocol.UndefinedError")]))
    | vImpl => pure vImpl)

mutual
  def «Lynx.Support.Depth.depth/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
    let lynxGenerated0 ← «Lynx.Support.Depth.impl_for!/1» _0
    (match lynxGenerated0 with
      | Lynx.Term.atom "Elixir.Lynx.Support.Depth.Integer" =>
        Elixir.Lynx.Support.Depth.Integer.«depth/1» _0
      | Lynx.Term.atom "Elixir.Lynx.Support.Depth.List" => «depth/1» _0
      | vImpl =>
        Except.error
          (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "case_clause", vImpl])))
  termination_by (sizeOf _0, 1)
  def «depth/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
    match _0 with
    | Lynx.Term.nil => pure (Lynx.Term.integer 1)
    | Lynx.Term.cons «_v_head@1» «_v_tail@1» => do
      let _2 ← «Lynx.Support.Depth.depth/1» «_v_head@1»
      let _3 ← Erlang.erlang.«+/2» _2 (Lynx.Term.integer 1)
      let _1 ← «depth/1» «_v_tail@1»
      Erlang.erlang.«max/2» _3 _1
    | _4 => Except.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  termination_by (sizeOf _0, 0)
end

end

end Elixir.Lynx.Support.Depth.List
