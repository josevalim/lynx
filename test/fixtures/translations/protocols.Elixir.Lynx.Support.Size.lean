module

public import Lynx
import Lynx.Runner.Elab
public import Elixir.Lynx.Support.Size.Integer
public import Elixir.Lynx.Support.Size.List
public import Elixir.Lynx.Support.Size.Lynx.Support.Point
public import Elixir.Lynx.Support.Size.Map
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Elixir.Lynx.Support.Size

section

set_option «match».ignoreUnusedAlts true

def «impl_for/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | Lynx.Term.nil => pure (Lynx.Term.atom "Elixir.Lynx.Support.Size.List")
  | Lynx.Term.cons _v_Head _v_Tail => pure (Lynx.Term.atom "Elixir.Lynx.Support.Size.List")
  | vOther@(Lynx.Term.map _) =>
    (fun {lynxValue : Type}
          (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
          (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
        lynxBody lynxNext)
      (fun lynxLabel_map_group_19 =>
        (fun {lynxValue : Type}
              (lynxBody :
                (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
              (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match _0 with
            | lynxMap30 =>
              match (Lynx.Term.getMapKeys [Lynx.Term.atom "__struct__"] lynxMap30) with
              | [lynxMapGroup19_0] =>
                match lynxMapGroup19_0 with
                | Lynx.Term.atom "Elixir.Lynx.Support.Point" =>
                  pure (Lynx.Term.atom "Elixir.Lynx.Support.Size.Lynx.Support.Point")
                | vStruct@(Lynx.Term.atom _) => pure (Lynx.Term.atom "nil")
                | _ => lynxLabel_map_group_19 ()
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            match _0 with
            | _ => lynxLabel_map_group_19 ()))
      (fun (_ : Unit) =>
        match _0 with
        | vMap => pure (Lynx.Term.atom "Elixir.Lynx.Support.Size.Map"))
  | vOther@(Lynx.Term.integer _) => pure (Lynx.Term.atom "Elixir.Lynx.Support.Size.Integer")
  | vOther => pure (Lynx.Term.atom "nil")

def «impl_for!/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let lynxGenerated0 ← «impl_for/1» _0
  (match lynxGenerated0 with
    | Lynx.Term.atom "nil" =>
      Except.error
        (Lynx.Exception.error
          (Lynx.Term.map
            [(Lynx.Term.atom "description", Lynx.Term.bitstring ⟨#[]⟩ 0 (by decide)),
              (Lynx.Term.atom "value", _0),
              (Lynx.Term.atom "protocol", Lynx.Term.atom "Elixir.Lynx.Support.Size"),
              (Lynx.Term.atom "__exception__", Lynx.Term.atom "true"),
              (Lynx.Term.atom "__struct__", Lynx.Term.atom "Elixir.Protocol.UndefinedError")]))
    | vImpl => pure vImpl)

def «size/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let lynxGenerated0 ← «impl_for!/1» _0
  (match lynxGenerated0 with
    | Lynx.Term.atom "Elixir.Lynx.Support.Size.Integer" =>
      Elixir.Lynx.Support.Size.Integer.«size/1» _0
    | Lynx.Term.atom "Elixir.Lynx.Support.Size.List" => Elixir.Lynx.Support.Size.List.«size/1» _0
    | Lynx.Term.atom "Elixir.Lynx.Support.Size.Lynx.Support.Point" =>
      Elixir.Lynx.Support.Size.Lynx.Support.Point.«size/1» _0
    | Lynx.Term.atom "Elixir.Lynx.Support.Size.Map" => Elixir.Lynx.Support.Size.Map.«size/1» _0
    | vImpl =>
      Except.error (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "case_clause", vImpl])))

end

end Elixir.Lynx.Support.Size
