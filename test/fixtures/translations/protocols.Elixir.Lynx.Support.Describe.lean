module

public import Lynx
import Lynx.Runner.Elab
public import Elixir.Lynx.Support.Describe.Any
public import Elixir.Lynx.Support.Describe.Atom
public import Elixir.Lynx.Support.Describe.Lynx.Support.Tagged
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Elixir.Lynx.Support.Describe

section

set_option «match».ignoreUnusedAlts true

def «impl_for/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  match _0 with
  | vOther@(Lynx.Term.atom _) => pure (Lynx.Term.atom "Elixir.Lynx.Support.Describe.Atom")
  | vOther@(Lynx.Term.map _) =>
    (fun {lynxValue : Type}
          (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
          (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
        lynxBody lynxNext)
      (fun lynxLabel_map_group_15 =>
        (fun {lynxValue : Type}
              (lynxBody :
                (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
              (lynxNext : Unit → Except Lynx.Exception lynxValue) =>
            lynxBody lynxNext)
          (fun lynxMatchNext =>
            match _0 with
            | lynxMap26 =>
              match (Lynx.Term.getMapKeys [Lynx.Term.atom "__struct__"] lynxMap26) with
              | [lynxMapGroup15_0] =>
                match lynxMapGroup15_0 with
                | Lynx.Term.atom "Elixir.Lynx.Support.Tagged" =>
                  pure (Lynx.Term.atom "Elixir.Lynx.Support.Describe.Lynx.Support.Tagged")
                | vStruct@(Lynx.Term.atom _) =>
                  pure (Lynx.Term.atom "Elixir.Lynx.Support.Describe.Any")
                | _ => lynxLabel_map_group_15 ()
              | _ => lynxMatchNext ())
          (fun (_ : Unit) =>
            match _0 with
            | _ => lynxLabel_map_group_15 ()))
      (fun (_ : Unit) =>
        match _0 with
        | vMap => pure (Lynx.Term.atom "Elixir.Lynx.Support.Describe.Any"))
  | vOther => pure (Lynx.Term.atom "Elixir.Lynx.Support.Describe.Any")

def «impl_for!/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  «impl_for/1» _0

def «describe/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term := do
  let lynxGenerated0 ← «impl_for!/1» _0
  (match lynxGenerated0 with
    | Lynx.Term.atom "Elixir.Lynx.Support.Describe.Any" =>
      Elixir.Lynx.Support.Describe.Any.«describe/2» _0 _1
    | Lynx.Term.atom "Elixir.Lynx.Support.Describe.Atom" =>
      Elixir.Lynx.Support.Describe.Atom.«describe/2» _0 _1
    | Lynx.Term.atom "Elixir.Lynx.Support.Describe.Lynx.Support.Tagged" =>
      Elixir.Lynx.Support.Describe.Lynx.Support.Tagged.«describe/2» _0 _1
    | vImpl =>
      Except.error (Lynx.Exception.error (Lynx.Term.tuple #[Lynx.Term.atom "case_clause", vImpl])))

end

end Elixir.Lynx.Support.Describe
