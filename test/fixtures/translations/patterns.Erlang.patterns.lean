module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.patterns

#lynx_pure
  def «grouped/1» (_0 : Lynx.Term) : Lynx.Result :=
    match _0 with
    | Lynx.Term.atom "a" => pure (Lynx.Term.atom "first")
    | Lynx.Term.atom "b" => pure (Lynx.Term.atom "second")
    | _ =>
      (fun lynxMatchNext =>
          match _0 with
          | Lynx.Term.cons (Lynx.Term.atom "c") vX =>
            Lynx.Result.tryWith (Erlang.erlang.«is_integer/1» vX)
              (fun lynxGuardValue =>
                match lynxGuardValue with
                | Lynx.Term.atom "true" => pure (Lynx.Term.atom "guarded")
                | _ => lynxMatchNext ())
              (fun _ => lynxMatchNext ())
          | _ => lynxMatchNext ())
        (fun (_ : Unit) =>
          match _0 with
          | Lynx.Term.cons (Lynx.Term.atom "c") _2 => pure (Lynx.Term.atom "rejected")
          | _3 => pure (Lynx.Term.atom "other"))

end Erlang.patterns
