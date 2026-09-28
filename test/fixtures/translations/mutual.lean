module

public import Lynx

namespace Erlang.mutual

#lynx_pure
  mutual
    public def «even/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.atom "true")
      | Lynx.Term.cons _2 vXs => «odd/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    public def «odd/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.atom "false")
      | Lynx.Term.cons _2 vXs => «even/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  mutual
    public def «first/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
      | Lynx.Term.cons _2 vXs => «second/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    public def «second/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 1)
      | Lynx.Term.cons _2 vXs => «third/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    public def «third/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 2)
      | Lynx.Term.cons _2 vXs => «first/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  public def «identity/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.ok _0

end Erlang.mutual
