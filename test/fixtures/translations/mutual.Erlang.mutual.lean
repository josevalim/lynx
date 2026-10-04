module

public import Lynx

@[expose] public section

namespace Erlang.mutual

#lynx_pure
  mutual
    def «odd/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.atom "false")
      | Lynx.Term.cons _2 vXs => «even/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def «even/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.atom "true")
      | Lynx.Term.cons _2 vXs => «odd/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  mutual
    def «first/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.integer 0)
      | Lynx.Term.cons _2 vXs => «second/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def «second/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.integer 1)
      | Lynx.Term.cons _2 vXs => «third/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def «third/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.integer 2)
      | Lynx.Term.cons _2 vXs => «first/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  def «identity/1» (_0 : Lynx.Term) : Lynx.Result :=
    pure _0

end Erlang.mutual
