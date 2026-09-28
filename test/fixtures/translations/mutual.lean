module

import Lynx

namespace «mutual»

#lynx_pure
  mutual
    public def even_1 (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.atom "true")
      | Lynx.Term.cons _2 vXs => odd_1 vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    public def odd_1 (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.atom "false")
      | Lynx.Term.cons _2 vXs => even_1 vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  mutual
    public def first_1 (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
      | Lynx.Term.cons _2 vXs => second_1 vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    public def second_1 (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 1)
      | Lynx.Term.cons _2 vXs => third_1 vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    public def third_1 (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 2)
      | Lynx.Term.cons _2 vXs => first_1 vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  public def identity_1 (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.ok _0

end «mutual»
