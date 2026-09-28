module

import Lynx

#lynx_pure
  mutual
    def even_1 (v0 : Lynx.Term) : Lynx.Result :=
      match v0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.atom "true")
      | Lynx.Term.cons v2 v_Xs => odd_1 v_Xs
      | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def odd_1 (v0 : Lynx.Term) : Lynx.Result :=
      match v0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.atom "false")
      | Lynx.Term.cons v2 v_Xs => even_1 v_Xs
      | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  mutual
    def first_1 (v0 : Lynx.Term) : Lynx.Result :=
      match v0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 0)
      | Lynx.Term.cons v2 v_Xs => second_1 v_Xs
      | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def second_1 (v0 : Lynx.Term) : Lynx.Result :=
      match v0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 1)
      | Lynx.Term.cons v2 v_Xs => third_1 v_Xs
      | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def third_1 (v0 : Lynx.Term) : Lynx.Result :=
      match v0 with
      | Lynx.Term.nil => Lynx.Result.ok (Lynx.Term.integer 2)
      | Lynx.Term.cons v2 v_Xs => first_1 v_Xs
      | _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  def identity_1 (v0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.ok v0
